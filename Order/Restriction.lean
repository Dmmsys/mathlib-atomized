/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Data.Finset.Update
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Restriction of a function indexed by a preorder

Given a preorder `α` and dependent function `f : (i : α) → π i` and `a : α`, one might want
to consider the restriction of `f` to elements `≤ a`.
This is defined in this file as `Preorder.restrictLe a f`.
Similarly, if we have `a b : α`, `hab : a ≤ b` and `f : (i : ↑(Set.Iic b)) → π ↑i`,
one might want to restrict it to elements `≤ a`.
This is defined in this file as `Preorder.restrictLe₂ hab f`.

We also provide versions where the intervals are seen as finite sets, see `Preorder.frestrictLe`
and `Preorder.frestrictLe₂`.

## Main definitions
* `Preorder.restrictLe a f`: Restricts the function `f` to the variables indexed by elements `≤ a`.
-/

@[expose] public section

namespace Preorder

variable {α : Type*} [Preorder α] {π : α -> Type*}

section Set

open Set

/--
Definition of `restrictLe` / `restrictLe` 的定义

English:
definition restrictLe
  signature: (a : α)
  body: (Iic a).domRestrict (π := π)

@[simp]

中文:
定义 restrictLe
  签名: (a : α)
  定义体: (Iic a).domRestrict (π := π)

@[simp]

Depends on / 依赖: domRestrict
-/
def restrictLe (a : α) := (Iic a).domRestrict (π := π)

@[simp]
/--
lemma `restrictLe_apply` / 引理 `restrictLe_apply`

English:
lemma restrictLe_apply
  given: (a : α) (f : (a : α) -> π a) (i : Iic a)
  statement: restrictLe a f i = f i
  proof: rfl

中文:
引理 restrictLe_apply
  条件: (a : α) (f : (a : α) -> π a) (i : Iic a)
  结论: restrictLe a f i = f i
  证明: rfl
-/
lemma restrictLe_apply (a : α) (f : (a : α) -> π a) (i : Iic a) : restrictLe a f i = f i := rfl

/--
Definition of `restrictLe₂` / `restrictLe₂` 的定义

English:
definition restrictLe₂
  signature: {a b : α} (hab : a <= b)
  body: Set.domRestrict₂ (π := π) (Iic_subset_Iic.2 hab)

@[simp]

中文:
定义 restrictLe₂
  签名: {a b : α} (hab : a <= b)
  定义体: Set.domRestrict₂ (π := π) (Iic_subset_Iic.2 hab)

@[simp]

Depends on / 依赖: Iic_subset_Iic, Set.domRestrict
-/
def restrictLe₂ {a b : α} (hab : a <= b) := Set.domRestrict₂ (π := π) (Iic_subset_Iic.2 hab)

@[simp]
/--
lemma `restrictLe₂_apply` / 引理 `restrictLe₂_apply`

English:
lemma restrictLe₂_apply
  given: {a b : α} (hab : a <= b) (f : (i : Iic b) -> π i) (i : Iic a)
  proof: rfl

中文:
引理 restrictLe₂_apply
  条件: {a b : α} (hab : a <= b) (f : (i : Iic b) -> π i) (i : Iic a)
  证明: rfl
-/
lemma restrictLe₂_apply {a b : α} (hab : a <= b) (f : (i : Iic b) -> π i) (i : Iic a) :
    restrictLe₂ hab f i = f ⟨i.1, Iic_subset_Iic.2 hab i.2⟩ := rfl

/--
theorem `restrictLe₂_comp_restrictLe` / 定理 `restrictLe₂_comp_restrictLe`

English:
theorem restrictLe₂_comp_restrictLe
  given: {a b : α} (hab : a <= b)
  proof: rfl

中文:
定理 restrictLe₂_comp_restrictLe
  条件: {a b : α} (hab : a <= b)
  证明: rfl

Depends on / 依赖: restrictLe
-/
theorem restrictLe₂_comp_restrictLe {a b : α} (hab : a <= b) :
    (restrictLe₂ (π := π) hab) ∘ (restrictLe b) = restrictLe a := rfl

/--
theorem `restrictLe₂_comp_restrictLe₂` / 定理 `restrictLe₂_comp_restrictLe₂`

English:
theorem restrictLe₂_comp_restrictLe₂
  given: {a b c : α} (hab : a <= b) (hbc : b <= c)
  proof: rfl

中文:
定理 restrictLe₂_comp_restrictLe₂
  条件: {a b c : α} (hab : a <= b) (hbc : b <= c)
  证明: rfl

Depends on / 依赖: hab.trans
-/
theorem restrictLe₂_comp_restrictLe₂ {a b c : α} (hab : a <= b) (hbc : b <= c) :
    (restrictLe₂ (π := π) hab) ∘ (restrictLe₂ hbc) = restrictLe₂ (hab.trans hbc) := rfl

/--
lemma `dependsOn_restrictLe` / 引理 `dependsOn_restrictLe`

English:
lemma dependsOn_restrictLe
  given: (a : α)
  statement: DependsOn (restrictLe (π := π) a) (Iic a)
  proof: (Iic a).dependsOn_domRestrict

中文:
引理 dependsOn_restrictLe
  条件: (a : α)
  结论: DependsOn (restrictLe (π := π) a) (Iic a)
  证明: (Iic a).dependsOn_domRestrict
-/
lemma dependsOn_restrictLe (a : α) : DependsOn (restrictLe (π := π) a) (Iic a) :=
  (Iic a).dependsOn_domRestrict

end Set

section Finset

variable [LocallyFiniteOrderBot α]

open Finset

/--
Definition of `frestrictLe` / `frestrictLe` 的定义

English:
definition frestrictLe
  signature: (a : α)
  body: (Iic a).restrict (π := π)

@[simp]

中文:
定义 frestrictLe
  签名: (a : α)
  定义体: (Iic a).restrict (π := π)

@[simp]

Depends on / 依赖: restrict
-/
def frestrictLe (a : α) := (Iic a).restrict (π := π)

@[simp]
/--
lemma `frestrictLe_apply` / 引理 `frestrictLe_apply`

English:
lemma frestrictLe_apply
  given: (a : α) (f : (a : α) -> π a) (i : Iic a)
  statement: frestrictLe a f i = f i
  proof: rfl

中文:
引理 frestrictLe_apply
  条件: (a : α) (f : (a : α) -> π a) (i : Iic a)
  结论: frestrictLe a f i = f i
  证明: rfl
-/
lemma frestrictLe_apply (a : α) (f : (a : α) -> π a) (i : Iic a) : frestrictLe a f i = f i := rfl

/--
Definition of `frestrictLe₂` / `frestrictLe₂` 的定义

English:
definition frestrictLe₂
  signature: {a b : α} (hab : a <= b)
  body: restrict₂ (π := π) (Iic_subset_Iic.2 hab)

@[simp]

中文:
定义 frestrictLe₂
  签名: {a b : α} (hab : a <= b)
  定义体: restrict₂ (π := π) (Iic_subset_Iic.2 hab)

@[simp]

Depends on / 依赖: Iic_subset_Iic
-/
def frestrictLe₂ {a b : α} (hab : a <= b) := restrict₂ (π := π) (Iic_subset_Iic.2 hab)

@[simp]
/--
lemma `frestrictLe₂_apply` / 引理 `frestrictLe₂_apply`

English:
lemma frestrictLe₂_apply
  given: {a b : α} (hab : a <= b) (f : (i : Iic b) -> π i) (i : Iic a)
  proof: rfl

中文:
引理 frestrictLe₂_apply
  条件: {a b : α} (hab : a <= b) (f : (i : Iic b) -> π i) (i : Iic a)
  证明: rfl
-/
lemma frestrictLe₂_apply {a b : α} (hab : a <= b) (f : (i : Iic b) -> π i) (i : Iic a) :
    frestrictLe₂ hab f i = f ⟨i.1, Iic_subset_Iic.2 hab i.2⟩ := rfl

/--
theorem `frestrictLe₂_comp_frestrictLe` / 定理 `frestrictLe₂_comp_frestrictLe`

English:
theorem frestrictLe₂_comp_frestrictLe
  given: {a b : α} (hab : a <= b)
  proof: rfl

中文:
定理 frestrictLe₂_comp_frestrictLe
  条件: {a b : α} (hab : a <= b)
  证明: rfl

Depends on / 依赖: frestrictLe
-/
theorem frestrictLe₂_comp_frestrictLe {a b : α} (hab : a <= b) :
    (frestrictLe₂ (π := π) hab) ∘ (frestrictLe b) = frestrictLe a := rfl

/--
theorem `frestrictLe₂_comp_frestrictLe₂` / 定理 `frestrictLe₂_comp_frestrictLe₂`

English:
theorem frestrictLe₂_comp_frestrictLe₂
  given: {a b c : α} (hab : a <= b) (hbc : b <= c)
  proof: rfl

中文:
定理 frestrictLe₂_comp_frestrictLe₂
  条件: {a b c : α} (hab : a <= b) (hbc : b <= c)
  证明: rfl

Depends on / 依赖: IsLocalization, IsLocalization.Away.mul, Localization, Localization.Away, algebraMap, hab.trans
-/
theorem frestrictLe₂_comp_frestrictLe₂ {a b c : α} (hab : a <= b) (hbc : b <= c) :
    (frestrictLe₂ (π := π) hab) ∘ (frestrictLe₂ hbc) = frestrictLe₂ (hab.trans hbc) := rfl

/--
theorem `piCongrLeft_comp_restrictLe` / 定理 `piCongrLeft_comp_restrictLe`

English:
theorem piCongrLeft_comp_restrictLe
  given: {a : α}
  proof: rfl

中文:
定理 piCongrLeft_comp_restrictLe
  条件: {a : α}
  证明: rfl

Depends on / 依赖: IsLocalization, IsLocalization.Away.mul, Localization, Localization.Away, algebraMap
-/
theorem piCongrLeft_comp_restrictLe {a : α} :
    ((Equiv.IicFinsetSet a).symm.piCongrLeft (fun i : Iic a => π i)) ∘ (restrictLe a) =
    frestrictLe a := rfl

/--
theorem `piCongrLeft_comp_frestrictLe` / 定理 `piCongrLeft_comp_frestrictLe`

English:
theorem piCongrLeft_comp_frestrictLe
  given: {a : α}
  proof: rfl

中文:
定理 piCongrLeft_comp_frestrictLe
  条件: {a : α}
  证明: rfl
-/
theorem piCongrLeft_comp_frestrictLe {a : α} :
    ((Equiv.IicFinsetSet a).piCongrLeft (fun i : Set.Iic a => π i)) ∘ (frestrictLe a) =
    restrictLe a := rfl

section updateFinset

open Function

variable [DecidableEq α]

/--
lemma `frestrictLe_updateFinset_of_le` / 引理 `frestrictLe_updateFinset_of_le`

English:
lemma frestrictLe_updateFinset_of_le
  given: {a b : α} (hab : a <= b) (x : Π c, π c) (y : Π c : Iic b, π c)
  proof: restrict_updateFinset_of_subset (Iic_subset_Iic.2 hab) ..

中文:
引理 frestrictLe_updateFinset_of_le
  条件: {a b : α} (hab : a <= b) (x : Π c, π c) (y : Π c : Iic b, π c)
  证明: restrict_updateFinset_of_subset (Iic_subset_Iic.2 hab) ..

Depends on / 依赖: Iic_subset_Iic, restrict_updateFinset_of_subset
-/
lemma frestrictLe_updateFinset_of_le {a b : α} (hab : a <= b) (x : Π c, π c) (y : Π c : Iic b, π c) :
    frestrictLe a (updateFinset x _ y) = frestrictLe₂ hab y :=
  restrict_updateFinset_of_subset (Iic_subset_Iic.2 hab) ..

/--
lemma `frestrictLe_updateFinset` / 引理 `frestrictLe_updateFinset`

English:
lemma frestrictLe_updateFinset
  given: {a : α} (x : Π a, π a) (y : Π b : Iic a, π b)
  proof: restrict_updateFinset ..

@[simp]

中文:
引理 frestrictLe_updateFinset
  条件: {a : α} (x : Π a, π a) (y : Π b : Iic a, π b)
  证明: restrict_updateFinset ..

@[simp]

Depends on / 依赖: restrict_updateFinset
-/
lemma frestrictLe_updateFinset {a : α} (x : Π a, π a) (y : Π b : Iic a, π b) :
    frestrictLe a (updateFinset x _ y) = y := restrict_updateFinset ..

@[simp]
/--
lemma `updateFinset_frestrictLe` / 引理 `updateFinset_frestrictLe`

English:
lemma updateFinset_frestrictLe
  given: (a : α) (x : Π a, π a)
  statement: updateFinset x _ (frestrictLe a x) = x
  proof: by
  simp [frestrictLe]

中文:
引理 updateFinset_frestrictLe
  条件: (a : α) (x : Π a, π a)
  结论: updateFinset x _ (frestrictLe a x) = x
  证明: by
  simp [frestrictLe]

Depends on / 依赖: frestrictLe
-/
lemma updateFinset_frestrictLe (a : α) (x : Π a, π a) : updateFinset x _ (frestrictLe a x) = x := by
  simp [frestrictLe]

end updateFinset

/--
lemma `dependsOn_frestrictLe` / 引理 `dependsOn_frestrictLe`

English:
lemma dependsOn_frestrictLe
  given: (a : α)
  statement: DependsOn (frestrictLe (π := π) a) (Set.Iic a)
  proof: coe_Iic a ▸ (Finset.Iic a).dependsOn_restrict

中文:
引理 dependsOn_frestrictLe
  条件: (a : α)
  结论: DependsOn (frestrictLe (π := π) a) (Set.Iic a)
  证明: coe_Iic a ▸ (Finset.Iic a).dependsOn_restrict

Depends on / 依赖: Set.Iic
-/
lemma dependsOn_frestrictLe (a : α) : DependsOn (frestrictLe (π := π) a) (Set.Iic a) :=
  coe_Iic a ▸ (Finset.Iic a).dependsOn_restrict

end Finset

end Preorder
