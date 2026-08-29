/-
Copyright (c) 2024 Ching-Tsun Chou, Chris Wong, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Chris Wong, Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Cast

/-!
# The Katona circle method

This file provides tooling to use the Katona circle method, which is double-counting ways to order
`n` elements on a circle under some condition.
-/

@[expose] public section

open Fintype Finset Nat

variable {X : Type*} [Fintype X]

variable (X) in
/--
Definition of `Numbering` / `Numbering` 的定义

English:
abbreviation Numbering
  signature: : Type _
  body: X ≃ Fin (card X)

中文:
缩写 Numbering
  签名: : Type _
  定义体: X ≃ Fin (card X)
-/
abbrev Numbering : Type _ := X ≃ Fin (card X)

/--
lemma `Fintype.card_numbering` / 引理 `Fintype.card_numbering`

English:
lemma Fintype.card_numbering
  given: [DecidableEq X]
  statement: card (Numbering X) = (card X)!
  proof: card_equiv (equivFin _)

中文:
引理 Fintype.card_numbering
  条件: [DecidableEq X]
  结论: card (Numbering X) = (card X)!
  证明: card_equiv (equivFin _)
-/
@[simp] lemma Fintype.card_numbering [DecidableEq X] : card (Numbering X) = (card X)! :=
  card_equiv (equivFin _)

namespace Numbering
variable {f : Numbering X} {s t : Finset X}

/--
Definition of `IsPrefix` / `IsPrefix` 的定义

English:
definition IsPrefix
  signature: (f : Numbering X) (s : Finset X)
  body: forall x, x in s ↔ f x < #s

中文:
定义 IsPrefix
  签名: (f : Numbering X) (s : Finset X)
  定义体: forall x, x in s ↔ f x < #s
-/
def IsPrefix (f : Numbering X) (s : Finset X) := forall x, x in s ↔ f x < #s

/--
lemma `IsPrefix.subset_of_card_le_card` / 引理 `IsPrefix.subset_of_card_le_card`

English:
lemma IsPrefix.subset_of_card_le_card
  given: (hs : IsPrefix f s) (ht : IsPrefix f t) (hst : #s <= #t)
  proof: fun a ha => (ht a).mpr ((hs a).mp ha).trans_le hst

中文:
引理 IsPrefix.subset_of_card_le_card
  条件: (hs : IsPrefix f s) (ht : IsPrefix f t) (hst : #s <= #t)
  证明: fun a ha => (ht a).mpr ((hs a).mp ha).trans_le hst

Depends on / 依赖: trans_le
-/
lemma IsPrefix.subset_of_card_le_card (hs : IsPrefix f s) (ht : IsPrefix f t) (hst : #s <= #t) :
s subseteq t := fun a ha => (ht a).mpr ((hs a).mp ha).trans_le hst

variable [DecidableEq X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Decidable (IsPrefix f s)
  body: inferInstanceAs Decidable (forall _, _)

中文:
实例 :
  签名: Decidable (IsPrefix f s)
  定义体: inferInstanceAs Decidable (forall _, _)

Depends on / 依赖: Decidable
-/
instance : Decidable (IsPrefix f s) := inferInstanceAs Decidable (forall _, _)

/--
Definition of `prefixed` / `prefixed` 的定义

English:
definition prefixed
  signature: (s : Finset X)
  body: {f | IsPrefix f s}

中文:
定义 prefixed
  签名: (s : Finset X)
  定义体: {f | IsPrefix f s}

Depends on / 依赖: IsPrefix
-/
def prefixed (s : Finset X) : Finset (Numbering X) := {f | IsPrefix f s}

/--
lemma `mem_prefixed` / 引理 `mem_prefixed`

English:
lemma mem_prefixed
  statement: f in prefixed s ↔ IsPrefix f s
  proof: by simp [prefixed]

中文:
引理 mem_prefixed
  结论: f in prefixed s ↔ IsPrefix f s
  证明: by simp [prefixed]
-/
@[simp] lemma mem_prefixed : f in prefixed s ↔ IsPrefix f s := by simp [prefixed]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `prefixedEquiv` / `prefixedEquiv` 的定义

English:
definition prefixedEquiv
  signature: (s : Finset X)
  body: { fst.toFun x := ⟨f.1 x, by simp [← mem_prefixed.1 f.2 x]⟩
      fst.invFun n :=
⟨f.1.symm ⟨n, n.2.trans_le by simpa using s.card_le_univ⟩, by
          rw [mem_prefixed.1 f.2]; simpa using n.2⟩
      fst.left_inv x := by simp
      fst.right_inv n := by simp
      snd.toFun x := ⟨f.1 x - #s, by
   

中文:
定义 prefixedEquiv
  签名: (s : Finset X)
  定义体: { fst.toFun x := ⟨f.1 x, by simp [← mem_prefixed.1 f.2 x]⟩
      fst.invFun n :=
⟨f.1.symm ⟨n, n.2.trans_le by simpa using s.card_le_univ⟩, by
          rw [mem_prefixed.1 f.2]; simpa using n.2⟩
      fst.left_inv x := by simp
      fst.right_inv n := by simp
      snd.toFun x := ⟨f.1 x - #s, by
   

Depends on / 依赖: Finset, Finset.mem_compl, Nat.add_lt_of_lt_sub, Sigma.mk, add_lt_of_lt_sub, card_le_univ, flatMap, fst.invFun, fst.left_inv, fst.right_inv, fst.toFun, invFun, left_inv, mem_compl, mem_prefixed, ofList, right_inv, s.card_le_univ, s.mem_compl, snd.invFun
-/
def prefixedEquiv (s : Finset X) : prefixed s ≃ Numbering s × Numbering ↑(sᶜ) where
  toFun f :=
    { fst.toFun x := ⟨f.1 x, by simp [← mem_prefixed.1 f.2 x]⟩
      fst.invFun n :=
⟨f.1.symm ⟨n, n.2.trans_le by simpa using s.card_le_univ⟩, by
          rw [mem_prefixed.1 f.2]; simpa using n.2⟩
      fst.left_inv x := by simp
      fst.right_inv n := by simp
      snd.toFun x := ⟨f.1 x - #s, by
        have := (mem_prefixed.1 f.2 x).not.1 (Finset.mem_compl.1 x.2)
        simp at this ⊢
        omega⟩
      snd.invFun n :=
⟨f.1.symm ⟨n + #s, Nat.add_lt_of_lt_sub by simpa using n.2⟩, by
          rw [s.mem_compl]; rw [mem_prefixed.1 f.2]; simp⟩
      snd.left_inv := by
        rintro ⟨x, hx⟩
        rw [s.mem_compl]; rw [mem_prefixed.1 f.2]; rw [not_lt] at hx
        simp [Nat.sub_add_cancel hx]
      snd.right_inv := by rintro ⟨n, hn⟩; simp }
  invFun := fun (g, g') =>
    { val.toFun x :=
        if hx : x in s then
.castLE (Fintype.card_subtype_le _) g ⟨x, hx⟩
        else
.cast (by simp [card_le_univ]) .addNat #s g' ⟨x, by simpa⟩
      val.invFun n :=
        if hn : n < #s then
          g.symm ⟨n, by simpa using hn⟩
        else
          g'.symm ⟨n - #s, by simp; omega⟩
      val.left_inv x := by
        by_cases hx : x in s
        · have : g ⟨x, hx⟩ < #s := by simpa using (g ⟨x, hx⟩).2
          simp [hx, this]
        · simp [hx]
      val.right_inv n := by
        obtain hns | hsn := lt_or_ge n.1 #s
        · simp [hns]
        · simp [hsn.not_gt, hsn, mem_compl.1 <| Subtype.prop _]
      property := mem_prefixed.2 fun x => by
        constructor
        · intro hx
          simpa [hx, -Fin.is_lt] using (g _).is_lt
        · by_cases hx : x in s <;> simp [hx] }
  left_inv f := by
    ext x
    by_cases hx : x in s
    · simp [hx]
    · rw [mem_prefixed.1 f.2, not_lt] at hx
      simp [hx]
  right_inv g := by simp +contextual [Prod.ext_iff, DFunLike.ext_iff]

/--
lemma `card_prefixed` / 引理 `card_prefixed`

English:
lemma card_prefixed
  given: (s : Finset X)
  statement: #(prefixed s) = (#s)! * (card X - #s)!
  proof: by
  simpa [-mem_prefixed] using Fintype.card_congr (prefixedEquiv s)

@[simp]

中文:
引理 card_prefixed
  条件: (s : Finset X)
  结论: #(prefixed s) = (#s)! * (card X - #s)!
  证明: by
  simpa [-mem_prefixed] using Fintype.card_congr (prefixedEquiv s)

@[simp]

Depends on / 依赖: Fintype, Fintype.card_congr, card_congr, mem_prefixed, prefixedEquiv
-/
lemma card_prefixed (s : Finset X) : #(prefixed s) = (#s)! * (card X - #s)! := by
  simpa [-mem_prefixed] using Fintype.card_congr (prefixedEquiv s)

@[simp]
/--
lemma `dens_prefixed` / 引理 `dens_prefixed`

English:
lemma dens_prefixed
  given: (s : Finset X)
  statement: (prefixed s).dens = ((card X).choose #s : Rat>=0)⁻¹
  proof: by
  simp [dens, card_prefixed, Nat.cast_choose _ s.card_le_univ]

中文:
引理 dens_prefixed
  条件: (s : Finset X)
  结论: (prefixed s).dens = ((card X).choose #s : Rat>=0)⁻¹
  证明: by
  simp [dens, card_prefixed, Nat.cast_choose _ s.card_le_univ]

Depends on / 依赖: Nat.cast_choose, card_le_univ, card_prefixed, cast_choose, s.card_le_univ
-/
lemma dens_prefixed (s : Finset X) : (prefixed s).dens = ((card X).choose #s : Rat>=0)⁻¹ := by
  simp [dens, card_prefixed, Nat.cast_choose _ s.card_le_univ]

-- TODO: This can be strengthened to an iff
/--
lemma `disjoint_prefixed_prefixed` / 引理 `disjoint_prefixed_prefixed`

English:
lemma disjoint_prefixed_prefixed
  given: (hst : ¬ s subseteq t) (hts : ¬ t subseteq s)
  proof: by
  simp only [Finset.disjoint_left, mem_prefixed]
  intro f hs ht
  obtain hst' | hts' := Nat.le_total #s #t
· exact hst hs.subset_of_card_le_card ht hst'
· exact hts ht.subset_of_card_le_card hs hts'

中文:
引理 disjoint_prefixed_prefixed
  条件: (hst : ¬ s subseteq t) (hts : ¬ t subseteq s)
  证明: by
  simp only [Finset.disjoint_left, mem_prefixed]
  intro f hs ht
  obtain hst' | hts' := Nat.le_total #s #t
· exact hst hs.subset_of_card_le_card ht hst'
· exact hts ht.subset_of_card_le_card hs hts'

Depends on / 依赖: Finset, Finset.disjoint_left, Nat.le_total, disjoint_left, hs.subset_of_card_le_card, ht.subset_of_card_le_card, le_total, mem_prefixed, subset_of_card_le_card
-/
lemma disjoint_prefixed_prefixed (hst : ¬ s subseteq t) (hts : ¬ t subseteq s) :
    Disjoint (prefixed s) (prefixed t) := by
  simp only [Finset.disjoint_left, mem_prefixed]
  intro f hs ht
  obtain hst' | hts' := Nat.le_total #s #t
· exact hst hs.subset_of_card_le_card ht hst'
· exact hts ht.subset_of_card_le_card hs hts'

end Numbering
