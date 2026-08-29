/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Lattice

/-!
# Sorting the elements of `Sym2`

This file provides `Sym2.sortEquiv`, the forward direction of which is somewhat analogous to
`Multiset.sort`.
-/

@[expose] public section

namespace Sym2

variable {α}

/--
Definition of `sup` / `sup` 的定义

English:
definition sup
  signature: [SemilatticeSup α] (x : Sym2 α)
  body: Sym2.lift ⟨(· ⊔ ·), sup_comm⟩ x

中文:
定义 sup
  签名: [SemilatticeSup α] (x : Sym2 α)
  定义体: Sym2.lift ⟨(· ⊔ ·), sup_comm⟩ x

Depends on / 依赖: Sym2.lift, sup_comm
-/
def sup [SemilatticeSup α] (x : Sym2 α) : α := Sym2.lift ⟨(· ⊔ ·), sup_comm⟩ x

/--
theorem `sup_mk` / 定理 `sup_mk`

English:
theorem sup_mk
  given: [SemilatticeSup α] (a b : α)
  statement: s(a, b).sup = a ⊔ b
  proof: rfl

中文:
定理 sup_mk
  条件: [SemilatticeSup α] (a b : α)
  结论: s(a, b).sup = a ⊔ b
  证明: rfl
-/
@[simp] theorem sup_mk [SemilatticeSup α] (a b : α) : s(a, b).sup = a ⊔ b := rfl

/--
Definition of `inf` / `inf` 的定义

English:
definition inf
  signature: [SemilatticeInf α] (x : Sym2 α)
  body: Sym2.lift ⟨(· ⊓ ·), inf_comm⟩ x

中文:
定义 inf
  签名: [SemilatticeInf α] (x : Sym2 α)
  定义体: Sym2.lift ⟨(· ⊓ ·), inf_comm⟩ x

Depends on / 依赖: Sym2.lift, inf_comm
-/
def inf [SemilatticeInf α] (x : Sym2 α) : α := Sym2.lift ⟨(· ⊓ ·), inf_comm⟩ x

/--
theorem `inf_mk` / 定理 `inf_mk`

English:
theorem inf_mk
  given: [SemilatticeInf α] (a b : α)
  statement: s(a, b).inf = a ⊓ b
  proof: rfl

中文:
定理 inf_mk
  条件: [SemilatticeInf α] (a b : α)
  结论: s(a, b).inf = a ⊓ b
  证明: rfl
-/
@[simp] theorem inf_mk [SemilatticeInf α] (a b : α) : s(a, b).inf = a ⊓ b := rfl

/--
theorem `inf_le_sup` / 定理 `inf_le_sup`

English:
theorem inf_le_sup
  given: [Lattice α] (s : Sym2 α)
  statement: s.inf <= s.sup
  proof: by
  cases s using Sym2.ind; simp

中文:
定理 inf_le_sup
  条件: [Lattice α] (s : Sym2 α)
  结论: s.inf <= s.sup
  证明: by
  cases s using Sym2.ind; simp
-/
protected theorem inf_le_sup [Lattice α] (s : Sym2 α) : s.inf <= s.sup := by
  cases s using Sym2.ind; simp

/-- In a linear order, symmetric squares are canonically identified with ordered pairs. -/
@[simps!]
/--
Definition of `sortEquiv` / `sortEquiv` 的定义

English:
definition sortEquiv
  signature: [LinearOrder α]
  body: ⟨(s.inf, s.sup), Sym2.inf_le_sup _⟩
  invFun p := s(p.1.1, p.1.2)
left_inv := Sym2.ind fun a b => eq_iff.mpr by
    cases le_total a b with
    | inl h => simp [h]
    | inr h => simp [h]
right_inv := Subtype.rec Prod.rec fun x y hxy =>
Subtype.ext Prod.ext (by simp [hxy]) (by simp [hxy])

中文:
定义 sortEquiv
  签名: [LinearOrder α]
  定义体: ⟨(s.inf, s.sup), Sym2.inf_le_sup _⟩
  invFun p := s(p.1.1, p.1.2)
left_inv := Sym2.ind fun a b => eq_iff.mpr by
    cases le_total a b with
    | inl h => simp [h]
    | inr h => simp [h]
right_inv := Subtype.rec Prod.rec fun x y hxy =>
Subtype.ext Prod.ext (by simp [hxy]) (by simp [hxy])

Depends on / 依赖: Sym2.inf_le_sup, inf_le_sup, s.inf, s.sup
-/
def sortEquiv [LinearOrder α] : Sym2 α ≃ { p : α × α // p.1 <= p.2 } where
  toFun s := ⟨(s.inf, s.sup), Sym2.inf_le_sup _⟩
  invFun p := s(p.1.1, p.1.2)
left_inv := Sym2.ind fun a b => eq_iff.mpr by
    cases le_total a b with
    | inl h => simp [h]
    | inr h => simp [h]
right_inv := Subtype.rec Prod.rec fun x y hxy =>
Subtype.ext Prod.ext (by simp [hxy]) (by simp [hxy])

/--
theorem `inf_eq_inf_and_sup_eq_sup` / 定理 `inf_eq_inf_and_sup_eq_sup`

English:
theorem inf_eq_inf_and_sup_eq_sup
  given: [LinearOrder α] {s t : Sym2 α}
  proof: by
  induction s with | _ a b
  induction t with | _ c d
  obtain hab | hba := le_total a b <;> obtain hcd | hdc := le_total c d <;>
    aesop (add unsafe le_antisymm)

中文:
定理 inf_eq_inf_and_sup_eq_sup
  条件: [LinearOrder α] {s t : Sym2 α}
  证明: by
  induction s with | _ a b
  induction t with | _ c d
  obtain hab | hba := le_total a b <;> obtain hcd | hdc := le_total c d <;>
    aesop (add unsafe le_antisymm)

Depends on / 依赖: le_antisymm, le_total, unsafe
-/
theorem inf_eq_inf_and_sup_eq_sup [LinearOrder α] {s t : Sym2 α} :
    s.inf = t.inf ∧ s.sup = t.sup ↔ s = t := by
  induction s with | _ a b
  induction t with | _ c d
  obtain hab | hba := le_total a b <;> obtain hcd | hdc := le_total c d <;>
    aesop (add unsafe le_antisymm)

end Sym2
