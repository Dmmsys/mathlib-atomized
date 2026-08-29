/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Huỳnh Trần Khanh, Stuart Presnell
-/
module

public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Stars and bars

In this file, we prove (in `Sym.card_sym_eq_multichoose`) that the function `multichoose n k`
defined in `Data/Nat/Choose/Basic` counts the number of multisets of cardinality `k` over an
alphabet of cardinality `n`. In conjunction with `Nat.multichoose_eq` proved in
`Data/Nat/Choose/Basic`, which shows that `multichoose n k = choose (n + k - 1) k`,
this is central to the "stars and bars" technique in combinatorics, where we switch between
counting multisets of size `k` over an alphabet of size `n` to counting strings of `k` elements
("stars") separated by `n-1` dividers ("bars").

## Informal statement

Many problems in mathematics are of the form of (or can be reduced to) putting `k` indistinguishable
objects into `n` distinguishable boxes; for example, the problem of finding natural numbers
`x1, ..., xn` whose sum is `k`. This is equivalent to forming a multiset of cardinality `k` from
an alphabet of cardinality `n` -- for each box `i ∈ [1, n]` the multiset contains as many copies
of `i` as there are items in the `i`th box.

The "stars and bars" technique arises from another way of presenting the same problem. Instead of
putting `k` items into `n` boxes, we take a row of `k` items (the "stars") and separate them by
inserting `n-1` dividers (the "bars"). For example, the pattern `*|||**|*|` exhibits 4 items
distributed into 6 boxes -- note that any box, including the first and last, may be empty.
Such arrangements of `k` stars and `n-1` bars are in 1-1 correspondence with multisets of size `k`
over an alphabet of size `n`, and are counted by `choose (n + k - 1) k`.

Note that this problem is one component of Gian-Carlo Rota's "Twelvefold Way"
https://en.wikipedia.org/wiki/Twelvefold_way

## Formal statement

Here we generalise the alphabet to an arbitrary fintype `α`, and we use `Sym α k` as the type of
multisets of size `k` over `α`. Thus the statement that these are counted by `multichoose` is:
`Sym.card_sym_eq_multichoose : card (Sym α k) = multichoose (card α) k`
while the "stars and bars" technique gives
`Sym.card_sym_eq_choose : card (Sym α k) = choose (card α + k - 1) k`


## Tags

stars and bars, multichoose
-/

@[expose] public section


open Finset Fintype Function Sum Nat

variable {α : Type*}

namespace Sym

section Sym

variable (α) (n : Nat)

/--
Definition of `e1` / `e1` 的定义

English:
definition e1
  signature: {n k : Nat}
  body: s.1.erase 0 s.2
  invFun s := ⟨cons 0 s, mem_cons_self 0 s⟩
  left_inv s := by simp
  right_inv s := by simp

中文:
定义 e1
  签名: {n k : 自然数}
  定义体: s.1.erase 0 s.2
  invFun s := ⟨cons 0 s, mem_cons_self 0 s⟩
  left_inv s := by simp
  right_inv s := by simp
-/
protected def e1 {n k : Nat} : { s : Sym (Fin (n + 1)) (k + 1) // ↑0 in s } ≃ Sym (Fin n.succ) k where
  toFun s := s.1.erase 0 s.2
  invFun s := ⟨cons 0 s, mem_cons_self 0 s⟩
  left_inv s := by simp
  right_inv s := by simp

/--
Definition of `e2` / `e2` 的定义

English:
definition e2
  signature: {n k : Nat}
  body: map (Fin.predAbove 0) s.1
  invFun s :=
    ⟨map (Fin.succAbove 0) s,
      (mt mem_map.1) (not_exists.2 fun t => not_and.2 fun _ => Fin.succAbove_ne _ t)⟩
  left_inv s := by
    ext1
    simp only [map_map]
    refine (Sym.map_congr fun v hv => ?_).trans (map_id' _)
    exact Fin.succAbove_predAbov

中文:
定义 e2
  签名: {n k : 自然数}
  定义体: map (Fin.predAbove 0) s.1
  invFun s :=
    ⟨map (Fin.succAbove 0) s,
      (mt mem_map.1) (not_exists.2 fun t => not_and.2 fun _ => Fin.succAbove_ne _ t)⟩
  left_inv s := by
    ext1
    simp only [map_map]
    refine (Sym.map_congr fun v hv => ?_).trans (map_id' _)
    exact Fin.succAbove_predAbov
-/
protected def e2 {n k : Nat} : { s : Sym (Fin n.succ.succ) k // ↑0 ∉ s } ≃ Sym (Fin n.succ) k where
  toFun s := map (Fin.predAbove 0) s.1
  invFun s :=
    ⟨map (Fin.succAbove 0) s,
      (mt mem_map.1) (not_exists.2 fun t => not_and.2 fun _ => Fin.succAbove_ne _ t)⟩
  left_inv s := by
    ext1
    simp only [map_map]
    refine (Sym.map_congr fun v hv => ?_).trans (map_id' _)
    exact Fin.succAbove_predAbove (ne_of_mem_of_not_mem hv s.2)
  right_inv s := by
    simp only [map_map, comp_apply, ← Fin.castSucc_zero, Fin.predAbove_succAbove, map_id']

/--
theorem `card_sym_fin_eq_multichoose` / 定理 `card_sym_fin_eq_multichoose`

English:
theorem card_sym_fin_eq_multichoose
  statement: forall n k : Nat, card (Sym (Fin n) k) = multichoose n k

中文:
定理 card_sym_fin_eq_multichoose
  结论: 对任意 n k : 自然数, card (Sym (Fin n) k) = multichoose n k
-/
theorem card_sym_fin_eq_multichoose : forall n k : Nat, card (Sym (Fin n) k) = multichoose n k
  | n, 0 => by simp
  | 0, k + 1 => by rw [multichoose_zero_succ]; exact card_eq_zero
  | 1, k + 1 => by simp
  | n + 2, k + 1 => by
    rw [multichoose_succ_succ]; rw [← card_sym_fin_eq_multichoose (n + 1) (k + 1)]; rw [← card_sym_fin_eq_multichoose (n + 2) k]; rw [add_comm (Fintype.card _)]; rw [← card_sum]
    refine Fintype.card_congr (Equiv.symm ?_)
    apply (Sym.e1.symm.sumCongr Sym.e2.symm).trans
    apply Equiv.sumCompl

/--
theorem `card_sym_eq_multichoose` / 定理 `card_sym_eq_multichoose`

English:
theorem card_sym_eq_multichoose
  given: (α : Type*) (k : Nat) [Fintype α] [Fintype (Sym α k)]
  proof: by
  rw [← card_sym_fin_eq_multichoose]
  exact card_congr (equivCongr (equivFin α))

中文:
定理 card_sym_eq_multichoose
  条件: (α : 类型) (k : 自然数) [Fintype α] [Fintype (Sym α k)]
  证明: by
  rw [← card_sym_fin_eq_multichoose]
  exact card_congr (equivCongr (equivFin α))

Depends on / 依赖: card_congr, card_sym_fin_eq_multichoose, equivCongr, equivFin
-/
theorem card_sym_eq_multichoose (α : Type*) (k : Nat) [Fintype α] [Fintype (Sym α k)] :
    card (Sym α k) = multichoose (card α) k := by
  rw [← card_sym_fin_eq_multichoose]
  exact card_congr (equivCongr (equivFin α))

/--
theorem `card_sym_eq_choose` / 定理 `card_sym_eq_choose`

English:
theorem card_sym_eq_choose
  given: {α : Type*} [Fintype α] (k : Nat) [Fintype (Sym α k)]
  proof: by
  rw [card_sym_eq_multichoose]; rw [Nat.multichoose_eq]

中文:
定理 card_sym_eq_choose
  条件: {α : 类型} [Fintype α] (k : 自然数) [Fintype (Sym α k)]
  证明: by
  rw [card_sym_eq_multichoose]; rw [Nat.multichoose_eq]

Depends on / 依赖: Nat.multichoose_eq, card_sym_eq_multichoose, multichoose_eq
-/
theorem card_sym_eq_choose {α : Type*} [Fintype α] (k : Nat) [Fintype (Sym α k)] :
    card (Sym α k) = (card α + k - 1).choose k := by
  rw [card_sym_eq_multichoose]; rw [Nat.multichoose_eq]

end Sym

end Sym

namespace Sym2

variable [DecidableEq α]

/--
theorem `card_image_diag` / 定理 `card_image_diag`

English:
theorem card_image_diag
  given: (s : Finset α)
  statement: #(s.diag.image Sym2.mk.uncurry) = #s
  proof: by
  simp [card_image_of_injOn]

中文:
定理 card_image_diag
  条件: (s : Finset α)
  结论: #(s.diag.image Sym2.mk.uncurry) = #s
  证明: by
  simp [card_image_of_injOn]

Depends on / 依赖: card_image_of_injOn
-/
theorem card_image_diag (s : Finset α) : #(s.diag.image Sym2.mk.uncurry) = #s := by
  simp [card_image_of_injOn]

/--
lemma `two_mul_card_image_offDiag` / 引理 `two_mul_card_image_offDiag`

English:
lemma two_mul_card_image_offDiag
  given: (s : Finset α)
  proof: by
  rw [card_eq_sum_card_image (Sym2.mk.uncurry : α × α -> _)]; rw [sum_const_nat (Sym2.ind _)]; rw [mul_comm]
  -- FIXME: Would be cool for the final `aesop` call not to require this `a ≠ b ∨ b ≠ a` trick.
  have (a b : α) (ha : a in s) (hb : b in s) (hab : a != b ∨ b != a) :
      {z in s.offDiag

中文:
引理 two_mul_card_image_offDiag
  条件: (s : Finset α)
  证明: by
  rw [card_eq_sum_card_image (Sym2.mk.uncurry : α × α -> _)]; rw [sum_const_nat (Sym2.ind _)]; rw [mul_comm]
  -- FIXME: Would be cool for the final `aesop` call not to require this `a ≠ b ∨ b ≠ a` trick.
  have (a b : α) (ha : a in s) (hb : b in s) (hab : a != b ∨ b != a) :
      {z in s.offDiag

Depends on / 依赖: Sym2.ind, Sym2.mk.uncurry, card_eq_sum_card_image, mul_comm, sum_const_nat, uncurry
-/
lemma two_mul_card_image_offDiag (s : Finset α) :
    2 * #(s.offDiag.image Sym2.mk.uncurry) = #s.offDiag := by
  rw [card_eq_sum_card_image (Sym2.mk.uncurry : α × α -> _)]; rw [sum_const_nat (Sym2.ind _)]; rw [mul_comm]
  -- FIXME: Would be cool for the final `aesop` call not to require this `a ≠ b ∨ b ≠ a` trick.
  have (a b : α) (ha : a in s) (hb : b in s) (hab : a != b ∨ b != a) :
      {z in s.offDiag | Sym2.mk.uncurry z = s(a, b)} = .cons (a, b) {(b, a)}
        (by simpa [eq_comm] using hab) := by aesop
  aesop

/--
theorem `card_image_offDiag` / 定理 `card_image_offDiag`

English:
theorem card_image_offDiag
  given: (s : Finset α)
  proof: by
  rw [Nat.choose_two_right]; rw [Nat.mul_sub_left_distrib]; rw [mul_one]; rw [← offDiag_card]; rw [Nat.div_eq_of_eq_mul_right Nat.zero_lt_two (two_mul_card_image_offDiag s).symm]

中文:
定理 card_image_offDiag
  条件: (s : Finset α)
  证明: by
  rw [Nat.choose_two_right]; rw [Nat.mul_sub_left_distrib]; rw [mul_one]; rw [← offDiag_card]; rw [Nat.div_eq_of_eq_mul_right Nat.zero_lt_two (two_mul_card_image_offDiag s).symm]

Depends on / 依赖: Nat.choose_two_right, Nat.div_eq_of_eq_mul_right, Nat.mul_sub_left_distrib, Nat.zero_lt_two, choose_two_right, div_eq_of_eq_mul_right, mul_one, mul_sub_left_distrib, offDiag_card, two_mul_card_image_offDiag, zero_lt_two
-/
theorem card_image_offDiag (s : Finset α) :
    #(s.offDiag.image Sym2.mk.uncurry) = (#s).choose 2 := by
  rw [Nat.choose_two_right]; rw [Nat.mul_sub_left_distrib]; rw [mul_one]; rw [← offDiag_card]; rw [Nat.div_eq_of_eq_mul_right Nat.zero_lt_two (two_mul_card_image_offDiag s).symm]

/--
theorem `card_subtype_diag` / 定理 `card_subtype_diag`

English:
theorem card_subtype_diag
  given: [Fintype α]
  statement: card { a : Sym2 α // a.IsDiag } = card α
  proof: card_congr diagElemEquiv

中文:
定理 card_subtype_diag
  条件: [Fintype α]
  结论: card { a : Sym2 α // a.IsDiag } = card α
  证明: card_congr diagElemEquiv

Depends on / 依赖: card_congr, diagElemEquiv
-/
theorem card_subtype_diag [Fintype α] : card { a : Sym2 α // a.IsDiag } = card α :=
  card_congr diagElemEquiv

/--
theorem `card_subtype_not_diag` / 定理 `card_subtype_not_diag`

English:
theorem card_subtype_not_diag
  given: [Fintype α]
  proof: by
  convert! card_image_offDiag (univ : Finset α)
  rw [← filter_image_mk_not_isDiag]; rw [Fintype.card_of_subtype]
  rintro x
  rw [mem_filter]; rw [univ_product_univ]; rw [mem_image]
  obtain ⟨a, ha⟩ := Quot.exists_rep x
  exact and_iff_right ⟨a, mem_univ _, ha⟩

中文:
定理 card_subtype_not_diag
  条件: [Fintype α]
  证明: by
  convert! card_image_offDiag (univ : Finset α)
  rw [← filter_image_mk_not_isDiag]; rw [Fintype.card_of_subtype]
  rintro x
  rw [mem_filter]; rw [univ_product_univ]; rw [mem_image]
  obtain ⟨a, ha⟩ := Quot.exists_rep x
  exact and_iff_right ⟨a, mem_univ _, ha⟩

Depends on / 依赖: Finset, Fintype, Fintype.card_of_subtype, Quot.exists_rep, and_iff_right, card_image_offDiag, card_of_subtype, convert, exists_rep, filter_image_mk_not_isDiag, mem_filter, mem_image, mem_univ, univ_product_univ
-/
theorem card_subtype_not_diag [Fintype α] :
    card { a : Sym2 α // ¬a.IsDiag } = (card α).choose 2 := by
  convert! card_image_offDiag (univ : Finset α)
  rw [← filter_image_mk_not_isDiag]; rw [Fintype.card_of_subtype]
  rintro x
  rw [mem_filter]; rw [univ_product_univ]; rw [mem_image]
  obtain ⟨a, ha⟩ := Quot.exists_rep x
  exact and_iff_right ⟨a, mem_univ _, ha⟩

/--
lemma `card_diagSet_compl` / 引理 `card_diagSet_compl`

English:
lemma card_diagSet_compl
  given: [Fintype α]
  statement: card (diagSetᶜ : Set (Sym2 α)) = (card α).choose 2
  proof: card_subtype_not_diag

中文:
引理 card_diagSet_compl
  条件: [Fintype α]
  结论: card (diagSetᶜ : Set (Sym2 α)) = (card α).choose 2
  证明: card_subtype_not_diag

Depends on / 依赖: card_subtype_not_diag
-/
lemma card_diagSet_compl [Fintype α] : card (diagSetᶜ : Set (Sym2 α)) = (card α).choose 2 :=
  card_subtype_not_diag

/--
theorem `card` / 定理 `card`

English:
theorem card
  given: {α} [Fintype α]
  statement: card (Sym2 α) = Nat.choose (card α + 1) 2
  proof: Finset.card_sym2 _

中文:
定理 card
  条件: {α} [Fintype α]
  结论: card (Sym2 α) = 自然数.choose (card α + 1) 2
  证明: Finset.card_sym2 _
-/
protected theorem card {α} [Fintype α] : card (Sym2 α) = Nat.choose (card α + 1) 2 :=
  Finset.card_sym2 _

end Sym2
