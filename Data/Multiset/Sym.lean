/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.List.Sym

/-! # Unordered tuples of elements of a multiset

Defines `Multiset.sym` and the specialized `Multiset.sym2` for computing multisets of all
unordered n-tuples from a given multiset. These are multiset versions of `Nat.multichoose`.

## Main declarations

* `Multiset.sym2`: `xs.sym2` is the multiset of all unordered pairs of elements from `xs`,
  with multiplicity. The multiset's values are in `Sym2 α`.

## TODO

* Once `List.Perm.sym` is defined, define
  ```lean
  protected def sym (n : Nat) (m : Multiset α) : Multiset (Sym α n) :=
    m.liftOn (fun xs => xs.sym n) (List.perm.sym n)
  ```
  and then use this to remove the `DecidableEq` assumption from `Finset.sym`.

* `theorem injective_sym2 : Function.Injective (Multiset.sym2 : Multiset α → _)`

* `theorem strictMono_sym2 : StrictMono (Multiset.sym2 : Multiset α → _)`

-/

@[expose] public section

namespace Multiset

variable {α β : Type*}

section Sym2

/--
Definition of `sym2` / `sym2` 的定义

English:
definition sym2
  signature: (m : Multiset α)
  body: m.liftOn (fun xs => xs.sym2) fun _ _ h => by rw [coe_eq_coe]; exact h.sym2

中文:
定义 sym2
  签名: (m : Multiset α)
  定义体: m.liftOn (fun xs => xs.sym2) fun _ _ h => by rw [coe_eq_coe]; exact h.sym2
-/
protected def sym2 (m : Multiset α) : Multiset (Sym2 α) :=
  m.liftOn (fun xs => xs.sym2) fun _ _ h => by rw [coe_eq_coe]; exact h.sym2

/--
theorem `sym2_coe` / 定理 `sym2_coe`

English:
theorem sym2_coe
  given: (xs : List α)
  statement: (xs : Multiset α).sym2 = xs.sym2
  proof: rfl

@[simp]

中文:
定理 sym2_coe
  条件: (xs : List α)
  结论: (xs : Multiset α).sym2 = xs.sym2
  证明: rfl

@[simp]
-/
@[simp] theorem sym2_coe (xs : List α) : (xs : Multiset α).sym2 = xs.sym2 := rfl

@[simp]
/--
theorem `sym2_eq_zero_iff` / 定理 `sym2_eq_zero_iff`

English:
theorem sym2_eq_zero_iff
  given: {m : Multiset α}
  statement: m.sym2 = 0 ↔ m = 0
  proof: m.inductionOn fun xs => by simp

@[simp]

中文:
定理 sym2_eq_zero_iff
  条件: {m : Multiset α}
  结论: m.sym2 = 0 ↔ m = 0
  证明: m.inductionOn fun xs => by simp

@[simp]

Depends on / 依赖: inductionOn, m.inductionOn
-/
theorem sym2_eq_zero_iff {m : Multiset α} : m.sym2 = 0 ↔ m = 0 :=
  m.inductionOn fun xs => by simp

@[simp]
/--
theorem `sym2_zero` / 定理 `sym2_zero`

English:
theorem sym2_zero
  statement: (0 : Multiset α).sym2 = 0
  proof: rfl

中文:
定理 sym2_zero
  结论: (0 : Multiset α).sym2 = 0
  证明: rfl
-/
theorem sym2_zero : (0 : Multiset α).sym2 = 0 := rfl

/--
theorem `sym2_cons` / 定理 `sym2_cons`

English:
theorem sym2_cons
  given: (a : α) (m : Multiset α)
  proof: m.inductionOn fun _ => rfl

中文:
定理 sym2_cons
  条件: (a : α) (m : Multiset α)
  证明: m.inductionOn fun _ => rfl

Depends on / 依赖: inductionOn, m.inductionOn
-/
theorem sym2_cons (a : α) (m : Multiset α) :
    (m.cons a).sym2 = ((m.cons a).map <| fun b => s(a, b)) + m.sym2 :=
  m.inductionOn fun _ => rfl

/--
theorem `sym2_map` / 定理 `sym2_map`

English:
theorem sym2_map
  given: (f : α -> β) (m : Multiset α)
  proof: m.inductionOn fun xs => by simp [List.sym2_map]

中文:
定理 sym2_map
  条件: (f : α -> β) (m : Multiset α)
  证明: m.inductionOn fun xs => by simp [List.sym2_map]

Depends on / 依赖: List.sym2_map, inductionOn, m.inductionOn, sym2_map
-/
theorem sym2_map (f : α -> β) (m : Multiset α) :
    (m.map f).sym2 = m.sym2.map (Sym2.map f) :=
  m.inductionOn fun xs => by simp [List.sym2_map]

/--
theorem `mk_mem_sym2_iff` / 定理 `mk_mem_sym2_iff`

English:
theorem mk_mem_sym2_iff
  given: {m : Multiset α} {a b : α}
  proof: m.inductionOn fun xs => by simp [List.mk_mem_sym2_iff]

中文:
定理 mk_mem_sym2_iff
  条件: {m : Multiset α} {a b : α}
  证明: m.inductionOn fun xs => by simp [List.mk_mem_sym2_iff]

Depends on / 依赖: List.mk_mem_sym2_iff, inductionOn, m.inductionOn, mk_mem_sym2_iff
-/
theorem mk_mem_sym2_iff {m : Multiset α} {a b : α} :
    s(a, b) in m.sym2 ↔ a in m ∧ b in m :=
  m.inductionOn fun xs => by simp [List.mk_mem_sym2_iff]

/--
theorem `mem_sym2_iff` / 定理 `mem_sym2_iff`

English:
theorem mem_sym2_iff
  given: {m : Multiset α} {z : Sym2 α}
  proof: m.inductionOn fun xs => by simp [List.mem_sym2_iff]

中文:
定理 mem_sym2_iff
  条件: {m : Multiset α} {z : Sym2 α}
  证明: m.inductionOn fun xs => by simp [List.mem_sym2_iff]

Depends on / 依赖: List.mem_sym2_iff, inductionOn, m.inductionOn, mem_sym2_iff
-/
theorem mem_sym2_iff {m : Multiset α} {z : Sym2 α} :
    z in m.sym2 ↔ forall y in z, y in m :=
  m.inductionOn fun xs => by simp [List.mem_sym2_iff]

/--
lemma `setOfPred_mem_sym2` / 引理 `setOfPred_mem_sym2`

English:
lemma setOfPred_mem_sym2
  given: {m : Multiset α}
  proof: Set.ext fun z => z.ind fun a b => by simp [mk_mem_sym2_iff]

@[deprecated (since := "2026-07-09")] alias setOf_mem_sym2 := setOfPred_mem_sym2

中文:
引理 setOfPred_mem_sym2
  条件: {m : Multiset α}
  证明: Set.ext fun z => z.ind fun a b => by simp [mk_mem_sym2_iff]

@[deprecated (since := "2026-07-09")] alias setOf_mem_sym2 := setOfPred_mem_sym2

Depends on / 依赖: Set.ext, mk_mem_sym2_iff, z.ind
-/
lemma setOfPred_mem_sym2 {m : Multiset α} :
    {z : Sym2 α | z in m.sym2} = {x : α | x in m}.sym2 :=
  Set.ext fun z => z.ind fun a b => by simp [mk_mem_sym2_iff]

@[deprecated (since := "2026-07-09")] alias setOf_mem_sym2 := setOfPred_mem_sym2

/--
theorem `Nodup.sym2` / 定理 `Nodup.sym2`

English:
theorem Nodup.sym2
  given: {m : Multiset α} (h : m.Nodup)
  statement: m.sym2.Nodup
  proof: m.inductionOn (fun _ h => List.Nodup.sym2 h) h

中文:
定理 Nodup.sym2
  条件: {m : Multiset α} (h : m.Nodup)
  结论: m.sym2.Nodup
  证明: m.inductionOn (fun _ h => List.Nodup.sym2 h) h
-/
protected theorem Nodup.sym2 {m : Multiset α} (h : m.Nodup) : m.sym2.Nodup :=
  m.inductionOn (fun _ h => List.Nodup.sym2 h) h

open scoped List in
@[simp, mono]
/--
theorem `sym2_mono` / 定理 `sym2_mono`

English:
theorem sym2_mono
  given: {m m' : Multiset α} (h : m <= m')
  statement: m.sym2 <= m'.sym2
  proof: by
  induction m, m' using Quotient.inductionOn₂ with | _ xs ys
  suffices xs <+~ ys from this.sym2
  simpa only [quot_mk_to_coe, coe_le, sym2_coe] using h

中文:
定理 sym2_mono
  条件: {m m' : Multiset α} (h : m <= m')
  结论: m.sym2 <= m'.sym2
  证明: by
  induction m, m' using Quotient.inductionOn₂ with | _ xs ys
  suffices xs <+~ ys from this.sym2
  simpa only [quot_mk_to_coe, coe_le, sym2_coe] using h

Depends on / 依赖: Quotient, Quotient.inductionOn, coe_le, quot_mk_to_coe, sym2_coe, this.sym2
-/
theorem sym2_mono {m m' : Multiset α} (h : m <= m') : m.sym2 <= m'.sym2 := by
  induction m, m' using Quotient.inductionOn₂ with | _ xs ys
  suffices xs <+~ ys from this.sym2
  simpa only [quot_mk_to_coe, coe_le, sym2_coe] using h

/--
theorem `monotone_sym2` / 定理 `monotone_sym2`

English:
theorem monotone_sym2
  statement: Monotone (Multiset.sym2 : Multiset α -> _)
  proof: fun _ _ => sym2_mono

中文:
定理 monotone_sym2
  结论: Monotone (Multiset.sym2 : Multiset α -> _)
  证明: fun _ _ => sym2_mono

Depends on / 依赖: sym2_mono
-/
theorem monotone_sym2 : Monotone (Multiset.sym2 : Multiset α -> _) := fun _ _ => sym2_mono

/--
theorem `card_sym2` / 定理 `card_sym2`

English:
theorem card_sym2
  given: {m : Multiset α}
  proof: by
  refine m.inductionOn fun xs => ?_
  simp [List.length_sym2]

中文:
定理 card_sym2
  条件: {m : Multiset α}
  证明: by
  refine m.inductionOn fun xs => ?_
  simp [List.length_sym2]

Depends on / 依赖: List.length_sym2, inductionOn, length_sym2, m.inductionOn
-/
theorem card_sym2 {m : Multiset α} :
    Multiset.card m.sym2 = Nat.choose (Multiset.card m + 1) 2 := by
  refine m.inductionOn fun xs => ?_
  simp [List.length_sym2]

/--
theorem `dedup_sym2` / 定理 `dedup_sym2`

English:
theorem dedup_sym2
  given: [DecidableEq α] (m : Multiset α)
  statement: m.sym2.dedup = m.dedup.sym2
  proof: m.inductionOn fun xs => by simp [List.dedup_sym2]

中文:
定理 dedup_sym2
  条件: [DecidableEq α] (m : Multiset α)
  结论: m.sym2.dedup = m.dedup.sym2
  证明: m.inductionOn fun xs => by simp [List.dedup_sym2]

Depends on / 依赖: LiftRel, LiftRel.swap_lem, List.dedup_sym2, dedup_sym2, inductionOn, m.inductionOn, propext, swap_lem
-/
theorem dedup_sym2 [DecidableEq α] (m : Multiset α) : m.sym2.dedup = m.dedup.sym2 :=
  m.inductionOn fun xs => by simp [List.dedup_sym2]

end Sym2

end Multiset
