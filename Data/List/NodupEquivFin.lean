/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.List.Duplicate
public import Mathlib.Data.List.Sort

/-!
# Equivalence between `Fin (length l)` and elements of a list

Given a list `l`,

* if `l` has no duplicates, then `List.Nodup.getEquiv` is the equivalence between
  `Fin (length l)` and `{x // x ∈ l}` sending `i` to `⟨get l i, _⟩` with the inverse
  sending `⟨x, hx⟩` to `⟨indexOf x l, _⟩`;

* if `l` has no duplicates and contains every element of a type `α`, then
  `List.Nodup.getEquivOfForallMemList` defines an equivalence between `Fin (length l)` and `α`;
  if `α` does not have decidable equality, then
  there is a bijection `List.Nodup.getBijectionOfForallMemList`;

* if `l` is sorted w.r.t. `(<)`, then `List.SortedLT.getIso` is the same bijection reinterpreted
  as an `OrderIso`.

-/

@[expose] public section


namespace List

variable {α : Type*}

namespace Nodup

/-- If `l` lists all the elements of `α` without duplicates, then `List.get` defines
a bijection `Fin l.length → α`. See `List.Nodup.getEquivOfForallMemList`
for a version giving an equivalence when there is decidable equality. -/
@[simps]
/--
Definition of `getBijectionOfForallMemList` / `getBijectionOfForallMemList` 的定义

English:
definition getBijectionOfForallMemList
  signature: (l : List α) (nd : l.Nodup) (h : forall x : α, x in l)
  body: ⟨fun i => l.get i, fun _ _ h => nd.get_inj_iff.1 h,
   fun x =>
    let ⟨i, hl⟩ := List.mem_iff_get.1 (h x)
    ⟨i, hl⟩⟩

中文:
定义 getBijectionOfForallMemList
  签名: (l : List α) (nd : l.Nodup) (h : 对任意 x : α, x in l)
  定义体: ⟨fun i => l.get i, fun _ _ h => nd.get_inj_iff.1 h,
   fun x =>
    let ⟨i, hl⟩ := List.mem_iff_get.1 (h x)
    ⟨i, hl⟩⟩

Depends on / 依赖: List.mem_iff_get, get_inj_iff, l.get, mem_iff_get, nd.get_inj_iff
-/
def getBijectionOfForallMemList (l : List α) (nd : l.Nodup) (h : forall x : α, x in l) :
    { f : Fin l.length -> α // Function.Bijective f } :=
  ⟨fun i => l.get i, fun _ _ h => nd.get_inj_iff.1 h,
   fun x =>
    let ⟨i, hl⟩ := List.mem_iff_get.1 (h x)
    ⟨i, hl⟩⟩

variable [DecidableEq α]

/-- If `l` has no duplicates, then `List.get` defines an equivalence between `Fin (length l)` and
the set of elements of `l`. -/
@[simps]
/--
Definition of `getEquiv` / `getEquiv` 的定义

English:
definition getEquiv
  signature: (l : List α) (H : Nodup l)
  body: ⟨get l i, get_mem _ _⟩
  invFun x := ⟨idxOf (↑x) l, idxOf_lt_length_iff.2 x.2⟩
  left_inv i := by simp only [List.get_idxOf, Fin.eta, H]
  right_inv x := by simp

中文:
定义 getEquiv
  签名: (l : List α) (H : Nodup l)
  定义体: ⟨get l i, get_mem _ _⟩
  invFun x := ⟨idxOf (↑x) l, idxOf_lt_length_iff.2 x.2⟩
  left_inv i := by simp only [List.get_idxOf, Fin.eta, H]
  right_inv x := by simp

Depends on / 依赖: get_mem
-/
def getEquiv (l : List α) (H : Nodup l) : Fin (length l) ≃ { x // x in l } where
  toFun i := ⟨get l i, get_mem _ _⟩
  invFun x := ⟨idxOf (↑x) l, idxOf_lt_length_iff.2 x.2⟩
  left_inv i := by simp only [List.get_idxOf, Fin.eta, H]
  right_inv x := by simp

/-- If `l` lists all the elements of `α` without duplicates, then `List.get` defines
an equivalence between `Fin l.length` and `α`.

See `List.Nodup.getBijectionOfForallMemList` for a version without decidable equality. -/
@[simps]
/--
Definition of `getEquivOfForallMemList` / `getEquivOfForallMemList` 的定义

English:
definition getEquivOfForallMemList
  signature: (l : List α) (nd : l.Nodup) (h : forall x : α, x in l)
  body: l.get i
  invFun a := ⟨_, idxOf_lt_length_iff.2 (h a)⟩
  left_inv i := by simp [nd]
  right_inv a := by simp

中文:
定义 getEquivOfForallMemList
  签名: (l : List α) (nd : l.Nodup) (h : 对任意 x : α, x in l)
  定义体: l.get i
  invFun a := ⟨_, idxOf_lt_length_iff.2 (h a)⟩
  left_inv i := by simp [nd]
  right_inv a := by simp

Depends on / 依赖: l.get
-/
def getEquivOfForallMemList (l : List α) (nd : l.Nodup) (h : forall x : α, x in l) :
    Fin l.length ≃ α where
  toFun i := l.get i
  invFun a := ⟨_, idxOf_lt_length_iff.2 (h a)⟩
  left_inv i := by simp [nd]
  right_inv a := by simp

end Nodup

section Sorted

/-- Alternative phrasing of `List.Nodup.getEquivOfForallMemList` using `List.count`. -/
@[simps!]
/--
Definition of `getEquivOfForallCountEqOne` / `getEquivOfForallCountEqOne` 的定义

English:
definition getEquivOfForallCountEqOne
  signature: [DecidableEq α] (l : List α) (h : forall x, l.count x = 1)
  body: Nodup.getEquivOfForallMemList _ (List.nodup_iff_count_eq_one.mpr fun _ _ => h _)
fun _ => List.count_pos_iff.mp h _ ▸ Nat.one_pos

中文:
定义 getEquivOfForallCountEqOne
  签名: [DecidableEq α] (l : List α) (h : 对任意 x, l.count x = 1)
  定义体: Nodup.getEquivOfForallMemList _ (List.nodup_iff_count_eq_one.mpr fun _ _ => h _)
fun _ => List.count_pos_iff.mp h _ ▸ Nat.one_pos

Depends on / 依赖: List.count_pos_iff.mp, List.nodup_iff_count_eq_one.mpr, Nat.one_pos, Nodup.getEquivOfForallMemList, count_pos_iff, getEquivOfForallMemList, nodup_iff_count_eq_one, one_pos
-/
def getEquivOfForallCountEqOne [DecidableEq α] (l : List α) (h : forall x, l.count x = 1) :
    Fin l.length ≃ α :=
  Nodup.getEquivOfForallMemList _ (List.nodup_iff_count_eq_one.mpr fun _ _ => h _)
fun _ => List.count_pos_iff.mp h _ ▸ Nat.one_pos

variable [Preorder α] {l : List α}

variable [DecidableEq α]

/--
Definition of `SortedLT.getIso` / `SortedLT.getIso` 的定义

English:
definition SortedLT.getIso
  signature: (l : List α) (H : SortedLT l)
  body: H.pairwise.nodup.getEquiv l
  map_rel_iff' := H.strictMono_get.le_iff_le

中文:
定义 SortedLT.getIso
  签名: (l : List α) (H : SortedLT l)
  定义体: H.pairwise.nodup.getEquiv l
  map_rel_iff' := H.strictMono_get.le_iff_le

Depends on / 依赖: H.pairwise.nodup.getEquiv, getEquiv, pairwise
-/
def SortedLT.getIso (l : List α) (H : SortedLT l) : Fin (length l) ≃o { x // x in l } where
  toEquiv := H.pairwise.nodup.getEquiv l
  map_rel_iff' := H.strictMono_get.le_iff_le

variable (H : SortedLT l) {x : { x // x in l }} {i : Fin l.length}

@[simp]
/--
theorem `SortedLT.coe_getIso_apply` / 定理 `SortedLT.coe_getIso_apply`

English:
theorem SortedLT.coe_getIso_apply
  statement: (H.getIso l i : α) = get l i
  proof: rfl

@[simp]

中文:
定理 SortedLT.coe_getIso_apply
  结论: (H.getIso l i : α) = get l i
  证明: rfl

@[simp]
-/
theorem SortedLT.coe_getIso_apply : (H.getIso l i : α) = get l i :=
  rfl

@[simp]
/--
theorem `SortedLT.coe_getIso_symm_apply` / 定理 `SortedLT.coe_getIso_symm_apply`

English:
theorem SortedLT.coe_getIso_symm_apply
  statement: ((H.getIso l).symm x : Nat) = idxOf (↑x) l
  proof: rfl

中文:
定理 SortedLT.coe_getIso_symm_apply
  结论: ((H.getIso l).symm x : 自然数) = idxOf (↑x) l
  证明: rfl
-/
theorem SortedLT.coe_getIso_symm_apply : ((H.getIso l).symm x : Nat) = idxOf (↑x) l :=
  rfl

end Sorted

section Sublist

/--
theorem `sublist_of_orderEmbedding_getElem?_eq` / 定理 `sublist_of_orderEmbedding_getElem?_eq`

English:
theorem sublist_of_orderEmbedding_getElem?_eq
  statement: {l l' : List α} (f : Nat ↪o Nat)
  proof: by
  induction l generalizing l' f with
  | nil => simp
  | cons hd tl IH => ?_
  have : some hd = l'[f 0]? := by simpa using hf 0
  rw [eq_comm]; rw [List.getElem?_eq_some_iff] at this
  obtain ⟨w, h⟩ := this
  let f' : Nat ↪o Nat :=
    OrderEmbedding.ofMapLEIff (fun i => f (i + 1) - (f 0 + 1)) fu

中文:
定理 sublist_of_orderEmbedding_getElem?_eq
  结论: {l l' : List α} (f : 自然数 ↪o 自然数)
  证明: by
  induction l generalizing l' f with
  | nil => simp
  | cons hd tl IH => ?_
  have : some hd = l'[f 0]? := by simpa using hf 0
  rw [eq_comm]; rw [List.getElem?_eq_some_iff] at this
  obtain ⟨w, h⟩ := this
  let f' : Nat ↪o Nat :=
    OrderEmbedding.ofMapLEIff (fun i => f (i + 1) - (f 0 + 1)) fu

Depends on / 依赖: List.getElem, Nat.sub_le_sub_iff_right, Nat.succ_le_iff, Nat.succ_le_succ_iff, OrderEmbedding, OrderEmbedding.le_iff_le, OrderEmbedding.lt_iff_lt, OrderEmbedding.ofMapLEIff, _eq_some_iff, b.succ_pos, eq_comm, generalizing, getElem, le_iff_le, lt_iff_lt, ofMapLEIff, sub_le_sub_iff_right, succ_le_iff, succ_le_succ_iff, succ_pos
-/
theorem sublist_of_orderEmbedding_getElem?_eq {l l' : List α} (f : Nat ↪o Nat)
    (hf : forall ix : Nat, l[ix]? = l'[f ix]?) : l <+ l' := by
  induction l generalizing l' f with
  | nil => simp
  | cons hd tl IH => ?_
  have : some hd = l'[f 0]? := by simpa using hf 0
  rw [eq_comm]; rw [List.getElem?_eq_some_iff] at this
  obtain ⟨w, h⟩ := this
  let f' : Nat ↪o Nat :=
    OrderEmbedding.ofMapLEIff (fun i => f (i + 1) - (f 0 + 1)) fun a b => by
      rw [Nat.sub_le_sub_iff_right]; rw [OrderEmbedding.le_iff_le]; rw [Nat.succ_le_succ_iff]
      rw [Nat.succ_le_iff]; rw [OrderEmbedding.lt_iff_lt]
      exact b.succ_pos
  have : forall ix, tl[ix]? = (l'.drop (f 0 + 1))[f' ix]? := by
    intro ix
    rw [List.getElem?_drop]; rw [OrderEmbedding.coe_ofMapLEIff]; rw [Nat.add_sub_cancel']; rw [← hf]
    · simp only [getElem?_cons_succ]
    rw [Nat.succ_le_iff]; rw [OrderEmbedding.lt_iff_lt]
    exact ix.succ_pos
  rw [← List.take_append_drop (f 0 + 1) l']; rw [← List.singleton_append]
  apply List.Sublist.append _ (IH _ this)
  rw [List.singleton_sublist]; rw [← h]; rw [l'.getElem_take' _ (Nat.lt_succ_self _)]
  exact List.getElem_mem _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `sublist_iff_exists_orderEmbedding_getElem?_eq` / 定理 `sublist_iff_exists_orderEmbedding_getElem?_eq`

English:
theorem sublist_iff_exists_orderEmbedding_getElem?_eq
  given: {l l' : List α}
  proof: by
  constructor
  · intro H
    induction H with
    | slnil => simp
    | cons _ _ IH =>
      obtain ⟨f, hf⟩ := IH
      refine ⟨f.trans (OrderEmbedding.ofStrictMono (· + 1) fun _ => by simp), ?_⟩
      simpa using hf
    | cons_cons _ _ IH =>
      obtain ⟨f, hf⟩ := IH
      refine
        ⟨Orde

中文:
定理 sublist_iff_exists_orderEmbedding_getElem?_eq
  条件: {l l' : List α}
  证明: by
  constructor
  · intro H
    induction H with
    | slnil => simp
    | cons _ _ IH =>
      obtain ⟨f, hf⟩ := IH
      refine ⟨f.trans (OrderEmbedding.ofStrictMono (· + 1) fun _ => by simp), ?_⟩
      simpa using hf
    | cons_cons _ _ IH =>
      obtain ⟨f, hf⟩ := IH
      refine
        ⟨Orde

Depends on / 依赖: Nat.succ_le_succ_iff, OrderEmbedding, OrderEmbedding.ofMapLEIff, OrderEmbedding.ofStrictMono, cons_cons, f.trans, ix.pred, ofMapLEIff, ofStrictMono, sublist_of_orderEmbedding_getElem, succ_le_succ_iff
-/
theorem sublist_iff_exists_orderEmbedding_getElem?_eq {l l' : List α} :
    l <+ l' ↔ exists f : Nat ↪o Nat, forall ix : Nat, l[ix]? = l'[f ix]? := by
  constructor
  · intro H
    induction H with
    | slnil => simp
    | cons _ _ IH =>
      obtain ⟨f, hf⟩ := IH
      refine ⟨f.trans (OrderEmbedding.ofStrictMono (· + 1) fun _ => by simp), ?_⟩
      simpa using hf
    | cons_cons _ _ IH =>
      obtain ⟨f, hf⟩ := IH
      refine
        ⟨OrderEmbedding.ofMapLEIff (fun ix : Nat => if ix = 0 then 0 else (f ix.pred).succ) ?_, ?_⟩
      · rintro ⟨_ | a⟩ ⟨_ | b⟩ <;> simp [Nat.succ_le_succ_iff]
      · rintro ⟨_ | i⟩
        · simp
        · simpa using hf _
  · rintro ⟨f, hf⟩
    exact sublist_of_orderEmbedding_getElem?_eq f hf

/--
theorem `sublist_iff_exists_fin_orderEmbedding_get_eq` / 定理 `sublist_iff_exists_fin_orderEmbedding_get_eq`

English:
theorem sublist_iff_exists_fin_orderEmbedding_get_eq
  given: {l l' : List α}
  proof: by
  rw [sublist_iff_exists_orderEmbedding_getElem?_eq]
  constructor
  · rintro ⟨f, hf⟩
    have h : forall {i : Nat}, i < l.length -> f i < l'.length := by
      intro i hi
      specialize hf i
      rw [getElem?_eq_getElem hi]; rw [eq_comm]; rw [getElem?_eq_some_iff] at hf
      obtain ⟨h, -⟩ :=

中文:
定理 sublist_iff_exists_fin_orderEmbedding_get_eq
  条件: {l l' : List α}
  证明: by
  rw [sublist_iff_exists_orderEmbedding_getElem?_eq]
  constructor
  · rintro ⟨f, hf⟩
    have h : forall {i : Nat}, i < l.length -> f i < l'.length := by
      intro i hi
      specialize hf i
      rw [getElem?_eq_getElem hi]; rw [eq_comm]; rw [getElem?_eq_some_iff] at hf
      obtain ⟨h, -⟩ :=

Depends on / 依赖: Option.some_injective, OrderEm, OrderEmbedding, OrderEmbedding.ofMapLEIff, _eq_getElem, _eq_some_iff, eq_comm, getElem, is_lt, ix.is_lt, l.length, length, ofMapLEIff, some_injective, specialize, sublist_iff_exists_orderEmbedding_getElem
-/
theorem sublist_iff_exists_fin_orderEmbedding_get_eq {l l' : List α} :
    l <+ l' ↔
      exists f : Fin l.length ↪o Fin l'.length,
        forall ix : Fin l.length, l.get ix = l'.get (f ix) := by
  rw [sublist_iff_exists_orderEmbedding_getElem?_eq]
  constructor
  · rintro ⟨f, hf⟩
    have h : forall {i : Nat}, i < l.length -> f i < l'.length := by
      intro i hi
      specialize hf i
      rw [getElem?_eq_getElem hi]; rw [eq_comm]; rw [getElem?_eq_some_iff] at hf
      obtain ⟨h, -⟩ := hf
      exact h
    refine ⟨OrderEmbedding.ofMapLEIff (fun ix => ⟨f ix, h ix.is_lt⟩) ?_, ?_⟩
    · simp
    · intro i
      apply Option.some_injective
      simpa [getElem?_eq_getElem i.2, getElem?_eq_getElem (h i.2)] using hf i
  · rintro ⟨f, hf⟩
    refine
      ⟨OrderEmbedding.ofStrictMono (fun i => if hi : i < l.length then f ⟨i, hi⟩ else i + l'.length)
          ?_,
        ?_⟩
    · intro i j h
      dsimp only
      split_ifs with hi hj hj
      · rwa [Fin.val_fin_lt, f.lt_iff_lt]
      · lia
      · exact absurd (h.trans hj) hi
      · simpa using h
    · grind

set_option backward.isDefEq.respectTransparency false in
/--
theorem `duplicate_iff_exists_distinct_get` / 定理 `duplicate_iff_exists_distinct_get`

English:
theorem duplicate_iff_exists_distinct_get
  given: {l : List α} {x : α}
  proof: by
  classical
    rw [duplicate_iff_two_le_count]; rw [← replicate_sublist_iff]; rw [sublist_iff_exists_fin_orderEmbedding_get_eq]
    constructor
    · rintro ⟨f, hf⟩
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f.lt_iff_lt.2 (Nat.zero_lt_one), ?_⟩
      rw [← hf]; rw [← hf]; simp
    · rintro ⟨n

中文:
定理 duplicate_iff_exists_distinct_get
  条件: {l : List α} {x : α}
  证明: by
  classical
    rw [duplicate_iff_two_le_count]; rw [← replicate_sublist_iff]; rw [sublist_iff_exists_fin_orderEmbedding_get_eq]
    constructor
    · rintro ⟨f, hf⟩
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f.lt_iff_lt.2 (Nat.zero_lt_one), ?_⟩
      rw [← hf]; rw [← hf]; simp
    · rintro ⟨n

Depends on / 依赖: Nat.lt_succ_iff, Nat.succ_le_succ_iff, Nat.zero_lt_one, OrderEmbedding, OrderEmbedding.ofStrictMono, classical, duplicate_iff_two_le_count, f.lt_iff_lt, lt_iff_lt, lt_succ_iff, ofStrictMono, replicate, replicate_sublist_iff, sublist_iff_exists_fin_orderEmbedding_get_eq, succ_le_succ_iff, zero_lt_one
-/
theorem duplicate_iff_exists_distinct_get {l : List α} {x : α} :
    l.Duplicate x ↔
      exists (n m : Fin l.length) (_ : n < m),
        x = l.get n ∧ x = l.get m := by
  classical
    rw [duplicate_iff_two_le_count]; rw [← replicate_sublist_iff]; rw [sublist_iff_exists_fin_orderEmbedding_get_eq]
    constructor
    · rintro ⟨f, hf⟩
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f.lt_iff_lt.2 (Nat.zero_lt_one), ?_⟩
      rw [← hf]; rw [← hf]; simp
    · rintro ⟨n, m, hnm, h, h'⟩
      refine ⟨OrderEmbedding.ofStrictMono (fun i => if (i : Nat) = 0 then n else m) ?_, ?_⟩
      · rintro ⟨⟨_ | i⟩, hi⟩ ⟨⟨_ | j⟩, hj⟩
        · simp
        · simp [hnm]
        · simp
        · simp only [Nat.lt_succ_iff, Nat.succ_le_succ_iff, replicate, length, Nat.le_zero] at hi hj
          simp [hi, hj]
      · rintro ⟨⟨_ | i⟩, hi⟩
        · simpa using h
        · simpa using h'

end Sublist

end List
