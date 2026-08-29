/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Wrenna Robson
-/
module

public import Batteries.Data.List.Pairwise
public import Batteries.Data.List.Perm
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Nodup
public import Mathlib.Order.Fin.Basic

/-!
# Sorting algorithms on lists

In this file we define the sorting algorithm `List.insertionSort r` and prove
that we have `(l.insertionSort r l).Pairwise r` under suitable conditions on `r`.

We then define `List.SortedLE`, `List.SortedGE`, `List.SortedLT` and `List.SortedGT`,
predicates which are equivalent to `List.Pairwise` when the relation derives from a
preorder (but which are defined in terms of the monotonicity predicates).
-/

public section

namespace List

section sort

variable {α β : Type*} (r : α -> α -> Prop) (s : β -> β -> Prop)

variable [DecidableRel r] [DecidableRel s]

local infixl:50 " ≼ " => r
local infixl:50 " ≼ " => s

/-! ### Insertion sort -/

section InsertionSort

/--
Definition of `orderedInsert` / `orderedInsert` 的定义

English:
definition orderedInsert
  signature: (a : α)

中文:
定义 orderedInsert
  签名: (a : α)
-/
def orderedInsert (a : α) : List α -> List α
  | [] => [a]
  | b :: l => if a ≼ b then a :: b :: l else b :: orderedInsert a l

/--
theorem `orderedInsert_nil` / 定理 `orderedInsert_nil`

English:
theorem orderedInsert_nil
  given: (a : α)
  statement: [].orderedInsert r a = [a]
  proof: .refl _

中文:
定理 orderedInsert_nil
  条件: (a : α)
  结论: [].orderedInsert r a = [a]
  证明: .refl _
-/
@[simp, grind =] theorem orderedInsert_nil (a : α) : [].orderedInsert r a = [a] := .refl _

/--
theorem `orderedInsert_cons` / 定理 `orderedInsert_cons`

English:
theorem orderedInsert_cons
  given: (a b : α) (l : List α)
  proof: .refl _

中文:
定理 orderedInsert_cons
  条件: (a b : α) (l : 列表 α)
  证明: .refl _
-/
@[simp, grind =] theorem orderedInsert_cons (a b : α) (l : List α) :
    (b :: l).orderedInsert r a = if r a b then a :: b :: l else b :: l.orderedInsert r a :=
  .refl _

/--
theorem `orderedInsert_cons_of_le` / 定理 `orderedInsert_cons_of_le`

English:
theorem orderedInsert_cons_of_le
  given: {a b : α} (l : List α) (h : a ≼ b)
  proof: dif_pos h

中文:
定理 orderedInsert_cons_of_le
  条件: {a b : α} (l : 列表 α) (h : a ≼ b)
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
theorem orderedInsert_cons_of_le {a b : α} (l : List α) (h : a ≼ b) :
    orderedInsert r a (b :: l) = a :: b :: l :=
  dif_pos h

/--
theorem `orderedInsert_of_not_le` / 定理 `orderedInsert_of_not_le`

English:
theorem orderedInsert_of_not_le
  given: {a b : α} (l : List α) (h : ¬ a ≼ b)
  proof: dif_neg h

中文:
定理 orderedInsert_of_not_le
  条件: {a b : α} (l : 列表 α) (h : ¬ a ≼ b)
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
theorem orderedInsert_of_not_le {a b : α} (l : List α) (h : ¬ a ≼ b) :
    orderedInsert r a (b :: l) = b :: orderedInsert r a l := dif_neg h

/--
Definition of `insertionSort` / `insertionSort` 的定义

English:
definition insertionSort
  signature: : List α -> List α
  body: foldr (orderedInsert r) []

@[simp, grind =]

中文:
定义 insertionSort
  签名: : 列表 α -> 列表 α
  定义体: foldr (orderedInsert r) []

@[simp, grind =]

Depends on / 依赖: orderedInsert
-/
def insertionSort : List α -> List α := foldr (orderedInsert r) []

@[simp, grind =]
/--
theorem `insertionSort_nil` / 定理 `insertionSort_nil`

English:
theorem insertionSort_nil
  statement: [].insertionSort r = []
  proof: .refl _

中文:
定理 insertionSort_nil
  结论: [].insertionSort r = []
  证明: .refl _
-/
theorem insertionSort_nil : [].insertionSort r = [] := .refl _

/--
theorem `insertionSort_cons` / 定理 `insertionSort_cons`

English:
theorem insertionSort_cons
  given: (a : α) (l : List α)
  proof: .refl _

中文:
定理 insertionSort_cons
  条件: (a : α) (l : 列表 α)
  证明: .refl _
-/
@[simp, grind =] theorem insertionSort_cons (a : α) (l : List α) :
    (a :: l).insertionSort r = orderedInsert r a (insertionSort r l) := .refl _

-- A quick check that insertionSort is stable:
example :
    insertionSort (fun m n => m / 10 <= n / 10) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12] =
      [5, 7, 2, 17, 12, 27, 23, 43, 95, 98, 221, 567] := rfl

/--
theorem `orderedInsert_length` / 定理 `orderedInsert_length`

English:
theorem orderedInsert_length
  given: (L : List α) (a : α)
  proof: by
  induction L <;> grind

中文:
定理 orderedInsert_length
  条件: (L : 列表 α) (a : α)
  证明: by
  induction L <;> grind

Depends on / 依赖: Nonempty, Nonempty.of_image2_left, of_image2_left
-/
theorem orderedInsert_length (L : List α) (a : α) :
    (L.orderedInsert r a).length = L.length + 1 := by
  induction L <;> grind

/--
theorem `orderedInsert_eq_take_drop` / 定理 `orderedInsert_eq_take_drop`

English:
theorem orderedInsert_eq_take_drop
  given: (a : α) (l : List α)
  proof: by
  induction l <;> grind [takeWhile, dropWhile]

中文:
定理 orderedInsert_eq_take_drop
  条件: (a : α) (l : 列表 α)
  证明: by
  induction l <;> grind [takeWhile, dropWhile]

Depends on / 依赖: Nonempty, Nonempty.of_image2_right, dropWhile, of_image2_right, takeWhile
-/
theorem orderedInsert_eq_take_drop (a : α) (l : List α) :
    l.orderedInsert r a = (l.takeWhile fun b => ¬a ≼ b) ++ a :: l.dropWhile fun b => ¬a ≼ b := by
  induction l <;> grind [takeWhile, dropWhile]

/--
theorem `insertionSort_cons_eq_take_drop` / 定理 `insertionSort_cons_eq_take_drop`

English:
theorem insertionSort_cons_eq_take_drop
  given: (a : α) (l : List α)
  proof: orderedInsert_eq_take_drop r a _

@[simp]

中文:
定理 insertionSort_cons_eq_take_drop
  条件: (a : α) (l : 列表 α)
  证明: orderedInsert_eq_take_drop r a _

@[simp]

Depends on / 依赖: orderedInsert_eq_take_drop
-/
theorem insertionSort_cons_eq_take_drop (a : α) (l : List α) :
    insertionSort r (a :: l) =
      ((insertionSort r l).takeWhile fun b => ¬a ≼ b) ++
        a :: (insertionSort r l).dropWhile fun b => ¬a ≼ b :=
  orderedInsert_eq_take_drop r a _

@[simp]
/--
theorem `mem_orderedInsert` / 定理 `mem_orderedInsert`

English:
theorem mem_orderedInsert
  given: {a b : α} {l : List α}
  proof: by
  induction l <;> grind

中文:
定理 mem_orderedInsert
  条件: {a b : α} {l : 列表 α}
  证明: by
  induction l <;> grind
-/
theorem mem_orderedInsert {a b : α} {l : List α} :
    a in orderedInsert r b l ↔ a = b ∨ a in l := by
  induction l <;> grind

/--
theorem `map_orderedInsert` / 定理 `map_orderedInsert`

English:
theorem map_orderedInsert
  statement: (f : α -> β) (l : List α) (x : α)
  proof: by
  induction l <;> grind

中文:
定理 map_orderedInsert
  结论: (f : α -> β) (l : 列表 α) (x : α)
  证明: by
  induction l <;> grind
-/
theorem map_orderedInsert (f : α -> β) (l : List α) (x : α)
    (hl₁ : forall a in l, a ≼ x ↔ f a ≼ f x) (hl₂ : forall a in l, x ≼ a ↔ f x ≼ f a) :
    (l.orderedInsert r x).map f = (l.map f).orderedInsert s (f x) := by
  induction l <;> grind

section Correctness

/--
theorem `perm_orderedInsert` / 定理 `perm_orderedInsert`

English:
theorem perm_orderedInsert
  given: (a)
  statement: forall l : List α, orderedInsert r a l ~ a :: l

中文:
定理 perm_orderedInsert
  条件: (a)
  结论: 对任意 l : 列表 α, orderedInsert r a l ~ a :: l
-/
theorem perm_orderedInsert (a) : forall l : List α, orderedInsert r a l ~ a :: l
  | [] => Perm.refl _
  | b :: l => by
    by_cases h : a ≼ b
    · simp [h]
    · simpa [h] using ((perm_orderedInsert a l).cons _).trans (Perm.swap _ _ _)

/--
theorem `orderedInsert_count` / 定理 `orderedInsert_count`

English:
theorem orderedInsert_count
  given: [DecidableEq α] (L : List α) (a b : α)
  proof: by
  rw [(L.perm_orderedInsert r b).count_eq]; rw [count_cons]
  simp

中文:
定理 orderedInsert_count
  条件: [DecidableEq α] (L : 列表 α) (a b : α)
  证明: by
  rw [(L.perm_orderedInsert r b).count_eq]; rw [count_cons]
  simp

Depends on / 依赖: L.perm_orderedInsert, count_cons, count_eq, perm_orderedInsert
-/
theorem orderedInsert_count [DecidableEq α] (L : List α) (a b : α) :
    count a (L.orderedInsert r b) = count a L + if b = a then 1 else 0 := by
  rw [(L.perm_orderedInsert r b).count_eq]; rw [count_cons]
  simp

/--
theorem `perm_insertionSort` / 定理 `perm_insertionSort`

English:
theorem perm_insertionSort
  given: (l : List α)
  statement: insertionSort r l ~ l
  proof: by
  induction l <;> grind [List.Perm, perm_orderedInsert]

@[simp]

中文:
定理 perm_insertionSort
  条件: (l : 列表 α)
  结论: insertionSort r l ~ l
  证明: by
  induction l <;> grind [List.Perm, perm_orderedInsert]

@[simp]

Depends on / 依赖: List.Perm, perm_orderedInsert
-/
theorem perm_insertionSort (l : List α) : insertionSort r l ~ l := by
  induction l <;> grind [List.Perm, perm_orderedInsert]

@[simp]
/--
theorem `mem_insertionSort` / 定理 `mem_insertionSort`

English:
theorem mem_insertionSort
  given: {l : List α} {x : α}
  statement: x in l.insertionSort r ↔ x in l
  proof: (perm_insertionSort r l).mem_iff

@[simp]

中文:
定理 mem_insertionSort
  条件: {l : 列表 α} {x : α}
  结论: x in l.insertionSort r ↔ x in l
  证明: (perm_insertionSort r l).mem_iff

@[simp]

Depends on / 依赖: mem_iff, perm_insertionSort
-/
theorem mem_insertionSort {l : List α} {x : α} : x in l.insertionSort r ↔ x in l :=
  (perm_insertionSort r l).mem_iff

@[simp]
/--
theorem `length_insertionSort` / 定理 `length_insertionSort`

English:
theorem length_insertionSort
  given: (l : List α)
  statement: (insertionSort r l).length = l.length
  proof: (perm_insertionSort r _).length_eq

中文:
定理 length_insertionSort
  条件: (l : 列表 α)
  结论: (insertionSort r l).length = l.length
  证明: (perm_insertionSort r _).length_eq

Depends on / 依赖: length_eq, perm_insertionSort
-/
theorem length_insertionSort (l : List α) : (insertionSort r l).length = l.length :=
  (perm_insertionSort r _).length_eq

/--
theorem `insertionSort_cons_of_forall_rel` / 定理 `insertionSort_cons_of_forall_rel`

English:
theorem insertionSort_cons_of_forall_rel
  given: {a : α} {l : List α} (h : forall b in l, r a b)
  proof: by
  rw [insertionSort_cons]
  cases hi : insertionSort r l with
  | nil => rfl
  | cons b m =>
    rw [orderedInsert_cons_of_le]
apply h b (mem_insertionSort r).1 _
    rw [hi]
    exact mem_cons_self

中文:
定理 insertionSort_cons_of_对任意_rel
  条件: {a : α} {l : 列表 α} (h : 对任意 b in l, r a b)
  证明: by
  rw [insertionSort_cons]
  cases hi : insertionSort r l with
  | nil => rfl
  | cons b m =>
    rw [orderedInsert_cons_of_le]
apply h b (mem_insertionSort r).1 _
    rw [hi]
    exact mem_cons_self

Depends on / 依赖: insertionSort, insertionSort_cons, mem_cons_self, mem_insertionSort, orderedInsert_cons_of_le
-/
theorem insertionSort_cons_of_forall_rel {a : α} {l : List α} (h : forall b in l, r a b) :
    insertionSort r (a :: l) = a :: insertionSort r l := by
  rw [insertionSort_cons]
  cases hi : insertionSort r l with
  | nil => rfl
  | cons b m =>
    rw [orderedInsert_cons_of_le]
apply h b (mem_insertionSort r).1 _
    rw [hi]
    exact mem_cons_self

/--
theorem `map_insertionSort` / 定理 `map_insertionSort`

English:
theorem map_insertionSort
  given: (f : α -> β) (l : List α) (hl : forall a in l, forall b in l, a ≼ b ↔ f a ≼ f b)
  proof: by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp_rw [List.forall_mem_cons, forall_and] at hl
    simp_rw [List.map, insertionSort_cons]
    rw [List.map_orderedInsert _ s]; rw [ih hl.2.2]
    · simpa only [mem_insertionSort] using hl.2.1
    · simpa only [mem_insertionSort] using hl.1.2

中文:
定理 map_insertionSort
  条件: (f : α -> β) (l : 列表 α) (hl : 对任意 a in l, 对任意 b in l, a ≼ b ↔ f a ≼ f b)
  证明: by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp_rw [List.forall_mem_cons, forall_and] at hl
    simp_rw [List.map, insertionSort_cons]
    rw [List.map_orderedInsert _ s]; rw [ih hl.2.2]
    · simpa only [mem_insertionSort] using hl.2.1
    · simpa only [mem_insertionSort] using hl.1.2

Depends on / 依赖: List.forall_mem_cons, List.map, List.map_orderedInsert, forall_and, forall_mem_cons, insertionSort_cons, map_orderedInsert, mem_insertionSort, simp_rw
-/
theorem map_insertionSort (f : α -> β) (l : List α) (hl : forall a in l, forall b in l, a ≼ b ↔ f a ≼ f b) :
    (l.insertionSort r).map f = (l.map f).insertionSort s := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp_rw [List.forall_mem_cons, forall_and] at hl
    simp_rw [List.map, insertionSort_cons]
    rw [List.map_orderedInsert _ s]; rw [ih hl.2.2]
    · simpa only [mem_insertionSort] using hl.2.1
    · simpa only [mem_insertionSort] using hl.1.2

variable {r}

/--
theorem `Pairwise.insertionSort_eq` / 定理 `Pairwise.insertionSort_eq`

English:
theorem Pairwise.insertionSort_eq
  given: {l : List α}
  statement: Pairwise r l -> insertionSort r l = l
  proof: by
  induction l <;> grind [cases List]

中文:
定理 两两.insertionSort_eq
  条件: {l : 列表 α}
  结论: 两两 r l -> insertionSort r l = l
  证明: by
  induction l <;> grind [cases List]
-/
theorem Pairwise.insertionSort_eq {l : List α} : Pairwise r l -> insertionSort r l = l := by
  induction l <;> grind [cases List]

/--
theorem `erase_orderedInsert` / 定理 `erase_orderedInsert`

English:
theorem erase_orderedInsert
  given: [DecidableEq α] [Std.Refl r] (x : α) (xs : List α)
  proof: by
  induction xs <;> grind [Std.Refl]

中文:
定理 erase_orderedInsert
  条件: [DecidableEq α] [Std.Refl r] (x : α) (xs : 列表 α)
  证明: by
  induction xs <;> grind [Std.Refl]

Depends on / 依赖: Std.Refl
-/
theorem erase_orderedInsert [DecidableEq α] [Std.Refl r] (x : α) (xs : List α) :
    (xs.orderedInsert r x).erase x = xs := by
  induction xs <;> grind [Std.Refl]

/--
theorem `erase_orderedInsert_of_notMem` / 定理 `erase_orderedInsert_of_notMem`

English:
theorem erase_orderedInsert_of_notMem
  statement: [DecidableEq α]
  proof: by
  induction xs <;> grind

中文:
定理 erase_orderedInsert_of_notMem
  结论: [DecidableEq α]
  证明: by
  induction xs <;> grind
-/
theorem erase_orderedInsert_of_notMem [DecidableEq α]
    {x : α} {xs : List α} (hx : x ∉ xs) :
    (xs.orderedInsert r x).erase x = xs := by
  induction xs <;> grind

/--
theorem `orderedInsert_erase` / 定理 `orderedInsert_erase`

English:
theorem orderedInsert_erase
  statement: [DecidableEq α] [Std.Antisymm r] (x : α) (xs : List α) (hx : x in xs)
  proof: by
  induction xs with grind +splitIndPred

中文:
定理 orderedInsert_erase
  结论: [DecidableEq α] [Std.反对称 r] (x : α) (xs : 列表 α) (hx : x in xs)
  证明: by
  induction xs with grind +splitIndPred

Depends on / 依赖: splitIndPred
-/
theorem orderedInsert_erase [DecidableEq α] [Std.Antisymm r] (x : α) (xs : List α) (hx : x in xs)
    (hxs : Pairwise r xs) :
    (xs.erase x).orderedInsert r x = xs := by
  induction xs with grind +splitIndPred

/--
theorem `sublist_orderedInsert` / 定理 `sublist_orderedInsert`

English:
theorem sublist_orderedInsert
  given: (x : α) (xs : List α)
  statement: xs <+ xs.orderedInsert r x
  proof: by
  induction xs <;> grind

中文:
定理 sublist_orderedInsert
  条件: (x : α) (xs : 列表 α)
  结论: xs <+ xs.orderedInsert r x
  证明: by
  induction xs <;> grind
-/
theorem sublist_orderedInsert (x : α) (xs : List α) : xs <+ xs.orderedInsert r x := by
  induction xs <;> grind

/--
theorem `cons_sublist_orderedInsert` / 定理 `cons_sublist_orderedInsert`

English:
theorem cons_sublist_orderedInsert
  given: {l c : List α} {a : α} (hl : c <+ l) (ha : forall a' in c, a ≼ a')
  proof: by
  induction l <;> grind

中文:
定理 cons_sublist_orderedInsert
  条件: {l c : 列表 α} {a : α} (hl : c <+ l) (ha : 对任意 a' in c, a ≼ a')
  证明: by
  induction l <;> grind
-/
theorem cons_sublist_orderedInsert {l c : List α} {a : α} (hl : c <+ l) (ha : forall a' in c, a ≼ a') :
    a :: c <+ orderedInsert r a l := by
  induction l <;> grind

/--
theorem `Sublist.orderedInsert_sublist` / 定理 `Sublist.orderedInsert_sublist`

English:
theorem Sublist.orderedInsert_sublist
  statement: [IsTrans α r] {as bs} (x) (hs : as <+ bs)
  proof: by
  cases as with
  | nil => simp
  | cons a as =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      unfold orderedInsert
      cases hs <;> split_ifs with hr
· exact .cons_cons _ .cons _ ‹a :: as <+ bs›
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs› hb.of_cons
        simp only [hr, orderedInsert_cons, ite_true] at ih
exact .trans ih .cons _ (.refl _)
.left _ (mem_of_cons_sublist ‹a :: as <+ bs›) · have hba := pairwise_cons.mp hb
        exact absurd (trans_of _ ‹r x b› hba) hr
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs› hb.of_cons
        rw [orderedInsert_cons]; rw [if_neg hr] at ih
        exact .cons _ ih
      · simp_all
· exact .cons_cons _ orderedInsert_sublist x ‹as <+ bs› hb.of_cons

中文:
定理 子表.orderedInsert_sublist
  结论: [是Trans α r] {as bs} (x) (hs : as <+ bs)
  证明: by
  cases as with
  | nil => simp
  | cons a as =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      unfold orderedInsert
      cases hs <;> split_ifs with hr
· exact .cons_cons _ .cons _ ‹a :: as <+ bs›
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs› hb.of_cons
        simp only [hr, orderedInsert_cons, ite_true] at ih
exact .trans ih .cons _ (.refl _)
.left _ (mem_of_cons_sublist ‹a :: as <+ bs›) · have hba := pairwise_cons.mp hb
        exact absurd (trans_of _ ‹r x b› hba) hr
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs› hb.of_cons
        rw [orderedInsert_cons]; rw [if_neg hr] at ih
        exact .cons _ ih
      · simp_all
· exact .cons_cons _ orderedInsert_sublist x ‹as <+ bs› hb.of_cons

Depends on / 依赖: absurd, cons_cons, hb.of_cons, ite_true, mem_of_cons_sublist, of_cons, orderedInsert, orderedInsert_cons, orderedInsert_sublist, pairwise_cons, pairwise_cons.mp, split_ifs, trans_of
-/
theorem Sublist.orderedInsert_sublist [IsTrans α r] {as bs} (x) (hs : as <+ bs)
    (hb : bs.Pairwise r) : orderedInsert r x as <+ orderedInsert r x bs := by
  cases as with
  | nil => simp
  | cons a as =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      unfold orderedInsert
      cases hs <;> split_ifs with hr
· exact .cons_cons _ .cons _ ‹a :: as <+ bs›
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs› hb.of_cons
        simp only [hr, orderedInsert_cons, ite_true] at ih
exact .trans ih .cons _ (.refl _)
.left _ (mem_of_cons_sublist ‹a :: as <+ bs›) · have hba := pairwise_cons.mp hb
        exact absurd (trans_of _ ‹r x b› hba) hr
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs› hb.of_cons
        rw [orderedInsert_cons]; rw [if_neg hr] at ih
        exact .cons _ ih
      · simp_all
· exact .cons_cons _ orderedInsert_sublist x ‹as <+ bs› hb.of_cons

section TotalAndTransitive

variable [Std.Total r] [IsTrans α r]

/--
theorem `Pairwise.orderedInsert` / 定理 `Pairwise.orderedInsert`

English:
theorem Pairwise.orderedInsert
  given: (a : α)
  statement: forall l, Pairwise r l -> Pairwise r (orderedInsert r a l)

中文:
定理 两两.orderedInsert
  条件: (a : α)
  结论: 对任意 l, 两两 r l -> 两两 r (orderedInsert r a l)
-/
theorem Pairwise.orderedInsert (a : α) : forall l, Pairwise r l -> Pairwise r (orderedInsert r a l)
  | [], _ => pairwise_singleton _ a
  | b :: l, h => by
    by_cases h' : a ≼ b
    · grind
    · suffices forall b' : α, b' in List.orderedInsert r a l -> r b b' by
        simpa [orderedInsert_cons, h', h.of_cons.orderedInsert a l]
      intro b' bm
      rcases (mem_orderedInsert r).mp bm with rfl | bm
      · exact (total_of r _ _).resolve_left h'
      · exact rel_of_pairwise_cons h bm

variable (r)

/--
theorem `pairwise_insertionSort` / 定理 `pairwise_insertionSort`

English:
theorem pairwise_insertionSort
  statement: forall l, Pairwise r (insertionSort r l)

中文:
定理 pairwise_insertionSort
  结论: 对任意 l, 两两 r (insertionSort r l)
-/
theorem pairwise_insertionSort : forall l, Pairwise r (insertionSort r l)
  | [] => Pairwise.nil
  | a :: l => (pairwise_insertionSort l).orderedInsert a _

end TotalAndTransitive

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
theorem `sublist_insertionSort` / 定理 `sublist_insertionSort`

English:
theorem sublist_insertionSort
  given: {l c : List α} (hr : c.Pairwise r) (hc : c <+ l)
  proof: by
  induction l generalizing c with
  | nil => grind
  | cons _ _ ih =>
    cases hc with
.trans (sublist_orderedInsert ..) | cons _ h => exact ih hr h
    | cons_cons _ h =>
      obtain ⟨hr, hp⟩ := pairwise_cons.mp hr
      exact cons_sublist_orderedInsert (ih hp h) hr

中文:
定理 sublist_insertionSort
  条件: {l c : 列表 α} (hr : c.两两 r) (hc : c <+ l)
  证明: by
  induction l generalizing c with
  | nil => grind
  | cons _ _ ih =>
    cases hc with
.trans (sublist_orderedInsert ..) | cons _ h => exact ih hr h
    | cons_cons _ h =>
      obtain ⟨hr, hp⟩ := pairwise_cons.mp hr
      exact cons_sublist_orderedInsert (ih hp h) hr

Depends on / 依赖: cons_cons, cons_sublist_orderedInsert, generalizing, pairwise_cons, pairwise_cons.mp, sublist_orderedInsert
-/
theorem sublist_insertionSort {l c : List α} (hr : c.Pairwise r) (hc : c <+ l) :
    c <+ insertionSort r l := by
  induction l generalizing c with
  | nil => grind
  | cons _ _ ih =>
    cases hc with
.trans (sublist_orderedInsert ..) | cons _ h => exact ih hr h
    | cons_cons _ h =>
      obtain ⟨hr, hp⟩ := pairwise_cons.mp hr
      exact cons_sublist_orderedInsert (ih hp h) hr

/--
theorem `pair_sublist_insertionSort` / 定理 `pair_sublist_insertionSort`

English:
theorem pair_sublist_insertionSort
  given: {a b : α} {l : List α} (hab : r a b) (h : [a, b] <+ l)
  proof: sublist_insertionSort (pairwise_pair.mpr hab) h

中文:
定理 pair_sublist_insertionSort
  条件: {a b : α} {l : 列表 α} (hab : r a b) (h : [a, b] <+ l)
  证明: sublist_insertionSort (pairwise_pair.mpr hab) h

Depends on / 依赖: pairwise_pair, pairwise_pair.mpr, sublist_insertionSort
-/
theorem pair_sublist_insertionSort {a b : α} {l : List α} (hab : r a b) (h : [a, b] <+ l) :
    [a, b] <+ insertionSort r l :=
  sublist_insertionSort (pairwise_pair.mpr hab) h

variable [Std.Antisymm r] [Std.Total r] [IsTrans α r]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
theorem `sublist_insertionSort'` / 定理 `sublist_insertionSort'`

English:
theorem sublist_insertionSort'
  given: {l c : List α} (hs : c.Pairwise r) (hc : c <+~ l)
  proof: by
  classical
  obtain ⟨d, hc, hd⟩ := hc
  induction l generalizing c d with
  | nil => grind [nil_perm]
  | cons a _ ih =>
    cases hd with
.trans (sublist_orderedInsert ..) | cons _ h => exact ih hs _ hc h
    | cons_cons _ h =>
      specialize ih (hs.erase _) _ (erase_cons_head a ‹List _› ▸ hc.erase a) h
have hm := hc.mem_iff.mp mem_cons_self ..
      have he := orderedInsert_erase _ _ hm hs
      exact he ▸ Sublist.orderedInsert_sublist _ ih (pairwise_insertionSort ..)

中文:
定理 sublist_insertionSort'
  条件: {l c : 列表 α} (hs : c.两两 r) (hc : c <+~ l)
  证明: by
  classical
  obtain ⟨d, hc, hd⟩ := hc
  induction l generalizing c d with
  | nil => grind [nil_perm]
  | cons a _ ih =>
    cases hd with
.trans (sublist_orderedInsert ..) | cons _ h => exact ih hs _ hc h
    | cons_cons _ h =>
      specialize ih (hs.erase _) _ (erase_cons_head a ‹List _› ▸ hc.erase a) h
have hm := hc.mem_iff.mp mem_cons_self ..
      have he := orderedInsert_erase _ _ hm hs
      exact he ▸ Sublist.orderedInsert_sublist _ ih (pairwise_insertionSort ..)

Depends on / 依赖: Sublist, Sublist.orderedInsert_sublist, classical, cons_cons, erase_cons_head, generalizing, hc.erase, hc.mem_iff.mp, hs.erase, mem_cons_self, mem_iff, nil_perm, orderedInsert_erase, orderedInsert_sublist, pairwise_insertionSort, specialize, sublist_orderedInsert
-/
theorem sublist_insertionSort' {l c : List α} (hs : c.Pairwise r) (hc : c <+~ l) :
    c <+ insertionSort r l := by
  classical
  obtain ⟨d, hc, hd⟩ := hc
  induction l generalizing c d with
  | nil => grind [nil_perm]
  | cons a _ ih =>
    cases hd with
.trans (sublist_orderedInsert ..) | cons _ h => exact ih hs _ hc h
    | cons_cons _ h =>
      specialize ih (hs.erase _) _ (erase_cons_head a ‹List _› ▸ hc.erase a) h
have hm := hc.mem_iff.mp mem_cons_self ..
      have he := orderedInsert_erase _ _ hm hs
      exact he ▸ Sublist.orderedInsert_sublist _ ih (pairwise_insertionSort ..)

/--
theorem `pair_sublist_insertionSort'` / 定理 `pair_sublist_insertionSort'`

English:
theorem pair_sublist_insertionSort'
  given: {a b : α} {l : List α} (hab : a ≼ b) (h : [a, b] <+~ l)
  proof: sublist_insertionSort' (pairwise_pair.mpr hab) h

中文:
定理 pair_sublist_insertionSort'
  条件: {a b : α} {l : 列表 α} (hab : a ≼ b) (h : [a, b] <+~ l)
  证明: sublist_insertionSort' (pairwise_pair.mpr hab) h

Depends on / 依赖: pairwise_pair, pairwise_pair.mpr, sublist_insertionSort
-/
theorem pair_sublist_insertionSort' {a b : α} {l : List α} (hab : a ≼ b) (h : [a, b] <+~ l) :
    [a, b] <+ insertionSort r l :=
  sublist_insertionSort' (pairwise_pair.mpr hab) h

end Correctness

end InsertionSort

/-! ### Merge sort

We provide some wrapper functions around the theorems for `mergeSort` provided in Lean,
which rather than using explicit hypotheses for transitivity and totality,
use Mathlib order typeclasses instead.
-/

set_option linter.hashCommand false in
#guard mergeSort [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12] (fun m n => m / 10 <= n / 10) =
  [5, 7, 2, 17, 12, 27, 23, 43, 95, 98, 221, 567]

section MergeSort

section Correctness

section Antisymm

variable {r : α -> α -> Prop} [Std.Antisymm r]

/--
theorem `Perm.eq_of_pairwise'` / 定理 `Perm.eq_of_pairwise'`

English:
theorem Perm.eq_of_pairwise'
  given: {l₁ l₂ : List α}
  proof: eq_of_pairwise (fun _ _ _ _ => antisymm)

中文:
定理 置换.eq_of_pairwise'
  条件: {l₁ l₂ : 列表 α}
  证明: eq_of_pairwise (fun _ _ _ _ => antisymm)

Depends on / 依赖: antisymm, eq_of_pairwise
-/
theorem Perm.eq_of_pairwise' {l₁ l₂ : List α} :
    Pairwise r l₁ -> Pairwise r l₂ -> (hl : l₁ ~ l₂) -> l₁ = l₂ :=
  eq_of_pairwise (fun _ _ _ _ => antisymm)

/--
theorem `sublist_of_subperm_of_pairwise` / 定理 `sublist_of_subperm_of_pairwise`

English:
theorem sublist_of_subperm_of_pairwise
  statement: {l₁ l₂ : List α} (hp : l₁ <+~ l₂)
  proof: by
  let ⟨_, h, h'⟩ := hp
  exact Sublist.trans (h.eq_of_pairwise' (hs₂.sublist h') hs₁ ▸ Sublist.refl _) h'

中文:
定理 sublist_of_subperm_of_pairwise
  结论: {l₁ l₂ : 列表 α} (hp : l₁ <+~ l₂)
  证明: by
  let ⟨_, h, h'⟩ := hp
  exact Sublist.trans (h.eq_of_pairwise' (hs₂.sublist h') hs₁ ▸ Sublist.refl _) h'

Depends on / 依赖: Sublist, Sublist.refl, Sublist.trans, eq_of_pairwise, h.eq_of_pairwise, sublist
-/
theorem sublist_of_subperm_of_pairwise {l₁ l₂ : List α} (hp : l₁ <+~ l₂)
    (hs₁ : l₁.Pairwise r) (hs₂ : l₂.Pairwise r) : l₁ <+ l₂ := by
  let ⟨_, h, h'⟩ := hp
  exact Sublist.trans (h.eq_of_pairwise' (hs₂.sublist h') hs₁ ▸ Sublist.refl _) h'

/--
theorem `Subset.antisymm_of_pairwise` / 定理 `Subset.antisymm_of_pairwise`

English:
theorem Subset.antisymm_of_pairwise
  statement: [Std.Irrefl r] {l₁ l₂ : List α}
  proof: ((subperm_of_subset h₁.nodup hl₁₂).antisymm
    (subperm_of_subset h₂.nodup hl₁₂')).eq_of_pairwise' h₁ h₂

中文:
定理 子集.antisymm_of_pairwise
  结论: [Std.Irrefl r] {l₁ l₂ : 列表 α}
  证明: ((subperm_of_subset h₁.nodup hl₁₂).antisymm
    (subperm_of_subset h₂.nodup hl₁₂')).eq_of_pairwise' h₁ h₂

Depends on / 依赖: antisymm, eq_of_pairwise, subperm_of_subset
-/
theorem Subset.antisymm_of_pairwise [Std.Irrefl r] {l₁ l₂ : List α}
    (h₁ : Pairwise r l₁) (h₂ : Pairwise r l₂) (hl₁₂ : l₁ subseteq l₂) (hl₁₂' : l₂ subseteq l₁) : l₁ = l₂ :=
  ((subperm_of_subset h₁.nodup hl₁₂).antisymm
    (subperm_of_subset h₂.nodup hl₁₂')).eq_of_pairwise' h₁ h₂

/--
theorem `Pairwise.eq_of_mem_iff` / 定理 `Pairwise.eq_of_mem_iff`

English:
theorem Pairwise.eq_of_mem_iff
  statement: [Std.Irrefl r] {l₁ l₂ : List α}
  proof: Subset.antisymm_of_pairwise h₁ h₂ (by grind) (by grind)

中文:
定理 两两.eq_of_mem_iff
  结论: [Std.Irrefl r] {l₁ l₂ : 列表 α}
  证明: Subset.antisymm_of_pairwise h₁ h₂ (by grind) (by grind)

Depends on / 依赖: Subset, Subset.antisymm_of_pairwise, antisymm_of_pairwise
-/
theorem Pairwise.eq_of_mem_iff [Std.Irrefl r] {l₁ l₂ : List α}
    (h₁ : Pairwise r l₁) (h₂ : Pairwise r l₂) (h : forall a : α, a in l₁ ↔ a in l₂) : l₁ = l₂ :=
  Subset.antisymm_of_pairwise h₁ h₂ (by grind) (by grind)

end Antisymm

section TotalAndTransitive

variable {r} [Std.Total r] [IsTrans α r]

/--
theorem `Pairwise.merge` / 定理 `Pairwise.merge`

English:
theorem Pairwise.merge
  given: {l l' : List α} (h : Pairwise r l) (h' : Pairwise r l')
  proof: by
  simpa using pairwise_merge (le := (r · ·))
    (fun a b c h₁ h₂ => by simpa using _root_.trans (by simpa using h₁) (by simpa using h₂))
    (fun a b => by simpa using Std.Total.total a b)
    l l' (by simpa using h) (by simpa using h')

中文:
定理 两两.merge
  条件: {l l' : 列表 α} (h : 两两 r l) (h' : 两两 r l')
  证明: by
  simpa using pairwise_merge (le := (r · ·))
    (fun a b c h₁ h₂ => by simpa using _root_.trans (by simpa using h₁) (by simpa using h₂))
    (fun a b => by simpa using Std.Total.total a b)
    l l' (by simpa using h) (by simpa using h')

Depends on / 依赖: Std.Total.total, _root_, _root_.trans, pairwise_merge
-/
theorem Pairwise.merge {l l' : List α} (h : Pairwise r l) (h' : Pairwise r l') :
    Pairwise r (merge l l' (r · ·)) := by
  simpa using pairwise_merge (le := (r · ·))
    (fun a b c h₁ h₂ => by simpa using _root_.trans (by simpa using h₁) (by simpa using h₂))
    (fun a b => by simpa using Std.Total.total a b)
    l l' (by simpa using h) (by simpa using h')

variable (r)

/--
theorem `pairwise_mergeSort'` / 定理 `pairwise_mergeSort'`

English:
theorem pairwise_mergeSort'
  given: (l : List α)
  statement: Pairwise r (mergeSort l (r · ·))
  proof: by
  simpa using pairwise_mergeSort (le := (r · ·))
    (fun _ _ _ => by simpa using trans_of r)
    (by simpa using total_of r)
    l

中文:
定理 pairwise_mergeSort'
  条件: (l : 列表 α)
  结论: 两两 r (mergeSort l (r · ·))
  证明: by
  simpa using pairwise_mergeSort (le := (r · ·))
    (fun _ _ _ => by simpa using trans_of r)
    (by simpa using total_of r)
    l

Depends on / 依赖: pairwise_mergeSort, total_of, trans_of
-/
theorem pairwise_mergeSort' (l : List α) : Pairwise r (mergeSort l (r · ·)) := by
  simpa using pairwise_mergeSort (le := (r · ·))
    (fun _ _ _ => by simpa using trans_of r)
    (by simpa using total_of r)
    l

variable [Std.Antisymm r]

/--
theorem `mergeSort_eq_self` / 定理 `mergeSort_eq_self`

English:
theorem mergeSort_eq_self
  given: {l : List α}
  statement: Pairwise r l -> mergeSort l (r · ·) = l
  proof: (mergeSort_perm _ _).eq_of_pairwise' (pairwise_mergeSort' _ l)

中文:
定理 mergeSort_eq_self
  条件: {l : 列表 α}
  结论: 两两 r l -> mergeSort l (r · ·) = l
  证明: (mergeSort_perm _ _).eq_of_pairwise' (pairwise_mergeSort' _ l)

Depends on / 依赖: eq_of_pairwise, mergeSort_perm, pairwise_mergeSort
-/
theorem mergeSort_eq_self {l : List α} : Pairwise r l -> mergeSort l (r · ·) = l :=
  (mergeSort_perm _ _).eq_of_pairwise' (pairwise_mergeSort' _ l)

/--
theorem `mergeSort_eq_insertionSort` / 定理 `mergeSort_eq_insertionSort`

English:
theorem mergeSort_eq_insertionSort
  given: (l : List α)
  proof: ((mergeSort_perm l _).trans (perm_insertionSort r l).symm).eq_of_pairwise'
    (pairwise_mergeSort' r l) (pairwise_insertionSort r l)

中文:
定理 mergeSort_eq_insertionSort
  条件: (l : 列表 α)
  证明: ((mergeSort_perm l _).trans (perm_insertionSort r l).symm).eq_of_pairwise'
    (pairwise_mergeSort' r l) (pairwise_insertionSort r l)

Depends on / 依赖: eq_of_pairwise, mergeSort_perm, pairwise_insertionSort, pairwise_mergeSort, perm_insertionSort
-/
theorem mergeSort_eq_insertionSort (l : List α) :
    mergeSort l (r · ·) = insertionSort r l :=
  ((mergeSort_perm l _).trans (perm_insertionSort r l).symm).eq_of_pairwise'
    (pairwise_mergeSort' r l) (pairwise_insertionSort r l)

end TotalAndTransitive

end Correctness

end MergeSort

end sort

section Sorted

variable {α : Type*} {l : List α}

/-!
### The predicates `List.SortedLE`, `List.SortedGE`, `List.SortedLT` and `List.SortedGT`
-/

section Preorder

variable [Preorder α]

/-!
These predicates are equivalent to `Monotone l.get`, but they are also equivalent to
`IsChain (· < ·)` and `Pairwise (· < ·)`. API is provided to move between these forms.

API has deliberately not been provided for decomposed lists to avoid unneeded API replication.
The provided API should be used to move to and from `IsChain`,
`Pairwise` or `Monotone` as needed.
--/

/--
Definition of `SortedLE` / `SortedLE` 的定义

English:
definition SortedLE
  signature: (l : List α)
  body: Monotone l.get

中文:
定义 SortedLE
  签名: (l : 列表 α)
  定义体: Monotone l.get

Depends on / 依赖: Monotone, l.get
-/
def SortedLE (l : List α) := Monotone l.get
/--
Definition of `SortedGE` / `SortedGE` 的定义

English:
definition SortedGE
  signature: (l : List α)
  body: Antitone l.get

中文:
定义 SortedGE
  签名: (l : 列表 α)
  定义体: Antitone l.get
-/
@[to_dual existing SortedLE] def SortedGE (l : List α) := Antitone l.get
/--
Definition of `SortedLT` / `SortedLT` 的定义

English:
definition SortedLT
  signature: (l : List α)
  body: StrictMono l.get

中文:
定义 SortedLT
  签名: (l : 列表 α)
  定义体: StrictMono l.get

Depends on / 依赖: StrictMono, l.get
-/
def SortedLT (l : List α) := StrictMono l.get
/--
Definition of `SortedGT` / `SortedGT` 的定义

English:
definition SortedGT
  signature: (l : List α)
  body: StrictAnti l.get

中文:
定义 SortedGT
  签名: (l : 列表 α)
  定义体: StrictAnti l.get
-/
@[to_dual existing SortedLT] def SortedGT (l : List α) := StrictAnti l.get

section Get

/--
theorem `sortedLE_iff_monotone_get` / 定理 `sortedLE_iff_monotone_get`

English:
theorem sortedLE_iff_monotone_get
  statement: l.SortedLE ↔ Monotone l.get
  proof: .rfl

中文:
定理 sortedLE_iff_monotone_get
  结论: l.SortedLE ↔ 递增 l.get
  证明: .rfl
-/
theorem sortedLE_iff_monotone_get : l.SortedLE ↔ Monotone l.get := .rfl
/--
theorem `sortedGE_iff_antitone_get` / 定理 `sortedGE_iff_antitone_get`

English:
theorem sortedGE_iff_antitone_get
  statement: l.SortedGE ↔ Antitone l.get
  proof: .rfl

中文:
定理 sortedGE_iff_antitone_get
  结论: l.SortedGE ↔ 递减 l.get
  证明: .rfl
-/
theorem sortedGE_iff_antitone_get : l.SortedGE ↔ Antitone l.get := .rfl
/--
theorem `sortedLT_iff_strictMono_get` / 定理 `sortedLT_iff_strictMono_get`

English:
theorem sortedLT_iff_strictMono_get
  statement: l.SortedLT ↔ StrictMono l.get
  proof: .rfl

中文:
定理 sortedLT_iff_strictMono_get
  结论: l.SortedLT ↔ 严格递增 l.get
  证明: .rfl
-/
theorem sortedLT_iff_strictMono_get : l.SortedLT ↔ StrictMono l.get := .rfl
/--
theorem `sortedGT_iff_strictAnti_get` / 定理 `sortedGT_iff_strictAnti_get`

English:
theorem sortedGT_iff_strictAnti_get
  statement: l.SortedGT ↔ StrictAnti l.get
  proof: .rfl

protected alias ⟨SortedLE.monotone_get, _root_.Monotone.sortedLE⟩ := sortedLE_iff_monotone_get
protected alias ⟨SortedGE.antitone_get, _root_.Antitone.sortedGE⟩ := sortedGE_iff_antitone_get
protected alias ⟨SortedLT.strictMono_get, _root_.StrictMono.sortedLT⟩ := sortedLT_iff_strictMono_get
protected alias ⟨SortedGT.strictAnti_get, _root_.StrictAnti.sortedGT⟩ := sortedGT_iff_strictAnti_get

中文:
定理 sortedGT_iff_strictAnti_get
  结论: l.SortedGT ↔ 严格递减 l.get
  证明: .rfl

protected alias ⟨SortedLE.monotone_get, _root_.Monotone.sortedLE⟩ := sortedLE_iff_monotone_get
protected alias ⟨SortedGE.antitone_get, _root_.Antitone.sortedGE⟩ := sortedGE_iff_antitone_get
protected alias ⟨SortedLT.strictMono_get, _root_.StrictMono.sortedLT⟩ := sortedLT_iff_strictMono_get
protected alias ⟨SortedGT.strictAnti_get, _root_.StrictAnti.sortedGT⟩ := sortedGT_iff_strictAnti_get
-/
theorem sortedGT_iff_strictAnti_get : l.SortedGT ↔ StrictAnti l.get := .rfl

protected alias ⟨SortedLE.monotone_get, _root_.Monotone.sortedLE⟩ := sortedLE_iff_monotone_get
protected alias ⟨SortedGE.antitone_get, _root_.Antitone.sortedGE⟩ := sortedGE_iff_antitone_get
protected alias ⟨SortedLT.strictMono_get, _root_.StrictMono.sortedLT⟩ := sortedLT_iff_strictMono_get
protected alias ⟨SortedGT.strictAnti_get, _root_.StrictAnti.sortedGT⟩ := sortedGT_iff_strictAnti_get

end Get

section Pairwise

/--
theorem `sortedLE_iff_pairwise` / 定理 `sortedLE_iff_pairwise`

English:
theorem sortedLE_iff_pairwise
  statement: l.SortedLE ↔ l.Pairwise (· <= ·)
  proof: by
  simp only [sortedLE_iff_monotone_get, monotone_iff_forall_lt, Fin.forall_iff]
  grind [pairwise_iff_getElem]

中文:
定理 sortedLE_iff_pairwise
  结论: l.SortedLE ↔ l.两两 (· <= ·)
  证明: by
  simp only [sortedLE_iff_monotone_get, monotone_iff_forall_lt, Fin.forall_iff]
  grind [pairwise_iff_getElem]
-/
@[grind =] theorem sortedLE_iff_pairwise : l.SortedLE ↔ l.Pairwise (· <= ·) := by
  simp only [sortedLE_iff_monotone_get, monotone_iff_forall_lt, Fin.forall_iff]
  grind [pairwise_iff_getElem]
/--
theorem `sortedGE_iff_pairwise` / 定理 `sortedGE_iff_pairwise`

English:
theorem sortedGE_iff_pairwise
  statement: l.SortedGE ↔ l.Pairwise (· >= ·)
  proof: by
  simp only [sortedGE_iff_antitone_get, antitone_iff_forall_lt, Fin.forall_iff]
  grind [pairwise_iff_getElem]

中文:
定理 sortedGE_iff_pairwise
  结论: l.SortedGE ↔ l.两两 (· >= ·)
  证明: by
  simp only [sortedGE_iff_antitone_get, antitone_iff_forall_lt, Fin.forall_iff]
  grind [pairwise_iff_getElem]
-/
@[grind =] theorem sortedGE_iff_pairwise : l.SortedGE ↔ l.Pairwise (· >= ·) := by
  simp only [sortedGE_iff_antitone_get, antitone_iff_forall_lt, Fin.forall_iff]
  grind [pairwise_iff_getElem]
/--
theorem `sortedLT_iff_pairwise` / 定理 `sortedLT_iff_pairwise`

English:
theorem sortedLT_iff_pairwise
  statement: l.SortedLT ↔ l.Pairwise (· < ·)
  proof: by
  simp only [sortedLT_iff_strictMono_get, StrictMono, Fin.forall_iff]
  grind [pairwise_iff_getElem]

中文:
定理 sortedLT_iff_pairwise
  结论: l.SortedLT ↔ l.两两 (· < ·)
  证明: by
  simp only [sortedLT_iff_strictMono_get, StrictMono, Fin.forall_iff]
  grind [pairwise_iff_getElem]
-/
@[grind =] theorem sortedLT_iff_pairwise : l.SortedLT ↔ l.Pairwise (· < ·) := by
  simp only [sortedLT_iff_strictMono_get, StrictMono, Fin.forall_iff]
  grind [pairwise_iff_getElem]
/--
theorem `sortedGT_iff_pairwise` / 定理 `sortedGT_iff_pairwise`

English:
theorem sortedGT_iff_pairwise
  statement: l.SortedGT ↔ l.Pairwise (· > ·)
  proof: by
  simp only [sortedGT_iff_strictAnti_get, StrictAnti, Fin.forall_iff]
  grind [pairwise_iff_getElem]

protected alias ⟨SortedLE.pairwise, Pairwise.sortedLE⟩ := sortedLE_iff_pairwise
protected alias ⟨SortedGE.pairwise, Pairwise.sortedGE⟩ := sortedGE_iff_pairwise
protected alias ⟨SortedLT.pairwise, Pairwise.sortedLT⟩ := sortedLT_iff_pairwise
protected alias ⟨SortedGT.pairwise, Pairwise.sortedGT⟩ := sortedGT_iff_pairwise

中文:
定理 sortedGT_iff_pairwise
  结论: l.SortedGT ↔ l.两两 (· > ·)
  证明: by
  simp only [sortedGT_iff_strictAnti_get, StrictAnti, Fin.forall_iff]
  grind [pairwise_iff_getElem]

protected alias ⟨SortedLE.pairwise, Pairwise.sortedLE⟩ := sortedLE_iff_pairwise
protected alias ⟨SortedGE.pairwise, Pairwise.sortedGE⟩ := sortedGE_iff_pairwise
protected alias ⟨SortedLT.pairwise, Pairwise.sortedLT⟩ := sortedLT_iff_pairwise
protected alias ⟨SortedGT.pairwise, Pairwise.sortedGT⟩ := sortedGT_iff_pairwise
-/
@[grind =] theorem sortedGT_iff_pairwise : l.SortedGT ↔ l.Pairwise (· > ·) := by
  simp only [sortedGT_iff_strictAnti_get, StrictAnti, Fin.forall_iff]
  grind [pairwise_iff_getElem]

protected alias ⟨SortedLE.pairwise, Pairwise.sortedLE⟩ := sortedLE_iff_pairwise
protected alias ⟨SortedGE.pairwise, Pairwise.sortedGE⟩ := sortedGE_iff_pairwise
protected alias ⟨SortedLT.pairwise, Pairwise.sortedLT⟩ := sortedLT_iff_pairwise
protected alias ⟨SortedGT.pairwise, Pairwise.sortedGT⟩ := sortedGT_iff_pairwise

end Pairwise

section IsChain

/--
theorem `sortedLE_iff_isChain` / 定理 `sortedLE_iff_isChain`

English:
theorem sortedLE_iff_isChain
  statement: l.SortedLE ↔ IsChain (· <= ·) l
  proof: sortedLE_iff_pairwise.trans isChain_iff_pairwise.symm

中文:
定理 sortedLE_iff_isChain
  结论: l.SortedLE ↔ IsChain (· <= ·) l
  证明: sortedLE_iff_pairwise.trans isChain_iff_pairwise.symm

Depends on / 依赖: isChain_iff_pairwise, isChain_iff_pairwise.symm, sortedLE_iff_pairwise, sortedLE_iff_pairwise.trans
-/
theorem sortedLE_iff_isChain : l.SortedLE ↔ IsChain (· <= ·) l :=
  sortedLE_iff_pairwise.trans isChain_iff_pairwise.symm
/--
theorem `sortedGE_iff_isChain` / 定理 `sortedGE_iff_isChain`

English:
theorem sortedGE_iff_isChain
  statement: l.SortedGE ↔ IsChain (· >= ·) l
  proof: sortedGE_iff_pairwise.trans isChain_iff_pairwise.symm

中文:
定理 sortedGE_iff_isChain
  结论: l.SortedGE ↔ IsChain (· >= ·) l
  证明: sortedGE_iff_pairwise.trans isChain_iff_pairwise.symm

Depends on / 依赖: isChain_iff_pairwise, isChain_iff_pairwise.symm, sortedGE_iff_pairwise, sortedGE_iff_pairwise.trans
-/
theorem sortedGE_iff_isChain : l.SortedGE ↔ IsChain (· >= ·) l :=
  sortedGE_iff_pairwise.trans isChain_iff_pairwise.symm
/--
theorem `sortedLT_iff_isChain` / 定理 `sortedLT_iff_isChain`

English:
theorem sortedLT_iff_isChain
  statement: l.SortedLT ↔ IsChain (· < ·) l
  proof: sortedLT_iff_pairwise.trans isChain_iff_pairwise.symm

中文:
定理 sortedLT_iff_isChain
  结论: l.SortedLT ↔ IsChain (· < ·) l
  证明: sortedLT_iff_pairwise.trans isChain_iff_pairwise.symm

Depends on / 依赖: isChain_iff_pairwise, isChain_iff_pairwise.symm, sortedLT_iff_pairwise, sortedLT_iff_pairwise.trans
-/
theorem sortedLT_iff_isChain : l.SortedLT ↔ IsChain (· < ·) l :=
  sortedLT_iff_pairwise.trans isChain_iff_pairwise.symm
/--
theorem `sortedGT_iff_isChain` / 定理 `sortedGT_iff_isChain`

English:
theorem sortedGT_iff_isChain
  statement: l.SortedGT ↔ IsChain (· > ·) l
  proof: sortedGT_iff_pairwise.trans isChain_iff_pairwise.symm

protected alias ⟨SortedLE.isChain, IsChain.sortedLE⟩ := sortedLE_iff_isChain
protected alias ⟨SortedGE.isChain, IsChain.sortedGE⟩ := sortedGE_iff_isChain
protected alias ⟨SortedLT.isChain, IsChain.sortedLT⟩ := sortedLT_iff_isChain
protected alias ⟨SortedGT.isChain, IsChain.sortedGT⟩ := sortedGT_iff_isChain

中文:
定理 sortedGT_iff_isChain
  结论: l.SortedGT ↔ IsChain (· > ·) l
  证明: sortedGT_iff_pairwise.trans isChain_iff_pairwise.symm

protected alias ⟨SortedLE.isChain, IsChain.sortedLE⟩ := sortedLE_iff_isChain
protected alias ⟨SortedGE.isChain, IsChain.sortedGE⟩ := sortedGE_iff_isChain
protected alias ⟨SortedLT.isChain, IsChain.sortedLT⟩ := sortedLT_iff_isChain
protected alias ⟨SortedGT.isChain, IsChain.sortedGT⟩ := sortedGT_iff_isChain

Depends on / 依赖: isChain_iff_pairwise, isChain_iff_pairwise.symm, sortedGT_iff_pairwise, sortedGT_iff_pairwise.trans
-/
theorem sortedGT_iff_isChain : l.SortedGT ↔ IsChain (· > ·) l :=
  sortedGT_iff_pairwise.trans isChain_iff_pairwise.symm

protected alias ⟨SortedLE.isChain, IsChain.sortedLE⟩ := sortedLE_iff_isChain
protected alias ⟨SortedGE.isChain, IsChain.sortedGE⟩ := sortedGE_iff_isChain
protected alias ⟨SortedLT.isChain, IsChain.sortedLT⟩ := sortedLT_iff_isChain
protected alias ⟨SortedGT.isChain, IsChain.sortedGT⟩ := sortedGT_iff_isChain

section Decidable

/--
Instance `decidableSortedLE` / 实例 `decidableSortedLE`

English:
instance decidableSortedLE
  signature: [DecidableLE α]
  body: fun _ => decidable_of_iff' _ sortedLE_iff_isChain

中文:
实例 decidableSortedLE
  签名: [DecidableLE α]
  定义体: fun _ => decidable_of_iff' _ sortedLE_iff_isChain
-/
instance decidableSortedLE [DecidableLE α] : DecidablePred (SortedLE (α := α)) :=
  fun _ => decidable_of_iff' _ sortedLE_iff_isChain
/--
Instance `decidableSortedGE` / 实例 `decidableSortedGE`

English:
instance decidableSortedGE
  signature: [DecidableLE α]
  body: fun _ => decidable_of_iff' _ sortedGE_iff_isChain

中文:
实例 decidableSortedGE
  签名: [DecidableLE α]
  定义体: fun _ => decidable_of_iff' _ sortedGE_iff_isChain
-/
instance decidableSortedGE [DecidableLE α] : DecidablePred (SortedGE (α := α)) :=
  fun _ => decidable_of_iff' _ sortedGE_iff_isChain
/--
Instance `decidableSortedLT` / 实例 `decidableSortedLT`

English:
instance decidableSortedLT
  signature: [DecidableLT α]
  body: fun _ => decidable_of_iff' _ sortedLT_iff_isChain

中文:
实例 decidableSortedLT
  签名: [DecidableLT α]
  定义体: fun _ => decidable_of_iff' _ sortedLT_iff_isChain
-/
instance decidableSortedLT [DecidableLT α] : DecidablePred (SortedLT (α := α)) :=
  fun _ => decidable_of_iff' _ sortedLT_iff_isChain
/--
Instance `decidableSortedGT` / 实例 `decidableSortedGT`

English:
instance decidableSortedGT
  signature: [DecidableLT α]
  body: fun _ => decidable_of_iff' _ sortedGT_iff_isChain

中文:
实例 decidableSortedGT
  签名: [DecidableLT α]
  定义体: fun _ => decidable_of_iff' _ sortedGT_iff_isChain
-/
instance decidableSortedGT [DecidableLT α] : DecidablePred (SortedGT (α := α)) :=
  fun _ => decidable_of_iff' _ sortedGT_iff_isChain

end Decidable

end IsChain

section GetElem

/--
theorem `sortedLE_iff_getElem_le_getElem_of_le` / 定理 `sortedLE_iff_getElem_le_getElem_of_le`

English:
theorem sortedLE_iff_getElem_le_getElem_of_le
  proof: ⟨fun h _ _ _ _ hij => h.monotone_get hij, fun h => Monotone.sortedLE fun _ _ => (h ·)⟩

中文:
定理 sortedLE_iff_getElem_le_getElem_of_le
  证明: ⟨fun h _ _ _ _ hij => h.monotone_get hij, fun h => Monotone.sortedLE fun _ _ => (h ·)⟩

Depends on / 依赖: Monotone, Monotone.sortedLE, h.monotone_get, monotone_get, sortedLE
-/
theorem sortedLE_iff_getElem_le_getElem_of_le :
    l.SortedLE ↔ forall ⦃i j : Nat⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, i <= j -> l[i] <= l[j] :=
⟨fun h _ _ _ _ hij => h.monotone_get hij, fun h => Monotone.sortedLE fun _ _ => (h ·)⟩
/--
theorem `sortedGE_iff_getElem_ge_getElem_of_le` / 定理 `sortedGE_iff_getElem_ge_getElem_of_le`

English:
theorem sortedGE_iff_getElem_ge_getElem_of_le
  proof: ⟨fun h _ _ _ _ hij => h.antitone_get hij, fun h => Antitone.sortedGE fun _ _ => (h ·)⟩

中文:
定理 sortedGE_iff_getElem_ge_getElem_of_le
  证明: ⟨fun h _ _ _ _ hij => h.antitone_get hij, fun h => Antitone.sortedGE fun _ _ => (h ·)⟩

Depends on / 依赖: Antitone, Antitone.sortedGE, antitone_get, h.antitone_get, sortedGE
-/
theorem sortedGE_iff_getElem_ge_getElem_of_le :
    l.SortedGE ↔ forall ⦃i j : Nat⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, j <= i -> l[i] <= l[j] :=
⟨fun h _ _ _ _ hij => h.antitone_get hij, fun h => Antitone.sortedGE fun _ _ => (h ·)⟩
/--
theorem `sortedLT_iff_getElem_lt_getElem_of_lt` / 定理 `sortedLT_iff_getElem_lt_getElem_of_lt`

English:
theorem sortedLT_iff_getElem_lt_getElem_of_lt
  proof: ⟨fun h _ _ _ _ hij => h.strictMono_get hij, fun h => StrictMono.sortedLT fun _ _ => (h ·)⟩

中文:
定理 sortedLT_iff_getElem_lt_getElem_of_lt
  证明: ⟨fun h _ _ _ _ hij => h.strictMono_get hij, fun h => StrictMono.sortedLT fun _ _ => (h ·)⟩

Depends on / 依赖: StrictMono, StrictMono.sortedLT, h.strictMono_get, sortedLT, strictMono_get
-/
theorem sortedLT_iff_getElem_lt_getElem_of_lt :
    l.SortedLT ↔ forall ⦃i j : Nat⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, i < j -> l[i] < l[j] :=
⟨fun h _ _ _ _ hij => h.strictMono_get hij, fun h => StrictMono.sortedLT fun _ _ => (h ·)⟩
/--
theorem `sortedGT_iff_getElem_gt_getElem_of_lt` / 定理 `sortedGT_iff_getElem_gt_getElem_of_lt`

English:
theorem sortedGT_iff_getElem_gt_getElem_of_lt
  proof: ⟨fun h _ _ _ _ hij => h.strictAnti_get hij, fun h => StrictAnti.sortedGT fun _ _ => (h ·)⟩

alias ⟨SortedLE.getElem_le_getElem_of_le, sortedLE_of_getElem_le_getElem_of_le⟩ :=
  sortedLE_iff_getElem_le_getElem_of_le
alias ⟨SortedGE.getElem_ge_getElem_of_le, sortedGE_of_getElem_ge_getElem_of_le⟩ :=
  sortedGE_iff_getElem_ge_getElem_of_le
alias ⟨SortedLT.getElem_lt_getElem_of_lt, sortedLT_of_getElem_lt_getElem_of_lt⟩ :=
  sortedLT_iff_getElem_lt_getElem_of_lt
alias ⟨SortedGT.getElem_gt_getElem_of_lt, sortedGT_of_getElem_gt_getElem_of_lt⟩ :=
  sortedGT_iff_getElem_gt_getElem_of_lt

中文:
定理 sortedGT_iff_getElem_gt_getElem_of_lt
  证明: ⟨fun h _ _ _ _ hij => h.strictAnti_get hij, fun h => StrictAnti.sortedGT fun _ _ => (h ·)⟩

alias ⟨SortedLE.getElem_le_getElem_of_le, sortedLE_of_getElem_le_getElem_of_le⟩ :=
  sortedLE_iff_getElem_le_getElem_of_le
alias ⟨SortedGE.getElem_ge_getElem_of_le, sortedGE_of_getElem_ge_getElem_of_le⟩ :=
  sortedGE_iff_getElem_ge_getElem_of_le
alias ⟨SortedLT.getElem_lt_getElem_of_lt, sortedLT_of_getElem_lt_getElem_of_lt⟩ :=
  sortedLT_iff_getElem_lt_getElem_of_lt
alias ⟨SortedGT.getElem_gt_getElem_of_lt, sortedGT_of_getElem_gt_getElem_of_lt⟩ :=
  sortedGT_iff_getElem_gt_getElem_of_lt

Depends on / 依赖: StrictAnti, StrictAnti.sortedGT, h.strictAnti_get, sortedGT, strictAnti_get
-/
theorem sortedGT_iff_getElem_gt_getElem_of_lt :
    l.SortedGT ↔ forall ⦃i j : Nat⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, j < i -> l[i] < l[j] :=
⟨fun h _ _ _ _ hij => h.strictAnti_get hij, fun h => StrictAnti.sortedGT fun _ _ => (h ·)⟩

alias ⟨SortedLE.getElem_le_getElem_of_le, sortedLE_of_getElem_le_getElem_of_le⟩ :=
  sortedLE_iff_getElem_le_getElem_of_le
alias ⟨SortedGE.getElem_ge_getElem_of_le, sortedGE_of_getElem_ge_getElem_of_le⟩ :=
  sortedGE_iff_getElem_ge_getElem_of_le
alias ⟨SortedLT.getElem_lt_getElem_of_lt, sortedLT_of_getElem_lt_getElem_of_lt⟩ :=
  sortedLT_iff_getElem_lt_getElem_of_lt
alias ⟨SortedGT.getElem_gt_getElem_of_lt, sortedGT_of_getElem_gt_getElem_of_lt⟩ :=
  sortedGT_iff_getElem_gt_getElem_of_lt

end GetElem

section

/--
theorem `SortedLT.sortedLE` / 定理 `SortedLT.sortedLE`

English:
theorem SortedLT.sortedLE
  given: {l : List α} (h : l.SortedLT)
  statement: l.SortedLE
  proof: h.strictMono_get.monotone.sortedLE

中文:
定理 SortedLT.sortedLE
  条件: {l : 列表 α} (h : l.SortedLT)
  结论: l.SortedLE
  证明: h.strictMono_get.monotone.sortedLE
-/
protected theorem SortedLT.sortedLE {l : List α} (h : l.SortedLT) : l.SortedLE :=
  h.strictMono_get.monotone.sortedLE
/--
theorem `SortedGT.sortedGE` / 定理 `SortedGT.sortedGE`

English:
theorem SortedGT.sortedGE
  given: {l : List α} (h : l.SortedGT)
  statement: l.SortedGE
  proof: h.strictAnti_get.antitone.sortedGE

中文:
定理 SortedGT.sortedGE
  条件: {l : 列表 α} (h : l.SortedGT)
  结论: l.SortedGE
  证明: h.strictAnti_get.antitone.sortedGE
-/
protected theorem SortedGT.sortedGE {l : List α} (h : l.SortedGT) : l.SortedGE :=
  h.strictAnti_get.antitone.sortedGE

/--
theorem `SortedLT.nodup` / 定理 `SortedLT.nodup`

English:
theorem SortedLT.nodup
  given: (h : l.SortedLT)
  statement: l.Nodup
  proof: h.strictMono_get.injective.nodup

中文:
定理 SortedLT.nodup
  条件: (h : l.SortedLT)
  结论: l.Nodup
  证明: h.strictMono_get.injective.nodup
-/
protected theorem SortedLT.nodup (h : l.SortedLT) : l.Nodup := h.strictMono_get.injective.nodup
/--
theorem `SortedGT.nodup` / 定理 `SortedGT.nodup`

English:
theorem SortedGT.nodup
  given: (h : l.SortedGT)
  statement: l.Nodup
  proof: h.strictAnti_get.injective.nodup

中文:
定理 SortedGT.nodup
  条件: (h : l.SortedGT)
  结论: l.Nodup
  证明: h.strictAnti_get.injective.nodup
-/
protected theorem SortedGT.nodup (h : l.SortedGT) : l.Nodup := h.strictAnti_get.injective.nodup

/--
theorem `sortedLE_replicate` / 定理 `sortedLE_replicate`

English:
theorem sortedLE_replicate
  given: {a : α} (n : Nat)
  statement: (replicate n a).SortedLE
  proof: (pairwise_replicate.mpr (Or.inr le_rfl)).sortedLE

中文:
定理 sortedLE_replicate
  条件: {a : α} (n : 自然数)
  结论: (replicate n a).SortedLE
  证明: (pairwise_replicate.mpr (Or.inr le_rfl)).sortedLE

Depends on / 依赖: Or.inr, le_rfl, pairwise_replicate, pairwise_replicate.mpr, sortedLE
-/
theorem sortedLE_replicate {a : α} (n : Nat) : (replicate n a).SortedLE :=
  (pairwise_replicate.mpr (Or.inr le_rfl)).sortedLE

/--
theorem `sortedLT_finRange` / 定理 `sortedLT_finRange`

English:
theorem sortedLT_finRange
  given: (n : Nat)
  statement: (finRange n).SortedLT
  proof: sortedLT_of_getElem_lt_getElem_of_lt by simp

中文:
定理 sortedLT_finRange
  条件: (n : 自然数)
  结论: (finRange n).SortedLT
  证明: sortedLT_of_getElem_lt_getElem_of_lt by simp

Depends on / 依赖: sortedLT_of_getElem_lt_getElem_of_lt
-/
theorem sortedLT_finRange (n : Nat) : (finRange n).SortedLT :=
sortedLT_of_getElem_lt_getElem_of_lt by simp

/--
theorem `sortedLT_range` / 定理 `sortedLT_range`

English:
theorem sortedLT_range
  given: (n : Nat)
  statement: (range n).SortedLT
  proof: pairwise_lt_range.sortedLT

中文:
定理 sortedLT_range
  条件: (n : 自然数)
  结论: (range n).SortedLT
  证明: pairwise_lt_range.sortedLT

Depends on / 依赖: pairwise_lt_range, pairwise_lt_range.sortedLT, sortedLT
-/
theorem sortedLT_range (n : Nat) : (range n).SortedLT := pairwise_lt_range.sortedLT

/--
theorem `sortedLT_range'` / 定理 `sortedLT_range'`

English:
theorem sortedLT_range'
  given: (a b) {s} (hs : s != 0)
  proof: (pairwise_lt_range' _ (Nat.pos_of_ne_zero hs)).sortedLT

中文:
定理 sortedLT_range'
  条件: (a b) {s} (hs : s != 0)
  证明: (pairwise_lt_range' _ (Nat.pos_of_ne_zero hs)).sortedLT

Depends on / 依赖: Nat.pos_of_ne_zero, pairwise_lt_range, pos_of_ne_zero, sortedLT
-/
theorem sortedLT_range' (a b) {s} (hs : s != 0) :
    (range' a b s).SortedLT := (pairwise_lt_range' _ (Nat.pos_of_ne_zero hs)).sortedLT

/--
theorem `sortedLE_range'` / 定理 `sortedLE_range'`

English:
theorem sortedLE_range'
  given: (a b s)
  proof: (pairwise_le_range' _).sortedLE

中文:
定理 sortedLE_range'
  条件: (a b s)
  证明: (pairwise_le_range' _).sortedLE

Depends on / 依赖: pairwise_le_range, sortedLE
-/
theorem sortedLE_range' (a b s) :
    (range' a b s).SortedLE := (pairwise_le_range' _).sortedLE

end

section OfFn

variable {n : Nat} {f : Fin n -> α}

/--
theorem `sortedLE_ofFn_iff` / 定理 `sortedLE_ofFn_iff`

English:
theorem sortedLE_ofFn_iff
  statement: (ofFn f).SortedLE ↔ Monotone f
  proof: by
  simp only [sortedLE_iff_monotone_get, Monotone, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_le_mk]

中文:
定理 sortedLE_ofFn_iff
  结论: (ofFn f).SortedLE ↔ 递增 f
  证明: by
  simp only [sortedLE_iff_monotone_get, Monotone, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_le_mk]
-/
@[simp] theorem sortedLE_ofFn_iff : (ofFn f).SortedLE ↔ Monotone f := by
  simp only [sortedLE_iff_monotone_get, Monotone, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_le_mk]

/--
theorem `sortedGE_ofFn_iff` / 定理 `sortedGE_ofFn_iff`

English:
theorem sortedGE_ofFn_iff
  statement: (ofFn f).SortedGE ↔ Antitone f
  proof: by
  simp only [sortedGE_iff_antitone_get, Antitone, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_le_mk]

中文:
定理 sortedGE_ofFn_iff
  结论: (ofFn f).SortedGE ↔ 递减 f
  证明: by
  simp only [sortedGE_iff_antitone_get, Antitone, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_le_mk]
-/
@[simp] theorem sortedGE_ofFn_iff : (ofFn f).SortedGE ↔ Antitone f := by
  simp only [sortedGE_iff_antitone_get, Antitone, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_le_mk]

/--
theorem `sortedLT_ofFn_iff` / 定理 `sortedLT_ofFn_iff`

English:
theorem sortedLT_ofFn_iff
  statement: (ofFn f).SortedLT ↔ StrictMono f
  proof: by
  simp only [sortedLT_iff_strictMono_get, StrictMono, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_lt_mk]

中文:
定理 sortedLT_ofFn_iff
  结论: (ofFn f).SortedLT ↔ 严格递增 f
  证明: by
  simp only [sortedLT_iff_strictMono_get, StrictMono, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_lt_mk]
-/
@[simp] theorem sortedLT_ofFn_iff : (ofFn f).SortedLT ↔ StrictMono f := by
  simp only [sortedLT_iff_strictMono_get, StrictMono, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_lt_mk]

/--
theorem `sortedGT_ofFn_iff` / 定理 `sortedGT_ofFn_iff`

English:
theorem sortedGT_ofFn_iff
  statement: (ofFn f).SortedGT ↔ StrictAnti f
  proof: by
  simp only [sortedGT_iff_strictAnti_get, StrictAnti, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_lt_mk]

中文:
定理 sortedGT_ofFn_iff
  结论: (ofFn f).SortedGT ↔ 严格递减 f
  证明: by
  simp only [sortedGT_iff_strictAnti_get, StrictAnti, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_lt_mk]
-/
@[simp] theorem sortedGT_ofFn_iff : (ofFn f).SortedGT ↔ StrictAnti f := by
  simp only [sortedGT_iff_strictAnti_get, StrictAnti, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_lt_mk]

/-- The list obtained from a monotone tuple is sorted. -/
protected alias ⟨SortedLE.monotone, _root_.Monotone.sortedLE_ofFn⟩ := sortedLE_ofFn_iff
/-- The list obtained from an antitone tuple is sorted. -/
protected alias ⟨SortedGE.antitone, _root_.Antitone.sortedGE_ofFn⟩ := sortedGE_ofFn_iff
/-- The list obtained from a strictly monotone tuple is sorted. -/
protected alias ⟨SortedLT.strictMono, _root_.StrictMono.sortedLT_ofFn⟩ := sortedLT_ofFn_iff
/-- The list obtained from a strictly antitone tuple is sorted. -/
protected alias ⟨SortedGT.strictAnti, _root_.StrictAnti.sortedGT_ofFn⟩ := sortedGT_ofFn_iff

end OfFn

section Reverse

/--
theorem `sortedLE_reverse` / 定理 `sortedLE_reverse`

English:
theorem sortedLE_reverse
  statement: l.reverse.SortedLE ↔ l.SortedGE
  proof: by grind

中文:
定理 sortedLE_reverse
  结论: l.reverse.SortedLE ↔ l.SortedGE
  证明: by grind
-/
@[simp] theorem sortedLE_reverse : l.reverse.SortedLE ↔ l.SortedGE := by grind
/--
theorem `sortedGE_reverse` / 定理 `sortedGE_reverse`

English:
theorem sortedGE_reverse
  statement: l.reverse.SortedGE ↔ l.SortedLE
  proof: by grind

中文:
定理 sortedGE_reverse
  结论: l.reverse.SortedGE ↔ l.SortedLE
  证明: by grind
-/
@[simp] theorem sortedGE_reverse : l.reverse.SortedGE ↔ l.SortedLE := by grind
/--
theorem `sortedLT_reverse` / 定理 `sortedLT_reverse`

English:
theorem sortedLT_reverse
  statement: l.reverse.SortedLT ↔ l.SortedGT
  proof: by grind

中文:
定理 sortedLT_reverse
  结论: l.reverse.SortedLT ↔ l.SortedGT
  证明: by grind
-/
@[simp] theorem sortedLT_reverse : l.reverse.SortedLT ↔ l.SortedGT := by grind
/--
theorem `sortedGT_reverse` / 定理 `sortedGT_reverse`

English:
theorem sortedGT_reverse
  statement: l.reverse.SortedGT ↔ l.SortedLT
  proof: by grind

protected alias ⟨SortedLE.of_reverse, SortedGE.reverse⟩ := sortedLE_reverse
protected alias ⟨SortedGE.of_reverse, SortedLE.reverse⟩ := sortedGE_reverse
protected alias ⟨SortedLT.of_reverse, SortedGT.reverse⟩ := sortedLT_reverse
protected alias ⟨SortedGT.of_reverse, SortedLT.reverse⟩ := sortedGT_reverse

中文:
定理 sortedGT_reverse
  结论: l.reverse.SortedGT ↔ l.SortedLT
  证明: by grind

protected alias ⟨SortedLE.of_reverse, SortedGE.reverse⟩ := sortedLE_reverse
protected alias ⟨SortedGE.of_reverse, SortedLE.reverse⟩ := sortedGE_reverse
protected alias ⟨SortedLT.of_reverse, SortedGT.reverse⟩ := sortedLT_reverse
protected alias ⟨SortedGT.of_reverse, SortedLT.reverse⟩ := sortedGT_reverse
-/
@[simp] theorem sortedGT_reverse : l.reverse.SortedGT ↔ l.SortedLT := by grind

protected alias ⟨SortedLE.of_reverse, SortedGE.reverse⟩ := sortedLE_reverse
protected alias ⟨SortedGE.of_reverse, SortedLE.reverse⟩ := sortedGE_reverse
protected alias ⟨SortedLT.of_reverse, SortedGT.reverse⟩ := sortedLT_reverse
protected alias ⟨SortedGT.of_reverse, SortedLT.reverse⟩ := sortedGT_reverse

end Reverse

section Dual

section OfDual

variable {l : List αᵒᵈ}

/--
theorem `sortedLE_map_ofDual` / 定理 `sortedLE_map_ofDual`

English:
theorem sortedLE_map_ofDual
  given: {l : List αᵒᵈ}
  proof: by
  grind [OrderDual.ofDual_le_ofDual]

中文:
定理 sortedLE_map_ofDual
  条件: {l : 列表 αᵒᵈ}
  证明: by
  grind [OrderDual.ofDual_le_ofDual]
-/
@[simp] theorem sortedLE_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedLE ↔ l.SortedGE := by
  grind [OrderDual.ofDual_le_ofDual]
/--
theorem `sortedGE_map_ofDual` / 定理 `sortedGE_map_ofDual`

English:
theorem sortedGE_map_ofDual
  proof: by
  grind [OrderDual.ofDual_le_ofDual]

中文:
定理 sortedGE_map_ofDual
  证明: by
  grind [OrderDual.ofDual_le_ofDual]
-/
@[simp] theorem sortedGE_map_ofDual :
    (l.map OrderDual.ofDual).SortedGE ↔ l.SortedLE := by
  grind [OrderDual.ofDual_le_ofDual]
/--
theorem `sortedLT_map_ofDual` / 定理 `sortedLT_map_ofDual`

English:
theorem sortedLT_map_ofDual
  given: {l : List αᵒᵈ}
  proof: by
  grind [OrderDual.ofDual_lt_ofDual]

中文:
定理 sortedLT_map_ofDual
  条件: {l : 列表 αᵒᵈ}
  证明: by
  grind [OrderDual.ofDual_lt_ofDual]
-/
@[simp] theorem sortedLT_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedLT ↔ l.SortedGT := by
  grind [OrderDual.ofDual_lt_ofDual]
/--
theorem `sortedGT_map_ofDual` / 定理 `sortedGT_map_ofDual`

English:
theorem sortedGT_map_ofDual
  given: {l : List αᵒᵈ}
  proof: by
  grind [OrderDual.ofDual_lt_ofDual]

protected alias ⟨SortedLE.map_ofDual, SortedGE.of_map_ofDual⟩ := sortedLE_map_ofDual
protected alias ⟨SortedGE.map_ofDual, SortedLE.of_map_ofDual⟩ := sortedGE_map_ofDual
protected alias ⟨SortedLT.map_ofDual, SortedGT.of_map_ofDual⟩ := sortedLT_map_ofDual
protected alias ⟨SortedGT.map_ofDual, SortedLT.of_map_ofDual⟩ := sortedGT_map_ofDual

中文:
定理 sortedGT_map_ofDual
  条件: {l : 列表 αᵒᵈ}
  证明: by
  grind [OrderDual.ofDual_lt_ofDual]

protected alias ⟨SortedLE.map_ofDual, SortedGE.of_map_ofDual⟩ := sortedLE_map_ofDual
protected alias ⟨SortedGE.map_ofDual, SortedLE.of_map_ofDual⟩ := sortedGE_map_ofDual
protected alias ⟨SortedLT.map_ofDual, SortedGT.of_map_ofDual⟩ := sortedLT_map_ofDual
protected alias ⟨SortedGT.map_ofDual, SortedLT.of_map_ofDual⟩ := sortedGT_map_ofDual
-/
@[simp] theorem sortedGT_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedGT ↔ l.SortedLT := by
  grind [OrderDual.ofDual_lt_ofDual]

protected alias ⟨SortedLE.map_ofDual, SortedGE.of_map_ofDual⟩ := sortedLE_map_ofDual
protected alias ⟨SortedGE.map_ofDual, SortedLE.of_map_ofDual⟩ := sortedGE_map_ofDual
protected alias ⟨SortedLT.map_ofDual, SortedGT.of_map_ofDual⟩ := sortedLT_map_ofDual
protected alias ⟨SortedGT.map_ofDual, SortedLT.of_map_ofDual⟩ := sortedGT_map_ofDual

end OfDual

section ToDual

variable {l : List α}

/--
theorem `sortedLE_map_toDual` / 定理 `sortedLE_map_toDual`

English:
theorem sortedLE_map_toDual
  given: {l : List α}
  proof: by
  grind [OrderDual.toDual_le_toDual]

中文:
定理 sortedLE_map_toDual
  条件: {l : 列表 α}
  证明: by
  grind [OrderDual.toDual_le_toDual]

Depends on / 依赖: OrderDual, OrderDual.toDual_le_toDual, toDual_le_toDual
-/
theorem sortedLE_map_toDual {l : List α} :
    (l.map OrderDual.toDual).SortedLE ↔ l.SortedGE := by
  grind [OrderDual.toDual_le_toDual]
/--
theorem `sortedGE_map_toDual` / 定理 `sortedGE_map_toDual`

English:
theorem sortedGE_map_toDual
  given: {l : List α}
  proof: by
  grind [OrderDual.toDual_le_toDual]

中文:
定理 sortedGE_map_toDual
  条件: {l : 列表 α}
  证明: by
  grind [OrderDual.toDual_le_toDual]

Depends on / 依赖: OrderDual, OrderDual.toDual_le_toDual, toDual_le_toDual
-/
theorem sortedGE_map_toDual {l : List α} :
    (l.map OrderDual.toDual).SortedGE ↔ l.SortedLE := by
  grind [OrderDual.toDual_le_toDual]
/--
theorem `sortedLT_map_toDual` / 定理 `sortedLT_map_toDual`

English:
theorem sortedLT_map_toDual
  given: {l : List α}
  proof: by
  grind [OrderDual.toDual_lt_toDual]

中文:
定理 sortedLT_map_toDual
  条件: {l : 列表 α}
  证明: by
  grind [OrderDual.toDual_lt_toDual]

Depends on / 依赖: OrderDual, OrderDual.toDual_lt_toDual, toDual_lt_toDual
-/
theorem sortedLT_map_toDual {l : List α} :
    (l.map OrderDual.toDual).SortedLT ↔ l.SortedGT := by
  grind [OrderDual.toDual_lt_toDual]
/--
theorem `sortedGT_map_toDual` / 定理 `sortedGT_map_toDual`

English:
theorem sortedGT_map_toDual
  given: {l : List αᵒᵈ}
  proof: by
  grind [OrderDual.toDual_lt_toDual]

protected alias ⟨SortedLE.map_toDual, SortedGE.of_map_toDual⟩ := sortedLE_map_toDual
protected alias ⟨SortedGE.map_toDual, SortedLE.of_map_toDual⟩ := sortedGE_map_toDual
protected alias ⟨SortedLT.map_toDual, SortedGT.of_map_toDual⟩ := sortedLT_map_toDual
protected alias ⟨SortedGT.map_toDual, SortedLT.of_map_toDual⟩ := sortedGT_map_toDual

中文:
定理 sortedGT_map_toDual
  条件: {l : 列表 αᵒᵈ}
  证明: by
  grind [OrderDual.toDual_lt_toDual]

protected alias ⟨SortedLE.map_toDual, SortedGE.of_map_toDual⟩ := sortedLE_map_toDual
protected alias ⟨SortedGE.map_toDual, SortedLE.of_map_toDual⟩ := sortedGE_map_toDual
protected alias ⟨SortedLT.map_toDual, SortedGT.of_map_toDual⟩ := sortedLT_map_toDual
protected alias ⟨SortedGT.map_toDual, SortedLT.of_map_toDual⟩ := sortedGT_map_toDual

Depends on / 依赖: OrderDual, OrderDual.toDual_lt_toDual, toDual_lt_toDual
-/
theorem sortedGT_map_toDual {l : List αᵒᵈ} :
    (l.map OrderDual.toDual).SortedGT ↔ l.SortedLT := by
  grind [OrderDual.toDual_lt_toDual]

protected alias ⟨SortedLE.map_toDual, SortedGE.of_map_toDual⟩ := sortedLE_map_toDual
protected alias ⟨SortedGE.map_toDual, SortedLE.of_map_toDual⟩ := sortedGE_map_toDual
protected alias ⟨SortedLT.map_toDual, SortedGT.of_map_toDual⟩ := sortedLT_map_toDual
protected alias ⟨SortedGT.map_toDual, SortedLT.of_map_toDual⟩ := sortedGT_map_toDual

end ToDual

end Dual

end Preorder

section PartialOrder

variable [PartialOrder α]

/--
theorem `SortedLE.sortedLT_of_nodup` / 定理 `SortedLE.sortedLT_of_nodup`

English:
theorem SortedLE.sortedLT_of_nodup
  given: {l : List α} (h₁ : l.SortedLE) (h₂ : l.Nodup)
  proof: (h₁.monotone_get.strictMono_of_injective h₂.injective_get).sortedLT

中文:
定理 SortedLE.sortedLT_of_nodup
  条件: {l : 列表 α} (h₁ : l.SortedLE) (h₂ : l.Nodup)
  证明: (h₁.monotone_get.strictMono_of_injective h₂.injective_get).sortedLT
-/
protected theorem SortedLE.sortedLT_of_nodup {l : List α} (h₁ : l.SortedLE) (h₂ : l.Nodup) :
    l.SortedLT := (h₁.monotone_get.strictMono_of_injective h₂.injective_get).sortedLT

/--
theorem `SortedGE.sortedGT_of_nodup` / 定理 `SortedGE.sortedGT_of_nodup`

English:
theorem SortedGE.sortedGT_of_nodup
  given: {l : List α} (h₁ : l.SortedGE) (h₂ : l.Nodup)
  proof: (h₁.antitone_get.strictAnti_of_injective h₂.injective_get).sortedGT

中文:
定理 SortedGE.sortedGT_of_nodup
  条件: {l : 列表 α} (h₁ : l.SortedGE) (h₂ : l.Nodup)
  证明: (h₁.antitone_get.strictAnti_of_injective h₂.injective_get).sortedGT
-/
protected theorem SortedGE.sortedGT_of_nodup {l : List α} (h₁ : l.SortedGE) (h₂ : l.Nodup) :
    l.SortedGT := (h₁.antitone_get.strictAnti_of_injective h₂.injective_get).sortedGT

/--
theorem `sortedLT_iff_nodup_and_sortedLE` / 定理 `sortedLT_iff_nodup_and_sortedLE`

English:
theorem sortedLT_iff_nodup_and_sortedLE
  statement: l.SortedLT ↔ l.Nodup ∧ l.SortedLE
  proof: ⟨fun h => ⟨h.nodup, h.sortedLE⟩, fun h => h.2.sortedLT_of_nodup h.1⟩

中文:
定理 sortedLT_iff_nodup_and_sortedLE
  结论: l.SortedLT ↔ l.Nodup ∧ l.SortedLE
  证明: ⟨fun h => ⟨h.nodup, h.sortedLE⟩, fun h => h.2.sortedLT_of_nodup h.1⟩

Depends on / 依赖: h.nodup, h.sortedLE, sortedLE, sortedLT_of_nodup
-/
theorem sortedLT_iff_nodup_and_sortedLE : l.SortedLT ↔ l.Nodup ∧ l.SortedLE :=
  ⟨fun h => ⟨h.nodup, h.sortedLE⟩, fun h => h.2.sortedLT_of_nodup h.1⟩

/--
theorem `sortedGT_iff_nodup_and_sortedGE` / 定理 `sortedGT_iff_nodup_and_sortedGE`

English:
theorem sortedGT_iff_nodup_and_sortedGE
  statement: l.SortedGT ↔ l.Nodup ∧ l.SortedGE
  proof: ⟨fun h => ⟨h.nodup, h.sortedGE⟩, fun h => h.2.sortedGT_of_nodup h.1⟩

中文:
定理 sortedGT_iff_nodup_and_sortedGE
  结论: l.SortedGT ↔ l.Nodup ∧ l.SortedGE
  证明: ⟨fun h => ⟨h.nodup, h.sortedGE⟩, fun h => h.2.sortedGT_of_nodup h.1⟩

Depends on / 依赖: h.nodup, h.sortedGE, sortedGE, sortedGT_of_nodup
-/
theorem sortedGT_iff_nodup_and_sortedGE : l.SortedGT ↔ l.Nodup ∧ l.SortedGE :=
  ⟨fun h => ⟨h.nodup, h.sortedGE⟩, fun h => h.2.sortedGT_of_nodup h.1⟩

/--
theorem `Perm.eq_of_sortedLE` / 定理 `Perm.eq_of_sortedLE`

English:
theorem Perm.eq_of_sortedLE
  statement: {l₁ l₂ : List α} (hl₁ : l₁.SortedLE)
  proof: Perm.eq_of_pairwise' hl₁.pairwise hl₂.pairwise

中文:
定理 置换.eq_of_sortedLE
  结论: {l₁ l₂ : 列表 α} (hl₁ : l₁.SortedLE)
  证明: Perm.eq_of_pairwise' hl₁.pairwise hl₂.pairwise

Depends on / 依赖: Perm.eq_of_pairwise, eq_of_pairwise, pairwise
-/
theorem Perm.eq_of_sortedLE {l₁ l₂ : List α} (hl₁ : l₁.SortedLE)
    (hl₂ : l₂.SortedLE) : (hl₁₂ : l₁ ~ l₂) -> l₁ = l₂ :=
  Perm.eq_of_pairwise' hl₁.pairwise hl₂.pairwise

/--
theorem `Perm.eq_of_sortedGE` / 定理 `Perm.eq_of_sortedGE`

English:
theorem Perm.eq_of_sortedGE
  statement: {l₁ l₂ : List α} (hl₁ : l₁.SortedGE)
  proof: Perm.eq_of_pairwise' hl₁.pairwise hl₂.pairwise

中文:
定理 置换.eq_of_sortedGE
  结论: {l₁ l₂ : 列表 α} (hl₁ : l₁.SortedGE)
  证明: Perm.eq_of_pairwise' hl₁.pairwise hl₂.pairwise

Depends on / 依赖: Perm.eq_of_pairwise, eq_of_pairwise, pairwise
-/
theorem Perm.eq_of_sortedGE {l₁ l₂ : List α} (hl₁ : l₁.SortedGE)
    (hl₂ : l₂.SortedGE) : (hl₁₂ : l₁ ~ l₂) -> l₁ = l₂ :=
  Perm.eq_of_pairwise' hl₁.pairwise hl₂.pairwise

/--
theorem `Subset.antisymm_of_sortedLT` / 定理 `Subset.antisymm_of_sortedLT`

English:
theorem Subset.antisymm_of_sortedLT
  statement: {l₁ l₂ : List α} (hl₁₂ : l₁ subseteq l₂) (hl₁₂' : l₂ subseteq l₁)
  proof: hl₁₂.antisymm_of_pairwise h₁.pairwise h₂.pairwise hl₁₂'

中文:
定理 子集.antisymm_of_sortedLT
  结论: {l₁ l₂ : 列表 α} (hl₁₂ : l₁ subseteq l₂) (hl₁₂' : l₂ subseteq l₁)
  证明: hl₁₂.antisymm_of_pairwise h₁.pairwise h₂.pairwise hl₁₂'

Depends on / 依赖: antisymm_of_pairwise, pairwise
-/
theorem Subset.antisymm_of_sortedLT {l₁ l₂ : List α} (hl₁₂ : l₁ subseteq l₂) (hl₁₂' : l₂ subseteq l₁)
    (h₁ : l₁.SortedLT) (h₂ : l₂.SortedLT) : l₁ = l₂ :=
  hl₁₂.antisymm_of_pairwise h₁.pairwise h₂.pairwise hl₁₂'

/--
theorem `Subset.antisymm_of_sortedGT` / 定理 `Subset.antisymm_of_sortedGT`

English:
theorem Subset.antisymm_of_sortedGT
  statement: {l₁ l₂ : List α} (hl₁₂ : l₁ subseteq l₂) (hl₁₂' : l₂ subseteq l₁)
  proof: hl₁₂.antisymm_of_pairwise h₁.pairwise h₂.pairwise hl₁₂'

中文:
定理 子集.antisymm_of_sortedGT
  结论: {l₁ l₂ : 列表 α} (hl₁₂ : l₁ subseteq l₂) (hl₁₂' : l₂ subseteq l₁)
  证明: hl₁₂.antisymm_of_pairwise h₁.pairwise h₂.pairwise hl₁₂'

Depends on / 依赖: antisymm_of_pairwise, pairwise
-/
theorem Subset.antisymm_of_sortedGT {l₁ l₂ : List α} (hl₁₂ : l₁ subseteq l₂) (hl₁₂' : l₂ subseteq l₁)
    (h₁ : l₁.SortedGT) (h₂ : l₂.SortedGT) : l₁ = l₂ :=
  hl₁₂.antisymm_of_pairwise h₁.pairwise h₂.pairwise hl₁₂'

/--
theorem `SortedLT.eq_of_mem_iff` / 定理 `SortedLT.eq_of_mem_iff`

English:
theorem SortedLT.eq_of_mem_iff
  statement: {l₁ l₂ : List α}
  proof: h₁.pairwise.eq_of_mem_iff h₂.pairwise

中文:
定理 SortedLT.eq_of_mem_iff
  结论: {l₁ l₂ : 列表 α}
  证明: h₁.pairwise.eq_of_mem_iff h₂.pairwise

Depends on / 依赖: eq_of_mem_iff, pairwise, pairwise.eq_of_mem_iff
-/
theorem SortedLT.eq_of_mem_iff {l₁ l₂ : List α}
    (h₁ : l₁.SortedLT) (h₂ : l₂.SortedLT) : (h : forall a : α, a in l₁ ↔ a in l₂) -> l₁ = l₂ :=
  h₁.pairwise.eq_of_mem_iff h₂.pairwise

/--
theorem `SortedGT.eq_of_mem_iff` / 定理 `SortedGT.eq_of_mem_iff`

English:
theorem SortedGT.eq_of_mem_iff
  statement: {l₁ l₂ : List α}
  proof: h₁.pairwise.eq_of_mem_iff h₂.pairwise h

中文:
定理 SortedGT.eq_of_mem_iff
  结论: {l₁ l₂ : 列表 α}
  证明: h₁.pairwise.eq_of_mem_iff h₂.pairwise h

Depends on / 依赖: eq_of_mem_iff, pairwise, pairwise.eq_of_mem_iff
-/
theorem SortedGT.eq_of_mem_iff {l₁ l₂ : List α}
    (h₁ : l₁.SortedGT) (h₂ : l₂.SortedGT) (h : forall a : α, a in l₁ ↔ a in l₂) : l₁ = l₂ :=
  h₁.pairwise.eq_of_mem_iff h₂.pairwise h

/--
theorem `Perm.eq_reverse_of_sortedLE_of_sortedGE` / 定理 `Perm.eq_reverse_of_sortedLE_of_sortedGE`

English:
theorem Perm.eq_reverse_of_sortedLE_of_sortedGE
  statement: {l₁ l₂ : List α} (hp : l₁ ~ l₂) (hl₁ : l₁.SortedLE)
  proof: (perm_reverse.mpr hp).eq_of_sortedLE hl₁ hl₂.reverse

中文:
定理 置换.eq_reverse_of_sortedLE_of_sortedGE
  结论: {l₁ l₂ : 列表 α} (hp : l₁ ~ l₂) (hl₁ : l₁.SortedLE)
  证明: (perm_reverse.mpr hp).eq_of_sortedLE hl₁ hl₂.reverse

Depends on / 依赖: eq_of_sortedLE, perm_reverse, perm_reverse.mpr, reverse
-/
theorem Perm.eq_reverse_of_sortedLE_of_sortedGE {l₁ l₂ : List α} (hp : l₁ ~ l₂) (hl₁ : l₁.SortedLE)
    (hl₂ : l₂.SortedGE) : l₁ = l₂.reverse :=
  (perm_reverse.mpr hp).eq_of_sortedLE hl₁ hl₂.reverse

/--
theorem `SortedLT.eq_reverse_of_mem_iff_of_sortedGT` / 定理 `SortedLT.eq_reverse_of_mem_iff_of_sortedGT`

English:
theorem SortedLT.eq_reverse_of_mem_iff_of_sortedGT
  statement: {l₁ l₂ : List α}
  proof: hl₁.eq_of_mem_iff hl₂.reverse (by simpa using h)

中文:
定理 SortedLT.eq_reverse_of_mem_iff_of_sortedGT
  结论: {l₁ l₂ : 列表 α}
  证明: hl₁.eq_of_mem_iff hl₂.reverse (by simpa using h)

Depends on / 依赖: eq_of_mem_iff, reverse
-/
theorem SortedLT.eq_reverse_of_mem_iff_of_sortedGT {l₁ l₂ : List α}
    (h : forall a : α, a in l₁ ↔ a in l₂) (hl₁ : l₁.SortedLT)
    (hl₂ : l₂.SortedGT) : l₁ = l₂.reverse := hl₁.eq_of_mem_iff hl₂.reverse (by simpa using h)

/--
theorem `SortedGT.eq_reverse_of_mem_iff_of_sortedLT` / 定理 `SortedGT.eq_reverse_of_mem_iff_of_sortedLT`

English:
theorem SortedGT.eq_reverse_of_mem_iff_of_sortedLT
  statement: {l₁ l₂ : List α}
  proof: hl₁.eq_of_mem_iff hl₂.reverse (by simpa using h)

中文:
定理 SortedGT.eq_reverse_of_mem_iff_of_sortedLT
  结论: {l₁ l₂ : 列表 α}
  证明: hl₁.eq_of_mem_iff hl₂.reverse (by simpa using h)

Depends on / 依赖: eq_of_mem_iff, reverse
-/
theorem SortedGT.eq_reverse_of_mem_iff_of_sortedLT {l₁ l₂ : List α}
    (h : forall a : α, a in l₁ ↔ a in l₂) (hl₁ : l₁.SortedGT)
    (hl₂ : l₂.SortedLT) : l₁ = l₂.reverse :=
  hl₁.eq_of_mem_iff hl₂.reverse (by simpa using h)

/--
theorem `sublist_of_subperm_of_sortedLE` / 定理 `sublist_of_subperm_of_sortedLE`

English:
theorem sublist_of_subperm_of_sortedLE
  statement: {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hl₁ : l₁.SortedLE)
  proof: sublist_of_subperm_of_pairwise hp hl₁.pairwise hl₂.pairwise

中文:
定理 sublist_of_subperm_of_sortedLE
  结论: {l₁ l₂ : 列表 α} (hp : l₁ <+~ l₂) (hl₁ : l₁.SortedLE)
  证明: sublist_of_subperm_of_pairwise hp hl₁.pairwise hl₂.pairwise

Depends on / 依赖: pairwise, sublist_of_subperm_of_pairwise
-/
theorem sublist_of_subperm_of_sortedLE {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hl₁ : l₁.SortedLE)
    (hl₂ : l₂.SortedLE) : l₁ <+ l₂ := sublist_of_subperm_of_pairwise hp hl₁.pairwise hl₂.pairwise

/--
theorem `sublist_of_subperm_of_sortedGE` / 定理 `sublist_of_subperm_of_sortedGE`

English:
theorem sublist_of_subperm_of_sortedGE
  statement: {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hl₁ : l₁.SortedGE)
  proof: sublist_of_subperm_of_pairwise hp hl₁.pairwise hl₂.pairwise

中文:
定理 sublist_of_subperm_of_sortedGE
  结论: {l₁ l₂ : 列表 α} (hp : l₁ <+~ l₂) (hl₁ : l₁.SortedGE)
  证明: sublist_of_subperm_of_pairwise hp hl₁.pairwise hl₂.pairwise

Depends on / 依赖: pairwise, sublist_of_subperm_of_pairwise
-/
theorem sublist_of_subperm_of_sortedGE {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hl₁ : l₁.SortedGE)
    (hl₂ : l₂.SortedGE) : l₁ <+ l₂ := sublist_of_subperm_of_pairwise hp hl₁.pairwise hl₂.pairwise

end PartialOrder

section LinearOrder

variable [LinearOrder α]

/--
theorem `sortedLE_mergeSort` / 定理 `sortedLE_mergeSort`

English:
theorem sortedLE_mergeSort
  statement: (l.mergeSort (· <= ·)).SortedLE
  proof: (pairwise_mergeSort' _ _).sortedLE

中文:
定理 sortedLE_mergeSort
  结论: (l.mergeSort (· <= ·)).SortedLE
  证明: (pairwise_mergeSort' _ _).sortedLE

Depends on / 依赖: pairwise_mergeSort, sortedLE
-/
theorem sortedLE_mergeSort : (l.mergeSort (· <= ·)).SortedLE :=
  (pairwise_mergeSort' _ _).sortedLE

/--
theorem `sortedGE_mergeSort` / 定理 `sortedGE_mergeSort`

English:
theorem sortedGE_mergeSort
  statement: (l.mergeSort (· >= ·)).SortedGE
  proof: (pairwise_mergeSort' _ _).sortedGE

中文:
定理 sortedGE_mergeSort
  结论: (l.mergeSort (· >= ·)).SortedGE
  证明: (pairwise_mergeSort' _ _).sortedGE

Depends on / 依赖: Decidable, Fintype, fintypeInsert, pairwise_mergeSort, sortedGE
-/
theorem sortedGE_mergeSort : (l.mergeSort (· >= ·)).SortedGE :=
  (pairwise_mergeSort' _ _).sortedGE

/--
theorem `sortedLE_insertionSort` / 定理 `sortedLE_insertionSort`

English:
theorem sortedLE_insertionSort
  statement: (l.insertionSort (· <= ·)).SortedLE
  proof: (pairwise_insertionSort _ _).sortedLE

中文:
定理 sortedLE_insertionSort
  结论: (l.insertionSort (· <= ·)).SortedLE
  证明: (pairwise_insertionSort _ _).sortedLE

Depends on / 依赖: pairwise_insertionSort, sortedLE
-/
theorem sortedLE_insertionSort : (l.insertionSort (· <= ·)).SortedLE :=
  (pairwise_insertionSort _ _).sortedLE

/--
theorem `sortedGE_insertionSort` / 定理 `sortedGE_insertionSort`

English:
theorem sortedGE_insertionSort
  statement: (l.insertionSort (· >= ·)).SortedGE
  proof: (pairwise_insertionSort _ _).sortedGE

@[simp]

中文:
定理 sortedGE_insertionSort
  结论: (l.insertionSort (· >= ·)).SortedGE
  证明: (pairwise_insertionSort _ _).sortedGE

@[simp]

Depends on / 依赖: pairwise_insertionSort, sortedGE
-/
theorem sortedGE_insertionSort : (l.insertionSort (· >= ·)).SortedGE :=
  (pairwise_insertionSort _ _).sortedGE

@[simp]
/--
theorem `SortedLT.getElem_le_getElem_iff` / 定理 `SortedLT.getElem_le_getElem_iff`

English:
theorem SortedLT.getElem_le_getElem_iff
  statement: (hl : l.SortedLT) {i j} {hi : i < l.length}
  proof: hl.strictMono_get.le_iff_le

@[simp]

中文:
定理 SortedLT.getElem_le_getElem_iff
  结论: (hl : l.SortedLT) {i j} {hi : i < l.length}
  证明: hl.strictMono_get.le_iff_le

@[simp]

Depends on / 依赖: hl.strictMono_get.le_iff_le, le_iff_le, strictMono_get
-/
theorem SortedLT.getElem_le_getElem_iff (hl : l.SortedLT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] <= l[j] ↔ i <= j := hl.strictMono_get.le_iff_le

@[simp]
/--
theorem `SortedGT.getElem_le_getElem_iff` / 定理 `SortedGT.getElem_le_getElem_iff`

English:
theorem SortedGT.getElem_le_getElem_iff
  statement: (hl : l.SortedGT) {i j} {hi : i < l.length}
  proof: hl.strictAnti_get.le_iff_ge

@[simp]

中文:
定理 SortedGT.getElem_le_getElem_iff
  结论: (hl : l.SortedGT) {i j} {hi : i < l.length}
  证明: hl.strictAnti_get.le_iff_ge

@[simp]

Depends on / 依赖: hl.strictAnti_get.le_iff_ge, le_iff_ge, strictAnti_get
-/
theorem SortedGT.getElem_le_getElem_iff (hl : l.SortedGT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] <= l[j] ↔ j <= i := hl.strictAnti_get.le_iff_ge

@[simp]
/--
theorem `SortedLT.getElem_lt_getElem_iff` / 定理 `SortedLT.getElem_lt_getElem_iff`

English:
theorem SortedLT.getElem_lt_getElem_iff
  statement: (hl : l.SortedLT) {i j} {hi : i < l.length}
  proof: hl.strictMono_get.lt_iff_lt

@[simp]

中文:
定理 SortedLT.getElem_lt_getElem_iff
  结论: (hl : l.SortedLT) {i j} {hi : i < l.length}
  证明: hl.strictMono_get.lt_iff_lt

@[simp]

Depends on / 依赖: hl.strictMono_get.lt_iff_lt, lt_iff_lt, strictMono_get
-/
theorem SortedLT.getElem_lt_getElem_iff (hl : l.SortedLT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] < l[j] ↔ i < j := hl.strictMono_get.lt_iff_lt

@[simp]
/--
theorem `SortedGT.getElem_lt_getElem_iff` / 定理 `SortedGT.getElem_lt_getElem_iff`

English:
theorem SortedGT.getElem_lt_getElem_iff
  statement: (hl : l.SortedGT) {i j} {hi : i < l.length}
  proof: hl.strictAnti_get.lt_iff_gt

中文:
定理 SortedGT.getElem_lt_getElem_iff
  结论: (hl : l.SortedGT) {i j} {hi : i < l.length}
  证明: hl.strictAnti_get.lt_iff_gt

Depends on / 依赖: hl.strictAnti_get.lt_iff_gt, lt_iff_gt, strictAnti_get
-/
theorem SortedGT.getElem_lt_getElem_iff (hl : l.SortedGT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] < l[j] ↔ j < i := hl.strictAnti_get.lt_iff_gt

end LinearOrder

end Sorted

end List

namespace RelEmbedding

open List

variable {α β : Type*} {ra : α -> α -> Prop} {rb : β -> β -> Prop}

@[simp]
/--
theorem `pairwise_listMap` / 定理 `pairwise_listMap`

English:
theorem pairwise_listMap
  given: (e : ra ↪r rb) {l : List α}
  statement: (l.map e).Pairwise rb ↔ l.Pairwise ra
  proof: by
  simp [pairwise_map, e.map_rel_iff]

@[simp]

中文:
定理 pairwise_listMap
  条件: (e : ra ↪r rb) {l : 列表 α}
  结论: (l.map e).两两 rb ↔ l.两两 ra
  证明: by
  simp [pairwise_map, e.map_rel_iff]

@[simp]

Depends on / 依赖: e.map_rel_iff, map_rel_iff, pairwise_map
-/
theorem pairwise_listMap (e : ra ↪r rb) {l : List α} : (l.map e).Pairwise rb ↔ l.Pairwise ra := by
  simp [pairwise_map, e.map_rel_iff]

@[simp]
/--
theorem `pairwise_swap_listMap` / 定理 `pairwise_swap_listMap`

English:
theorem pairwise_swap_listMap
  given: (e : ra ↪r rb) {l : List α}
  proof: by
  simp [pairwise_map, e.map_rel_iff]

中文:
定理 pairwise_swap_listMap
  条件: (e : ra ↪r rb) {l : 列表 α}
  证明: by
  simp [pairwise_map, e.map_rel_iff]

Depends on / 依赖: e.map_rel_iff, map_rel_iff, pairwise_map
-/
theorem pairwise_swap_listMap (e : ra ↪r rb) {l : List α} :
    (l.map e).Pairwise (Function.swap rb) ↔ l.Pairwise (Function.swap ra) := by
  simp [pairwise_map, e.map_rel_iff]

end RelEmbedding

namespace RelIso

variable {α β : Type*} {ra : α -> α -> Prop} {rb : β -> β -> Prop}

@[simp]
/--
theorem `pairwise_listMap` / 定理 `pairwise_listMap`

English:
theorem pairwise_listMap
  given: (e : ra ≃r rb) {l : List α}
  statement: (l.map e).Pairwise rb ↔ l.Pairwise ra
  proof: e.toRelEmbedding.pairwise_listMap

@[simp]

中文:
定理 pairwise_listMap
  条件: (e : ra ≃r rb) {l : 列表 α}
  结论: (l.map e).两两 rb ↔ l.两两 ra
  证明: e.toRelEmbedding.pairwise_listMap

@[simp]

Depends on / 依赖: e.toRelEmbedding.pairwise_listMap, pairwise_listMap, toRelEmbedding
-/
theorem pairwise_listMap (e : ra ≃r rb) {l : List α} : (l.map e).Pairwise rb ↔ l.Pairwise ra :=
  e.toRelEmbedding.pairwise_listMap

@[simp]
/--
theorem `pairwise_swap_listMap` / 定理 `pairwise_swap_listMap`

English:
theorem pairwise_swap_listMap
  given: (e : ra ≃r rb) {l : List α}
  proof: e.toRelEmbedding.pairwise_swap_listMap

中文:
定理 pairwise_swap_listMap
  条件: (e : ra ≃r rb) {l : 列表 α}
  证明: e.toRelEmbedding.pairwise_swap_listMap

Depends on / 依赖: e.toRelEmbedding.pairwise_swap_listMap, pairwise_swap_listMap, toRelEmbedding
-/
theorem pairwise_swap_listMap (e : ra ≃r rb) {l : List α} :
    (l.map e).Pairwise (Function.swap rb) ↔ l.Pairwise (Function.swap ra) :=
  e.toRelEmbedding.pairwise_swap_listMap

end RelIso

namespace OrderEmbedding

open List

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
/--
theorem `sortedLE_listMap` / 定理 `sortedLE_listMap`

English:
theorem sortedLE_listMap
  given: (e : α ↪o β) {l : List α}
  proof: by
  simp_rw [sortedLE_iff_pairwise, e.pairwise_listMap]

@[simp]

中文:
定理 sortedLE_listMap
  条件: (e : α ↪o β) {l : 列表 α}
  证明: by
  simp_rw [sortedLE_iff_pairwise, e.pairwise_listMap]

@[simp]

Depends on / 依赖: e.pairwise_listMap, pairwise_listMap, simp_rw, sortedLE_iff_pairwise
-/
theorem sortedLE_listMap (e : α ↪o β) {l : List α} :
    (l.map e).SortedLE ↔ l.SortedLE := by
  simp_rw [sortedLE_iff_pairwise, e.pairwise_listMap]

@[simp]
/--
theorem `sortedLT_listMap` / 定理 `sortedLT_listMap`

English:
theorem sortedLT_listMap
  given: (e : α ↪o β) {l : List α}
  proof: by
  simp_rw [sortedLT_iff_pairwise]
  exact e.ltEmbedding.pairwise_listMap

@[simp]

中文:
定理 sortedLT_listMap
  条件: (e : α ↪o β) {l : 列表 α}
  证明: by
  simp_rw [sortedLT_iff_pairwise]
  exact e.ltEmbedding.pairwise_listMap

@[simp]

Depends on / 依赖: e.ltEmbedding.pairwise_listMap, ltEmbedding, pairwise_listMap, simp_rw, sortedLT_iff_pairwise
-/
theorem sortedLT_listMap (e : α ↪o β) {l : List α} :
    (l.map e).SortedLT ↔ l.SortedLT := by
  simp_rw [sortedLT_iff_pairwise]
  exact e.ltEmbedding.pairwise_listMap

@[simp]
/--
theorem `sortedGE_listMap` / 定理 `sortedGE_listMap`

English:
theorem sortedGE_listMap
  given: (e : α ↪o β) {l : List α}
  proof: by
  simp_rw [← sortedLE_reverse, ← map_reverse, sortedLE_listMap]

@[simp]

中文:
定理 sortedGE_listMap
  条件: (e : α ↪o β) {l : 列表 α}
  证明: by
  simp_rw [← sortedLE_reverse, ← map_reverse, sortedLE_listMap]

@[simp]

Depends on / 依赖: map_reverse, simp_rw, sortedLE_listMap, sortedLE_reverse
-/
theorem sortedGE_listMap (e : α ↪o β) {l : List α} :
    (l.map e).SortedGE ↔ l.SortedGE := by
  simp_rw [← sortedLE_reverse, ← map_reverse, sortedLE_listMap]

@[simp]
/--
theorem `sortedGT_listMap` / 定理 `sortedGT_listMap`

English:
theorem sortedGT_listMap
  given: (e : α ↪o β) {l : List α}
  proof: by
  simp_rw [← sortedLT_reverse, ← map_reverse, sortedLT_listMap]

中文:
定理 sortedGT_listMap
  条件: (e : α ↪o β) {l : 列表 α}
  证明: by
  simp_rw [← sortedLT_reverse, ← map_reverse, sortedLT_listMap]

Depends on / 依赖: OrderIso, OrderIso.finsetSetFinite.symm.toOrderEmbedding.wellFoundedLT, finsetSetFinite, map_reverse, simp_rw, sortedLT_listMap, sortedLT_reverse, toOrderEmbedding, wellFoundedLT
-/
theorem sortedGT_listMap (e : α ↪o β) {l : List α} :
    (l.map e).SortedGT ↔ l.SortedGT := by
  simp_rw [← sortedLT_reverse, ← map_reverse, sortedLT_listMap]

end OrderEmbedding

namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
/--
theorem `sortedLT_listMap` / 定理 `sortedLT_listMap`

English:
theorem sortedLT_listMap
  given: (e : α ≃o β) {l : List α}
  proof: e.toOrderEmbedding.sortedLT_listMap

@[simp]

中文:
定理 sortedLT_listMap
  条件: (e : α ≃o β) {l : 列表 α}
  证明: e.toOrderEmbedding.sortedLT_listMap

@[simp]

Depends on / 依赖: e.toOrderEmbedding.sortedLT_listMap, sortedLT_listMap, toOrderEmbedding
-/
theorem sortedLT_listMap (e : α ≃o β) {l : List α} :
    (l.map e).SortedLT ↔ l.SortedLT :=
  e.toOrderEmbedding.sortedLT_listMap

@[simp]
/--
theorem `sortedGT_listMap` / 定理 `sortedGT_listMap`

English:
theorem sortedGT_listMap
  given: (e : α ≃o β) {l : List α}
  proof: e.toOrderEmbedding.sortedGT_listMap

中文:
定理 sortedGT_listMap
  条件: (e : α ≃o β) {l : 列表 α}
  证明: e.toOrderEmbedding.sortedGT_listMap

Depends on / 依赖: e.toOrderEmbedding.sortedGT_listMap, sortedGT_listMap, toOrderEmbedding
-/
theorem sortedGT_listMap (e : α ≃o β) {l : List α} :
    (l.map e).SortedGT ↔ l.SortedGT :=
  e.toOrderEmbedding.sortedGT_listMap

end OrderIso

namespace StrictMono

variable {α β : Type*} [LinearOrder α] [Preorder β] {f : α -> β} {l : List α}

/--
theorem `sortedLE_listMap` / 定理 `sortedLE_listMap`

English:
theorem sortedLE_listMap
  given: (hf : StrictMono f)
  proof: (OrderEmbedding.ofStrictMono f hf).sortedLE_listMap

中文:
定理 sortedLE_listMap
  条件: (hf : 严格递增 f)
  证明: (OrderEmbedding.ofStrictMono f hf).sortedLE_listMap

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, ofStrictMono, sortedLE_listMap
-/
theorem sortedLE_listMap (hf : StrictMono f) :
    (l.map f).SortedLE ↔ l.SortedLE :=
  (OrderEmbedding.ofStrictMono f hf).sortedLE_listMap

/--
theorem `sortedGE_listMap` / 定理 `sortedGE_listMap`

English:
theorem sortedGE_listMap
  given: (hf : StrictMono f)
  proof: (OrderEmbedding.ofStrictMono f hf).sortedGE_listMap

中文:
定理 sortedGE_listMap
  条件: (hf : 严格递增 f)
  证明: (OrderEmbedding.ofStrictMono f hf).sortedGE_listMap

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, ofStrictMono, sortedGE_listMap
-/
theorem sortedGE_listMap (hf : StrictMono f) :
    (l.map f).SortedGE ↔ l.SortedGE :=
  (OrderEmbedding.ofStrictMono f hf).sortedGE_listMap

/--
theorem `sortedLT_listMap` / 定理 `sortedLT_listMap`

English:
theorem sortedLT_listMap
  given: (hf : StrictMono f)
  proof: (OrderEmbedding.ofStrictMono f hf).sortedLT_listMap

中文:
定理 sortedLT_listMap
  条件: (hf : 严格递增 f)
  证明: (OrderEmbedding.ofStrictMono f hf).sortedLT_listMap

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, ofStrictMono, sortedLT_listMap
-/
theorem sortedLT_listMap (hf : StrictMono f) :
    (l.map f).SortedLT ↔ l.SortedLT :=
  (OrderEmbedding.ofStrictMono f hf).sortedLT_listMap

/--
theorem `sortedGT_listMap` / 定理 `sortedGT_listMap`

English:
theorem sortedGT_listMap
  given: (hf : StrictMono f)
  proof: (OrderEmbedding.ofStrictMono f hf).sortedGT_listMap

中文:
定理 sortedGT_listMap
  条件: (hf : 严格递增 f)
  证明: (OrderEmbedding.ofStrictMono f hf).sortedGT_listMap

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, ofStrictMono, sortedGT_listMap
-/
theorem sortedGT_listMap (hf : StrictMono f) :
    (l.map f).SortedGT ↔ l.SortedGT :=
  (OrderEmbedding.ofStrictMono f hf).sortedGT_listMap

end StrictMono

namespace StrictAnti

open List

variable {α β : Type*} [LinearOrder α] [Preorder β] {f : α -> β} {l : List α}

/--
theorem `sortedLE_listMap` / 定理 `sortedLE_listMap`

English:
theorem sortedLE_listMap
  given: (hf : StrictAnti f)
  proof: by
  grind [hf.le_iff_ge]

中文:
定理 sortedLE_listMap
  条件: (hf : 严格递减 f)
  证明: by
  grind [hf.le_iff_ge]

Depends on / 依赖: hf.le_iff_ge, le_iff_ge
-/
theorem sortedLE_listMap (hf : StrictAnti f) :
    (l.map f).SortedLE ↔ l.SortedGE := by
  grind [hf.le_iff_ge]

/--
theorem `sortedGE_listMap` / 定理 `sortedGE_listMap`

English:
theorem sortedGE_listMap
  given: (hf : StrictAnti f)
  proof: by
  grind [hf.le_iff_ge]

中文:
定理 sortedGE_listMap
  条件: (hf : 严格递减 f)
  证明: by
  grind [hf.le_iff_ge]

Depends on / 依赖: hf.le_iff_ge, le_iff_ge
-/
theorem sortedGE_listMap (hf : StrictAnti f) :
    (l.map f).SortedGE ↔ l.SortedLE := by
  grind [hf.le_iff_ge]

/--
theorem `sortedLT_listMap` / 定理 `sortedLT_listMap`

English:
theorem sortedLT_listMap
  given: (hf : StrictAnti f)
  proof: by
  grind [hf.lt_iff_gt]

中文:
定理 sortedLT_listMap
  条件: (hf : 严格递减 f)
  证明: by
  grind [hf.lt_iff_gt]

Depends on / 依赖: hf.lt_iff_gt, lt_iff_gt
-/
theorem sortedLT_listMap (hf : StrictAnti f) :
    (l.map f).SortedLT ↔ l.SortedGT := by
  grind [hf.lt_iff_gt]

/--
theorem `sortedGT_listMap` / 定理 `sortedGT_listMap`

English:
theorem sortedGT_listMap
  given: (hf : StrictAnti f)
  proof: by
  grind [hf.lt_iff_gt]

中文:
定理 sortedGT_listMap
  条件: (hf : 严格递减 f)
  证明: by
  grind [hf.lt_iff_gt]

Depends on / 依赖: hf.lt_iff_gt, lt_iff_gt
-/
theorem sortedGT_listMap (hf : StrictAnti f) :
    (l.map f).SortedGT ↔ l.SortedLT := by
  grind [hf.lt_iff_gt]

end StrictAnti
