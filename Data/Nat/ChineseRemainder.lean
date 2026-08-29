/-
Copyright (c) 2023 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
module

public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Algebra.Ring.Nat

/-!
# Chinese Remainder Theorem

This file provides definitions and theorems for the Chinese Remainder Theorem. These are used in
Gödel's Beta function, which is used in proving Gödel's incompleteness theorems.

## Main result

- `chineseRemainderOfList`: Definition of the Chinese remainder of a list

## Tags

Chinese Remainder Theorem, Gödel, beta function
-/

@[expose] public section

open scoped Function -- required for scoped `on` notation
namespace Nat

variable {ι : Type*}

/--
lemma `modEq_list_prod_iff` / 引理 `modEq_list_prod_iff`

English:
lemma modEq_list_prod_iff
  given: {a b} {l : List Nat} (co : l.Pairwise Coprime)
  proof: by
  induction l with
  | nil => simp [modEq_one]
  | cons m l ih =>
    have : Coprime m l.prod := coprime_list_prod_right_iff.mpr (List.pairwise_cons.mp co).1
    simp only [List.prod_cons, ← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co),
      List.length_cons]
    constructor
    · rintro ⟨h0, hs⟩ i
      cases i using Fin.cases <;> simp_all
    · intro h; exact ⟨h 0, fun i => h i.succ⟩

中文:
引理 modEq_list_prod_iff
  条件: {a b} {l : 列表 自然数} (co : l.两两 Coprime)
  证明: by
  induction l with
  | nil => simp [modEq_one]
  | cons m l ih =>
    have : Coprime m l.prod := coprime_list_prod_right_iff.mpr (List.pairwise_cons.mp co).1
    simp only [List.prod_cons, ← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co),
      List.length_cons]
    constructor
    · rintro ⟨h0, hs⟩ i
      cases i using Fin.cases <;> simp_all
    · intro h; exact ⟨h 0, fun i => h i.succ⟩

Depends on / 依赖: Coprime, Fin.cases, List.Pairwise.of_cons, List.length_cons, List.pairwise_cons.mp, List.prod_cons, Pairwise, coprime_list_prod_right_iff, coprime_list_prod_right_iff.mpr, i.succ, l.prod, length_cons, modEq_and_modEq_iff_modEq_mul, modEq_one, of_cons, pairwise_cons, prod_cons
-/
lemma modEq_list_prod_iff {a b} {l : List Nat} (co : l.Pairwise Coprime) :
    a ≡ b [MOD l.prod] ↔ forall i, a ≡ b [MOD l.get i] := by
  induction l with
  | nil => simp [modEq_one]
  | cons m l ih =>
    have : Coprime m l.prod := coprime_list_prod_right_iff.mpr (List.pairwise_cons.mp co).1
    simp only [List.prod_cons, ← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co),
      List.length_cons]
    constructor
    · rintro ⟨h0, hs⟩ i
      cases i using Fin.cases <;> simp_all
    · intro h; exact ⟨h 0, fun i => h i.succ⟩

/--
lemma `modEq_list_map_prod_iff` / 引理 `modEq_list_map_prod_iff`

English:
lemma modEq_list_map_prod_iff
  given: {a b} {s : ι -> Nat} {l : List ι} (co : l.Pairwise (Coprime on s))
  proof: by
  induction l with
  | nil => simp [modEq_one]
  | cons i l ih =>
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    simp [← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co)]

中文:
引理 modEq_list_map_prod_iff
  条件: {a b} {s : ι -> 自然数} {l : 列表 ι} (co : l.两两 (Coprime on s))
  证明: by
  induction l with
  | nil => simp [modEq_one]
  | cons i l ih =>
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    simp [← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co)]

Depends on / 依赖: Coprime, List.Pairwise.of_cons, List.mem_map, List.pairwise_cons.mp, Pairwise, and_imp, coprime_list_prod_right_iff, forall_exists_index, l.map, mem_map, modEq_and_modEq_iff_modEq_mul, modEq_one, of_cons, pairwise_cons
-/
lemma modEq_list_map_prod_iff {a b} {s : ι -> Nat} {l : List ι} (co : l.Pairwise (Coprime on s)) :
    a ≡ b [MOD (l.map s).prod] ↔ forall i in l, a ≡ b [MOD s i] := by
  induction l with
  | nil => simp [modEq_one]
  | cons i l ih =>
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    simp [← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co)]

variable (a s : ι -> Nat)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `chineseRemainderOfList` / `chineseRemainderOfList` 的定义

English:
definition chineseRemainderOfList
  signature: : (l : List ι) -> l.Pairwise (Coprime on s) ->
  body: by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    have ih := chineseRemainderOfList l co.of_cons
    have k := chineseRemainder this (a i) ih
    use k
    simp only [List.mem_cons, forall_eq_or_imp, k.prop.1, true_and]
    intro j hj
    exact ((modEq_list_map_prod_iff co.of_cons).mp k.prop.2 j hj).trans (ih.prop j hj)

中文:
定义 chineseRemainderOfList
  签名: : (l : 列表 ι) -> l.两两 (Coprime on s) ->
  定义体: by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    have ih := chineseRemainderOfList l co.of_cons
    have k := chineseRemainder this (a i) ih
    use k
    simp only [List.mem_cons, forall_eq_or_imp, k.prop.1, true_and]
    intro j hj
    exact ((modEq_list_map_prod_iff co.of_cons).mp k.prop.2 j hj).trans (ih.prop j hj)

Depends on / 依赖: List.mem_cons, List.mem_map, List.pairwise_cons.mp, and_imp, chineseRemainder, chineseRemainderOfList, co.of_cons, coprime_list_prod_right_iff, forall_eq_or_imp, forall_exists_index, ih.prop, k.prop, mem_cons, mem_map, modEq_list_map_prod_iff, of_cons, pairwise_cons, true_and
-/
def chineseRemainderOfList : (l : List ι) -> l.Pairwise (Coprime on s) ->
    { k // forall i in l, k ≡ a i [MOD s i] }
  | [], _ => ⟨0, by simp⟩
  | i :: l, co => by
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    have ih := chineseRemainderOfList l co.of_cons
    have k := chineseRemainder this (a i) ih
    use k
    simp only [List.mem_cons, forall_eq_or_imp, k.prop.1, true_and]
    intro j hj
    exact ((modEq_list_map_prod_iff co.of_cons).mp k.prop.2 j hj).trans (ih.prop j hj)

/--
theorem `chineseRemainderOfList_nil` / 定理 `chineseRemainderOfList_nil`

English:
theorem chineseRemainderOfList_nil
  proof: rfl

中文:
定理 chineseRemainderOfList_nil
  证明: rfl
-/
@[simp] theorem chineseRemainderOfList_nil :
    (chineseRemainderOfList a s [] List.Pairwise.nil : Nat) = 0 := rfl

/--
theorem `chineseRemainderOfList_lt_prod` / 定理 `chineseRemainderOfList_lt_prod`

English:
theorem chineseRemainderOfList_lt_prod
  statement: (l : List ι)
  proof: by
  cases l with
  | nil => simp
  | cons i l =>
    simp only [chineseRemainderOfList, List.map_cons, List.prod_cons]
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    refine chineseRemainder_lt_mul this (a i) (chineseRemainderOfList a s l co.of_cons)
      (hs i List.mem_cons_self) ?_
    simp only [ne_eq, List.prod_eq_zero_iff, List.mem_map, not_exists, not_and]
    intro j hj
    exact hs j (List.mem_cons_of_mem _ hj)

中文:
定理 chineseRemainderOfList_lt_prod
  结论: (l : 列表 ι)
  证明: by
  cases l with
  | nil => simp
  | cons i l =>
    simp only [chineseRemainderOfList, List.map_cons, List.prod_cons]
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    refine chineseRemainder_lt_mul this (a i) (chineseRemainderOfList a s l co.of_cons)
      (hs i List.mem_cons_self) ?_
    simp only [ne_eq, List.prod_eq_zero_iff, List.mem_map, not_exists, not_and]
    intro j hj
    exact hs j (List.mem_cons_of_mem _ hj)

Depends on / 依赖: Coprime, List.map_cons, List.mem_cons_self, List.mem_map, List.pairwise_cons.mp, List.prod_cons, List.prod_eq_zero_iff, and_imp, chineseRemainderOfList, chineseRemainder_lt_mul, co.of_cons, coprime_list_prod_right_iff, forall_exists_index, l.map, map_cons, mem_cons_self, mem_map, ne_eq, not_and, not_exists
-/
theorem chineseRemainderOfList_lt_prod (l : List ι)
    (co : l.Pairwise (Coprime on s)) (hs : forall i in l, s i != 0) :
    chineseRemainderOfList a s l co < (l.map s).prod := by
  cases l with
  | nil => simp
  | cons i l =>
    simp only [chineseRemainderOfList, List.map_cons, List.prod_cons]
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    refine chineseRemainder_lt_mul this (a i) (chineseRemainderOfList a s l co.of_cons)
      (hs i List.mem_cons_self) ?_
    simp only [ne_eq, List.prod_eq_zero_iff, List.mem_map, not_exists, not_and]
    intro j hj
    exact hs j (List.mem_cons_of_mem _ hj)

/--
theorem `chineseRemainderOfList_modEq_unique` / 定理 `chineseRemainderOfList_modEq_unique`

English:
theorem chineseRemainderOfList_modEq_unique
  statement: (l : List ι)
  proof: by
  induction l with
  | nil => simp [modEq_one]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, chineseRemainderOfList]
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    exact chineseRemainder_modEq_unique this
      (hz i List.mem_cons_self) (ih co.of_cons (fun j hj => hz j (List.mem_cons_of_mem _ hj)))

中文:
定理 chineseRemainderOfList_modEq_unique
  结论: (l : 列表 ι)
  证明: by
  induction l with
  | nil => simp [modEq_one]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, chineseRemainderOfList]
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    exact chineseRemainder_modEq_unique this
      (hz i List.mem_cons_self) (ih co.of_cons (fun j hj => hz j (List.mem_cons_of_mem _ hj)))

Depends on / 依赖: Coprime, List.map_cons, List.mem_cons_of_mem, List.mem_cons_self, List.mem_map, List.pairwise_cons.mp, List.prod_cons, and_imp, chineseRemainderOfList, chineseRemainder_modEq_unique, co.of_cons, coprime_list_prod_right_iff, forall_exists_index, l.map, map_cons, mem_cons_of_mem, mem_cons_self, mem_map, modEq_one, of_cons
-/
theorem chineseRemainderOfList_modEq_unique (l : List ι)
    (co : l.Pairwise (Coprime on s)) {z} (hz : forall i in l, z ≡ a i [MOD s i]) :
    z ≡ chineseRemainderOfList a s l co [MOD (l.map s).prod] := by
  induction l with
  | nil => simp [modEq_one]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, chineseRemainderOfList]
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    exact chineseRemainder_modEq_unique this
      (hz i List.mem_cons_self) (ih co.of_cons (fun j hj => hz j (List.mem_cons_of_mem _ hj)))

/--
theorem `chineseRemainderOfList_perm` / 定理 `chineseRemainderOfList_perm`

English:
theorem chineseRemainderOfList_perm
  statement: {l l' : List ι} (hl : l.Perm l')
  proof: by
  let z := chineseRemainderOfList a s l' (co.perm hl coprime_comm.mpr)
  have hlp : (l.map s).prod = (l'.map s).prod := List.Perm.prod_eq (List.Perm.map s hl)
  exact (chineseRemainderOfList_modEq_unique a s l co (z := z)
    (fun i hi => z.prop i (hl.symm.mem_iff.mpr hi))).symm.eq_of_lt_of_lt
      (chineseRemainderOfList_lt_prod _ _ _ _ hs)
      (by rw [hlp]
          exact chineseRemainderOfList_lt_prod _ _ _ _
            (by simpa [List.Perm.mem_iff hl.symm] using hs))

中文:
定理 chineseRemainderOfList_perm
  结论: {l l' : 列表 ι} (hl : l.置换 l')
  证明: by
  let z := chineseRemainderOfList a s l' (co.perm hl coprime_comm.mpr)
  have hlp : (l.map s).prod = (l'.map s).prod := List.Perm.prod_eq (List.Perm.map s hl)
  exact (chineseRemainderOfList_modEq_unique a s l co (z := z)
    (fun i hi => z.prop i (hl.symm.mem_iff.mpr hi))).symm.eq_of_lt_of_lt
      (chineseRemainderOfList_lt_prod _ _ _ _ hs)
      (by rw [hlp]
          exact chineseRemainderOfList_lt_prod _ _ _ _
            (by simpa [List.Perm.mem_iff hl.symm] using hs))

Depends on / 依赖: List.Perm.map, List.Perm.mem_iff, List.Perm.prod_eq, chineseRemainderOfList, chineseRemainderOfList_lt_prod, chineseRemainderOfList_modEq_unique, co.perm, coprime_comm, coprime_comm.mpr, eq_of_lt_of_lt, hl.symm, hl.symm.mem_iff.mpr, l.map, mem_iff, prod_eq, symm.eq_of_lt_of_lt, z.prop
-/
theorem chineseRemainderOfList_perm {l l' : List ι} (hl : l.Perm l')
    (hs : forall i in l, s i != 0) (co : l.Pairwise (Coprime on s)) :
    (chineseRemainderOfList a s l co : Nat) =
    chineseRemainderOfList a s l' (co.perm hl coprime_comm.mpr) := by
  let z := chineseRemainderOfList a s l' (co.perm hl coprime_comm.mpr)
  have hlp : (l.map s).prod = (l'.map s).prod := List.Perm.prod_eq (List.Perm.map s hl)
  exact (chineseRemainderOfList_modEq_unique a s l co (z := z)
    (fun i hi => z.prop i (hl.symm.mem_iff.mpr hi))).symm.eq_of_lt_of_lt
      (chineseRemainderOfList_lt_prod _ _ _ _ hs)
      (by rw [hlp]
          exact chineseRemainderOfList_lt_prod _ _ _ _
            (by simpa [List.Perm.mem_iff hl.symm] using hs))

/--
Definition of `chineseRemainderOfMultiset` / `chineseRemainderOfMultiset` 的定义

English:
definition chineseRemainderOfMultiset
  signature: {m : Multiset ι}
  body: Quotient.recOn m
    (fun l nod _ co =>
      chineseRemainderOfList a s l (List.Nodup.pairwise_of_forall_ne nod co))
    (fun l l' (pp : l.Perm l') =>
      funext fun nod' : l'.Nodup =>
      have nod : l.Nodup := pp.symm.nodup_iff.mp nod'
      funext fun hs' : forall i in l', s i != 0 =>
      have hs : forall i in l, s i != 0 := by simpa [List.Perm.mem_iff pp] using hs'
      funext fun co' : Set.Pairwise {x | x in l'} (Coprime on s) =>
      have co : Set.Pairwise {x | x in l} (Coprime on s) := by simpa [List.Perm.mem_iff pp] using co'
      have lco : l.Pairwise (Coprime on s) := List.Nodup.pairwise_of_forall_ne nod co
      have : forall {m' e nod'' hs'' co''}, @Eq.ndrec (Multiset ι) l
        (fun m => m.Nodup -> (forall i in m, s i != 0) ->
          Set.Pairwise {x | x in m} (Coprime on s) -> { k // forall i in m, k ≡ a i [MOD s i] })
        (fun nod _ co => chineseRemainderOfList a s l (List.Nodup.pairwise_of_forall_ne nod co))
          m' e nod'' hs'' co'' =
        (chineseRemainderOfList a s l lco : Nat) := by
          rintro _ rfl _ _ _; rfl
by ext; exact this.trans chineseRemainderOfList_perm a s pp hs lco)

中文:
定义 chineseRemainderOfMultiset
  签名: {m : Multiset ι}
  定义体: Quotient.recOn m
    (fun l nod _ co =>
      chineseRemainderOfList a s l (List.Nodup.pairwise_of_forall_ne nod co))
    (fun l l' (pp : l.Perm l') =>
      funext fun nod' : l'.Nodup =>
      have nod : l.Nodup := pp.symm.nodup_iff.mp nod'
      funext fun hs' : forall i in l', s i != 0 =>
      have hs : forall i in l, s i != 0 := by simpa [List.Perm.mem_iff pp] using hs'
      funext fun co' : Set.Pairwise {x | x in l'} (Coprime on s) =>
      have co : Set.Pairwise {x | x in l} (Coprime on s) := by simpa [List.Perm.mem_iff pp] using co'
      have lco : l.Pairwise (Coprime on s) := List.Nodup.pairwise_of_forall_ne nod co
      have : forall {m' e nod'' hs'' co''}, @Eq.ndrec (Multiset ι) l
        (fun m => m.Nodup -> (forall i in m, s i != 0) ->
          Set.Pairwise {x | x in m} (Coprime on s) -> { k // forall i in m, k ≡ a i [MOD s i] })
        (fun nod _ co => chineseRemainderOfList a s l (List.Nodup.pairwise_of_forall_ne nod co))
          m' e nod'' hs'' co'' =
        (chineseRemainderOfList a s l lco : Nat) := by
          rintro _ rfl _ _ _; rfl
by ext; exact this.trans chineseRemainderOfList_perm a s pp hs lco)

Depends on / 依赖: Coprime, List.Nodup.pairwise_of_forall_ne, List.Perm.mem_iff, Pairwise, Quotient, Quotient.recOn, Set.Pairwise, chineseRemainderOfList, l.Nodup, l.Perm, mem_iff, nodup_iff, pairwise_of_forall_ne, pp.symm.nodup_iff.mp
-/
def chineseRemainderOfMultiset {m : Multiset ι} :
    m.Nodup -> (forall i in m, s i != 0) -> Set.Pairwise {x | x in m} (Coprime on s) ->
    { k // forall i in m, k ≡ a i [MOD s i] } :=
  Quotient.recOn m
    (fun l nod _ co =>
      chineseRemainderOfList a s l (List.Nodup.pairwise_of_forall_ne nod co))
    (fun l l' (pp : l.Perm l') =>
      funext fun nod' : l'.Nodup =>
      have nod : l.Nodup := pp.symm.nodup_iff.mp nod'
      funext fun hs' : forall i in l', s i != 0 =>
      have hs : forall i in l, s i != 0 := by simpa [List.Perm.mem_iff pp] using hs'
      funext fun co' : Set.Pairwise {x | x in l'} (Coprime on s) =>
      have co : Set.Pairwise {x | x in l} (Coprime on s) := by simpa [List.Perm.mem_iff pp] using co'
      have lco : l.Pairwise (Coprime on s) := List.Nodup.pairwise_of_forall_ne nod co
      have : forall {m' e nod'' hs'' co''}, @Eq.ndrec (Multiset ι) l
        (fun m => m.Nodup -> (forall i in m, s i != 0) ->
          Set.Pairwise {x | x in m} (Coprime on s) -> { k // forall i in m, k ≡ a i [MOD s i] })
        (fun nod _ co => chineseRemainderOfList a s l (List.Nodup.pairwise_of_forall_ne nod co))
          m' e nod'' hs'' co'' =
        (chineseRemainderOfList a s l lco : Nat) := by
          rintro _ rfl _ _ _; rfl
by ext; exact this.trans chineseRemainderOfList_perm a s pp hs lco)

/--
theorem `chineseRemainderOfMultiset_lt_prod` / 定理 `chineseRemainderOfMultiset_lt_prod`

English:
theorem chineseRemainderOfMultiset_lt_prod
  statement: {m : Multiset ι}
  proof: by
  induction m using Quot.ind with | _ l
  unfold chineseRemainderOfMultiset
  simpa using! chineseRemainderOfList_lt_prod a s l
    (List.Nodup.pairwise_of_forall_ne nod pp) (by simpa using! hs)

中文:
定理 chineseRemainderOfMultiset_lt_prod
  结论: {m : Multiset ι}
  证明: by
  induction m using Quot.ind with | _ l
  unfold chineseRemainderOfMultiset
  simpa using! chineseRemainderOfList_lt_prod a s l
    (List.Nodup.pairwise_of_forall_ne nod pp) (by simpa using! hs)

Depends on / 依赖: List.Nodup.pairwise_of_forall_ne, Quot.ind, chineseRemainderOfList_lt_prod, chineseRemainderOfMultiset, pairwise_of_forall_ne
-/
theorem chineseRemainderOfMultiset_lt_prod {m : Multiset ι}
    (nod : m.Nodup) (hs : forall i in m, s i != 0) (pp : Set.Pairwise {x | x in m} (Coprime on s)) :
    chineseRemainderOfMultiset a s nod hs pp < (m.map s).prod := by
  induction m using Quot.ind with | _ l
  unfold chineseRemainderOfMultiset
  simpa using! chineseRemainderOfList_lt_prod a s l
    (List.Nodup.pairwise_of_forall_ne nod pp) (by simpa using! hs)

/--
Definition of `chineseRemainderOfFinset` / `chineseRemainderOfFinset` 的定义

English:
definition chineseRemainderOfFinset
  signature: (t : Finset ι)
  body: by
  simpa using chineseRemainderOfMultiset a s t.nodup (by simpa using hs) (by simpa using pp)

中文:
定义 chineseRemainderOfFinset
  签名: (t : 有限集 ι)
  定义体: by
  simpa using chineseRemainderOfMultiset a s t.nodup (by simpa using hs) (by simpa using pp)

Depends on / 依赖: chineseRemainderOfMultiset, t.nodup
-/
def chineseRemainderOfFinset (t : Finset ι)
    (hs : forall i in t, s i != 0) (pp : Set.Pairwise t (Coprime on s)) :
    { k // forall i in t, k ≡ a i [MOD s i] } := by
  simpa using chineseRemainderOfMultiset a s t.nodup (by simpa using hs) (by simpa using pp)

/--
theorem `chineseRemainderOfFinset_lt_prod` / 定理 `chineseRemainderOfFinset_lt_prod`

English:
theorem chineseRemainderOfFinset_lt_prod
  statement: {t : Finset ι}
  proof: by
  simpa [chineseRemainderOfFinset] using
    chineseRemainderOfMultiset_lt_prod a s t.nodup (by simpa using hs) (by simpa using pp)

中文:
定理 chineseRemainderOfFinset_lt_prod
  结论: {t : 有限集 ι}
  证明: by
  simpa [chineseRemainderOfFinset] using
    chineseRemainderOfMultiset_lt_prod a s t.nodup (by simpa using hs) (by simpa using pp)

Depends on / 依赖: chineseRemainderOfFinset, chineseRemainderOfMultiset_lt_prod, t.nodup
-/
theorem chineseRemainderOfFinset_lt_prod {t : Finset ι}
    (hs : forall i in t, s i != 0) (pp : Set.Pairwise t (Coprime on s)) :
    chineseRemainderOfFinset a s t hs pp < ∏ i in t, s i := by
  simpa [chineseRemainderOfFinset] using
    chineseRemainderOfMultiset_lt_prod a s t.nodup (by simpa using hs) (by simpa using pp)

end Nat
