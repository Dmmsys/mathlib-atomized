/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn,
Mario Carneiro
-/
module

public import Mathlib.Data.List.Defs
public import Mathlib.Logic.Basic

/-! # getD and getI

This file provides theorems for working with the `getD` and `getI` functions. These are used to
access an element of a list by numerical index, with a default value as a fallback when the index
is out of range.
-/

@[expose] public section

assert_not_imported Mathlib.Algebra.Order.Group.Nat

namespace List

universe u v

variable {α : Type u} {β : Type v} (l : List α) (x : α) (xs : List α) (n : Nat)

section getD

variable (d : α)

/--
theorem `getD_eq_getElem` / 定理 `getD_eq_getElem`

English:
theorem getD_eq_getElem
  given: {n : Nat} (hn : n < l.length)
  statement: l.getD n d = l[n]
  proof: by
  grind

中文:
定理 getD_eq_getElem
  条件: {n : 自然数} (hn : n < l.length)
  结论: l.getD n d = l[n]
  证明: by
  grind
-/
theorem getD_eq_getElem {n : Nat} (hn : n < l.length) : l.getD n d = l[n] := by
  grind

/--
theorem `getD_eq_getElem?` / 定理 `getD_eq_getElem?`

English:
theorem getD_eq_getElem?
  given: (i : Fin l.length)
  statement: l.getD i d = l[i]?.get (by simp)
  proof: by
  simp only [getD_eq_getElem?_getD, Fin.is_lt, getElem?_pos, Option.getD_some, Fin.getElem_fin,
    Option.get_some]

中文:
定理 getD_eq_getElem?
  条件: (i : Fin l.length)
  结论: l.getD i d = l[i]?.get (by simp)
  证明: by
  simp only [getD_eq_getElem?_getD, Fin.is_lt, getElem?_pos, Option.getD_some, Fin.getElem_fin,
    Option.get_some]
-/
theorem getD_eq_getElem? (i : Fin l.length) : l.getD i d = l[i]?.get (by simp) := by
  simp only [getD_eq_getElem?_getD, Fin.is_lt, getElem?_pos, Option.getD_some, Fin.getElem_fin,
    Option.get_some]

/--
theorem `getD_eq_get` / 定理 `getD_eq_get`

English:
theorem getD_eq_get
  given: (i : Fin l.length)
  statement: l.getD i d = l.get i
  proof: getD_eq_getElem ..

中文:
定理 getD_eq_get
  条件: (i : Fin l.length)
  结论: l.getD i d = l.get i
  证明: getD_eq_getElem ..

Depends on / 依赖: getD_eq_getElem
-/
theorem getD_eq_get (i : Fin l.length) : l.getD i d = l.get i :=
  getD_eq_getElem ..

/--
theorem `getD_map` / 定理 `getD_map`

English:
theorem getD_map
  given: {n : Nat} (f : α -> β)
  statement: (map f l).getD n (f d) = f (l.getD n d)
  proof: by
  simp only [getD_eq_getElem?_getD, getElem?_map, Option.getD_map]

中文:
定理 getD_map
  条件: {n : 自然数} (f : α -> β)
  结论: (map f l).getD n (f d) = f (l.getD n d)
  证明: by
  simp only [getD_eq_getElem?_getD, getElem?_map, Option.getD_map]

Depends on / 依赖: Option.getD_map, _getD, _map, getD_eq_getElem, getD_map, getElem
-/
theorem getD_map {n : Nat} (f : α -> β) : (map f l).getD n (f d) = f (l.getD n d) := by
  simp only [getD_eq_getElem?_getD, getElem?_map, Option.getD_map]

/--
theorem `getD_eq_default` / 定理 `getD_eq_default`

English:
theorem getD_eq_default
  given: {n : Nat} (hn : l.length <= n)
  statement: l.getD n d = d
  proof: by
  grind

中文:
定理 getD_eq_default
  条件: {n : 自然数} (hn : l.length <= n)
  结论: l.getD n d = d
  证明: by
  grind
-/
theorem getD_eq_default {n : Nat} (hn : l.length <= n) : l.getD n d = d := by
  grind

/--
theorem `getD_reverse` / 定理 `getD_reverse`

English:
theorem getD_reverse
  given: {l : List α} (i) (h : i < length l)
  proof: by
  grind

中文:
定理 getD_reverse
  条件: {l : List α} (i) (h : i < length l)
  证明: by
  grind
-/
theorem getD_reverse {l : List α} (i) (h : i < length l) :
    getD l.reverse i = getD l (l.length - 1 - i) := by
  grind

/-- An empty list can always be decidably checked for the presence of an element.
Not an instance because it would clash with `DecidableEq α`. -/
@[instance_reducible]
/--
Definition of `decidableGetDNilNe` / `decidableGetDNilNe` 的定义

English:
definition decidableGetDNilNe
  signature: (a : α)
  body: fun _ => isFalse fun H => H getD_nil

@[simp]

中文:
定义 decidableGetDNilNe
  签名: (a : α)
  定义体: fun _ => isFalse fun H => H getD_nil

@[simp]

Depends on / 依赖: getD_nil, isFalse
-/
def decidableGetDNilNe (a : α) : DecidablePred fun i : Nat => getD ([] : List α) i a != a :=
  fun _ => isFalse fun H => H getD_nil

@[simp]
/--
theorem `getElem?_getD_singleton_default_eq` / 定理 `getElem?_getD_singleton_default_eq`

English:
theorem getElem?_getD_singleton_default_eq
  given: (n : Nat)
  statement: [d][n]?.getD d = d
  proof: by
  grind

@[simp]

中文:
定理 getElem?_getD_singleton_default_eq
  条件: (n : 自然数)
  结论: [d][n]?.getD d = d
  证明: by
  grind

@[simp]
-/
theorem getElem?_getD_singleton_default_eq (n : Nat) : [d][n]?.getD d = d := by
  grind

@[simp]
/--
theorem `getElem?_getD_replicate_default_eq` / 定理 `getElem?_getD_replicate_default_eq`

English:
theorem getElem?_getD_replicate_default_eq
  given: (r n : Nat)
  statement: (replicate r d)[n]?.getD d = d
  proof: by
  grind

中文:
定理 getElem?_getD_replicate_default_eq
  条件: (r n : 自然数)
  结论: (replicate r d)[n]?.getD d = d
  证明: by
  grind
-/
theorem getElem?_getD_replicate_default_eq (r n : Nat) : (replicate r d)[n]?.getD d = d := by
  grind

/--
theorem `getD_replicate` / 定理 `getD_replicate`

English:
theorem getD_replicate
  given: {y i n} (h : i < n)
  statement: getD (replicate n x) i y = x
  proof: by
  grind

中文:
定理 getD_replicate
  条件: {y i n} (h : i < n)
  结论: getD (replicate n x) i y = x
  证明: by
  grind
-/
theorem getD_replicate {y i n} (h : i < n) : getD (replicate n x) i y = x := by
  grind

/--
theorem `getD_append` / 定理 `getD_append`

English:
theorem getD_append
  given: (l l' : List α) (d : α) (n : Nat) (h : n < l.length)
  proof: by
  grind

中文:
定理 getD_append
  条件: (l l' : List α) (d : α) (n : 自然数) (h : n < l.length)
  证明: by
  grind
-/
theorem getD_append (l l' : List α) (d : α) (n : Nat) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  grind

/--
theorem `getD_append_right` / 定理 `getD_append_right`

English:
theorem getD_append_right
  given: (l l' : List α) (d : α) (n : Nat) (h : l.length <= n)
  proof: by
  grind

中文:
定理 getD_append_right
  条件: (l l' : List α) (d : α) (n : 自然数) (h : l.length <= n)
  证明: by
  grind
-/
theorem getD_append_right (l l' : List α) (d : α) (n : Nat) (h : l.length <= n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  grind

/--
theorem `getD_surjective_iff` / 定理 `getD_surjective_iff`

English:
theorem getD_surjective_iff
  given: {l : List α} {d : α}
  proof: by
  apply forall_congr'
  have : exists x, l.length <= x := ⟨_, Nat.le_refl _⟩
  simp only [getD_eq_getElem?_getD, getD_getElem?, dite_eq_iff, Nat.not_lt, exists_prop, exists_or,
    exists_and_right, this, mem_iff_getElem?, getElem?_eq_some_iff]
  grind

中文:
定理 getD_surjective_iff
  条件: {l : List α} {d : α}
  证明: by
  apply forall_congr'
  have : exists x, l.length <= x := ⟨_, Nat.le_refl _⟩
  simp only [getD_eq_getElem?_getD, getD_getElem?, dite_eq_iff, Nat.not_lt, exists_prop, exists_or,
    exists_and_right, this, mem_iff_getElem?, getElem?_eq_some_iff]
  grind

Depends on / 依赖: Nat.le_refl, Nat.not_lt, _eq_some_iff, _getD, dite_eq_iff, exists_and_right, exists_or, exists_prop, forall_congr, getD_eq_getElem, getD_getElem, getElem, l.length, le_refl, length, mem_iff_getElem, not_lt
-/
theorem getD_surjective_iff {l : List α} {d : α} :
    (l.getD · d).Surjective ↔ (forall x, x = d ∨ x in l) := by
  apply forall_congr'
  have : exists x, l.length <= x := ⟨_, Nat.le_refl _⟩
  simp only [getD_eq_getElem?_getD, getD_getElem?, dite_eq_iff, Nat.not_lt, exists_prop, exists_or,
    exists_and_right, this, mem_iff_getElem?, getElem?_eq_some_iff]
  grind

/--
theorem `getD_surjective` / 定理 `getD_surjective`

English:
theorem getD_surjective
  given: {l : List α} (h : forall x, x in l) (d : α)
  statement: (l.getD · d).Surjective
  proof: getD_surjective_iff.mpr fun _ => .inr h _

中文:
定理 getD_surjective
  条件: {l : List α} (h : 对任意 x, x in l) (d : α)
  结论: (l.getD · d).Surjective
  证明: getD_surjective_iff.mpr fun _ => .inr h _

Depends on / 依赖: getD_surjective_iff, getD_surjective_iff.mpr
-/
theorem getD_surjective {l : List α} (h : forall x, x in l) (d : α) : (l.getD · d).Surjective :=
getD_surjective_iff.mpr fun _ => .inr h _

end getD

section getI

variable [Inhabited α]

@[simp]
/--
theorem `getI_nil` / 定理 `getI_nil`

English:
theorem getI_nil
  statement: getI ([] : List α) n = default
  proof: rfl

@[simp]

中文:
定理 getI_nil
  结论: getI ([] : List α) n = default
  证明: rfl

@[simp]
-/
theorem getI_nil : getI ([] : List α) n = default :=
  rfl

@[simp]
/--
theorem `getI_cons_zero` / 定理 `getI_cons_zero`

English:
theorem getI_cons_zero
  statement: getI (x :: xs) 0 = x
  proof: rfl

@[simp]

中文:
定理 getI_cons_zero
  结论: getI (x :: xs) 0 = x
  证明: rfl

@[simp]
-/
theorem getI_cons_zero : getI (x :: xs) 0 = x :=
  rfl

@[simp]
/--
theorem `getI_cons_succ` / 定理 `getI_cons_succ`

English:
theorem getI_cons_succ
  statement: getI (x :: xs) (n + 1) = getI xs n
  proof: rfl

中文:
定理 getI_cons_succ
  结论: getI (x :: xs) (n + 1) = getI xs n
  证明: rfl
-/
theorem getI_cons_succ : getI (x :: xs) (n + 1) = getI xs n :=
  rfl

/--
theorem `getI_eq_getElem` / 定理 `getI_eq_getElem`

English:
theorem getI_eq_getElem
  given: {n : Nat} (hn : n < l.length)
  statement: l.getI n = l[n]
  proof: getD_eq_getElem l default hn

中文:
定理 getI_eq_getElem
  条件: {n : 自然数} (hn : n < l.length)
  结论: l.getI n = l[n]
  证明: getD_eq_getElem l default hn

Depends on / 依赖: getD_eq_getElem
-/
theorem getI_eq_getElem {n : Nat} (hn : n < l.length) : l.getI n = l[n] :=
  getD_eq_getElem l default hn

/--
theorem `getI_eq_default` / 定理 `getI_eq_default`

English:
theorem getI_eq_default
  given: {n : Nat} (hn : l.length <= n)
  statement: l.getI n = default
  proof: getD_eq_default _ _ hn

中文:
定理 getI_eq_default
  条件: {n : 自然数} (hn : l.length <= n)
  结论: l.getI n = default
  证明: getD_eq_default _ _ hn

Depends on / 依赖: getD_eq_default
-/
theorem getI_eq_default {n : Nat} (hn : l.length <= n) : l.getI n = default :=
  getD_eq_default _ _ hn

/--
theorem `getD_default_eq_getI` / 定理 `getD_default_eq_getI`

English:
theorem getD_default_eq_getI
  given: {n : Nat}
  statement: l.getD n default = l.getI n
  proof: rfl

中文:
定理 getD_default_eq_getI
  条件: {n : 自然数}
  结论: l.getD n default = l.getI n
  证明: rfl
-/
theorem getD_default_eq_getI {n : Nat} : l.getD n default = l.getI n :=
  rfl

/--
theorem `getI_append` / 定理 `getI_append`

English:
theorem getI_append
  given: (l l' : List α) (n : Nat) (h : n < l.length)
  proof: getD_append _ _ _ _ h

中文:
定理 getI_append
  条件: (l l' : List α) (n : 自然数) (h : n < l.length)
  证明: getD_append _ _ _ _ h

Depends on / 依赖: getD_append
-/
theorem getI_append (l l' : List α) (n : Nat) (h : n < l.length) :
    (l ++ l').getI n = l.getI n := getD_append _ _ _ _ h

/--
theorem `getI_append_right` / 定理 `getI_append_right`

English:
theorem getI_append_right
  given: (l l' : List α) (n : Nat) (h : l.length <= n)
  proof: getD_append_right _ _ _ _ h

中文:
定理 getI_append_right
  条件: (l l' : List α) (n : 自然数) (h : l.length <= n)
  证明: getD_append_right _ _ _ _ h

Depends on / 依赖: getD_append_right
-/
theorem getI_append_right (l l' : List α) (n : Nat) (h : l.length <= n) :
    (l ++ l').getI n = l'.getI (n - l.length) :=
  getD_append_right _ _ _ _ h

/--
theorem `getI_eq_getElem?_getD` / 定理 `getI_eq_getElem?_getD`

English:
theorem getI_eq_getElem?_getD
  given: (n : Nat)
  statement: l.getI n = (l[n]?).getD default
  proof: by
  rw [← getD_default_eq_getI]; rw [getD_eq_getElem?_getD]

@[deprecated getI_eq_getElem?_getD (since := "2026-01-05")]

中文:
定理 getI_eq_getElem?_getD
  条件: (n : 自然数)
  结论: l.getI n = (l[n]?).getD default
  证明: by
  rw [← getD_default_eq_getI]; rw [getD_eq_getElem?_getD]

@[deprecated getI_eq_getElem?_getD (since := "2026-01-05")]
-/
theorem getI_eq_getElem?_getD (n : Nat) : l.getI n = (l[n]?).getD default := by
  rw [← getD_default_eq_getI]; rw [getD_eq_getElem?_getD]

@[deprecated getI_eq_getElem?_getD (since := "2026-01-05")]
/--
theorem `getI_eq_iget_getElem?` / 定理 `getI_eq_iget_getElem?`

English:
theorem getI_eq_iget_getElem?
  given: (n : Nat)
  statement: l.getI n = l[n]?.getD default
  proof: getI_eq_getElem?_getD (l := l) n

中文:
定理 getI_eq_iget_getElem?
  条件: (n : 自然数)
  结论: l.getI n = l[n]?.getD default
  证明: getI_eq_getElem?_getD (l := l) n

Depends on / 依赖: _getD, getI_eq_getElem
-/
theorem getI_eq_iget_getElem? (n : Nat) : l.getI n = l[n]?.getD default :=
  getI_eq_getElem?_getD (l := l) n

/--
theorem `getI_zero_eq_headI` / 定理 `getI_zero_eq_headI`

English:
theorem getI_zero_eq_headI
  statement: l.getI 0 = l.headI
  proof: by cases l <;> rfl

中文:
定理 getI_zero_eq_headI
  结论: l.getI 0 = l.headI
  证明: by cases l <;> rfl
-/
theorem getI_zero_eq_headI : l.getI 0 = l.headI := by cases l <;> rfl

end getI

end List
