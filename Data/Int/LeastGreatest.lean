/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Bounds.Defs

/-! # Least upper bound and greatest lower bound properties for integers

In this file we prove that a bounded above nonempty set of integers has the greatest element, and a
counterpart of this statement for the least element.

## Main definitions

* `Int.leastOfBdd`: if `P : ℤ → Prop` is a decidable predicate, `b` is a lower bound of the set
  `{m | P m}`, and there exists `m : ℤ` such that `P m` (this time, no witness is required), then
  `Int.leastOfBdd` returns the least number `m` such that `P m`, together with proofs of `P m` and
  of the minimality. This definition is computable and does not rely on the axiom of choice.
* `Int.greatestOfBdd`: a similar definition with all inequalities reversed.

## Main statements

* `Int.exists_least_of_bdd`: if `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is
  bounded below and nonempty, then this set has the least element. This lemma uses classical logic
  to avoid assumption `[DecidablePred P]`. See `Int.leastOfBdd` for a constructive counterpart.

* `Int.coe_leastOfBdd_eq`: `(Int.leastOfBdd b Hb Hinh : ℤ)` does not depend on `b`.

* `Int.exists_greatest_of_bdd`, `Int.coe_greatest_of_bdd_eq`: versions of the above lemmas with all
  inequalities reversed.

## Tags

integer numbers, least element, greatest element
-/

@[expose] public section


namespace Int

/--
Definition of `leastOfBdd` / `leastOfBdd` 的定义

English:
definition leastOfBdd
  signature: {P : Int -> Prop} [DecidablePred P] (b : Int) (Hb : forall z : Int, P z -> b <= z)
  body: have EX : exists n : Nat, P (b + n) :=
    let ⟨elt, Helt⟩ := Hinh
    match elt, le.dest (Hb _ Helt), Helt with
    | _, ⟨n, rfl⟩, Hn => ⟨n, Hn⟩
  ⟨b + (Nat.find EX : Int), Nat.find_spec EX, fun z h => by
    obtain ⟨n, rfl⟩ := le.dest (Hb _ h); grw [Nat.find_min' EX h]⟩

中文:
定义 leastOfBdd
  签名: {P : 整数 -> 命题} [DecidablePred P] (b : 整数) (Hb : 对任意 z : 整数, P z -> b <= z)
  定义体: have EX : exists n : Nat, P (b + n) :=
    let ⟨elt, Helt⟩ := Hinh
    match elt, le.dest (Hb _ Helt), Helt with
    | _, ⟨n, rfl⟩, Hn => ⟨n, Hn⟩
  ⟨b + (Nat.find EX : Int), Nat.find_spec EX, fun z h => by
    obtain ⟨n, rfl⟩ := le.dest (Hb _ h); grw [Nat.find_min' EX h]⟩

Depends on / 依赖: Nat.find, Nat.find_min, Nat.find_spec, find_min, find_spec, le.dest
-/
def leastOfBdd {P : Int -> Prop} [DecidablePred P] (b : Int) (Hb : forall z : Int, P z -> b <= z)
    (Hinh : exists z : Int, P z) : { lb : Int // P lb ∧ forall z : Int, P z -> lb <= z } :=
  have EX : exists n : Nat, P (b + n) :=
    let ⟨elt, Helt⟩ := Hinh
    match elt, le.dest (Hb _ Helt), Helt with
    | _, ⟨n, rfl⟩, Hn => ⟨n, Hn⟩
  ⟨b + (Nat.find EX : Int), Nat.find_spec EX, fun z h => by
    obtain ⟨n, rfl⟩ := le.dest (Hb _ h); grw [Nat.find_min' EX h]⟩

/--
lemma `isLeast_coe_leastOfBdd` / 引理 `isLeast_coe_leastOfBdd`

English:
lemma isLeast_coe_leastOfBdd
  statement: {P : Int -> Prop} [DecidablePred P] (b : Int) (Hb : forall z : Int, P z -> b <= z)
  proof: (leastOfBdd b Hb Hinh).2

中文:
引理 isLeast_coe_leastOfBdd
  结论: {P : 整数 -> 命题} [DecidablePred P] (b : 整数) (Hb : 对任意 z : 整数, P z -> b <= z)
  证明: (leastOfBdd b Hb Hinh).2

Depends on / 依赖: leastOfBdd
-/
lemma isLeast_coe_leastOfBdd {P : Int -> Prop} [DecidablePred P] (b : Int) (Hb : forall z : Int, P z -> b <= z)
    (Hinh : exists z : Int, P z) : IsLeast {z | P z} (leastOfBdd b Hb Hinh : Int) :=
  (leastOfBdd b Hb Hinh).2

/--
theorem `exists_least_of_bdd` / 定理 `exists_least_of_bdd`

English:
theorem exists_least_of_bdd
  proof: by
  classical
  let ⟨b, Hb⟩ := Hbdd
  let ⟨lb, H⟩ := leastOfBdd b Hb Hinh
  exact ⟨lb, H⟩

中文:
定理 存在_least_of_bdd
  证明: by
  classical
  let ⟨b, Hb⟩ := Hbdd
  let ⟨lb, H⟩ := leastOfBdd b Hb Hinh
  exact ⟨lb, H⟩

Depends on / 依赖: classical, leastOfBdd
-/
theorem exists_least_of_bdd
    {P : Int -> Prop}
    (Hbdd : exists b : Int, forall z : Int, P z -> b <= z)
    (Hinh : exists z : Int, P z) : exists lb : Int, P lb ∧ forall z : Int, P z -> lb <= z := by
  classical
  let ⟨b, Hb⟩ := Hbdd
  let ⟨lb, H⟩ := leastOfBdd b Hb Hinh
  exact ⟨lb, H⟩

/--
theorem `coe_leastOfBdd_eq` / 定理 `coe_leastOfBdd_eq`

English:
theorem coe_leastOfBdd_eq
  statement: {P : Int -> Prop} [DecidablePred P] {b b' : Int} (Hb : forall z : Int, P z -> b <= z)
  proof: by grind

中文:
定理 coe_leastOfBdd_eq
  结论: {P : 整数 -> 命题} [DecidablePred P] {b b' : 整数} (Hb : 对任意 z : 整数, P z -> b <= z)
  证明: by grind
-/
theorem coe_leastOfBdd_eq {P : Int -> Prop} [DecidablePred P] {b b' : Int} (Hb : forall z : Int, P z -> b <= z)
    (Hb' : forall z : Int, P z -> b' <= z) (Hinh : exists z : Int, P z) :
    (leastOfBdd b Hb Hinh : Int) = leastOfBdd b' Hb' Hinh := by grind

/--
Definition of `greatestOfBdd` / `greatestOfBdd` 的定义

English:
definition greatestOfBdd
  signature: {P : Int -> Prop} [DecidablePred P] (b : Int) (Hb : forall z : Int, P z -> z <= b)
  body: have Hbdd' : forall z : Int, P (-z) -> -b <= z := fun _ h => neg_le.1 (Hb _ h)
  have Hinh' : exists z : Int, P (-z) :=
    let ⟨elt, Helt⟩ := Hinh
    ⟨-elt, by rw [neg_neg]; exact Helt⟩
  let ⟨lb, Plb, al⟩ := leastOfBdd (-b) Hbdd' Hinh'
⟨-lb, Plb, fun z h => le_neg.1 al _ by rwa [neg_neg]⟩

中文:
定义 greatestOfBdd
  签名: {P : 整数 -> 命题} [DecidablePred P] (b : 整数) (Hb : 对任意 z : 整数, P z -> z <= b)
  定义体: have Hbdd' : forall z : Int, P (-z) -> -b <= z := fun _ h => neg_le.1 (Hb _ h)
  have Hinh' : exists z : Int, P (-z) :=
    let ⟨elt, Helt⟩ := Hinh
    ⟨-elt, by rw [neg_neg]; exact Helt⟩
  let ⟨lb, Plb, al⟩ := leastOfBdd (-b) Hbdd' Hinh'
⟨-lb, Plb, fun z h => le_neg.1 al _ by rwa [neg_neg]⟩

Depends on / 依赖: le_neg, leastOfBdd, neg_le, neg_neg
-/
def greatestOfBdd {P : Int -> Prop} [DecidablePred P] (b : Int) (Hb : forall z : Int, P z -> z <= b)
    (Hinh : exists z : Int, P z) : { ub : Int // P ub ∧ forall z : Int, P z -> z <= ub } :=
  have Hbdd' : forall z : Int, P (-z) -> -b <= z := fun _ h => neg_le.1 (Hb _ h)
  have Hinh' : exists z : Int, P (-z) :=
    let ⟨elt, Helt⟩ := Hinh
    ⟨-elt, by rw [neg_neg]; exact Helt⟩
  let ⟨lb, Plb, al⟩ := leastOfBdd (-b) Hbdd' Hinh'
⟨-lb, Plb, fun z h => le_neg.1 al _ by rwa [neg_neg]⟩

/--
lemma `isGreatest_coe_greatestOfBdd` / 引理 `isGreatest_coe_greatestOfBdd`

English:
lemma isGreatest_coe_greatestOfBdd
  statement: {P : Int -> Prop} [DecidablePred P] (b : Int)
  proof: (greatestOfBdd b Hb Hinh).2

中文:
引理 isGreatest_coe_greatestOfBdd
  结论: {P : 整数 -> 命题} [DecidablePred P] (b : 整数)
  证明: (greatestOfBdd b Hb Hinh).2

Depends on / 依赖: greatestOfBdd
-/
lemma isGreatest_coe_greatestOfBdd {P : Int -> Prop} [DecidablePred P] (b : Int)
    (Hb : forall z : Int, P z -> z <= b) (Hinh : exists z : Int, P z) :
    IsGreatest {z | P z} (greatestOfBdd b Hb Hinh : Int) :=
  (greatestOfBdd b Hb Hinh).2

/--
theorem `exists_greatest_of_bdd` / 定理 `exists_greatest_of_bdd`

English:
theorem exists_greatest_of_bdd
  proof: by
  classical
  let ⟨b, Hb⟩ := Hbdd
  let ⟨lb, H⟩ := greatestOfBdd b Hb Hinh
  exact ⟨lb, H⟩

中文:
定理 存在_greatest_of_bdd
  证明: by
  classical
  let ⟨b, Hb⟩ := Hbdd
  let ⟨lb, H⟩ := greatestOfBdd b Hb Hinh
  exact ⟨lb, H⟩

Depends on / 依赖: classical, greatestOfBdd
-/
theorem exists_greatest_of_bdd
    {P : Int -> Prop}
    (Hbdd : exists b : Int, forall z : Int, P z -> z <= b)
    (Hinh : exists z : Int, P z) : exists ub : Int, P ub ∧ forall z : Int, P z -> z <= ub := by
  classical
  let ⟨b, Hb⟩ := Hbdd
  let ⟨lb, H⟩ := greatestOfBdd b Hb Hinh
  exact ⟨lb, H⟩

/--
theorem `coe_greatestOfBdd_eq` / 定理 `coe_greatestOfBdd_eq`

English:
theorem coe_greatestOfBdd_eq
  statement: {P : Int -> Prop} [DecidablePred P] {b b' : Int}
  proof: by grind

中文:
定理 coe_greatestOfBdd_eq
  结论: {P : 整数 -> 命题} [DecidablePred P] {b b' : 整数}
  证明: by grind
-/
theorem coe_greatestOfBdd_eq {P : Int -> Prop} [DecidablePred P] {b b' : Int}
    (Hb : forall z : Int, P z -> z <= b) (Hb' : forall z : Int, P z -> z <= b') (Hinh : exists z : Int, P z) :
    (greatestOfBdd b Hb Hinh : Int) = greatestOfBdd b' Hb' Hinh := by grind

end Int
