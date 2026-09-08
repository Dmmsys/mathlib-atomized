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

/-- A computable version of `exists_least_of_bdd`: given a decidable predicate on the
integers, with an explicit lower bound and a proof that it is somewhere true, return
the least value for which the predicate is true. -/
/-
**Int.leastOfBdd** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：leastOfBdd {P : Int -> Prop} [DecidablePred P] (b : Int) (Hb : forall z : 
Int, P z -> b <= z) (Hinh : exists z : Int, P z) : { lb : Int // P lb ∧ forall z
 : Int, P z -> lb <= z }
参数：b : Int；Hb : forall z : Int, P z -> b <= z；Hinh : exists z : Int, P z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A computable version of `exists_least_of_bdd`: given a decidable predicate on th
e
integers, with an explicit lower bound and a proof that it is somewhere true, re
turn
the least value for which the predicate is true.
-/
def leastOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ) (Hb : ∀ z : ℤ, P z → b ≤ z)
    (Hinh : ∃ z : ℤ, P z) : { lb : ℤ // P lb ∧ ∀ z : ℤ, P z → lb ≤ z } :=
  have EX : ∃ n : ℕ, P (b + n) :=
    let ⟨elt, Helt⟩ := Hinh
    match elt, le.dest (Hb _ Helt), Helt with
    | _, ⟨n, rfl⟩, Hn => ⟨n, Hn⟩
  ⟨b + (Nat.find EX : ℤ), Nat.find_spec EX, fun z h => by
    obtain ⟨n, rfl⟩ := le.dest (Hb _ h); grw [Nat.find_min' EX h]⟩

/-- `Int.leastOfBdd` is the least integer satisfying a predicate which is false for all `z : ℤ` with
`z < b` for some fixed `b : ℤ`. -/
/-
**Int.isLeast_coe_leastOfBdd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：isLeast_coe_leastOfBdd {P : Int -> Prop} [DecidablePred P] (b : Int) (Hb :
 forall z : Int, P z -> b <= z) (Hinh : exists z : Int, P z) : IsLeast {z | P z}
 (leastOfBdd b Hb Hinh : Int)
参数：b : Int；Hb : forall z : Int, P z -> b <= z；Hinh : exists z : Int, P z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
`Int.leastOfBdd` is the least integer satisfying a predicate which is false for 
all `z : ℤ` with
`z < b` for some fixed `b : ℤ`.
-/
lemma isLeast_coe_leastOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ) (Hb : ∀ z : ℤ, P z → b ≤ z)
    (Hinh : ∃ z : ℤ, P z) : IsLeast {z | P z} (leastOfBdd b Hb Hinh : ℤ) :=
  (leastOfBdd b Hb Hinh).2

/--
If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded below and nonempty,
then this set has the least element. This lemma uses classical logic to avoid assumption
`[DecidablePred P]`. See `Int.leastOfBdd` for a constructive counterpart. -/
/-
**Int.exists_least_of_bdd** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：exists_least_of_bdd {P : Int -> Prop} (Hbdd : exists b : Int, forall z : I
nt, P z -> b <= z) (Hinh : exists z : Int, P z) : exists lb : Int, P lb ∧ forall
 z : Int, P z -> lb <= z
参数：Hbdd : exists b : Int, forall z : Int, P z -> b <= z；Hinh : exists z : Int, P
 z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded below 
and nonempty,
then this set has the least element. This lemma uses classical logic to avoid as
sumption
`[DecidablePred P]`. See `Int.leastOfBdd` for a constructive counterpart.
-/
theorem exists_least_of_bdd
    {P : ℤ → Prop}
    (Hbdd : ∃ b : ℤ, ∀ z : ℤ, P z → b ≤ z)
    (Hinh : ∃ z : ℤ, P z) : ∃ lb : ℤ, P lb ∧ ∀ z : ℤ, P z → lb ≤ z := by
  classical
  let ⟨b, Hb⟩ := Hbdd
  let ⟨lb, H⟩ := leastOfBdd b Hb Hinh
  exact ⟨lb, H⟩
/-
**Int.coe_leastOfBdd_eq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：coe_leastOfBdd_eq {P : Int -> Prop} [DecidablePred P] {b b' : Int} (Hb : f
orall z : Int, P z -> b <= z) (Hb' : forall z : Int, P z -> b' <= z) (Hinh : exi
sts z : Int, P z) : (leastOfBdd b Hb Hinh : Int) = leastOfBdd b' Hb' Hinh
参数：Hb : forall z : Int, P z -> b <= z；Hb' : forall z : Int, P z -> b' <= z；Hinh 
: exists z : Int, P z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_leastOfBdd_eq {P : ℤ → Prop} [DecidablePred P] {b b' : ℤ} (Hb : ∀ z : ℤ, P z → b ≤ z)
    (Hb' : ∀ z : ℤ, P z → b' ≤ z) (Hinh : ∃ z : ℤ, P z) :
    (leastOfBdd b Hb Hinh : ℤ) = leastOfBdd b' Hb' Hinh := by grind

/-- A computable version of `exists_greatest_of_bdd`: given a decidable predicate on the
integers, with an explicit upper bound and a proof that it is somewhere true, return
the greatest value for which the predicate is true. -/
/-
**Int.greatestOfBdd** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：greatestOfBdd {P : Int -> Prop} [DecidablePred P] (b : Int) (Hb : forall z
 : Int, P z -> z <= b) (Hinh : exists z : Int, P z) : { ub : Int // P ub ∧ foral
l z : Int, P z -> z <= ub }
参数：b : Int；Hb : forall z : Int, P z -> z <= b；Hinh : exists z : Int, P z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A computable version of `exists_greatest_of_bdd`: given a decidable predicate on
 the
integers, with an explicit upper bound and a proof that it is somewhere true, re
turn
the greatest value for which the predicate is true.
-/
def greatestOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ) (Hb : ∀ z : ℤ, P z → z ≤ b)
    (Hinh : ∃ z : ℤ, P z) : { ub : ℤ // P ub ∧ ∀ z : ℤ, P z → z ≤ ub } :=
  have Hbdd' : ∀ z : ℤ, P (-z) → -b ≤ z := fun _ h => neg_le.1 (Hb _ h)
  have Hinh' : ∃ z : ℤ, P (-z) :=
    let ⟨elt, Helt⟩ := Hinh
    ⟨-elt, by rw [neg_neg]; exact Helt⟩
  let ⟨lb, Plb, al⟩ := leastOfBdd (-b) Hbdd' Hinh'
  ⟨-lb, Plb, fun z h => le_neg.1 <| al _ <| by rwa [neg_neg]⟩

/-- `Int.greatestOfBdd` is the greatest integer satisfying a predicate which is false for all
`z : ℤ` with `b < z` for some fixed `b : ℤ`. -/
/-
**Int.isGreatest_coe_greatestOfBdd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：isGreatest_coe_greatestOfBdd {P : Int -> Prop} [DecidablePred P] (b : Int)
 (Hb : forall z : Int, P z -> z <= b) (Hinh : exists z : Int, P z) : IsGreatest 
{z | P z} (greatestOfBdd b Hb Hinh : Int)
参数：b : Int；Hb : forall z : Int, P z -> z <= b；Hinh : exists z : Int, P z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
`Int.greatestOfBdd` is the greatest integer satisfying a predicate which is fals
e for all
`z : ℤ` with `b < z` for some fixed `b : ℤ`.
-/
lemma isGreatest_coe_greatestOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ)
    (Hb : ∀ z : ℤ, P z → z ≤ b) (Hinh : ∃ z : ℤ, P z) :
    IsGreatest {z | P z} (greatestOfBdd b Hb Hinh : ℤ) :=
  (greatestOfBdd b Hb Hinh).2

/--
If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded above and nonempty,
then this set has the greatest element. This lemma uses classical logic to avoid assumption
`[DecidablePred P]`. See `Int.greatestOfBdd` for a constructive counterpart. -/
/-
**Int.exists_greatest_of_bdd** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：exists_greatest_of_bdd {P : Int -> Prop} (Hbdd : exists b : Int, forall z 
: Int, P z -> z <= b) (Hinh : exists z : Int, P z) : exists ub : Int, P ub ∧ for
all z : Int, P z -> z <= ub
参数：Hbdd : exists b : Int, forall z : Int, P z -> z <= b；Hinh : exists z : Int, P
 z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded above 
and nonempty,
then this set has the greatest element. This lemma uses classical logic to avoid
 assumption
`[DecidablePred P]`. See `Int.greatestOfBdd` for a constructive counterpart.
-/
theorem exists_greatest_of_bdd
    {P : ℤ → Prop}
    (Hbdd : ∃ b : ℤ, ∀ z : ℤ, P z → z ≤ b)
    (Hinh : ∃ z : ℤ, P z) : ∃ ub : ℤ, P ub ∧ ∀ z : ℤ, P z → z ≤ ub := by
  classical
  let ⟨b, Hb⟩ := Hbdd
  let ⟨lb, H⟩ := greatestOfBdd b Hb Hinh
  exact ⟨lb, H⟩
/-
**Int.coe_greatestOfBdd_eq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：coe_greatestOfBdd_eq {P : Int -> Prop} [DecidablePred P] {b b' : Int} (Hb 
: forall z : Int, P z -> z <= b) (Hb' : forall z : Int, P z -> z <= b') (Hinh : 
exists z : Int, P z) : (greatestOfBdd b Hb Hinh : Int) = greatestOfBdd b' Hb' Hi
nh
参数：Hb : forall z : Int, P z -> z <= b；Hb' : forall z : Int, P z -> z <= b'；Hinh 
: exists z : Int, P z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_greatestOfBdd_eq {P : ℤ → Prop} [DecidablePred P] {b b' : ℤ}
    (Hb : ∀ z : ℤ, P z → z ≤ b) (Hb' : ∀ z : ℤ, P z → z ≤ b') (Hinh : ∃ z : ℤ, P z) :
    (greatestOfBdd b Hb Hinh : ℤ) = greatestOfBdd b' Hb' Hinh := by grind

end Int

