/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Data.Rel

/-!
# Uniform separation

This file defines a notion of separation of a set relative to a relation.

For a relation `R`, an `R`-separated set `s` is a set such that every pair of elements of `s` is
`R`-unrelated.

The concept of uniformly separated sets is used to define two further notions of separation:
* Metric separation: `Metric.IsSeparated`, defined using the small distance relation.
* Dynamical nets: `Dynamics.IsDynNetIn`, defined using the dynamical relation.

## TODO

* Actually use `SetRel.IsSeparated` to define the above two notions.
* Link to the notion of separation given by pairwise disjoint balls.
-/

@[expose] public section

open Set

namespace SetRel
variable {X : Type*} {R S : SetRel X X} {s t : Set X} {x : X}

/--
Definition of `IsSeparated` / `IsSeparated` 的定义

English:
definition IsSeparated
  signature: (R : SetRel X X) (s : Set X)
  body: s.Pairwise fun x y => ¬ x ~[R] y

中文:
定义 是分离
  签名: (R : SetRel X X) (s : 集合 X)
  定义体: s.Pairwise fun x y => ¬ x ~[R] y

Depends on / 依赖: Pairwise, s.Pairwise
-/
def IsSeparated (R : SetRel X X) (s : Set X) : Prop := s.Pairwise fun x y => ¬ x ~[R] y

/--
lemma `IsSeparated.empty` / 引理 `IsSeparated.empty`

English:
lemma IsSeparated.empty
  statement: IsSeparated R (∅ : Set X)
  proof: pairwise_empty _

中文:
引理 是分离.empty
  结论: 是分离 R (∅ : 集合 X)
  证明: pairwise_empty _
-/
protected lemma IsSeparated.empty : IsSeparated R (∅ : Set X) := pairwise_empty _
/--
lemma `IsSeparated.singleton` / 引理 `IsSeparated.singleton`

English:
lemma IsSeparated.singleton
  statement: IsSeparated R {x}
  proof: pairwise_singleton ..

中文:
引理 是分离.singleton
  结论: 是分离 R {x}
  证明: pairwise_singleton ..
-/
protected lemma IsSeparated.singleton : IsSeparated R {x} := pairwise_singleton ..

/--
lemma `IsSeparated.of_subsingleton` / 引理 `IsSeparated.of_subsingleton`

English:
lemma IsSeparated.of_subsingleton
  given: (hs : s.Subsingleton)
  statement: IsSeparated R s
  proof: hs.pairwise _

alias _root_.Set.Subsingleton.relIsSeparated := IsSeparated.of_subsingleton

nonrec lemma IsSeparated.mono_left (hUV : R subseteq S) (hs : IsSeparated S s) : IsSeparated R s :=
hs.mono' fun _x _y hxy h => hxy hUV h

中文:
引理 是分离.of_subsingleton
  条件: (hs : s.子单例)
  结论: 是分离 R s
  证明: hs.pairwise _

alias _root_.Set.Subsingleton.relIsSeparated := IsSeparated.of_subsingleton

nonrec lemma IsSeparated.mono_left (hUV : R subseteq S) (hs : IsSeparated S s) : IsSeparated R s :=
hs.mono' fun _x _y hxy h => hxy hUV h
-/
@[simp] lemma IsSeparated.of_subsingleton (hs : s.Subsingleton) : IsSeparated R s := hs.pairwise _

alias _root_.Set.Subsingleton.relIsSeparated := IsSeparated.of_subsingleton

nonrec lemma IsSeparated.mono_left (hUV : R subseteq S) (hs : IsSeparated S s) : IsSeparated R s :=
hs.mono' fun _x _y hxy h => hxy hUV h

/--
lemma `IsSeparated.mono_right` / 引理 `IsSeparated.mono_right`

English:
lemma IsSeparated.mono_right
  given: (hst : s subseteq t) (ht : IsSeparated R t)
  statement: IsSeparated R s
  proof: ht.mono hst

中文:
引理 是分离.mono_right
  条件: (hst : s subseteq t) (ht : 是分离 R t)
  结论: 是分离 R s
  证明: ht.mono hst

Depends on / 依赖: ht.mono
-/
lemma IsSeparated.mono_right (hst : s subseteq t) (ht : IsSeparated R t) : IsSeparated R s := ht.mono hst

/--
lemma `isSeparated_insert'` / 引理 `isSeparated_insert'`

English:
lemma isSeparated_insert'
  proof: by
  simp [IsSeparated, pairwise_insert, not_imp_comm (a := _ = _), -not_and, forall_and]

中文:
引理 isSeparated_insert'
  证明: by
  simp [IsSeparated, pairwise_insert, not_imp_comm (a := _ = _), -not_and, forall_and]

Depends on / 依赖: IsSeparated, forall_and, not_and, not_imp_comm, pairwise_insert
-/
lemma isSeparated_insert' :
    IsSeparated R (insert x s) ↔ IsSeparated R s ∧ (forall y in s, x ~[R] y -> x = y) ∧
        forall y in s, y ~[R] x -> x = y := by
  simp [IsSeparated, pairwise_insert, not_imp_comm (a := _ = _), -not_and, forall_and]

/--
lemma `isSeparated_insert` / 引理 `isSeparated_insert`

English:
lemma isSeparated_insert
  given: [R.IsSymm]
  proof: by
  have : Std.Symm fun x y => ¬(x, y) in R := { symm _ _ := mt R.symm }
  simpa [not_imp_not, IsSeparated] using pairwise_insert_of_symm (r := fun x y => ¬(x, y) in R)

中文:
引理 isSeparated_insert
  条件: [R.是Symm]
  证明: by
  have : Std.Symm fun x y => ¬(x, y) in R := { symm _ _ := mt R.symm }
  simpa [not_imp_not, IsSeparated] using pairwise_insert_of_symm (r := fun x y => ¬(x, y) in R)

Depends on / 依赖: IsSeparated, R.symm, Std.Symm, not_imp_not, pairwise_insert_of_symm
-/
lemma isSeparated_insert [R.IsSymm] :
    IsSeparated R (insert x s) ↔ IsSeparated R s ∧ forall y in s, x ~[R] y -> x = y := by
  have : Std.Symm fun x y => ¬(x, y) in R := { symm _ _ := mt R.symm }
  simpa [not_imp_not, IsSeparated] using pairwise_insert_of_symm (r := fun x y => ¬(x, y) in R)

/--
lemma `isSeparated_insert_of_notMem` / 引理 `isSeparated_insert_of_notMem`

English:
lemma isSeparated_insert_of_notMem
  given: [R.IsSymm] (hx : x ∉ s)
  proof: have : Std.Symm fun x y => ¬(x, y) in R := { symm _ _ := mt R.symm }
  pairwise_insert_of_symm_of_notMem hx

中文:
引理 isSeparated_insert_of_notMem
  条件: [R.是Symm] (hx : x ∉ s)
  证明: have : Std.Symm fun x y => ¬(x, y) in R := { symm _ _ := mt R.symm }
  pairwise_insert_of_symm_of_notMem hx

Depends on / 依赖: R.symm, Std.Symm, pairwise_insert_of_symm_of_notMem
-/
lemma isSeparated_insert_of_notMem [R.IsSymm] (hx : x ∉ s) :
    IsSeparated R (insert x s) ↔ IsSeparated R s ∧ forall y in s, ¬ x ~[R] y :=
  have : Std.Symm fun x y => ¬(x, y) in R := { symm _ _ := mt R.symm }
  pairwise_insert_of_symm_of_notMem hx

/--
lemma `IsSeparated.insert'` / 引理 `IsSeparated.insert'`

English:
lemma IsSeparated.insert'
  statement: (hs : IsSeparated R s) (h : forall y in s, x ~[R] y -> x = y)
  proof: isSeparated_insert'.2 ⟨hs, h, h'⟩

中文:
引理 是分离.insert'
  结论: (hs : 是分离 R s) (h : 对任意 y in s, x ~[R] y -> x = y)
  证明: isSeparated_insert'.2 ⟨hs, h, h'⟩
-/
protected lemma IsSeparated.insert' (hs : IsSeparated R s) (h : forall y in s, x ~[R] y -> x = y)
    (h' : forall y in s, y ~[R] x -> x = y) : IsSeparated R (insert x s) :=
  isSeparated_insert'.2 ⟨hs, h, h'⟩

/--
lemma `IsSeparated.insert` / 引理 `IsSeparated.insert`

English:
lemma IsSeparated.insert
  statement: [R.IsSymm] (hs : IsSeparated R s)
  proof: isSeparated_insert.2 ⟨hs, h⟩

中文:
引理 是分离.insert
  结论: [R.是Symm] (hs : 是分离 R s)
  证明: isSeparated_insert.2 ⟨hs, h⟩
-/
protected lemma IsSeparated.insert [R.IsSymm] (hs : IsSeparated R s)
    (h : forall y in s, x ~[R] y -> x = y) : IsSeparated R (insert x s) :=
  isSeparated_insert.2 ⟨hs, h⟩

end SetRel
