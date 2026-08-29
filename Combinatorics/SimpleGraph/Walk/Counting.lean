/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Counting walks of a given length

## Main definitions
- `walkLengthTwoEquivCommonNeighbors`: bijective correspondence between walks of length two
  from `u` to `v` and common neighbours of `u` and `v`. Note that `u` and `v` may be the same.
- `finsetWalkLength`: the `Finset` of length-`n` walks from `u` to `v`.
  This is used to give `{p : G.walk u v | p.length = n}` a `Fintype` instance, and it
  can also be useful as a recursive description of this set when `V` is finite.

TODO: should this be extended further?
-/

@[expose] public section

assert_not_exists Field

open Finset Function

universe u v w

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/--
theorem `Walk.setOfPred_length_eq_zero` / 定理 `Walk.setOfPred_length_eq_zero`

English:
theorem Walk.setOfPred_length_eq_zero
  given: (u : V)
  statement: {p : G.Walk u u | p.length = 0} = {.nil}
  proof: by
  simp [Walk.length_eq_zero_iff, ← Walk.eq_nil_iff_nil]

@[deprecated (since := "2026-07-09")]
alias Walk.setOf_length_eq_zero := Walk.setOfPred_length_eq_zero

@[deprecated (since := "2026-05-12")]
alias set_walk_self_length_zero_eq := Walk.setOfPred_length_eq_zero

中文:
定理 途径.setOfPred_length_eq_zero
  条件: (u : V)
  结论: {p : G.途径 u u | p.length = 0} = {.nil}
  证明: by
  simp [Walk.length_eq_zero_iff, ← Walk.eq_nil_iff_nil]

@[deprecated (since := "2026-07-09")]
alias Walk.setOf_length_eq_zero := Walk.setOfPred_length_eq_zero

@[deprecated (since := "2026-05-12")]
alias set_walk_self_length_zero_eq := Walk.setOfPred_length_eq_zero

Depends on / 依赖: Walk.eq_nil_iff_nil, Walk.length_eq_zero_iff, eq_nil_iff_nil, length_eq_zero_iff
-/
theorem Walk.setOfPred_length_eq_zero (u : V) : {p : G.Walk u u | p.length = 0} = {.nil} := by
  simp [Walk.length_eq_zero_iff, ← Walk.eq_nil_iff_nil]

@[deprecated (since := "2026-07-09")]
alias Walk.setOf_length_eq_zero := Walk.setOfPred_length_eq_zero

@[deprecated (since := "2026-05-12")]
alias set_walk_self_length_zero_eq := Walk.setOfPred_length_eq_zero

/--
theorem `Walk.setOfPred_length_eq_zero_of_ne` / 定理 `Walk.setOfPred_length_eq_zero_of_ne`

English:
theorem Walk.setOfPred_length_eq_zero_of_ne
  given: {u v : V} (h : u != v)
  proof: Set.eq_empty_of_forall_notMem (h <| ·.eq_of_length_eq_zero ·)

@[deprecated (since := "2026-07-09")]
alias Walk.setOf_length_eq_zero_of_ne := Walk.setOfPred_length_eq_zero_of_ne

@[deprecated (since := "2026-05-12")]
alias set_walk_length_zero_eq_of_ne := Walk.setOfPred_length_eq_zero_of_ne

中文:
定理 途径.setOfPred_length_eq_zero_of_ne
  条件: {u v : V} (h : u != v)
  证明: Set.eq_empty_of_forall_notMem (h <| ·.eq_of_length_eq_zero ·)

@[deprecated (since := "2026-07-09")]
alias Walk.setOf_length_eq_zero_of_ne := Walk.setOfPred_length_eq_zero_of_ne

@[deprecated (since := "2026-05-12")]
alias set_walk_length_zero_eq_of_ne := Walk.setOfPred_length_eq_zero_of_ne

Depends on / 依赖: Set.eq_empty_of_forall_notMem, eq_empty_of_forall_notMem, eq_of_length_eq_zero
-/
theorem Walk.setOfPred_length_eq_zero_of_ne {u v : V} (h : u != v) :
    {p : G.Walk u v | p.length = 0} = ∅ :=
  Set.eq_empty_of_forall_notMem (h <| ·.eq_of_length_eq_zero ·)

@[deprecated (since := "2026-07-09")]
alias Walk.setOf_length_eq_zero_of_ne := Walk.setOfPred_length_eq_zero_of_ne

@[deprecated (since := "2026-05-12")]
alias set_walk_length_zero_eq_of_ne := Walk.setOfPred_length_eq_zero_of_ne

/--
theorem `Walk.setOfPred_length_eq_add_one` / 定理 `Walk.setOfPred_length_eq_add_one`

English:
theorem Walk.setOfPred_length_eq_add_one
  given: (u v : V) (n : Nat)
  proof: by
  ext p
  cases p with
  | nil => simp [eq_comm]
  | cons huw pwv => grind [length_cons, Set.mem_iUnion]

@[deprecated (since := "2026-07-09")]
alias Walk.setOf_length_eq_add_one := Walk.setOfPred_length_eq_add_one

@[deprecated (since := "2026-05-12")]
alias set_walk_length_succ_eq := Walk.setOf

中文:
定理 途径.setOfPred_length_eq_add_one
  条件: (u v : V) (n : 自然数)
  证明: by
  ext p
  cases p with
  | nil => simp [eq_comm]
  | cons huw pwv => grind [length_cons, Set.mem_iUnion]

@[deprecated (since := "2026-07-09")]
alias Walk.setOf_length_eq_add_one := Walk.setOfPred_length_eq_add_one

@[deprecated (since := "2026-05-12")]
alias set_walk_length_succ_eq := Walk.setOf

Depends on / 依赖: Set.mem_iUnion, eq_comm, length_cons, mem_iUnion
-/
theorem Walk.setOfPred_length_eq_add_one (u v : V) (n : Nat) :
    {p : G.Walk u v | p.length = n + 1} =
      ⋃ (w : V) (h : G.Adj u w), Walk.cons h '' {p' : G.Walk w v | p'.length = n} := by
  ext p
  cases p with
  | nil => simp [eq_comm]
  | cons huw pwv => grind [length_cons, Set.mem_iUnion]

@[deprecated (since := "2026-07-09")]
alias Walk.setOf_length_eq_add_one := Walk.setOfPred_length_eq_add_one

@[deprecated (since := "2026-05-12")]
alias set_walk_length_succ_eq := Walk.setOfPred_length_eq_add_one

/-- Walks of length two from `u` to `v` correspond bijectively to common neighbours of `u` and `v`.
Note that `u` and `v` may be the same. -/
@[simps]
/--
Definition of `walkLengthTwoEquivCommonNeighbors` / `walkLengthTwoEquivCommonNeighbors` 的定义

English:
definition walkLengthTwoEquivCommonNeighbors
  signature: (u v : V)
  body: ⟨p.val.snd, match p with
    | ⟨.cons _ (.cons _ .nil), _⟩ => ⟨‹G.Adj u _›, ‹G.Adj _ v›.symm⟩⟩
  invFun w := ⟨w.prop.1.toWalk.concat w.prop.2.symm, rfl⟩
  left_inv | ⟨.cons _ (.cons _ .nil), hp⟩ => by rfl

中文:
定义 walkLengthTwoEquivCommonNeighbors
  签名: (u v : V)
  定义体: ⟨p.val.snd, match p with
    | ⟨.cons _ (.cons _ .nil), _⟩ => ⟨‹G.Adj u _›, ‹G.Adj _ v›.symm⟩⟩
  invFun w := ⟨w.prop.1.toWalk.concat w.prop.2.symm, rfl⟩
  left_inv | ⟨.cons _ (.cons _ .nil), hp⟩ => by rfl

Depends on / 依赖: p.val.snd
-/
def walkLengthTwoEquivCommonNeighbors (u v : V) :
    {p : G.Walk u v // p.length = 2} ≃ G.commonNeighbors u v where
  toFun p := ⟨p.val.snd, match p with
    | ⟨.cons _ (.cons _ .nil), _⟩ => ⟨‹G.Adj u _›, ‹G.Adj _ v›.symm⟩⟩
  invFun w := ⟨w.prop.1.toWalk.concat w.prop.2.symm, rfl⟩
  left_inv | ⟨.cons _ (.cons _ .nil), hp⟩ => by rfl

section LocallyFinite

variable [DecidableEq V] [LocallyFinite G]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `finsetWalkLength` / `finsetWalkLength` 的定义

English:
definition finsetWalkLength
  signature: (n : Nat) (u v : V)
  body: match n with
  | 0 =>
    if h : u = v then by
      subst u
      exact {Walk.nil}
    else ∅
  | n + 1 =>
    Finset.univ.biUnion fun (w : G.neighborSet u) =>
      (finsetWalkLength n w v).map ⟨fun p => Walk.cons w.property p, fun _ _ => by simp⟩

中文:
定义 finsetWalkLength
  签名: (n : 自然数) (u v : V)
  定义体: match n with
  | 0 =>
    if h : u = v then by
      subst u
      exact {Walk.nil}
    else ∅
  | n + 1 =>
    Finset.univ.biUnion fun (w : G.neighborSet u) =>
      (finsetWalkLength n w v).map ⟨fun p => Walk.cons w.property p, fun _ _ => by simp⟩

Depends on / 依赖: Finset, Finset.univ.biUnion, G.neighborSet, Walk.cons, Walk.nil, biUnion, finsetWalkLength, neighborSet, property, w.property
-/
def finsetWalkLength (n : Nat) (u v : V) : Finset (G.Walk u v) :=
  match n with
  | 0 =>
    if h : u = v then by
      subst u
      exact {Walk.nil}
    else ∅
  | n + 1 =>
    Finset.univ.biUnion fun (w : G.neighborSet u) =>
      (finsetWalkLength n w v).map ⟨fun p => Walk.cons w.property p, fun _ _ => by simp⟩

/--
theorem `coe_finsetWalkLength_eq` / 定理 `coe_finsetWalkLength_eq`

English:
theorem coe_finsetWalkLength_eq
  given: (n : Nat) (u v : V)
  proof: by
  induction n generalizing u v with
  | zero => grind [finsetWalkLength, Walk.eq_nil_iff_nil]
  | succ n ih =>
    simp only [finsetWalkLength, Walk.setOfPred_length_eq_add_one, Finset.coe_biUnion,
      Finset.mem_coe, Finset.mem_univ, Set.iUnion_true, Finset.coe_map, Set.iUnion_coe_set]
    con

中文:
定理 coe_finsetWalkLength_eq
  条件: (n : 自然数) (u v : V)
  证明: by
  induction n generalizing u v with
  | zero => grind [finsetWalkLength, Walk.eq_nil_iff_nil]
  | succ n ih =>
    simp only [finsetWalkLength, Walk.setOfPred_length_eq_add_one, Finset.coe_biUnion,
      Finset.mem_coe, Finset.mem_univ, Set.iUnion_true, Finset.coe_map, Set.iUnion_coe_set]
    con

Depends on / 依赖: Finset, Finset.coe_biUnion, Finset.coe_map, Finset.mem_coe, Finset.mem_univ, Set.iUnion_coe_set, Set.iUnion_true, Walk.eq_nil_iff_nil, Walk.setOfPred_length_eq_add_one, coe_biUnion, coe_map, eq_nil_iff_nil, finsetWalkLength, generalizing, iUnion_coe_set, iUnion_true, mem_coe, mem_univ, setOfPred_length_eq_add_one
-/
theorem coe_finsetWalkLength_eq (n : Nat) (u v : V) :
    (G.finsetWalkLength n u v : Set (G.Walk u v)) = {p : G.Walk u v | p.length = n} := by
  induction n generalizing u v with
  | zero => grind [finsetWalkLength, Walk.eq_nil_iff_nil]
  | succ n ih =>
    simp only [finsetWalkLength, Walk.setOfPred_length_eq_add_one, Finset.coe_biUnion,
      Finset.mem_coe, Finset.mem_univ, Set.iUnion_true, Finset.coe_map, Set.iUnion_coe_set]
    congr!
    grind

variable {G} in
/--
theorem `mem_finsetWalkLength_iff` / 定理 `mem_finsetWalkLength_iff`

English:
theorem mem_finsetWalkLength_iff
  given: {n : Nat} {u v : V} {p : G.Walk u v}
  proof: Set.ext_iff.mp (G.coe_finsetWalkLength_eq n u v) p

中文:
定理 mem_finsetWalkLength_iff
  条件: {n : 自然数} {u v : V} {p : G.途径 u v}
  证明: Set.ext_iff.mp (G.coe_finsetWalkLength_eq n u v) p

Depends on / 依赖: G.coe_finsetWalkLength_eq, Set.ext_iff.mp, coe_finsetWalkLength_eq, ext_iff
-/
theorem mem_finsetWalkLength_iff {n : Nat} {u v : V} {p : G.Walk u v} :
    p in G.finsetWalkLength n u v ↔ p.length = n :=
  Set.ext_iff.mp (G.coe_finsetWalkLength_eq n u v) p

/--
Definition of `finsetWalkLengthLT` / `finsetWalkLengthLT` 的定义

English:
definition finsetWalkLengthLT
  signature: (n : Nat) (u v : V)
  body: (Finset.range n).disjiUnion
    (fun l => G.finsetWalkLength l u v)
    (fun l _ l' _ hne _ hsl hsl' p hp =>
      have hl : p.length = l := mem_finsetWalkLength_iff.mp (hsl hp)
      have hl' : p.length = l' := mem_finsetWalkLength_iff.mp (hsl' hp)
False.elim hne hl.symm.trans hl')

中文:
定义 finsetWalkLengthLT
  签名: (n : 自然数) (u v : V)
  定义体: (Finset.range n).disjiUnion
    (fun l => G.finsetWalkLength l u v)
    (fun l _ l' _ hne _ hsl hsl' p hp =>
      have hl : p.length = l := mem_finsetWalkLength_iff.mp (hsl hp)
      have hl' : p.length = l' := mem_finsetWalkLength_iff.mp (hsl' hp)
False.elim hne hl.symm.trans hl')

Depends on / 依赖: False.elim, Finset, Finset.range, G.finsetWalkLength, disjiUnion, finsetWalkLength, hl.symm.trans, length, mem_finsetWalkLength_iff, mem_finsetWalkLength_iff.mp, p.length
-/
def finsetWalkLengthLT (n : Nat) (u v : V) : Finset (G.Walk u v) :=
  (Finset.range n).disjiUnion
    (fun l => G.finsetWalkLength l u v)
    (fun l _ l' _ hne _ hsl hsl' p hp =>
      have hl : p.length = l := mem_finsetWalkLength_iff.mp (hsl hp)
      have hl' : p.length = l' := mem_finsetWalkLength_iff.mp (hsl' hp)
False.elim hne hl.symm.trans hl')

set_option backward.isDefEq.respectTransparency.types false in
open Finset in
/--
theorem `coe_finsetWalkLengthLT_eq` / 定理 `coe_finsetWalkLengthLT_eq`

English:
theorem coe_finsetWalkLengthLT_eq
  given: (n : Nat) (u v : V)
  proof: by
  ext p
  simp [finsetWalkLengthLT, mem_finsetWalkLength_iff]

中文:
定理 coe_finsetWalkLengthLT_eq
  条件: (n : 自然数) (u v : V)
  证明: by
  ext p
  simp [finsetWalkLengthLT, mem_finsetWalkLength_iff]

Depends on / 依赖: finsetWalkLengthLT, mem_finsetWalkLength_iff
-/
theorem coe_finsetWalkLengthLT_eq (n : Nat) (u v : V) :
    (G.finsetWalkLengthLT n u v : Set (G.Walk u v)) = {p : G.Walk u v | p.length < n} := by
  ext p
  simp [finsetWalkLengthLT, mem_finsetWalkLength_iff]

variable {G} in
/--
theorem `mem_finsetWalkLengthLT_iff` / 定理 `mem_finsetWalkLengthLT_iff`

English:
theorem mem_finsetWalkLengthLT_iff
  given: {n : Nat} {u v : V} {p : G.Walk u v}
  proof: Set.ext_iff.mp (G.coe_finsetWalkLengthLT_eq n u v) p

中文:
定理 mem_finsetWalkLengthLT_iff
  条件: {n : 自然数} {u v : V} {p : G.途径 u v}
  证明: Set.ext_iff.mp (G.coe_finsetWalkLengthLT_eq n u v) p

Depends on / 依赖: G.coe_finsetWalkLengthLT_eq, Set.ext_iff.mp, coe_finsetWalkLengthLT_eq, ext_iff
-/
theorem mem_finsetWalkLengthLT_iff {n : Nat} {u v : V} {p : G.Walk u v} :
    p in G.finsetWalkLengthLT n u v ↔ p.length < n :=
  Set.ext_iff.mp (G.coe_finsetWalkLengthLT_eq n u v) p

/--
Instance `fintypeSetWalkLength` / 实例 `fintypeSetWalkLength`

English:
instance fintypeSetWalkLength
  signature: (u v : V) (n : Nat)
  body: Fintype.ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe]; rw [coe_finsetWalkLength_eq]

中文:
实例 fintypeSetWalkLength
  签名: (u v : V) (n : 自然数)
  定义体: Fintype.ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe]; rw [coe_finsetWalkLength_eq]

Depends on / 依赖: Finset, Finset.mem_coe, Fintype, Fintype.ofFinset, G.finsetWalkLength, coe_finsetWalkLength_eq, finsetWalkLength, mem_coe, ofFinset
-/
instance fintypeSetWalkLength (u v : V) (n : Nat) : Fintype {p : G.Walk u v | p.length = n} :=
  Fintype.ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe]; rw [coe_finsetWalkLength_eq]

/--
Instance `fintypeSubtypeWalkLength` / 实例 `fintypeSubtypeWalkLength`

English:
instance fintypeSubtypeWalkLength
  signature: (u v : V) (n : Nat)
  body: inferInstanceAs Fintype {p : G.Walk u v | p.length = n}

中文:
实例 fintypeSubtypeWalkLength
  签名: (u v : V) (n : 自然数)
  定义体: inferInstanceAs Fintype {p : G.Walk u v | p.length = n}

Depends on / 依赖: Fintype, G.Walk, length, p.length
-/
instance fintypeSubtypeWalkLength (u v : V) (n : Nat) : Fintype {p : G.Walk u v // p.length = n} :=
inferInstanceAs Fintype {p : G.Walk u v | p.length = n}

/--
theorem `set_walk_length_toFinset_eq` / 定理 `set_walk_length_toFinset_eq`

English:
theorem set_walk_length_toFinset_eq
  given: (n : Nat) (u v : V)
  proof: by
  simp [← coe_finsetWalkLength_eq]

中文:
定理 set_walk_length_toFinset_eq
  条件: (n : 自然数) (u v : V)
  证明: by
  simp [← coe_finsetWalkLength_eq]

Depends on / 依赖: coe_finsetWalkLength_eq
-/
theorem set_walk_length_toFinset_eq (n : Nat) (u v : V) :
    {p : G.Walk u v | p.length = n}.toFinset = G.finsetWalkLength n u v := by
  simp [← coe_finsetWalkLength_eq]

/--
theorem `card_set_walk_length_eq` / 定理 `card_set_walk_length_eq`

English:
theorem card_set_walk_length_eq
  given: (u v : V) (n : Nat)
  proof: Fintype.card_ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe]; rw [coe_finsetWalkLength_eq]

中文:
定理 card_set_walk_length_eq
  条件: (u v : V) (n : 自然数)
  证明: Fintype.card_ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe]; rw [coe_finsetWalkLength_eq]

Depends on / 依赖: Finset, Finset.mem_coe, Fintype, Fintype.card_ofFinset, G.finsetWalkLength, card_ofFinset, coe_finsetWalkLength_eq, finsetWalkLength, mem_coe
-/
theorem card_set_walk_length_eq (u v : V) (n : Nat) :
    Fintype.card {p : G.Walk u v | p.length = n} = #(G.finsetWalkLength n u v) :=
  Fintype.card_ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe]; rw [coe_finsetWalkLength_eq]

/--
Instance `fintypeSetWalkLengthLT` / 实例 `fintypeSetWalkLengthLT`

English:
instance fintypeSetWalkLengthLT
  signature: (u v : V) (n : Nat)
  body: Fintype.ofFinset (G.finsetWalkLengthLT n u v) fun p => by
    rw [← Finset.mem_coe]; rw [coe_finsetWalkLengthLT_eq]

中文:
实例 fintypeSetWalkLengthLT
  签名: (u v : V) (n : 自然数)
  定义体: Fintype.ofFinset (G.finsetWalkLengthLT n u v) fun p => by
    rw [← Finset.mem_coe]; rw [coe_finsetWalkLengthLT_eq]

Depends on / 依赖: Finset, Finset.mem_coe, Fintype, Fintype.ofFinset, G.finsetWalkLengthLT, coe_finsetWalkLengthLT_eq, finsetWalkLengthLT, mem_coe, ofFinset
-/
instance fintypeSetWalkLengthLT (u v : V) (n : Nat) : Fintype {p : G.Walk u v | p.length < n} :=
  Fintype.ofFinset (G.finsetWalkLengthLT n u v) fun p => by
    rw [← Finset.mem_coe]; rw [coe_finsetWalkLengthLT_eq]

/--
Instance `fintypeSubtypeWalkLengthLT` / 实例 `fintypeSubtypeWalkLengthLT`

English:
instance fintypeSubtypeWalkLengthLT
  signature: (u v : V) (n : Nat)
  body: inferInstanceAs Fintype {p : G.Walk u v | p.length < n}

中文:
实例 fintypeSubtypeWalkLengthLT
  签名: (u v : V) (n : 自然数)
  定义体: inferInstanceAs Fintype {p : G.Walk u v | p.length < n}

Depends on / 依赖: Fintype, G.Walk, length, p.length
-/
instance fintypeSubtypeWalkLengthLT (u v : V) (n : Nat) : Fintype {p : G.Walk u v // p.length < n} :=
inferInstanceAs Fintype {p : G.Walk u v | p.length < n}

/--
Instance `fintypeSetPathLength` / 实例 `fintypeSetPathLength`

English:
instance fintypeSetPathLength
  signature: (u v : V) (n : Nat)
  body: Fintype.ofFinset {w in G.finsetWalkLength n u v | w.IsPath} by
    simp [mem_finsetWalkLength_iff, and_comm]

中文:
实例 fintypeSetPathLength
  签名: (u v : V) (n : 自然数)
  定义体: Fintype.ofFinset {w in G.finsetWalkLength n u v | w.IsPath} by
    simp [mem_finsetWalkLength_iff, and_comm]

Depends on / 依赖: Fintype, Fintype.ofFinset, G.finsetWalkLength, IsPath, and_comm, finsetWalkLength, mem_finsetWalkLength_iff, ofFinset, w.IsPath
-/
instance fintypeSetPathLength (u v : V) (n : Nat) :
    Fintype {p : G.Walk u v | p.IsPath ∧ p.length = n} :=
Fintype.ofFinset {w in G.finsetWalkLength n u v | w.IsPath} by
    simp [mem_finsetWalkLength_iff, and_comm]

/--
Instance `fintypeSubtypePathLength` / 实例 `fintypeSubtypePathLength`

English:
instance fintypeSubtypePathLength
  signature: (u v : V) (n : Nat)
  body: inferInstanceAs Fintype {p : G.Walk u v | p.IsPath ∧ p.length = n}

中文:
实例 fintypeSubtypePathLength
  签名: (u v : V) (n : 自然数)
  定义体: inferInstanceAs Fintype {p : G.Walk u v | p.IsPath ∧ p.length = n}

Depends on / 依赖: Fintype, G.Walk, IsPath, length, p.IsPath, p.length
-/
instance fintypeSubtypePathLength (u v : V) (n : Nat) :
    Fintype {p : G.Walk u v // p.IsPath ∧ p.length = n} :=
inferInstanceAs Fintype {p : G.Walk u v | p.IsPath ∧ p.length = n}

/--
Instance `fintypeSetPathLengthLT` / 实例 `fintypeSetPathLengthLT`

English:
instance fintypeSetPathLengthLT
  signature: (u v : V) (n : Nat)
  body: Fintype.ofFinset {w in G.finsetWalkLengthLT n u v | w.IsPath} by
    simp [mem_finsetWalkLengthLT_iff, and_comm]

中文:
实例 fintypeSetPathLengthLT
  签名: (u v : V) (n : 自然数)
  定义体: Fintype.ofFinset {w in G.finsetWalkLengthLT n u v | w.IsPath} by
    simp [mem_finsetWalkLengthLT_iff, and_comm]

Depends on / 依赖: Fintype, Fintype.ofFinset, G.finsetWalkLengthLT, IsPath, and_comm, finsetWalkLengthLT, mem_finsetWalkLengthLT_iff, ofFinset, w.IsPath
-/
instance fintypeSetPathLengthLT (u v : V) (n : Nat) :
    Fintype {p : G.Walk u v | p.IsPath ∧ p.length < n} :=
Fintype.ofFinset {w in G.finsetWalkLengthLT n u v | w.IsPath} by
    simp [mem_finsetWalkLengthLT_iff, and_comm]

/--
Instance `fintypeSubtypePathLengthLT` / 实例 `fintypeSubtypePathLengthLT`

English:
instance fintypeSubtypePathLengthLT
  signature: (u v : V) (n : Nat)
  body: inferInstanceAs Fintype {p : G.Walk u v | p.IsPath ∧ p.length < n}

中文:
实例 fintypeSubtypePathLengthLT
  签名: (u v : V) (n : 自然数)
  定义体: inferInstanceAs Fintype {p : G.Walk u v | p.IsPath ∧ p.length < n}

Depends on / 依赖: Fintype, G.Walk, IsPath, length, p.IsPath, p.length
-/
instance fintypeSubtypePathLengthLT (u v : V) (n : Nat) :
    Fintype {p : G.Walk u v // p.IsPath ∧ p.length < n} :=
inferInstanceAs Fintype {p : G.Walk u v | p.IsPath ∧ p.length < n}

end LocallyFinite

section Fintype
variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

/--
Instance `Path.instFintype` / 实例 `Path.instFintype`

English:
instance Path.instFintype
  signature: {u v : V}
  body: (univ (α := { p : G.Walk u v | p.IsPath ∧ p.length < Fintype.card V })).map
    ⟨fun p => { val := p.val, property := p.prop.left },
fun _ _ h => SetCoe.ext Subtype.mk.injEq .. ▸ h⟩
  complete p := mem_map.mpr ⟨
    ⟨p.val, ⟨p.prop, p.prop.length_lt⟩⟩,
    ⟨mem_univ _, rfl⟩⟩

中文:
实例 道路.instFintype
  签名: {u v : V}
  定义体: (univ (α := { p : G.Walk u v | p.IsPath ∧ p.length < Fintype.card V })).map
    ⟨fun p => { val := p.val, property := p.prop.left },
fun _ _ h => SetCoe.ext Subtype.mk.injEq .. ▸ h⟩
  complete p := mem_map.mpr ⟨
    ⟨p.val, ⟨p.prop, p.prop.length_lt⟩⟩,
    ⟨mem_univ _, rfl⟩⟩

Depends on / 依赖: Fintype, Fintype.card, G.Walk, IsPath, length, p.IsPath, p.length
-/
instance Path.instFintype {u v : V} : Fintype (G.Path u v) where
  elems := (univ (α := { p : G.Walk u v | p.IsPath ∧ p.length < Fintype.card V })).map
    ⟨fun p => { val := p.val, property := p.prop.left },
fun _ _ h => SetCoe.ext Subtype.mk.injEq .. ▸ h⟩
  complete p := mem_map.mpr ⟨
    ⟨p.val, ⟨p.prop, p.prop.length_lt⟩⟩,
    ⟨mem_univ _, rfl⟩⟩

end Fintype
end SimpleGraph
