/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Data.Seq.Defs
public import Mathlib.Tactic.ENatToNat

/-!
# Non-primitive corecursion for sequences

Primitive corecursive definition of the form
```
def foo (x : X) := hd x :: foo (tlArg x)
```
(where hd and tlArg are arbitrary functions) can be encoded via the corecursor `Seq.corec`.

It is not enough, however, to define multiplication and `powser` operation for multiseries.

This file implements a more general form of corecursion in the spirit of [blanchette2015].
This is a bare minimum that needed for the tactic, it justifies a weaker class of
corecursive definitions than [blanchette2015] does, and only works for `Seq`.

A function `f : Seq α → Seq α` is called *friendly* if for all `n : ℕ` the `n`-prefix of its result
`f s` depends only on the `n`-prefix of its input `s`.

In this file we develop a theory that justifies corecursive definitions of the form
```
def foo (x : X) := hd x :: f (foo (tlArg x))
```
where f is friendly.

## Main definitions

* `FriendlyOperation f` means that `f` is friendly.
* `FriendlyOperationClass` is a typeclass meaning that some indexed family of operations
  are friendly.
* `gcorec`: a generalization of `Seq.corec` that allows a corecursive call to be guarded by
  a friendly function.
* `FriendlyOperation.coind`, `FriendlyOperation.coind_comp_friend_left`,
  `FriendlyOperation.coind_comp_friend_right`: coinduction principles for proving that an operation
  is friendly.
* `FriendlyOperation.eq_of_bisim`: a generalisation of `Seq.eq_of_bisim'` that allows using a
  friendly operation in the tail of the sequences.

## Implementation details

To prove that the definition of the form
```
def foo (x : X) := hd x :: f (foo (tlArg x))
```
is correct we prove that there exists a function satisfying this equation. For that we employ a
Banach fixed point theorem. We treat `Seq α` as a metric space here with the metric
`d(s, t) := 2 ^ (-n)` where `n` is the minimal index where `s` and `t` differ.

Then `f` is friendly iff it is `1`-Lipschitz.
-/

@[expose] public section

namespace Tactic.ComputeAsymptotics.Seq

open Stream' Stream'.Seq

open scoped UniformConvergence

variable {α β γ γ' : Type*}

/-- Metric space structure on `Stream' α` considering `α` as a discrete metric space. -/
noncomputable local instance : MetricSpace (Stream' α) :=
  letI := @PiNat.metricSpace (fun _ => α) (fun _ => ⊥) (fun _ => discreteTopology_bot _)
inferInstanceAs MetricSpace (Nat -> α)

/-- Metric space structure on `Seq α` considering `α` as a discrete metric space. -/
noncomputable local instance : MetricSpace (Seq α) :=
inferInstanceAs MetricSpace (Subtype _)

local instance : CompleteSpace (Stream' α) :=
  @PiNat.completeSpace _ (fun _ => ⊥) (fun _ => discreteTopology_bot _)

set_option backward.isDefEq.respectTransparency false in
local instance : CompleteSpace (Seq α) := by
  suffices IsClosed (X := Stream' (Option α)) {x | forall {n : Nat}, x n = none -> x (n + 1) = none} by
    exact this.completeSpace_coe
  rw [isClosed_iff_clusterPt]
  intro s hs n hn
  rw [clusterPt_principal_iff] at hs
  obtain ⟨t, hts, ht⟩ := hs (Metric.ball s ((1 / 2 : Real) ^ (n + 1)))
    (Metric.ball_mem_nhds _ (by positivity))
  simp only [Metric.ball, Set.mem_ofPred_eq] at hts
  rw [← PiNat.apply_eq_of_dist_lt hts (by simp)] at hn
  rw [← PiNat.apply_eq_of_dist_lt hts (by rfl)]
  exact ht hn

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Stream'.dist_le_one` / 定理 `Stream'.dist_le_one`

English:
theorem Stream'.dist_le_one
  given: (s t : Stream' α)
  statement: dist s t <= 1
  proof: by
  by_cases h : s = t
  · simp [h]
  rw [PiNat.dist_eq_of_ne h]
  bound

@[simp]

中文:
定理 Stream'.dist_le_one
  条件: (s t : Stream' α)
  结论: dist s t <= 1
  证明: by
  by_cases h : s = t
  · simp [h]
  rw [PiNat.dist_eq_of_ne h]
  bound

@[simp]

Depends on / 依赖: PiNat.dist_eq_of_ne, dist_eq_of_ne
-/
theorem Stream'.dist_le_one (s t : Stream' α) : dist s t <= 1 := by
  by_cases h : s = t
  · simp [h]
  rw [PiNat.dist_eq_of_ne h]
  bound

@[simp]
/--
theorem `dist_le_one` / 定理 `dist_le_one`

English:
theorem dist_le_one
  given: (s t : Seq α)
  statement: dist s t <= 1
  proof: PiNat.dist_le_one _ _

local instance : BoundedSpace (Stream' α) :=
  @PiNat.boundedSpace _ (fun _ => ⊥) (fun _ => discreteTopology_bot _)

local instance : BoundedSpace (Seq α) :=
  instBoundedSpaceSubtype

中文:
定理 dist_le_one
  条件: (s t : 序列 α)
  结论: dist s t <= 1
  证明: PiNat.dist_le_one _ _

local instance : BoundedSpace (Stream' α) :=
  @PiNat.boundedSpace _ (fun _ => ⊥) (fun _ => discreteTopology_bot _)

local instance : BoundedSpace (Seq α) :=
  instBoundedSpaceSubtype

Depends on / 依赖: PiNat.dist_le_one, dist_le_one
-/
theorem dist_le_one (s t : Seq α) : dist s t <= 1 := PiNat.dist_le_one _ _

local instance : BoundedSpace (Stream' α) :=
  @PiNat.boundedSpace _ (fun _ => ⊥) (fun _ => discreteTopology_bot _)

local instance : BoundedSpace (Seq α) :=
  instBoundedSpaceSubtype

set_option backward.isDefEq.respectTransparency false in
/--
theorem `dist_eq_two_inv_pow` / 定理 `dist_eq_two_inv_pow`

English:
theorem dist_eq_two_inv_pow
  given: {s t : Seq α} (h : s != t)
  statement: exists n, dist s t = 2⁻¹ ^ n
  proof: by
  rw [Subtype.dist_eq]; rw [PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h)]
  simp

中文:
定理 dist_eq_two_inv_pow
  条件: {s t : 序列 α} (h : s != t)
  结论: 存在 n, dist s t = 2⁻¹ ^ n
  证明: by
  rw [Subtype.dist_eq]; rw [PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h)]
  simp

Depends on / 依赖: PiNat.dist_eq_of_ne, Subtype, Subtype.coe_ne_coe.mpr, Subtype.dist_eq, coe_ne_coe, dist_eq, dist_eq_of_ne
-/
theorem dist_eq_two_inv_pow {s t : Seq α} (h : s != t) : exists n, dist s t = 2⁻¹ ^ n := by
  rw [Subtype.dist_eq]; rw [PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h)]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward false in
@[simp]
/--
theorem `dist_cons_cons` / 定理 `dist_cons_cons`

English:
theorem dist_cons_cons
  given: (x : α) (s t : Seq α)
  statement: dist (cons x s) (cons x t) = 2⁻¹ * dist s t
  proof: by
  by_cases! h : s = t
  · simp [h]
  have h' : cons x s != cons x t := by
    simpa
  rw [Subtype.dist_eq]; rw [Subtype.dist_eq]; rw [PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h)]; rw [PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h')]
  simp only [show (1 / 2 : Real) = 2⁻¹ by simp, ← pow_succ']
  congr
  simp only [val_cons, PiNat.firstDiff, ne_eq, Classical.dite_not, Subtype.coe_ne_coe.mpr h,
    not_false_eq_true, ↓reduceDIte, val_eq_get]
  split_ifs with h_if
  · contrapose! h'
    apply_fun Subtype.val using Subtype.val_injective
    simpa
  · convert! Nat.find_comp_succ _ _ _
    simp [Stream'.cons]

中文:
定理 dist_cons_cons
  条件: (x : α) (s t : 序列 α)
  结论: dist (cons x s) (cons x t) = 2⁻¹ * dist s t
  证明: by
  by_cases! h : s = t
  · simp [h]
  have h' : cons x s != cons x t := by
    simpa
  rw [Subtype.dist_eq]; rw [Subtype.dist_eq]; rw [PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h)]; rw [PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h')]
  simp only [show (1 / 2 : Real) = 2⁻¹ by simp, ← pow_succ']
  congr
  simp only [val_cons, PiNat.firstDiff, ne_eq, Classical.dite_not, Subtype.coe_ne_coe.mpr h,
    not_false_eq_true, ↓reduceDIte, val_eq_get]
  split_ifs with h_if
  · contrapose! h'
    apply_fun Subtype.val using Subtype.val_injective
    simpa
  · convert! Nat.find_comp_succ _ _ _
    simp [Stream'.cons]

Depends on / 依赖: Classical, Classical.dite_not, PiNat.dist_eq_of_ne, PiNat.firstDiff, Subtype, Subtype.coe_ne_coe.mpr, Subtype.dist_eq, Subtype.val, apply_fun, coe_ne_coe, contrapose, dist_eq, dist_eq_of_ne, dite_not, firstDiff, h_if, ne_eq, not_false_eq_true, pow_succ, reduceDIte
-/
theorem dist_cons_cons (x : α) (s t : Seq α) : dist (cons x s) (cons x t) = 2⁻¹ * dist s t := by
  by_cases! h : s = t
  · simp [h]
  have h' : cons x s != cons x t := by
    simpa
  rw [Subtype.dist_eq]; rw [Subtype.dist_eq]; rw [PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h)]; rw [PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h')]
  simp only [show (1 / 2 : Real) = 2⁻¹ by simp, ← pow_succ']
  congr
  simp only [val_cons, PiNat.firstDiff, ne_eq, Classical.dite_not, Subtype.coe_ne_coe.mpr h,
    not_false_eq_true, ↓reduceDIte, val_eq_get]
  split_ifs with h_if
  · contrapose! h'
    apply_fun Subtype.val using Subtype.val_injective
    simpa
  · convert! Nat.find_comp_succ _ _ _
    simp [Stream'.cons]

/--
theorem `dist_eq_half_of_head` / 定理 `dist_eq_half_of_head`

English:
theorem dist_eq_half_of_head
  given: {s t : Seq α} (h : s.head = t.head)
  proof: by
  cases s <;> cases t <;> simp at h <;> simp [h]

中文:
定理 dist_eq_half_of_head
  条件: {s t : 序列 α} (h : s.head = t.head)
  证明: by
  cases s <;> cases t <;> simp at h <;> simp [h]
-/
theorem dist_eq_half_of_head {s t : Seq α} (h : s.head = t.head) :
    dist s t = 2⁻¹ * dist s.tail t.tail := by
  cases s <;> cases t <;> simp at h <;> simp [h]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `dist_eq_one_of_head` / 定理 `dist_eq_one_of_head`

English:
theorem dist_eq_one_of_head
  given: {s t : Seq α} (h : s.head != t.head)
  statement: dist s t = 1
  proof: by
  rw [Subtype.dist_eq]; rw [PiNat.dist_eq_of_ne]
  · convert! pow_zero _
    simp only [PiNat.firstDiff, ne_eq, Classical.dite_not, dite_eq_left_iff,
      Nat.find_eq_zero]
    intro h'
    simpa [Stream'.cons]
  · rw [Subtype.coe_ne_coe]
    contrapose h
    simp [h]

中文:
定理 dist_eq_one_of_head
  条件: {s t : 序列 α} (h : s.head != t.head)
  结论: dist s t = 1
  证明: by
  rw [Subtype.dist_eq]; rw [PiNat.dist_eq_of_ne]
  · convert! pow_zero _
    simp only [PiNat.firstDiff, ne_eq, Classical.dite_not, dite_eq_left_iff,
      Nat.find_eq_zero]
    intro h'
    simpa [Stream'.cons]
  · rw [Subtype.coe_ne_coe]
    contrapose h
    simp [h]

Depends on / 依赖: Classical, Classical.dite_not, Nat.find_eq_zero, PiNat.dist_eq_of_ne, PiNat.firstDiff, Stream, Subtype, Subtype.coe_ne_coe, Subtype.dist_eq, coe_ne_coe, contrapose, convert, dist_eq, dist_eq_of_ne, dite_eq_left_iff, dite_not, find_eq_zero, firstDiff, ne_eq, pow_zero
-/
theorem dist_eq_one_of_head {s t : Seq α} (h : s.head != t.head) : dist s t = 1 := by
  rw [Subtype.dist_eq]; rw [PiNat.dist_eq_of_ne]
  · convert! pow_zero _
    simp only [PiNat.firstDiff, ne_eq, Classical.dite_not, dite_eq_left_iff,
      Nat.find_eq_zero]
    intro h'
    simpa [Stream'.cons]
  · rw [Subtype.coe_ne_coe]
    contrapose h
    simp [h]

/--
theorem `dist_cons_cons_eq_one` / 定理 `dist_cons_cons_eq_one`

English:
theorem dist_cons_cons_eq_one
  given: {x y : α} {s t : Seq α} (h : x != y)
  proof: by
  apply dist_eq_one_of_head
  simpa

@[simp]

中文:
定理 dist_cons_cons_eq_one
  条件: {x y : α} {s t : 序列 α} (h : x != y)
  证明: by
  apply dist_eq_one_of_head
  simpa

@[simp]

Depends on / 依赖: dist_eq_one_of_head
-/
theorem dist_cons_cons_eq_one {x y : α} {s t : Seq α} (h : x != y) :
    dist (cons x s) (cons y t) = 1 := by
  apply dist_eq_one_of_head
  simpa

@[simp]
/--
theorem `dist_cons_nil` / 定理 `dist_cons_nil`

English:
theorem dist_cons_nil
  given: (x : α) (s : Seq α)
  statement: dist (cons x s) nil = 1
  proof: by
  apply dist_eq_one_of_head
  simp

@[simp]

中文:
定理 dist_cons_nil
  条件: (x : α) (s : 序列 α)
  结论: dist (cons x s) nil = 1
  证明: by
  apply dist_eq_one_of_head
  simp

@[simp]

Depends on / 依赖: dist_eq_one_of_head
-/
theorem dist_cons_nil (x : α) (s : Seq α) : dist (cons x s) nil = 1 := by
  apply dist_eq_one_of_head
  simp

@[simp]
/--
theorem `dist_nil_cons` / 定理 `dist_nil_cons`

English:
theorem dist_nil_cons
  given: (x : α) (s : Seq α)
  statement: dist nil (cons x s) = 1
  proof: by
  rw [dist_comm]
  simp

中文:
定理 dist_nil_cons
  条件: (x : α) (s : 序列 α)
  结论: dist nil (cons x s) = 1
  证明: by
  rw [dist_comm]
  simp

Depends on / 依赖: dist_comm
-/
theorem dist_nil_cons (x : α) (s : Seq α) : dist nil (cons x s) = 1 := by
  rw [dist_comm]
  simp

/--
theorem `dist_le_half_iff` / 定理 `dist_le_half_iff`

English:
theorem dist_le_half_iff
  given: {s t : Seq α}
  proof: by
    cases s <;> cases t <;> norm_num at h <;> simp
    grind [dist_cons_cons_eq_one]
  mpr h := by
    obtain ⟨rfl, rfl⟩ | ⟨hd, s', t', rfl, rfl⟩ := h <;> simp

中文:
定理 dist_le_half_iff
  条件: {s t : 序列 α}
  证明: by
    cases s <;> cases t <;> norm_num at h <;> simp
    grind [dist_cons_cons_eq_one]
  mpr h := by
    obtain ⟨rfl, rfl⟩ | ⟨hd, s', t', rfl, rfl⟩ := h <;> simp

Depends on / 依赖: dist_cons_cons_eq_one
-/
theorem dist_le_half_iff {s t : Seq α} :
    dist s t <= 2⁻¹ ↔ (s = .nil ∧ t = .nil) ∨ exists hd s' t', s = .cons hd s' ∧ t = .cons hd t' where
  mp h := by
    cases s <;> cases t <;> norm_num at h <;> simp
    grind [dist_cons_cons_eq_one]
  mpr h := by
    obtain ⟨rfl, rfl⟩ | ⟨hd, s', t', rfl, rfl⟩ := h <;> simp

/--
Definition of `FriendlyOperation` / `FriendlyOperation` 的定义

English:
definition FriendlyOperation
  signature: (op : Seq α -> Seq α)
  body: LipschitzWith 1 op

中文:
定义 FriendlyOperation
  签名: (op : 序列 α -> 序列 α)
  定义体: LipschitzWith 1 op

Depends on / 依赖: LipschitzWith
-/
def FriendlyOperation (op : Seq α -> Seq α) : Prop := LipschitzWith 1 op

/--
Definition of `FriendlyOperationClass` / `FriendlyOperationClass` 的定义

English:
class FriendlyOperationClass
  parameters: (F : γ -> Seq α -> Seq α)
  axioms and operations (1):
    - friend : forall c : γ, FriendlyOperation (F c)

中文:
类 FriendlyOperation类
  参数: (F : γ -> 序列 α -> 序列 α)
  公理与运算 (1 个):
    - friend : 对任意 c : γ, FriendlyOperation (F c)
-/
class FriendlyOperationClass (F : γ -> Seq α -> Seq α) : Prop where
  friend : forall c : γ, FriendlyOperation (F c)

/--
theorem `friendlyOperation_iff_dist_le_dist` / 定理 `friendlyOperation_iff_dist_le_dist`

English:
theorem friendlyOperation_iff_dist_le_dist
  given: (op : Seq α -> Seq α)
  proof: by
  simp [FriendlyOperation, lipschitzWith_iff_dist_le_mul]

中文:
定理 friendlyOperation_iff_dist_le_dist
  条件: (op : 序列 α -> 序列 α)
  证明: by
  simp [FriendlyOperation, lipschitzWith_iff_dist_le_mul]

Depends on / 依赖: FriendlyOperation, lipschitzWith_iff_dist_le_mul
-/
theorem friendlyOperation_iff_dist_le_dist (op : Seq α -> Seq α) :
    FriendlyOperation op ↔ forall s t, dist (op s) (op t) <= dist s t := by
  simp [FriendlyOperation, lipschitzWith_iff_dist_le_mul]

/--
theorem `FriendlyOperation.id` / 定理 `FriendlyOperation.id`

English:
theorem FriendlyOperation.id
  statement: FriendlyOperation (id : Seq α -> Seq α)
  proof: LipschitzWith.id

中文:
定理 FriendlyOperation.id
  结论: FriendlyOperation (id : 序列 α -> 序列 α)
  证明: LipschitzWith.id

Depends on / 依赖: LipschitzWith, LipschitzWith.id
-/
theorem FriendlyOperation.id : FriendlyOperation (id : Seq α -> Seq α) :=
  LipschitzWith.id

/--
theorem `FriendlyOperation.comp` / 定理 `FriendlyOperation.comp`

English:
theorem FriendlyOperation.comp
  statement: {op op' : Seq α -> Seq α}
  proof: by
  rw [FriendlyOperation] at h h' ⊢
  convert! h.comp h'
  simp

中文:
定理 FriendlyOperation.comp
  结论: {op op' : 序列 α -> 序列 α}
  证明: by
  rw [FriendlyOperation] at h h' ⊢
  convert! h.comp h'
  simp

Depends on / 依赖: FriendlyOperation, convert, h.comp
-/
theorem FriendlyOperation.comp {op op' : Seq α -> Seq α}
    (h : FriendlyOperation op) (h' : FriendlyOperation op') :
    FriendlyOperation (op ∘ op') := by
  rw [FriendlyOperation] at h h' ⊢
  convert! h.comp h'
  simp

/--
theorem `FriendlyOperation.const` / 定理 `FriendlyOperation.const`

English:
theorem FriendlyOperation.const
  given: {s : Seq α}
  statement: FriendlyOperation (fun _ => s)
  proof: by
  simp [friendlyOperation_iff_dist_le_dist]

中文:
定理 FriendlyOperation.const
  条件: {s : 序列 α}
  结论: FriendlyOperation (fun _ => s)
  证明: by
  simp [friendlyOperation_iff_dist_le_dist]

Depends on / 依赖: friendlyOperation_iff_dist_le_dist
-/
theorem FriendlyOperation.const {s : Seq α} : FriendlyOperation (fun _ => s) := by
  simp [friendlyOperation_iff_dist_le_dist]

/--
theorem `FriendlyOperationClass.comp` / 定理 `FriendlyOperationClass.comp`

English:
theorem FriendlyOperationClass.comp
  statement: (F : γ -> Seq α -> Seq α) (g : γ' -> γ)
  proof: by
  grind [FriendlyOperationClass]

中文:
定理 FriendlyOperation类.comp
  结论: (F : γ -> 序列 α -> 序列 α) (g : γ' -> γ)
  证明: by
  grind [FriendlyOperationClass]

Depends on / 依赖: FriendlyOperationClass
-/
theorem FriendlyOperationClass.comp (F : γ -> Seq α -> Seq α) (g : γ' -> γ)
    [h : FriendlyOperationClass F] : FriendlyOperationClass (fun c => F (g c)) := by
  grind [FriendlyOperationClass]

/--
theorem `FriendlyOperation.ite` / 定理 `FriendlyOperation.ite`

English:
theorem FriendlyOperation.ite
  statement: {op₁ op₂ : Seq α -> Seq α}
  proof: by
  rw [friendlyOperation_iff_dist_le_dist] at h₁ h₂ ⊢
  intro s t
  by_cases! h_head : s.head != t.head
  · simp [dist_eq_one_of_head h_head]
  grind

中文:
定理 FriendlyOperation.ite
  结论: {op₁ op₂ : 序列 α -> 序列 α}
  证明: by
  rw [friendlyOperation_iff_dist_le_dist] at h₁ h₂ ⊢
  intro s t
  by_cases! h_head : s.head != t.head
  · simp [dist_eq_one_of_head h_head]
  grind

Depends on / 依赖: dist_eq_one_of_head, friendlyOperation_iff_dist_le_dist, h_head, s.head, t.head
-/
theorem FriendlyOperation.ite {op₁ op₂ : Seq α -> Seq α}
    (h₁ : FriendlyOperation op₁) (h₂ : FriendlyOperation op₂)
    {P : Option α -> Prop} [DecidablePred P] :
    FriendlyOperation (fun s => if P s.head then op₁ s else op₂ s) := by
  rw [friendlyOperation_iff_dist_le_dist] at h₁ h₂ ⊢
  intro s t
  by_cases! h_head : s.head != t.head
  · simp [dist_eq_one_of_head h_head]
  grind

/--
theorem `FriendlyOperation.dist_le` / 定理 `FriendlyOperation.dist_le`

English:
theorem FriendlyOperation.dist_le
  statement: {op : Seq α -> Seq α} (h : FriendlyOperation op)
  proof: by
  rw [FriendlyOperation]; rw [lipschitzWith_iff_dist_le_mul] at h
  simpa using h s t

中文:
定理 FriendlyOperation.dist_le
  结论: {op : 序列 α -> 序列 α} (h : FriendlyOperation op)
  证明: by
  rw [FriendlyOperation]; rw [lipschitzWith_iff_dist_le_mul] at h
  simpa using h s t

Depends on / 依赖: FriendlyOperation, lipschitzWith_iff_dist_le_mul
-/
theorem FriendlyOperation.dist_le {op : Seq α -> Seq α} (h : FriendlyOperation op)
    {s t : Seq α} : dist (op s) (op t) <= dist s t := by
  rw [FriendlyOperation]; rw [lipschitzWith_iff_dist_le_mul] at h
  simpa using h s t

/--
theorem `exists_fixed_point_of_contractible` / 定理 `exists_fixed_point_of_contractible`

English:
theorem exists_fixed_point_of_contractible
  statement: (F : (β ->ᵤ Seq α) -> (β ->ᵤ Seq α))
  proof: by
  have hF : ContractingWith 2⁻¹ F := by
    constructor
    · norm_num
    · exact h
  let f := hF.fixedPoint _
  use f
  exact hF.fixedPoint_isFixedPt

中文:
定理 存在_fixed_point_of_contractible
  结论: (F : (β ->ᵤ 序列 α) -> (β ->ᵤ 序列 α))
  证明: by
  have hF : ContractingWith 2⁻¹ F := by
    constructor
    · norm_num
    · exact h
  let f := hF.fixedPoint _
  use f
  exact hF.fixedPoint_isFixedPt

Depends on / 依赖: ContractingWith, fixedPoint, fixedPoint_isFixedPt, hF.fixedPoint, hF.fixedPoint_isFixedPt
-/
theorem exists_fixed_point_of_contractible (F : (β ->ᵤ Seq α) -> (β ->ᵤ Seq α))
    (h : LipschitzWith 2⁻¹ F) :
    exists f : β -> Seq α, Function.IsFixedPt F f := by
  have hF : ContractingWith 2⁻¹ F := by
    constructor
    · norm_num
    · exact h
  let f := hF.fixedPoint _
  use f
  exact hF.fixedPoint_isFixedPt

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FriendlyOperation.exists_fixed_point` / 定理 `FriendlyOperation.exists_fixed_point`

English:
theorem FriendlyOperation.exists_fixed_point
  statement: (F : β -> Option (α × γ × β)) (op : γ -> Seq α -> Seq α)
  proof: by
  let T : (β ->ᵤ Seq α) -> (β ->ᵤ Seq α) := fun f b =>
    match F b with
    | none => nil
    | some (a, c, b') => Seq.cons a (op c (f b'))
  have hT : LipschitzWith 2⁻¹ T := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro f g
    rw [UniformFun.dist_le (by positivity)]
    intro b
    simp only [UniformFun.toFun, UniformFun.ofFun, Equiv.coe_fn_symm_mk, NNReal.coe_inv,
      NNReal.coe_ofNat, T]
    cases F b with
    | none => simp
    | some v =>
      obtain ⟨a, c, b'⟩ := v
      simp
      calc
        _ <= dist (f b') (g b') := by
          have := h.friend c
          rw [FriendlyOperation]; rw [lipschitzWith_iff_dist_le_mul] at this
          specialize this (f b') (g b')
          simpa using this
        _ <= _ := by
          simp only [UniformFun.dist_def]
          apply le_ciSup (f := fun b => dist (f b) (g b))
          have : exists C, forall (a b : Seq α), dist a b <= C := by
            rw [← Metric.boundedSpace_iff]
            infer_instance
          obtain ⟨C, hC⟩ := this
          use C
          simp [upperBounds]
          grind
  obtain ⟨f, hf⟩ := exists_fixed_point_of_contractible T hT
  use f
  intro b
  rw [← hf]
  simp only [T]
  cases hb : F b with
  | none =>
    simp
  | some v =>
    obtain ⟨a, c, b'⟩ := v
    simp only [cons_eq_cons, true_and]
    congr
    change f b' = T f b'
    rw [hf]

中文:
定理 FriendlyOperation.存在_fixed_point
  结论: (F : β -> 选项类型 (α × γ × β)) (op : γ -> 序列 α -> 序列 α)
  证明: by
  let T : (β ->ᵤ Seq α) -> (β ->ᵤ Seq α) := fun f b =>
    match F b with
    | none => nil
    | some (a, c, b') => Seq.cons a (op c (f b'))
  have hT : LipschitzWith 2⁻¹ T := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro f g
    rw [UniformFun.dist_le (by positivity)]
    intro b
    simp only [UniformFun.toFun, UniformFun.ofFun, Equiv.coe_fn_symm_mk, NNReal.coe_inv,
      NNReal.coe_ofNat, T]
    cases F b with
    | none => simp
    | some v =>
      obtain ⟨a, c, b'⟩ := v
      simp
      calc
        _ <= dist (f b') (g b') := by
          have := h.friend c
          rw [FriendlyOperation]; rw [lipschitzWith_iff_dist_le_mul] at this
          specialize this (f b') (g b')
          simpa using this
        _ <= _ := by
          simp only [UniformFun.dist_def]
          apply le_ciSup (f := fun b => dist (f b) (g b))
          have : exists C, forall (a b : Seq α), dist a b <= C := by
            rw [← Metric.boundedSpace_iff]
            infer_instance
          obtain ⟨C, hC⟩ := this
          use C
          simp [upperBounds]
          grind
  obtain ⟨f, hf⟩ := exists_fixed_point_of_contractible T hT
  use f
  intro b
  rw [← hf]
  simp only [T]
  cases hb : F b with
  | none =>
    simp
  | some v =>
    obtain ⟨a, c, b'⟩ := v
    simp only [cons_eq_cons, true_and]
    congr
    change f b' = T f b'
    rw [hf]

Depends on / 依赖: Equiv.coe_fn_symm_mk, Friend, LipschitzWith, NNReal, NNReal.coe_inv, NNReal.coe_ofNat, Seq.cons, UniformFun, UniformFun.dist_le, UniformFun.ofFun, UniformFun.toFun, coe_fn_symm_mk, coe_inv, coe_ofNat, dist_le, friend, h.friend, lipschitzWith_iff_dist_le_mul
-/
theorem FriendlyOperation.exists_fixed_point (F : β -> Option (α × γ × β)) (op : γ -> Seq α -> Seq α)
    [h : FriendlyOperationClass op] :
    exists f : β -> Seq α, forall b : β,
    match F b with
    | none => f b = nil
    | some (a, c, b') => f b = Seq.cons a (op c (f b')) := by
  let T : (β ->ᵤ Seq α) -> (β ->ᵤ Seq α) := fun f b =>
    match F b with
    | none => nil
    | some (a, c, b') => Seq.cons a (op c (f b'))
  have hT : LipschitzWith 2⁻¹ T := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro f g
    rw [UniformFun.dist_le (by positivity)]
    intro b
    simp only [UniformFun.toFun, UniformFun.ofFun, Equiv.coe_fn_symm_mk, NNReal.coe_inv,
      NNReal.coe_ofNat, T]
    cases F b with
    | none => simp
    | some v =>
      obtain ⟨a, c, b'⟩ := v
      simp
      calc
        _ <= dist (f b') (g b') := by
          have := h.friend c
          rw [FriendlyOperation]; rw [lipschitzWith_iff_dist_le_mul] at this
          specialize this (f b') (g b')
          simpa using this
        _ <= _ := by
          simp only [UniformFun.dist_def]
          apply le_ciSup (f := fun b => dist (f b) (g b))
          have : exists C, forall (a b : Seq α), dist a b <= C := by
            rw [← Metric.boundedSpace_iff]
            infer_instance
          obtain ⟨C, hC⟩ := this
          use C
          simp [upperBounds]
          grind
  obtain ⟨f, hf⟩ := exists_fixed_point_of_contractible T hT
  use f
  intro b
  rw [← hf]
  simp only [T]
  cases hb : F b with
  | none =>
    simp
  | some v =>
    obtain ⟨a, c, b'⟩ := v
    simp only [cons_eq_cons, true_and]
    congr
    change f b' = T f b'
    rw [hf]

/--
Definition of `gcorec` / `gcorec` 的定义

English:
definition gcorec
  signature: (F : β -> Option (α × γ × β)) (op : γ -> Seq α -> Seq α)
  body: (FriendlyOperation.exists_fixed_point F op).choose

中文:
定义 gcorec
  签名: (F : β -> 选项类型 (α × γ × β)) (op : γ -> 序列 α -> 序列 α)
  定义体: (FriendlyOperation.exists_fixed_point F op).choose

Depends on / 依赖: FriendlyOperation, FriendlyOperation.exists_fixed_point, exists_fixed_point
-/
noncomputable def gcorec (F : β -> Option (α × γ × β)) (op : γ -> Seq α -> Seq α)
    [FriendlyOperationClass op] :
  β -> Seq α := (FriendlyOperation.exists_fixed_point F op).choose

/--
theorem `gcorec_nil` / 定理 `gcorec_nil`

English:
theorem gcorec_nil
  statement: {F : β -> Option (α × γ × β)} {op : γ -> Seq α -> Seq α}
  proof: by
  have := (FriendlyOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using! this

中文:
定理 gcorec_nil
  结论: {F : β -> 选项类型 (α × γ × β)} {op : γ -> 序列 α -> 序列 α}
  证明: by
  have := (FriendlyOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using! this

Depends on / 依赖: FriendlyOperation, FriendlyOperation.exists_fixed_point, choose_spec, exists_fixed_point
-/
theorem gcorec_nil {F : β -> Option (α × γ × β)} {op : γ -> Seq α -> Seq α}
    [FriendlyOperationClass op] {b : β}
    (h : F b = none) :
    gcorec F op b = nil := by
  have := (FriendlyOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using! this

/--
theorem `gcorec_some` / 定理 `gcorec_some`

English:
theorem gcorec_some
  statement: {F : β -> Option (α × γ × β)} {op : γ -> Seq α -> Seq α}
  proof: by
  have := (FriendlyOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using! this

中文:
定理 gcorec_some
  结论: {F : β -> 选项类型 (α × γ × β)} {op : γ -> 序列 α -> 序列 α}
  证明: by
  have := (FriendlyOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using! this

Depends on / 依赖: FriendlyOperation, FriendlyOperation.exists_fixed_point, choose_spec, exists_fixed_point
-/
theorem gcorec_some {F : β -> Option (α × γ × β)} {op : γ -> Seq α -> Seq α}
    [FriendlyOperationClass op] {b : β}
    {a : α} {c : γ} {b' : β}
    (h : F b = some (a, c, b')) :
    gcorec F op b = Seq.cons a (op c (gcorec F op b')) := by
  have := (FriendlyOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using! this

/--
theorem `FriendlyOperation.cons` / 定理 `FriendlyOperation.cons`

English:
theorem FriendlyOperation.cons
  given: (hd : α)
  statement: FriendlyOperation (cons hd)
  proof: by
  simp only [friendlyOperation_iff_dist_le_dist, dist_cons_cons]
  intro x y
  linarith [dist_nonneg (x := x) (y := y)]

中文:
定理 FriendlyOperation.cons
  条件: (hd : α)
  结论: FriendlyOperation (cons hd)
  证明: by
  simp only [friendlyOperation_iff_dist_le_dist, dist_cons_cons]
  intro x y
  linarith [dist_nonneg (x := x) (y := y)]

Depends on / 依赖: dist_cons_cons, dist_nonneg, friendlyOperation_iff_dist_le_dist
-/
theorem FriendlyOperation.cons (hd : α) : FriendlyOperation (cons hd) := by
  simp only [friendlyOperation_iff_dist_le_dist, dist_cons_cons]
  intro x y
  linarith [dist_nonneg (x := x) (y := y)]

/--
lemma `dist_const_tail_cons_tail_le` / 引理 `dist_const_tail_cons_tail_le`

English:
lemma dist_const_tail_cons_tail_le
  proof: by
  rwa [dist_cons_cons, dist_eq_half_of_head, mul_le_mul_iff_right₀ (by norm_num)] at h
  grw [dist_le_one x y, mul_one] at h
  obtain (⟨hx, hy⟩ | ⟨_, _, _, hx, hy⟩) := dist_le_half_iff.mp h <;> simp [hx, hy]

中文:
引理 dist_const_tail_cons_tail_le
  证明: by
  rwa [dist_cons_cons, dist_eq_half_of_head, mul_le_mul_iff_right₀ (by norm_num)] at h
  grw [dist_le_one x y, mul_one] at h
  obtain (⟨hx, hy⟩ | ⟨_, _, _, hx, hy⟩) := dist_le_half_iff.mp h <;> simp [hx, hy]

Depends on / 依赖: dist_cons_cons, dist_eq_half_of_head, dist_le_half_iff, dist_le_half_iff.mp, dist_le_one, mul_one
-/
lemma dist_const_tail_cons_tail_le
    {op : Seq α -> Seq α} {hd : α} {x y : Stream'.Seq α}
    (h : dist (op (cons hd x)) (op (cons hd y)) <= dist (cons hd x) (cons hd y)) :
    dist (op (cons hd x)).tail (op (cons hd y)).tail <= dist x y := by
  rwa [dist_cons_cons, dist_eq_half_of_head, mul_le_mul_iff_right₀ (by norm_num)] at h
  grw [dist_le_one x y, mul_one] at h
  obtain (⟨hx, hy⟩ | ⟨_, _, _, hx, hy⟩) := dist_le_half_iff.mp h <;> simp [hx, hy]

/--
theorem `FriendlyOperation.cons_tail` / 定理 `FriendlyOperation.cons_tail`

English:
theorem FriendlyOperation.cons_tail
  given: {op : Seq α -> Seq α} {hd : α} (h : FriendlyOperation op)
  proof: by
  simp_rw [friendlyOperation_iff_dist_le_dist] at h ⊢
  intro x y
  specialize h (.cons hd x) (.cons hd y)
  exact dist_const_tail_cons_tail_le h

中文:
定理 FriendlyOperation.cons_tail
  条件: {op : 序列 α -> 序列 α} {hd : α} (h : FriendlyOperation op)
  证明: by
  simp_rw [friendlyOperation_iff_dist_le_dist] at h ⊢
  intro x y
  specialize h (.cons hd x) (.cons hd y)
  exact dist_const_tail_cons_tail_le h

Depends on / 依赖: dist_const_tail_cons_tail_le, friendlyOperation_iff_dist_le_dist, simp_rw, specialize
-/
theorem FriendlyOperation.cons_tail {op : Seq α -> Seq α} {hd : α} (h : FriendlyOperation op) :
    FriendlyOperation (fun s => (op (.cons hd s)).tail) := by
  simp_rw [friendlyOperation_iff_dist_le_dist] at h ⊢
  intro x y
  specialize h (.cons hd x) (.cons hd y)
  exact dist_const_tail_cons_tail_le h

/--
theorem `FriendlyOperation.op_cons_head_eq` / 定理 `FriendlyOperation.op_cons_head_eq`

English:
theorem FriendlyOperation.op_cons_head_eq
  statement: {op : Seq α -> Seq α} (h : FriendlyOperation op) {a : α}
  proof: by
  rw [friendlyOperation_iff_dist_le_dist] at h
  specialize h (.cons a s) (.cons a t)
  simp only [dist_cons_cons] at h
  replace h : dist (op (.cons a s)) (op (.cons a t)) <= 2⁻¹ := by
    apply h.trans
    simp
  rw [dist_le_half_iff] at h
  generalize op (Seq.cons a s) = s' at *
  generalize op (Seq.cons a t) = t' at *
  obtain ⟨rfl, rfl⟩ | ⟨hd, s_tl, t_tl, rfl, rfl⟩ := h <;> rfl

中文:
定理 FriendlyOperation.op_cons_head_eq
  结论: {op : 序列 α -> 序列 α} (h : FriendlyOperation op) {a : α}
  证明: by
  rw [friendlyOperation_iff_dist_le_dist] at h
  specialize h (.cons a s) (.cons a t)
  simp only [dist_cons_cons] at h
  replace h : dist (op (.cons a s)) (op (.cons a t)) <= 2⁻¹ := by
    apply h.trans
    simp
  rw [dist_le_half_iff] at h
  generalize op (Seq.cons a s) = s' at *
  generalize op (Seq.cons a t) = t' at *
  obtain ⟨rfl, rfl⟩ | ⟨hd, s_tl, t_tl, rfl, rfl⟩ := h <;> rfl

Depends on / 依赖: Seq.cons, dist_cons_cons, dist_le_half_iff, friendlyOperation_iff_dist_le_dist, generalize, h.trans, replace, s_tl, specialize, t_tl
-/
theorem FriendlyOperation.op_cons_head_eq {op : Seq α -> Seq α} (h : FriendlyOperation op) {a : α}
    {s t : Seq α} : (op <| .cons a s).head = (op <| .cons a t).head := by
  rw [friendlyOperation_iff_dist_le_dist] at h
  specialize h (.cons a s) (.cons a t)
  simp only [dist_cons_cons] at h
  replace h : dist (op (.cons a s)) (op (.cons a t)) <= 2⁻¹ := by
    apply h.trans
    simp
  rw [dist_le_half_iff] at h
  generalize op (Seq.cons a s) = s' at *
  generalize op (Seq.cons a t) = t' at *
  obtain ⟨rfl, rfl⟩ | ⟨hd, s_tl, t_tl, rfl, rfl⟩ := h <;> rfl

/--
Definition of `FriendlyOperation.unfold` / `FriendlyOperation.unfold` 的定义

English:
definition FriendlyOperation.unfold
  signature: {op : Seq α -> Seq α} (h : FriendlyOperation op) (hd? : Option α)
  body: match hd? with
  | none =>
    match (op nil).destruct with
    | none => none
    | some (t_hd, t_tl) =>
      some (t_hd, ⟨fun _ => t_tl, FriendlyOperation.const⟩)
  | some s_hd =>
    match (op <| .cons s_hd nil).destruct with
    | none => none
    | some (t_hd, _) =>
      some (t_hd, ⟨fun s_tl => (op (.cons s_hd s_tl)).tail, FriendlyOperation.cons_tail h⟩)

中文:
定义 FriendlyOperation.unfold
  签名: {op : 序列 α -> 序列 α} (h : FriendlyOperation op) (hd? : 选项类型 α)
  定义体: match hd? with
  | none =>
    match (op nil).destruct with
    | none => none
    | some (t_hd, t_tl) =>
      some (t_hd, ⟨fun _ => t_tl, FriendlyOperation.const⟩)
  | some s_hd =>
    match (op <| .cons s_hd nil).destruct with
    | none => none
    | some (t_hd, _) =>
      some (t_hd, ⟨fun s_tl => (op (.cons s_hd s_tl)).tail, FriendlyOperation.cons_tail h⟩)

Depends on / 依赖: FriendlyOperation, FriendlyOperation.cons_tail, FriendlyOperation.const, cons_tail, destruct, s_hd, s_tl, t_hd, t_tl
-/
def FriendlyOperation.unfold {op : Seq α -> Seq α} (h : FriendlyOperation op) (hd? : Option α) :
    Option (α × Subtype (@FriendlyOperation α)) :=
  match hd? with
  | none =>
    match (op nil).destruct with
    | none => none
    | some (t_hd, t_tl) =>
      some (t_hd, ⟨fun _ => t_tl, FriendlyOperation.const⟩)
  | some s_hd =>
    match (op <| .cons s_hd nil).destruct with
    | none => none
    | some (t_hd, _) =>
      some (t_hd, ⟨fun s_tl => (op (.cons s_hd s_tl)).tail, FriendlyOperation.cons_tail h⟩)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FriendlyOperation.destruct_apply_eq_unfold` / 定理 `FriendlyOperation.destruct_apply_eq_unfold`

English:
theorem FriendlyOperation.destruct_apply_eq_unfold
  statement: {op : Seq α -> Seq α} (h : FriendlyOperation op)
  proof: by
  unfold unfold
  cases s with
  | nil =>
    generalize op nil = t
    cases t <;> simp
  | cons s_hd s_tl =>
    simp only [Seq.tail_cons, Seq.head_cons]
    generalize ht0 : op (.cons s_hd nil) = t0 at *
    generalize ht : op (.cons s_hd s_tl) = t at *
    have : t0.head = t.head := by
      rw [← ht0]; rw [← ht]; rw [FriendlyOperation.op_cons_head_eq h]
    cases t0 with
    | nil =>
      cases t with
      | nil => simp
      | cons => simp at this
    | cons =>
      cases t with
      | nil => simp at this
      | cons => simp_all

中文:
定理 FriendlyOperation.destruct_apply_eq_unfold
  结论: {op : 序列 α -> 序列 α} (h : FriendlyOperation op)
  证明: by
  unfold unfold
  cases s with
  | nil =>
    generalize op nil = t
    cases t <;> simp
  | cons s_hd s_tl =>
    simp only [Seq.tail_cons, Seq.head_cons]
    generalize ht0 : op (.cons s_hd nil) = t0 at *
    generalize ht : op (.cons s_hd s_tl) = t at *
    have : t0.head = t.head := by
      rw [← ht0]; rw [← ht]; rw [FriendlyOperation.op_cons_head_eq h]
    cases t0 with
    | nil =>
      cases t with
      | nil => simp
      | cons => simp at this
    | cons =>
      cases t with
      | nil => simp at this
      | cons => simp_all

Depends on / 依赖: FriendlyOperation, FriendlyOperation.op_cons_head_eq, Seq.head_cons, Seq.tail_cons, generalize, head_cons, op_cons_head_eq, s_hd, s_tl, t.head, t0.head, tail_cons
-/
theorem FriendlyOperation.destruct_apply_eq_unfold {op : Seq α -> Seq α} (h : FriendlyOperation op)
    {s : Seq α} :
    destruct (op s) = (h.unfold s.head).map (fun (hd, op') => (hd, op'.val s.tail)) := by
  unfold unfold
  cases s with
  | nil =>
    generalize op nil = t
    cases t <;> simp
  | cons s_hd s_tl =>
    simp only [Seq.tail_cons, Seq.head_cons]
    generalize ht0 : op (.cons s_hd nil) = t0 at *
    generalize ht : op (.cons s_hd s_tl) = t at *
    have : t0.head = t.head := by
      rw [← ht0]; rw [← ht]; rw [FriendlyOperation.op_cons_head_eq h]
    cases t0 with
    | nil =>
      cases t with
      | nil => simp
      | cons => simp at this
    | cons =>
      cases t with
      | nil => simp at this
      | cons => simp_all

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FriendlyOperation.op_head_eq` / 定理 `FriendlyOperation.op_head_eq`

English:
theorem FriendlyOperation.op_head_eq
  statement: {op : Seq α -> Seq α} (h : FriendlyOperation op) {s t : Seq α}
  proof: by
  simp only [head_eq_destruct, Option.map_eq_map, h.destruct_apply_eq_unfold, Option.map_map]
    at h_head ⊢
  simp [h_head]
  rfl

中文:
定理 FriendlyOperation.op_head_eq
  结论: {op : 序列 α -> 序列 α} (h : FriendlyOperation op) {s t : 序列 α}
  证明: by
  simp only [head_eq_destruct, Option.map_eq_map, h.destruct_apply_eq_unfold, Option.map_map]
    at h_head ⊢
  simp [h_head]
  rfl

Depends on / 依赖: Option.map_eq_map, Option.map_map, destruct_apply_eq_unfold, h.destruct_apply_eq_unfold, h_head, head_eq_destruct, map_eq_map, map_map
-/
theorem FriendlyOperation.op_head_eq {op : Seq α -> Seq α} (h : FriendlyOperation op) {s t : Seq α}
    (h_head : s.head = t.head) : (op s).head = (op t).head := by
  simp only [head_eq_destruct, Option.map_eq_map, h.destruct_apply_eq_unfold, Option.map_map]
    at h_head ⊢
  simp [h_head]
  rfl

/--
theorem `FriendlyOperation.of_dist_le_pow` / 定理 `FriendlyOperation.of_dist_le_pow`

English:
theorem FriendlyOperation.of_dist_le_pow
  statement: {op : Seq α -> Seq α}
  proof: by
  rw [friendlyOperation_iff_dist_le_dist]
  intro s t
  by_cases hst : s = t
  · simp [hst]
  obtain ⟨n, hst⟩ := dist_eq_two_inv_pow hst
  grind

中文:
定理 FriendlyOperation.of_dist_le_pow
  结论: {op : 序列 α -> 序列 α}
  证明: by
  rw [friendlyOperation_iff_dist_le_dist]
  intro s t
  by_cases hst : s = t
  · simp [hst]
  obtain ⟨n, hst⟩ := dist_eq_two_inv_pow hst
  grind

Depends on / 依赖: dist_eq_two_inv_pow, friendlyOperation_iff_dist_le_dist
-/
theorem FriendlyOperation.of_dist_le_pow {op : Seq α -> Seq α}
    (h : forall s t n, dist s t <= (2⁻¹ : Real) ^ n -> dist (op s) (op t) <= (2⁻¹ : Real) ^ n) :
    FriendlyOperation op := by
  rw [friendlyOperation_iff_dist_le_dist]
  intro s t
  by_cases hst : s = t
  · simp [hst]
  obtain ⟨n, hst⟩ := dist_eq_two_inv_pow hst
  grind

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `FriendlyOperation.coind` / 定理 `FriendlyOperation.coind`

English:
theorem FriendlyOperation.coind
  statement: (motive : (Seq α -> Seq α) -> Prop)
  proof: by
  apply of_dist_le_pow
  intro s t n hn
  induction n generalizing op s t with
  | zero => simp
  | succ n ih =>
    obtain ⟨T, hT⟩ := h_step _ h_base
    have h_head : s.head = t.head := by
      replace hn : dist s t <= 2⁻¹ := by
        apply hn.trans
        simp only [pow_succ, inv_pos, Nat.ofNat_pos, mul_le_iff_le_one_left]
        apply pow_le_one₀ <;> norm_num
      rw [dist_le_half_iff] at hn
      obtain ⟨rfl, rfl⟩ | ⟨hd, s_tl, t_tl, rfl, rfl⟩ := hn <;> rfl
    have hs := hT s
    have ht := hT t
    cases hT_head : T s.head with
    | none =>
      simp only [hT_head, Option.map_none, ← h_head] at hs ht
      simp [hs, ht, destruct_eq_none]
    | some v =>
      obtain ⟨hd, op', h_next⟩ := v
      simp only [hT_head, Option.map_some, ← h_head] at hs ht
      simp only [destruct_eq_cons hs, destruct_eq_cons ht, dist_cons_cons, pow_succ', inv_pos,
        Nat.ofNat_pos, mul_le_mul_iff_right₀, ge_iff_le]
      apply ih h_next
      simpa [dist_eq_half_of_head h_head, pow_succ'] using hn

中文:
定理 FriendlyOperation.coind
  结论: (motive : (序列 α -> 序列 α) -> 命题)
  证明: by
  apply of_dist_le_pow
  intro s t n hn
  induction n generalizing op s t with
  | zero => simp
  | succ n ih =>
    obtain ⟨T, hT⟩ := h_step _ h_base
    have h_head : s.head = t.head := by
      replace hn : dist s t <= 2⁻¹ := by
        apply hn.trans
        simp only [pow_succ, inv_pos, Nat.ofNat_pos, mul_le_iff_le_one_left]
        apply pow_le_one₀ <;> norm_num
      rw [dist_le_half_iff] at hn
      obtain ⟨rfl, rfl⟩ | ⟨hd, s_tl, t_tl, rfl, rfl⟩ := hn <;> rfl
    have hs := hT s
    have ht := hT t
    cases hT_head : T s.head with
    | none =>
      simp only [hT_head, Option.map_none, ← h_head] at hs ht
      simp [hs, ht, destruct_eq_none]
    | some v =>
      obtain ⟨hd, op', h_next⟩ := v
      simp only [hT_head, Option.map_some, ← h_head] at hs ht
      simp only [destruct_eq_cons hs, destruct_eq_cons ht, dist_cons_cons, pow_succ', inv_pos,
        Nat.ofNat_pos, mul_le_mul_iff_right₀, ge_iff_le]
      apply ih h_next
      simpa [dist_eq_half_of_head h_head, pow_succ'] using hn

Depends on / 依赖: Nat.ofNat_pos, dist_le_half_iff, generalizing, hT_head, h_base, h_head, h_step, hn.trans, inv_pos, mul_le_iff_le_one_left, ofNat_pos, of_dist_le_pow, pow_succ, replace, s.head, s_tl, t.head, t_tl
-/
theorem FriendlyOperation.coind (motive : (Seq α -> Seq α) -> Prop)
    {op : Seq α -> Seq α}
    (h_base : motive op)
    (h_step : forall op, motive op -> exists T : Option α -> Option (α × Subtype motive),
      forall s, (op s).destruct = (T s.head).map (fun (hd, op') => (hd, op'.val s.tail))) :
    FriendlyOperation op := by
  apply of_dist_le_pow
  intro s t n hn
  induction n generalizing op s t with
  | zero => simp
  | succ n ih =>
    obtain ⟨T, hT⟩ := h_step _ h_base
    have h_head : s.head = t.head := by
      replace hn : dist s t <= 2⁻¹ := by
        apply hn.trans
        simp only [pow_succ, inv_pos, Nat.ofNat_pos, mul_le_iff_le_one_left]
        apply pow_le_one₀ <;> norm_num
      rw [dist_le_half_iff] at hn
      obtain ⟨rfl, rfl⟩ | ⟨hd, s_tl, t_tl, rfl, rfl⟩ := hn <;> rfl
    have hs := hT s
    have ht := hT t
    cases hT_head : T s.head with
    | none =>
      simp only [hT_head, Option.map_none, ← h_head] at hs ht
      simp [hs, ht, destruct_eq_none]
    | some v =>
      obtain ⟨hd, op', h_next⟩ := v
      simp only [hT_head, Option.map_some, ← h_head] at hs ht
      simp only [destruct_eq_cons hs, destruct_eq_cons ht, dist_cons_cons, pow_succ', inv_pos,
        Nat.ofNat_pos, mul_le_mul_iff_right₀, ge_iff_le]
      apply ih h_next
      simpa [dist_eq_half_of_head h_head, pow_succ'] using hn

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FriendlyOperation.coind_comp_friend_left` / 定理 `FriendlyOperation.coind_comp_friend_left`

English:
theorem FriendlyOperation.coind_comp_friend_left
  statement: {op : Seq α -> Seq α}
  proof: by
  let motive' (op : Seq α -> Seq α) : Prop :=
    exists opf op', op = opf ∘ op' ∧ FriendlyOperation opf ∧ motive op'
  apply FriendlyOperation.coind motive'
  · exact ⟨_root_.id, op, rfl, FriendlyOperation.id, h_base⟩
  rintro _ ⟨opf, op, rfl, h_opf, h_op⟩
  obtain ⟨T, hT⟩ := h_step _ h_op
  use fun hd? =>
    match (T hd?) with
    | none => (h_opf.unfold none).map fun (hd, opf') =>
      (hd, ⟨_, fun _ => opf'.val nil, op, rfl, FriendlyOperation.const, h_op⟩)
    | some (hd, opf', op') => (h_opf.unfold (some hd)).map fun (hd', opf'') =>
      (hd', ⟨_, opf''.val ∘ opf'.val, op'.val, rfl,
        FriendlyOperation.comp opf''.prop opf'.prop, op'.prop⟩)
  intro s
  specialize hT s
  simp only [Function.comp_apply]
  generalize op s = s' at *
  cases s' with
  | nil =>
    symm at hT
    simp at hT
    simp [hT, destruct_apply_eq_unfold h_opf]
    rfl
  | cons s_hd s_tl =>
    simp only [destruct_cons] at hT
    simp only [destruct_apply_eq_unfold h_opf, Seq.tail_cons, Seq.head_cons]
    generalize T s.head = t? at *
    cases t? with
    | none => simp at hT
    | some v =>
      obtain ⟨hd, opf', op'⟩ := v
      simp at hT
      simp [hT]
      rfl

中文:
定理 FriendlyOperation.coind_comp_friend_left
  结论: {op : 序列 α -> 序列 α}
  证明: by
  let motive' (op : Seq α -> Seq α) : Prop :=
    exists opf op', op = opf ∘ op' ∧ FriendlyOperation opf ∧ motive op'
  apply FriendlyOperation.coind motive'
  · exact ⟨_root_.id, op, rfl, FriendlyOperation.id, h_base⟩
  rintro _ ⟨opf, op, rfl, h_opf, h_op⟩
  obtain ⟨T, hT⟩ := h_step _ h_op
  use fun hd? =>
    match (T hd?) with
    | none => (h_opf.unfold none).map fun (hd, opf') =>
      (hd, ⟨_, fun _ => opf'.val nil, op, rfl, FriendlyOperation.const, h_op⟩)
    | some (hd, opf', op') => (h_opf.unfold (some hd)).map fun (hd', opf'') =>
      (hd', ⟨_, opf''.val ∘ opf'.val, op'.val, rfl,
        FriendlyOperation.comp opf''.prop opf'.prop, op'.prop⟩)
  intro s
  specialize hT s
  simp only [Function.comp_apply]
  generalize op s = s' at *
  cases s' with
  | nil =>
    symm at hT
    simp at hT
    simp [hT, destruct_apply_eq_unfold h_opf]
    rfl
  | cons s_hd s_tl =>
    simp only [destruct_cons] at hT
    simp only [destruct_apply_eq_unfold h_opf, Seq.tail_cons, Seq.head_cons]
    generalize T s.head = t? at *
    cases t? with
    | none => simp at hT
    | some v =>
      obtain ⟨hd, opf', op'⟩ := v
      simp at hT
      simp [hT]
      rfl

Depends on / 依赖: FriendlyOperation, FriendlyOperation.coind, FriendlyOperation.const, FriendlyOperation.id, _root_, _root_.id, h_base, h_op, h_opf, h_opf.unfold, h_step, motive
-/
theorem FriendlyOperation.coind_comp_friend_left {op : Seq α -> Seq α}
    (motive : (Seq α -> Seq α) -> Prop)
    (h_base : motive op)
    (h_step : forall op, motive op ->
      exists T : Option α -> Option (α × Subtype FriendlyOperation × Subtype motive),
      forall s, (op s).destruct = (T s.head).map fun (hd, opf, op') => (hd, opf.val <| op'.val s.tail)) :
    FriendlyOperation op := by
  let motive' (op : Seq α -> Seq α) : Prop :=
    exists opf op', op = opf ∘ op' ∧ FriendlyOperation opf ∧ motive op'
  apply FriendlyOperation.coind motive'
  · exact ⟨_root_.id, op, rfl, FriendlyOperation.id, h_base⟩
  rintro _ ⟨opf, op, rfl, h_opf, h_op⟩
  obtain ⟨T, hT⟩ := h_step _ h_op
  use fun hd? =>
    match (T hd?) with
    | none => (h_opf.unfold none).map fun (hd, opf') =>
      (hd, ⟨_, fun _ => opf'.val nil, op, rfl, FriendlyOperation.const, h_op⟩)
    | some (hd, opf', op') => (h_opf.unfold (some hd)).map fun (hd', opf'') =>
      (hd', ⟨_, opf''.val ∘ opf'.val, op'.val, rfl,
        FriendlyOperation.comp opf''.prop opf'.prop, op'.prop⟩)
  intro s
  specialize hT s
  simp only [Function.comp_apply]
  generalize op s = s' at *
  cases s' with
  | nil =>
    symm at hT
    simp at hT
    simp [hT, destruct_apply_eq_unfold h_opf]
    rfl
  | cons s_hd s_tl =>
    simp only [destruct_cons] at hT
    simp only [destruct_apply_eq_unfold h_opf, Seq.tail_cons, Seq.head_cons]
    generalize T s.head = t? at *
    cases t? with
    | none => simp at hT
    | some v =>
      obtain ⟨hd, opf', op'⟩ := v
      simp at hT
      simp [hT]
      rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FriendlyOperation.coind_comp_friend_right` / 定理 `FriendlyOperation.coind_comp_friend_right`

English:
theorem FriendlyOperation.coind_comp_friend_right
  statement: {op : Seq α -> Seq α}
  proof: by
  let motive' (op : Seq α -> Seq α) : Prop :=
    exists opf op', op = op' ∘ opf ∧ FriendlyOperation opf ∧ motive op'
  apply FriendlyOperation.coind motive'
  · exact ⟨_root_.id, op, rfl, FriendlyOperation.id, h_base⟩
  clear h_base op
  rintro _ ⟨opf, op, rfl, h_opf, h_op⟩
  obtain ⟨T, hT⟩ := h_step _ h_op
  use fun hd? =>
    match (h_opf.unfold hd?) with
    | none => (T none).map fun (hd, opf', op') =>
      (hd, ⟨_, fun _ => opf'.val nil, op', rfl, FriendlyOperation.const, op'.prop⟩)
    | some (hd, opf') => (T (some hd)).map fun (hd', opf'', op') =>
      (hd', ⟨_, opf''.val ∘ opf'.val, op'.val, rfl,
        FriendlyOperation.comp opf''.prop opf'.prop, op'.prop⟩)
  intro s
  simp only [Function.comp_apply]
  have hF := h_opf.destruct_apply_eq_unfold (s := s)
  generalize opf s = s' at *
  cases s' with
  | nil =>
    symm at hF
    simp only [destruct_nil, Option.map_eq_none_iff] at hF
    simp only [hF, Option.map_map]
    specialize hT nil
    simp only [tail_nil, head_nil] at hT
    simp [hT]
    rfl
  | cons s_hd s_tl =>
  simp only [destruct_cons] at hF
  generalize h_opf.unfold s.head = t? at *
  cases t? with
  | none => simp at hF
  | some v =>
  obtain ⟨hd, opf', op'⟩ := v
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hF
  simp only [hF, Option.map_map]
  rw [hT]
  rfl

中文:
定理 FriendlyOperation.coind_comp_friend_right
  结论: {op : 序列 α -> 序列 α}
  证明: by
  let motive' (op : Seq α -> Seq α) : Prop :=
    exists opf op', op = op' ∘ opf ∧ FriendlyOperation opf ∧ motive op'
  apply FriendlyOperation.coind motive'
  · exact ⟨_root_.id, op, rfl, FriendlyOperation.id, h_base⟩
  clear h_base op
  rintro _ ⟨opf, op, rfl, h_opf, h_op⟩
  obtain ⟨T, hT⟩ := h_step _ h_op
  use fun hd? =>
    match (h_opf.unfold hd?) with
    | none => (T none).map fun (hd, opf', op') =>
      (hd, ⟨_, fun _ => opf'.val nil, op', rfl, FriendlyOperation.const, op'.prop⟩)
    | some (hd, opf') => (T (some hd)).map fun (hd', opf'', op') =>
      (hd', ⟨_, opf''.val ∘ opf'.val, op'.val, rfl,
        FriendlyOperation.comp opf''.prop opf'.prop, op'.prop⟩)
  intro s
  simp only [Function.comp_apply]
  have hF := h_opf.destruct_apply_eq_unfold (s := s)
  generalize opf s = s' at *
  cases s' with
  | nil =>
    symm at hF
    simp only [destruct_nil, Option.map_eq_none_iff] at hF
    simp only [hF, Option.map_map]
    specialize hT nil
    simp only [tail_nil, head_nil] at hT
    simp [hT]
    rfl
  | cons s_hd s_tl =>
  simp only [destruct_cons] at hF
  generalize h_opf.unfold s.head = t? at *
  cases t? with
  | none => simp at hF
  | some v =>
  obtain ⟨hd, opf', op'⟩ := v
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hF
  simp only [hF, Option.map_map]
  rw [hT]
  rfl

Depends on / 依赖: FriendlyOperation, FriendlyOperation.coind, FriendlyOperation.const, FriendlyOperation.id, _root_, _root_.id, h_base, h_op, h_opf, h_opf.unfold, h_step, motive
-/
theorem FriendlyOperation.coind_comp_friend_right {op : Seq α -> Seq α}
    (motive : (Seq α -> Seq α) -> Prop)
    (h_base : motive op)
    (h_step : forall op, motive op ->
      exists T : Option α -> Option (α × Subtype FriendlyOperation × Subtype motive),
      forall s, (op s).destruct = (T s.head).map fun (hd, opf, op') => (hd, op'.val <| opf.val s.tail)) :
    FriendlyOperation op := by
  let motive' (op : Seq α -> Seq α) : Prop :=
    exists opf op', op = op' ∘ opf ∧ FriendlyOperation opf ∧ motive op'
  apply FriendlyOperation.coind motive'
  · exact ⟨_root_.id, op, rfl, FriendlyOperation.id, h_base⟩
  clear h_base op
  rintro _ ⟨opf, op, rfl, h_opf, h_op⟩
  obtain ⟨T, hT⟩ := h_step _ h_op
  use fun hd? =>
    match (h_opf.unfold hd?) with
    | none => (T none).map fun (hd, opf', op') =>
      (hd, ⟨_, fun _ => opf'.val nil, op', rfl, FriendlyOperation.const, op'.prop⟩)
    | some (hd, opf') => (T (some hd)).map fun (hd', opf'', op') =>
      (hd', ⟨_, opf''.val ∘ opf'.val, op'.val, rfl,
        FriendlyOperation.comp opf''.prop opf'.prop, op'.prop⟩)
  intro s
  simp only [Function.comp_apply]
  have hF := h_opf.destruct_apply_eq_unfold (s := s)
  generalize opf s = s' at *
  cases s' with
  | nil =>
    symm at hF
    simp only [destruct_nil, Option.map_eq_none_iff] at hF
    simp only [hF, Option.map_map]
    specialize hT nil
    simp only [tail_nil, head_nil] at hT
    simp [hT]
    rfl
  | cons s_hd s_tl =>
  simp only [destruct_cons] at hF
  generalize h_opf.unfold s.head = t? at *
  cases t? with
  | none => simp at hF
  | some v =>
  obtain ⟨hd, opf', op'⟩ := v
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hF
  simp only [hF, Option.map_map]
  rw [hT]
  rfl

/--
theorem `FriendlyOperationClass.eq_of_bisim` / 定理 `FriendlyOperationClass.eq_of_bisim`

English:
theorem FriendlyOperationClass.eq_of_bisim
  statement: {s t : Seq α} {op : γ -> Seq α -> Seq α}
  proof: by
  suffices dist s t = 0 by simpa using this
  suffices forall n, dist s t <= (2⁻¹ : Real) ^ n by
    apply eq_of_le_of_ge
    · apply ge_of_tendsto' (x := Filter.atTop) _ this
      rw [tendsto_pow_atTop_nhds_zero_iff]
      norm_num
    · simp
  intro n
  induction n generalizing s t with
  | zero => simp
  | succ n ih =>
    obtain step | ⟨hd, u, v, c, rfl, rfl, h_next⟩ := step s t base
    · simp [step]
    simp only [dist_cons_cons]
    specialize ih h_next
    calc
      _ <= 2⁻¹ * dist u v := by
        gcongr
        exact (FriendlyOperationClass.friend _).dist_le
      _ <= _ := by
        grw [ih, pow_succ']

中文:
定理 FriendlyOperation类.eq_of_bisim
  结论: {s t : 序列 α} {op : γ -> 序列 α -> 序列 α}
  证明: by
  suffices dist s t = 0 by simpa using this
  suffices forall n, dist s t <= (2⁻¹ : Real) ^ n by
    apply eq_of_le_of_ge
    · apply ge_of_tendsto' (x := Filter.atTop) _ this
      rw [tendsto_pow_atTop_nhds_zero_iff]
      norm_num
    · simp
  intro n
  induction n generalizing s t with
  | zero => simp
  | succ n ih =>
    obtain step | ⟨hd, u, v, c, rfl, rfl, h_next⟩ := step s t base
    · simp [step]
    simp only [dist_cons_cons]
    specialize ih h_next
    calc
      _ <= 2⁻¹ * dist u v := by
        gcongr
        exact (FriendlyOperationClass.friend _).dist_le
      _ <= _ := by
        grw [ih, pow_succ']

Depends on / 依赖: Filter, Filter.atTop, FriendlyOperationClass, FriendlyOperationClass.friend, dist_, dist_cons_cons, eq_of_le_of_ge, friend, ge_of_tendsto, generalizing, h_next, specialize, tendsto_pow_atTop_nhds_zero_iff
-/
theorem FriendlyOperationClass.eq_of_bisim {s t : Seq α} {op : γ -> Seq α -> Seq α}
    [FriendlyOperationClass op]
    (motive : Seq α -> Seq α -> Prop)
    (base : motive s t)
    (step : forall u v, motive u v -> (u = v) ∨
      exists hd u' v' c, u = cons hd (op c u') ∧ v = cons hd (op c v') ∧
        motive u' v') :
    s = t := by
  suffices dist s t = 0 by simpa using this
  suffices forall n, dist s t <= (2⁻¹ : Real) ^ n by
    apply eq_of_le_of_ge
    · apply ge_of_tendsto' (x := Filter.atTop) _ this
      rw [tendsto_pow_atTop_nhds_zero_iff]
      norm_num
    · simp
  intro n
  induction n generalizing s t with
  | zero => simp
  | succ n ih =>
    obtain step | ⟨hd, u, v, c, rfl, rfl, h_next⟩ := step s t base
    · simp [step]
    simp only [dist_cons_cons]
    specialize ih h_next
    calc
      _ <= 2⁻¹ * dist u v := by
        gcongr
        exact (FriendlyOperationClass.friend _).dist_le
      _ <= _ := by
        grw [ih, pow_succ']

end Tactic.ComputeAsymptotics.Seq
