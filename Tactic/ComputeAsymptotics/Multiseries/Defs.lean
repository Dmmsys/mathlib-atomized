/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.Seq.Basic
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Majorized
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Corecursion

/-!

# Multiseries definitions

In this file, we define the multiseries and its main properties: sortedness and approximation.
A multiseries in a basis `[b₁, ..., bₙ]` represents a multivariate series:
it is a formal series made from monomials `b₁ ^ e₁ * ... * bₙ ^ eₙ` where `e₁, ..., eₙ` are real
numbers. We treat multivariate series in a basis `[b₁, ..., bₙ]` as a univariate series in the
variable `b₁` (`basis_hd`) with coefficients being multiseries
in the basis `[b₂, ..., bₙ]` (`basis_tl`).

## Main definitions

* `Basis` is the list of functions used to construct monomials in multiseries.
* `Multiseries basis_hd basis_tl` is the type of multiseries in a basis `basis_hd :: basis_tl`.
* `MultiseriesExpansion basis` is a multiseries expansion of some function `f : ℝ → ℝ`.
  If `basis = []`, then the multiseries represents a constant function, otherwise it is
  a pair of a multiseries `ms : Multiseries basis_hd basis_tl` and a function `f : ℝ → ℝ`.
* `Multiseries.Sorted ms` means that at each level of `ms` as a nested tree all exponents are
  strictly decreasing.
* `MultiseriesExpansion.Approximates ms` means that the multiseries `ms` can be used to obtain
  an asymptotical approximation of its attached function.

## Implementation details

* `Multiseries basis_hd basis_tl` is defined as a `Seq (ℝ × MultiseriesExpansion basis_tl)`, so
  we need to port some `Seq` API to `Multiseries`.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Filter Stream' Topology

/--
Definition of `Basis` / `Basis` 的定义

English:
abbreviation Basis
  body: List (Real -> Real)

中文:
缩写 Basis
  定义体: List (Real -> Real)
-/
abbrev Basis := List (Real -> Real)

/--
Definition of `MultiseriesExpansion` / `MultiseriesExpansion` 的定义

English:
definition MultiseriesExpansion
  signature: (basis : Basis)
  body: match basis with
  | [] => Real
  | .cons _ basis_tl => Seq (Real × MultiseriesExpansion basis_tl) × (Real -> Real)

中文:
定义 MultiseriesExpansion
  签名: (basis : Basis)
  定义体: match basis with
  | [] => Real
  | .cons _ basis_tl => Seq (Real × MultiseriesExpansion basis_tl) × (Real -> Real)

Depends on / 依赖: MultiseriesExpansion, basis_tl
-/
def MultiseriesExpansion (basis : Basis) : Type :=
  match basis with
  | [] => Real
  | .cons _ basis_tl => Seq (Real × MultiseriesExpansion basis_tl) × (Real -> Real)

namespace MultiseriesExpansion

set_option linter.unusedVariables false in
/-- Multiseries in a basis `basis_hd :: basis_tl`. It is a generalisation of asymptotic expansions.
A multiseries in a basis `[b₁, ..., bₙ]` is a formal series made from monomials
`b₁ ^ e₁ * ... * bₙ ^ eₙ` where `e₁, ..., eₙ` are real numbers. We treat multivariate series in
a basis `[b₁, ..., bₙ]` as a univariate series in the variable `b₁` (`basis_hd`) with coefficients
being multiseries in the basis `[b₂, ..., bₙ]` (`basis_tl`). We represent such a series as a lazy
list (`Seq`) of pairs `(exp, coef)` where `exp` is the exponent of `b₁` and `coef` is the
coefficient (a multiseries in `basis_tl`).

`MultiseriesExpansion` is a `Multiseries` with an attached real function.
-/
@[nolint unusedArguments]
/--
Definition of `Multiseries` / `Multiseries` 的定义

English:
definition Multiseries
  signature: (basis_hd : Real -> Real) (basis_tl : Basis)
  body: Seq (Real × MultiseriesExpansion basis_tl)

中文:
定义 Multiseries
  签名: (basis_hd : 实数 -> 实数) (basis_tl : Basis)
  定义体: Seq (Real × MultiseriesExpansion basis_tl)

Depends on / 依赖: MultiseriesExpansion, basis_tl
-/
def Multiseries (basis_hd : Real -> Real) (basis_tl : Basis) : Type :=
  Seq (Real × MultiseriesExpansion basis_tl)

namespace Multiseries

/--
Definition of `toSeq` / `toSeq` 的定义

English:
definition toSeq
  signature: {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl)
  body: ms

中文:
定义 toSeq
  签名: {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl)
  定义体: ms
-/
def toSeq {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Seq (Real × MultiseriesExpansion basis_tl) :=
  ms

/--
Definition of `nil` / `nil` 的定义

English:
definition nil
  signature: {basis_hd basis_tl}
  body: Seq.nil

中文:
定义 nil
  签名: {basis_hd basis_tl}
  定义体: Seq.nil

Depends on / 依赖: Seq.nil
-/
def nil {basis_hd basis_tl} : Multiseries basis_hd basis_tl := Seq.nil

/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: {basis_hd basis_tl} (exp : Real) (coef : MultiseriesExpansion basis_tl)
  body: Seq.cons (exp, coef) tl

中文:
定义 cons
  签名: {basis_hd basis_tl} (exp : 实数) (coef : MultiseriesExpansion basis_tl)
  定义体: Seq.cons (exp, coef) tl

Depends on / 依赖: Seq.cons
-/
def cons {basis_hd basis_tl} (exp : Real) (coef : MultiseriesExpansion basis_tl)
    (tl : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd basis_tl :=
  Seq.cons (exp, coef) tl

/-- Recursion principle for `Multiseries basis_hd basis_tl`. It is equivalent to
`Stream'.Seq.recOn` but provides some convenience. -/
@[cases_eliminator]
/--
Definition of `recOn` / `recOn` 的定义

English:
definition recOn
  signature: {basis_hd basis_tl} {motive : Multiseries basis_hd basis_tl -> Sort*}
  body: Stream'.Seq.recOn _ nil fun _ _ => cons _ _ _

中文:
定义 recOn
  签名: {basis_hd basis_tl} {motive : Multiseries basis_hd basis_tl -> Sort*}
  定义体: Stream'.Seq.recOn _ nil fun _ _ => cons _ _ _

Depends on / 依赖: Seq.recOn, Stream
-/
def recOn {basis_hd basis_tl} {motive : Multiseries basis_hd basis_tl -> Sort*}
    (ms : Multiseries basis_hd basis_tl) (nil : motive nil)
    (cons : forall exp coef (tl : Multiseries basis_hd basis_tl), motive (cons exp coef tl)) :
    motive ms := Stream'.Seq.recOn _ nil fun _ _ => cons _ _ _

/--
Definition of `destruct` / `destruct` 的定义

English:
definition destruct
  signature: {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl)
  body: (Seq.destruct ms).map (fun ((exp, coef), tl) => (exp, coef, tl))

中文:
定义 destruct
  签名: {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl)
  定义体: (Seq.destruct ms).map (fun ((exp, coef), tl) => (exp, coef, tl))

Depends on / 依赖: Seq.destruct, destruct
-/
def destruct {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Option (Real × MultiseriesExpansion basis_tl × Multiseries basis_hd basis_tl) :=
  (Seq.destruct ms).map (fun ((exp, coef), tl) => (exp, coef, tl))

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl)
  body: Seq.head ms

中文:
定义 head
  签名: {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl)
  定义体: Seq.head ms

Depends on / 依赖: Seq.head
-/
def head {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Option (Real × MultiseriesExpansion basis_tl) :=
  Seq.head ms

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl)
  body: Seq.tail ms

中文:
定义 tail
  签名: {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl)
  定义体: Seq.tail ms

Depends on / 依赖: Seq.tail
-/
def tail {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) : Multiseries basis_hd basis_tl :=
  Seq.tail ms

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {basis_hd basis_tl basis_hd' basis_tl'} (f : Real -> Real)
  body: Seq.map (fun (exp, coef) => (f exp, g coef)) ms

中文:
定义 map
  签名: {basis_hd basis_tl basis_hd' basis_tl'} (f : 实数 -> 实数)
  定义体: Seq.map (fun (exp, coef) => (f exp, g coef)) ms

Depends on / 依赖: Seq.map
-/
def map {basis_hd basis_tl basis_hd' basis_tl'} (f : Real -> Real)
    (g : MultiseriesExpansion basis_tl -> MultiseriesExpansion basis_tl')
    (ms : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd' basis_tl' :=
  Seq.map (fun (exp, coef) => (f exp, g coef)) ms

/--
Definition of `corec` / `corec` 的定义

English:
definition corec
  signature: {β : Type*} {basis_hd} {basis_tl}
  body: Seq.corec (fun a => (f a).map (fun (exp, coef, next) => ((exp, coef), next))) b

中文:
定义 corec
  签名: {β : 类型} {basis_hd} {basis_tl}
  定义体: Seq.corec (fun a => (f a).map (fun (exp, coef, next) => ((exp, coef), next))) b

Depends on / 依赖: Seq.corec
-/
def corec {β : Type*} {basis_hd} {basis_tl}
    (f : β -> Option (Real × MultiseriesExpansion basis_tl × β)) (b : β) :
    Multiseries basis_hd basis_tl :=
  Seq.corec (fun a => (f a).map (fun (exp, coef, next) => ((exp, coef), next))) b

/--
Definition of `FriendlyOperation` / `FriendlyOperation` 的定义

English:
definition FriendlyOperation
  signature: {basis_hd basis_tl}
  body: Seq.FriendlyOperation op

中文:
定义 FriendlyOperation
  签名: {basis_hd basis_tl}
  定义体: Seq.FriendlyOperation op

Depends on / 依赖: FriendlyOperation, Seq.FriendlyOperation
-/
def FriendlyOperation {basis_hd basis_tl}
    (op : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl) : Prop :=
  Seq.FriendlyOperation op

/--
Definition of `FriendlyOperationClass` / `FriendlyOperationClass` 的定义

English:
class FriendlyOperationClass
  parameters: {basis_hd basis_tl} {γ : Type*}
  extends: Seq.FriendlyOperationClass op
  (no additional axioms)

中文:
类 FriendlyOperationClass
  参数: {basis_hd basis_tl} {γ : 类型}
  继承: Seq.FriendlyOperationClass op
  (无附加公理)
-/
class FriendlyOperationClass {basis_hd basis_tl} {γ : Type*}
    (op : γ -> Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl) : Prop
    extends Seq.FriendlyOperationClass op

/--
theorem `FriendlyOperationClass.mk'` / 定理 `FriendlyOperationClass.mk'`

English:
theorem FriendlyOperationClass.mk'
  statement: {basis_hd basis_tl} {γ : Type*}
  proof: by
  suffices Seq.FriendlyOperationClass op by constructor
  exact ⟨h⟩

中文:
定理 FriendlyOperationClass.mk'
  结论: {basis_hd basis_tl} {γ : 类型}
  证明: by
  suffices Seq.FriendlyOperationClass op by constructor
  exact ⟨h⟩

Depends on / 依赖: FriendlyOperationClass, Seq.FriendlyOperationClass
-/
theorem FriendlyOperationClass.mk' {basis_hd basis_tl} {γ : Type*}
    {op : γ -> Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    (h : forall c, FriendlyOperation (op c)) :
    FriendlyOperationClass op := by
  suffices Seq.FriendlyOperationClass op by constructor
  exact ⟨h⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `destruct_eq_destruct_map` / 引理 `destruct_eq_destruct_map`

English:
lemma destruct_eq_destruct_map
  statement: {basis_hd basis_tl}
  proof: by
  simp only [destruct, Option.map_map]
  exact Option.map_id_apply.symm

中文:
引理 destruct_eq_destruct_map
  结论: {basis_hd basis_tl}
  证明: by
  simp only [destruct, Option.map_map]
  exact Option.map_id_apply.symm
-/
private lemma destruct_eq_destruct_map {basis_hd basis_tl}
    (s : Stream'.Seq (Real × MultiseriesExpansion basis_tl)) :
    s.destruct = (Multiseries.destruct (basis_hd := basis_hd) s).map
      (fun (exp, coef, tl) => ((exp, coef), tl)) := by
  simp only [destruct, Option.map_map]
  exact Option.map_id_apply.symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FriendlyOperation.coind_comp_friend_left` / 定理 `FriendlyOperation.coind_comp_friend_left`

English:
theorem FriendlyOperation.coind_comp_friend_left
  statement: {basis_hd basis_tl}
  proof: by
  refine Seq.FriendlyOperation.coind_comp_friend_left motive h_base (fun op h_op => ?_)
  obtain ⟨T, hT⟩ := h_step op h_op
  use fun hd? => (T hd?).map (fun (exp, coef, opf, op') => ((exp, coef), opf, op'))
  intro s
  rw [destruct_eq_destruct_map]; rw [hT s]
  simp
  rfl

中文:
定理 FriendlyOperation.coind_comp_friend_left
  结论: {basis_hd basis_tl}
  证明: by
  refine Seq.FriendlyOperation.coind_comp_friend_left motive h_base (fun op h_op => ?_)
  obtain ⟨T, hT⟩ := h_step op h_op
  use fun hd? => (T hd?).map (fun (exp, coef, opf, op') => ((exp, coef), opf, op'))
  intro s
  rw [destruct_eq_destruct_map]; rw [hT s]
  simp
  rfl
-/
theorem FriendlyOperation.coind_comp_friend_left {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    (motive : (Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl) -> Prop)
    (h_base : motive op)
    (h_step : forall op, motive op -> exists T : Option (Real × MultiseriesExpansion basis_tl) ->
        Option (Real × MultiseriesExpansion basis_tl × Subtype FriendlyOperation × Subtype motive),
      forall s, (op s).destruct =
        (T s.head).map (fun (exp, coef, opf, op') => (exp, coef, opf.val <| op'.val (s.tail)))) :
    FriendlyOperation op := by
  refine Seq.FriendlyOperation.coind_comp_friend_left motive h_base (fun op h_op => ?_)
  obtain ⟨T, hT⟩ := h_step op h_op
  use fun hd? => (T hd?).map (fun (exp, coef, opf, op') => ((exp, coef), opf, op'))
  intro s
  rw [destruct_eq_destruct_map]; rw [hT s]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FriendlyOperation.coind_comp_friend_right` / 定理 `FriendlyOperation.coind_comp_friend_right`

English:
theorem FriendlyOperation.coind_comp_friend_right
  statement: {basis_hd basis_tl}
  proof: by
  refine Seq.FriendlyOperation.coind_comp_friend_right motive h_base (fun op h_op => ?_)
  obtain ⟨T, hT⟩ := h_step op h_op
  use fun hd? => (T hd?).map (fun (exp, coef, opf, op') => ((exp, coef), opf, op'))
  intro s
  rw [destruct_eq_destruct_map]; rw [hT s]
  simp
  rfl

中文:
定理 FriendlyOperation.coind_comp_friend_right
  结论: {basis_hd basis_tl}
  证明: by
  refine Seq.FriendlyOperation.coind_comp_friend_right motive h_base (fun op h_op => ?_)
  obtain ⟨T, hT⟩ := h_step op h_op
  use fun hd? => (T hd?).map (fun (exp, coef, opf, op') => ((exp, coef), opf, op'))
  intro s
  rw [destruct_eq_destruct_map]; rw [hT s]
  simp
  rfl
-/
theorem FriendlyOperation.coind_comp_friend_right {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    (motive : (Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl) -> Prop)
    (h_base : motive op)
    (h_step : forall op, motive op -> exists T : Option (Real × MultiseriesExpansion basis_tl) ->
        Option (Real × MultiseriesExpansion basis_tl × Subtype FriendlyOperation × Subtype motive),
      forall s, (op s).destruct =
        (T s.head).map (fun (exp, coef, opf, op') => (exp, coef, op'.val <| opf.val (s.tail)))) :
    FriendlyOperation op := by
  refine Seq.FriendlyOperation.coind_comp_friend_right motive h_base (fun op h_op => ?_)
  obtain ⟨T, hT⟩ := h_step op h_op
  use fun hd? => (T hd?).map (fun (exp, coef, opf, op') => ((exp, coef), opf, op'))
  intro s
  rw [destruct_eq_destruct_map]; rw [hT s]
  simp
  rfl

/--
Definition of `gcorec` / `gcorec` 的定义

English:
definition gcorec
  signature: {β γ : Type*} {basis_hd} {basis_tl}
  body: Seq.gcorec (fun a => (F a).map (fun (exp, coef, c, next) => ((exp, coef), c, next))) op b

中文:
定义 gcorec
  签名: {β γ : 类型} {basis_hd} {basis_tl}
  定义体: Seq.gcorec (fun a => (F a).map (fun (exp, coef, c, next) => ((exp, coef), c, next))) op b

Depends on / 依赖: Seq.gcorec, gcorec
-/
noncomputable def gcorec {β γ : Type*} {basis_hd} {basis_tl}
    (F : β -> Option (Real × MultiseriesExpansion basis_tl × γ × β))
    (op : γ -> Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl)
    [FriendlyOperationClass op]
    (b : β) :
    Multiseries basis_hd basis_tl :=
  Seq.gcorec (fun a => (F a).map (fun (exp, coef, c, next) => ((exp, coef), c, next))) op b

instance (basis_hd basis_tl) : Inhabited (Multiseries basis_hd basis_tl) where
  default := (default : Seq (Real × MultiseriesExpansion basis_tl))

instance {basis_hd basis_tl} :
    Membership (Real × MultiseriesExpansion basis_tl) (Multiseries basis_hd basis_tl) where
  mem ms x := x in ms.toSeq

/--
theorem `eq_of_bisim` / 定理 `eq_of_bisim`

English:
theorem eq_of_bisim
  statement: {basis_hd : Real -> Real} {basis_tl : Basis} {x y : Multiseries basis_hd basis_tl}
  proof: Seq.eq_of_bisim' motive base (by grind [nil, cons])

中文:
定理 eq_of_bisim
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {x y : Multiseries basis_hd basis_tl}
  证明: Seq.eq_of_bisim' motive base (by grind [nil, cons])

Depends on / 依赖: Seq.eq_of_bisim, eq_of_bisim, motive
-/
theorem eq_of_bisim {basis_hd : Real -> Real} {basis_tl : Basis} {x y : Multiseries basis_hd basis_tl}
    (motive : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl -> Prop)
    (base : motive x y)
    (step : forall x y, motive x y -> (x = .nil ∧ y = .nil) ∨ exists exp coef,
      exists (x' y' : Multiseries basis_hd basis_tl),
      x = cons exp coef x' ∧ y = cons exp coef y' ∧ motive x' y') :
    x = y := Seq.eq_of_bisim' motive base (by grind [nil, cons])

/--
theorem `eq_of_bisim_strong` / 定理 `eq_of_bisim_strong`

English:
theorem eq_of_bisim_strong
  statement: {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: Seq.eq_of_bisim_strong motive base (by grind [nil, cons])

中文:
定理 eq_of_bisim_strong
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis}
  证明: Seq.eq_of_bisim_strong motive base (by grind [nil, cons])

Depends on / 依赖: Seq.eq_of_bisim_strong, eq_of_bisim_strong, motive
-/
theorem eq_of_bisim_strong {basis_hd : Real -> Real} {basis_tl : Basis}
    {x y : Multiseries basis_hd basis_tl}
    (motive : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl -> Prop)
    (base : motive x y)
    (step : forall x y, motive x y -> (x = y) ∨ exists exp coef,
      exists (x' y' : Multiseries basis_hd basis_tl),
      x = cons exp coef x' ∧ y = cons exp coef y' ∧ motive x' y') :
    x = y := Seq.eq_of_bisim_strong motive base (by grind [nil, cons])

/--
theorem `FriendlyOperationClass.FriendlyOperation` / 定理 `FriendlyOperationClass.FriendlyOperation`

English:
theorem FriendlyOperationClass.FriendlyOperation
  statement: {basis_hd basis_tl} {γ : Type*}
  proof: h.friend c

中文:
定理 FriendlyOperationClass.FriendlyOperation
  结论: {basis_hd basis_tl} {γ : 类型}
  证明: h.friend c

Depends on / 依赖: friend, h.friend
-/
theorem FriendlyOperationClass.FriendlyOperation {basis_hd basis_tl} {γ : Type*}
    {op : γ -> Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    [h : FriendlyOperationClass op]
    (c : γ) :
    FriendlyOperation (op c) :=
  h.friend c

/--
Definition of `FriendlyOperation.unfold` / `FriendlyOperation.unfold` 的定义

English:
definition FriendlyOperation.unfold
  signature: {basis_hd basis_tl}
  body: .map (fun ((exp, coef), op') => (exp, coef, op')) Seq.FriendlyOperation.unfold h hd?

中文:
定义 FriendlyOperation.unfold
  签名: {basis_hd basis_tl}
  定义体: .map (fun ((exp, coef), op') => (exp, coef, op')) Seq.FriendlyOperation.unfold h hd?
-/
def FriendlyOperation.unfold {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    (h : FriendlyOperation op) (hd? : Option (Real × MultiseriesExpansion basis_tl)) :
    Option (Real × MultiseriesExpansion basis_tl × Subtype (
      @Multiseries.FriendlyOperation basis_hd basis_tl)) :=
.map (fun ((exp, coef), op') => (exp, coef, op')) Seq.FriendlyOperation.unfold h hd?

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FriendlyOperation.destruct_apply_eq_unfold` / 定理 `FriendlyOperation.destruct_apply_eq_unfold`

English:
theorem FriendlyOperation.destruct_apply_eq_unfold
  statement: {basis_hd basis_tl}
  proof: by
  unfold Multiseries.destruct
  simp [Seq.FriendlyOperation.destruct_apply_eq_unfold h, FriendlyOperation.unfold, head]
  cases Seq.FriendlyOperation.unfold h (Seq.head ms) <;> rfl

中文:
定理 FriendlyOperation.destruct_apply_eq_unfold
  结论: {basis_hd basis_tl}
  证明: by
  unfold Multiseries.destruct
  simp [Seq.FriendlyOperation.destruct_apply_eq_unfold h, FriendlyOperation.unfold, head]
  cases Seq.FriendlyOperation.unfold h (Seq.head ms) <;> rfl
-/
theorem FriendlyOperation.destruct_apply_eq_unfold {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    (h : FriendlyOperation op) (ms : Multiseries basis_hd basis_tl) :
      destruct (op ms) = (h.unfold ms.head).map
        (fun (exp, coef, op') => (exp, coef, op'.val ms.tail)) := by
  unfold Multiseries.destruct
  simp [Seq.FriendlyOperation.destruct_apply_eq_unfold h, FriendlyOperation.unfold, head]
  cases Seq.FriendlyOperation.unfold h (Seq.head ms) <;> rfl

/--
theorem `FriendlyOperation.head_eq_head` / 定理 `FriendlyOperation.head_eq_head`

English:
theorem FriendlyOperation.head_eq_head
  statement: {basis_hd basis_tl}
  proof: Seq.FriendlyOperation.op_head_eq h h_head

中文:
定理 FriendlyOperation.head_eq_head
  结论: {basis_hd basis_tl}
  证明: Seq.FriendlyOperation.op_head_eq h h_head

Depends on / 依赖: FriendlyOperation, Seq.FriendlyOperation.op_head_eq, h_head, op_head_eq
-/
theorem FriendlyOperation.head_eq_head {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    (h : FriendlyOperation op) {x y : Multiseries basis_hd basis_tl}
    (h_head : x.head = y.head) : (op x).head = (op y).head :=
  Seq.FriendlyOperation.op_head_eq h h_head

/--
theorem `FriendlyOperation.id` / 定理 `FriendlyOperation.id`

English:
theorem FriendlyOperation.id
  given: {basis_hd basis_tl}
  proof: Seq.FriendlyOperation.id

中文:
定理 FriendlyOperation.id
  条件: {basis_hd basis_tl}
  证明: Seq.FriendlyOperation.id
-/
theorem FriendlyOperation.id {basis_hd basis_tl} :
    FriendlyOperation (id : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl) :=
  Seq.FriendlyOperation.id

/--
theorem `FriendlyOperation.comp` / 定理 `FriendlyOperation.comp`

English:
theorem FriendlyOperation.comp
  statement: {basis_hd basis_tl}
  proof: Seq.FriendlyOperation.comp h₁ h₂

中文:
定理 FriendlyOperation.comp
  结论: {basis_hd basis_tl}
  证明: Seq.FriendlyOperation.comp h₁ h₂
-/
theorem FriendlyOperation.comp {basis_hd basis_tl}
    {op₁ op₂ : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    (h₁ : FriendlyOperation op₁) (h₂ : FriendlyOperation op₂) :
    FriendlyOperation (op₁ ∘ op₂) :=
  Seq.FriendlyOperation.comp h₁ h₂

/--
theorem `FriendlyOperation.const` / 定理 `FriendlyOperation.const`

English:
theorem FriendlyOperation.const
  given: {basis_hd basis_tl} {s : Multiseries basis_hd basis_tl}
  proof: Seq.FriendlyOperation.const

中文:
定理 FriendlyOperation.const
  条件: {basis_hd basis_tl} {s : Multiseries basis_hd basis_tl}
  证明: Seq.FriendlyOperation.const
-/
theorem FriendlyOperation.const {basis_hd basis_tl} {s : Multiseries basis_hd basis_tl} :
    FriendlyOperation (fun _ => s) :=
  Seq.FriendlyOperation.const

/--
theorem `FriendlyOperation.ite` / 定理 `FriendlyOperation.ite`

English:
theorem FriendlyOperation.ite
  statement: {basis_hd basis_tl}
  proof: Seq.FriendlyOperation.ite h₁ h₂

中文:
定理 FriendlyOperation.ite
  结论: {basis_hd basis_tl}
  证明: Seq.FriendlyOperation.ite h₁ h₂
-/
theorem FriendlyOperation.ite {basis_hd basis_tl}
    {op₁ op₂ : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    (h₁ : FriendlyOperation op₁) (h₂ : FriendlyOperation op₂)
    {P : Option (Real × MultiseriesExpansion basis_tl) -> Prop} [DecidablePred P] :
    FriendlyOperation (fun ms => if P ms.head then op₁ ms else op₂ ms) :=
  Seq.FriendlyOperation.ite h₁ h₂

/--
theorem `FriendlyOperation.cons` / 定理 `FriendlyOperation.cons`

English:
theorem FriendlyOperation.cons
  statement: {basis_hd basis_tl} (exp : Real)
  proof: Seq.FriendlyOperation.cons _

中文:
定理 FriendlyOperation.cons
  结论: {basis_hd basis_tl} (exp : 实数)
  证明: Seq.FriendlyOperation.cons _
-/
theorem FriendlyOperation.cons {basis_hd basis_tl} (exp : Real)
    (coef : MultiseriesExpansion basis_tl) :
    FriendlyOperation (cons (basis_hd := basis_hd) exp coef) :=
  Seq.FriendlyOperation.cons _

/--
theorem `FriendlyOperation.cons_tail` / 定理 `FriendlyOperation.cons_tail`

English:
theorem FriendlyOperation.cons_tail
  statement: {basis_hd basis_tl}
  proof: Seq.FriendlyOperation.cons_tail h

中文:
定理 FriendlyOperation.cons_tail
  结论: {basis_hd basis_tl}
  证明: Seq.FriendlyOperation.cons_tail h

Depends on / 依赖: LinearOrder, LinearOrder.topologicalLattice, TopologicalSpace, topologicalLattice
-/
theorem FriendlyOperation.cons_tail {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    {exp : Real} {coef : MultiseriesExpansion basis_tl}
    (h : FriendlyOperation op) :
    FriendlyOperation (fun ms => (op (.cons exp coef ms)).tail) :=
  Seq.FriendlyOperation.cons_tail h

/--
theorem `FriendlyOperationClass.comp` / 定理 `FriendlyOperationClass.comp`

English:
theorem FriendlyOperationClass.comp
  statement: {basis_hd basis_tl} {γ γ' : Type*}
  proof: by
  have : Seq.FriendlyOperationClass (fun c => op (g c)) := Seq.FriendlyOperationClass.comp _ _
  constructor

中文:
定理 FriendlyOperationClass.comp
  结论: {basis_hd basis_tl} {γ γ' : 类型}
  证明: by
  have : Seq.FriendlyOperationClass (fun c => op (g c)) := Seq.FriendlyOperationClass.comp _ _
  constructor
-/
theorem FriendlyOperationClass.comp {basis_hd basis_tl} {γ γ' : Type*}
    {g : γ' -> γ}
    {op : γ -> Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    [h : FriendlyOperationClass op] : FriendlyOperationClass (fun c => op (g c)) := by
  have : Seq.FriendlyOperationClass (fun c => op (g c)) := Seq.FriendlyOperationClass.comp _ _
  constructor

/--
theorem `eq_of_bisim_friend` / 定理 `eq_of_bisim_friend`

English:
theorem eq_of_bisim_friend
  statement: {γ : Type*} {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: by
  apply Seq.FriendlyOperationClass.eq_of_bisim (op := op) motive base
  peel step with x y ih h
  obtain h | ⟨exp, coef, c, x', y', rfl, rfl, h_next⟩ := h
  · simp [h]
  right
  use (exp, coef), x', y', c
  simpa [cons]

中文:
定理 eq_of_bisim_friend
  结论: {γ : 类型} {basis_hd : 实数 -> 实数} {basis_tl : Basis}
  证明: by
  apply Seq.FriendlyOperationClass.eq_of_bisim (op := op) motive base
  peel step with x y ih h
  obtain h | ⟨exp, coef, c, x', y', rfl, rfl, h_next⟩ := h
  · simp [h]
  right
  use (exp, coef), x', y', c
  simpa [cons]

Depends on / 依赖: FriendlyOperationClass, Seq.FriendlyOperationClass.eq_of_bisim, eq_of_bisim, h_next, motive
-/
theorem eq_of_bisim_friend {γ : Type*} {basis_hd : Real -> Real} {basis_tl : Basis}
    {op : γ -> Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    [FriendlyOperationClass op]
    {x y : Multiseries basis_hd basis_tl}
    (motive : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl -> Prop)
    (base : motive x y)
    (step : forall x y, motive x y -> (x = y) ∨ exists exp coef,
      exists (c : γ) (x' y' : Multiseries basis_hd basis_tl),
      x = cons exp coef (op c x') ∧ y = cons exp coef (op c y') ∧ motive x' y') :
    x = y := by
  apply Seq.FriendlyOperationClass.eq_of_bisim (op := op) motive base
  peel step with x y ih h
  obtain h | ⟨exp, coef, c, x', y', rfl, rfl, h_next⟩ := h
  · simp [h]
  right
  use (exp, coef), x', y', c
  simpa [cons]

section simp

@[simp]
/--
theorem `cons_ne_nil` / 定理 `cons_ne_nil`

English:
theorem cons_ne_nil
  statement: {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real}
  proof: by
  intro h
  simp only [cons, nil] at h
  apply Seq.cons_ne_nil h

@[simp]

中文:
定理 cons_ne_nil
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {exp : 实数}
  证明: by
  intro h
  simp only [cons, nil] at h
  apply Seq.cons_ne_nil h

@[simp]

Depends on / 依赖: Seq.cons_ne_nil, cons_ne_nil
-/
theorem cons_ne_nil {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    cons exp coef tl != .nil := by
  intro h
  simp only [cons, nil] at h
  apply Seq.cons_ne_nil h

@[simp]
/--
theorem `nil_ne_cons` / 定理 `nil_ne_cons`

English:
theorem nil_ne_cons
  statement: {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real}
  proof: cons_ne_nil.symm

中文:
定理 nil_ne_cons
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {exp : 实数}
  证明: cons_ne_nil.symm

Depends on / 依赖: cons_ne_nil, cons_ne_nil.symm
-/
theorem nil_ne_cons {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    .nil != cons exp coef tl := cons_ne_nil.symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `cons_eq_cons` / 定理 `cons_eq_cons`

English:
theorem cons_eq_cons
  statement: {basis_hd : Real -> Real} {basis_tl : Basis} {exp1 exp2 : Real}
  proof: by
  rw [cons]; rw [cons]; rw [Seq.cons_eq_cons]
  grind

中文:
定理 cons_eq_cons
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {exp1 exp2 : 实数}
  证明: by
  rw [cons]; rw [cons]; rw [Seq.cons_eq_cons]
  grind

Depends on / 依赖: Seq.cons_eq_cons, cons_eq_cons
-/
theorem cons_eq_cons {basis_hd : Real -> Real} {basis_tl : Basis} {exp1 exp2 : Real}
    {coef1 coef2 : MultiseriesExpansion basis_tl} {tl1 tl2 : Multiseries basis_hd basis_tl} :
    cons exp1 coef1 tl1 = cons exp2 coef2 tl2 ↔ exp1 = exp2 ∧ coef1 = coef2 ∧ tl1 = tl2 := by
  rw [cons]; rw [cons]; rw [Seq.cons_eq_cons]
  grind

/--
theorem `corec_nil` / 定理 `corec_nil`

English:
theorem corec_nil
  statement: {β : Type*} {basis_hd} {basis_tl}
  proof: by
  simp only [corec, nil]
  rw [Seq.corec_nil]
  simpa

中文:
定理 corec_nil
  结论: {β : 类型} {basis_hd} {basis_tl}
  证明: by
  simp only [corec, nil]
  rw [Seq.corec_nil]
  simpa

Depends on / 依赖: Seq.corec_nil, corec_nil
-/
theorem corec_nil {β : Type*} {basis_hd} {basis_tl}
    {f : β -> Option (Real × MultiseriesExpansion basis_tl × β)} {b : β} (h : f b = none) :
    corec f b = (nil : Multiseries basis_hd basis_tl) := by
  simp only [corec, nil]
  rw [Seq.corec_nil]
  simpa

/--
theorem `corec_cons` / 定理 `corec_cons`

English:
theorem corec_cons
  statement: {β : Type*} {basis_hd} {basis_tl} {exp : Real}
  proof: by
  simp only [corec, cons]
  rw [Seq.corec_cons]
  simpa

中文:
定理 corec_cons
  结论: {β : 类型} {basis_hd} {basis_tl} {exp : 实数}
  证明: by
  simp only [corec, cons]
  rw [Seq.corec_cons]
  simpa

Depends on / 依赖: Seq.corec_cons, corec_cons
-/
theorem corec_cons {β : Type*} {basis_hd} {basis_tl} {exp : Real}
    {coef : MultiseriesExpansion basis_tl} {next : β}
    {f : β -> Option (Real × MultiseriesExpansion basis_tl × β)} {b : β}
    (h : f b = some (exp, coef, next)) :
    (corec f b : Multiseries basis_hd basis_tl) = cons exp coef (corec f next) := by
  simp only [corec, cons]
  rw [Seq.corec_cons]
  simpa

set_option backward.isDefEq.respectTransparency false in
/--
theorem `gcorec_nil` / 定理 `gcorec_nil`

English:
theorem gcorec_nil
  statement: {β γ : Type*} {basis_hd} {basis_tl}
  proof: by
  unfold gcorec
  rw [Seq.gcorec_nil]
  · simp [nil]
  · simpa

中文:
定理 gcorec_nil
  结论: {β γ : 类型} {basis_hd} {basis_tl}
  证明: by
  unfold gcorec
  rw [Seq.gcorec_nil]
  · simp [nil]
  · simpa

Depends on / 依赖: Seq.gcorec_nil, gcorec, gcorec_nil
-/
theorem gcorec_nil {β γ : Type*} {basis_hd} {basis_tl}
    {F : β -> Option (Real × MultiseriesExpansion basis_tl × γ × β)}
    {op : γ -> Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    [FriendlyOperationClass op] {b : β}
    (h : F b = none) :
    gcorec F op b = nil := by
  unfold gcorec
  rw [Seq.gcorec_nil]
  · simp [nil]
  · simpa

set_option backward.isDefEq.respectTransparency false in
/--
theorem `gcorec_some` / 定理 `gcorec_some`

English:
theorem gcorec_some
  statement: {β γ : Type*} {basis_hd} {basis_tl}
  proof: by
  unfold gcorec
  rw [Seq.gcorec_some]
  · simp [cons]
    rfl
  · simpa

@[simp]

中文:
定理 gcorec_some
  结论: {β γ : 类型} {basis_hd} {basis_tl}
  证明: by
  unfold gcorec
  rw [Seq.gcorec_some]
  · simp [cons]
    rfl
  · simpa

@[simp]

Depends on / 依赖: Seq.gcorec_some, gcorec, gcorec_some
-/
theorem gcorec_some {β γ : Type*} {basis_hd} {basis_tl}
    {F : β -> Option (Real × MultiseriesExpansion basis_tl × γ × β)}
    {op : γ -> Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl}
    [FriendlyOperationClass op] {b : β}
    {exp : Real} {coef : MultiseriesExpansion basis_tl} {c : γ} {next : β}
    (h : F b = some (exp, coef, c, next)) :
    gcorec F op b = cons exp coef (op c (gcorec F op next)) := by
  unfold gcorec
  rw [Seq.gcorec_some]
  · simp [cons]
    rfl
  · simpa

@[simp]
/--
theorem `destruct_nil` / 定理 `destruct_nil`

English:
theorem destruct_nil
  given: {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: by
  simp [destruct, nil]

中文:
定理 destruct_nil
  条件: {basis_hd : 实数 -> 实数} {basis_tl : Basis}
  证明: by
  simp [destruct, nil]

Depends on / 依赖: Finset, Finset.sup, _apply, _nhds, destruct, finset_sup
-/
theorem destruct_nil {basis_hd : Real -> Real} {basis_tl : Basis} :
    destruct (nil : Multiseries basis_hd basis_tl) = none := by
  simp [destruct, nil]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `destruct_cons` / 定理 `destruct_cons`

English:
theorem destruct_cons
  statement: {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real}
  proof: by
  simp [destruct, cons]

中文:
定理 destruct_cons
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {exp : 实数}
  证明: by
  simp [destruct, cons]

Depends on / 依赖: destruct
-/
theorem destruct_cons {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    destruct (cons exp coef tl) = some (exp, coef, tl) := by
  simp [destruct, cons]

/--
theorem `destruct_eq_none` / 定理 `destruct_eq_none`

English:
theorem destruct_eq_none
  statement: {basis_hd : Real -> Real} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
  proof: by
  apply Stream'.Seq.destruct_eq_none
  simpa [destruct] using h

中文:
定理 destruct_eq_none
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
  证明: by
  apply Stream'.Seq.destruct_eq_none
  simpa [destruct] using h

Depends on / 依赖: Seq.destruct_eq_none, Stream, _nhds_apply, destruct, destruct_eq_none, finset_sup
-/
theorem destruct_eq_none {basis_hd : Real -> Real} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    (h : destruct ms = none) : ms = nil := by
  apply Stream'.Seq.destruct_eq_none
  simpa [destruct] using h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `destruct_eq_cons` / 定理 `destruct_eq_cons`

English:
theorem destruct_eq_cons
  statement: {basis_hd : Real -> Real} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
  proof: by
  apply Stream'.Seq.destruct_eq_cons
  rw [destruct_eq_destruct_map]; rw [h]
  rfl

@[simp]

中文:
定理 destruct_eq_cons
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
  证明: by
  apply Stream'.Seq.destruct_eq_cons
  rw [destruct_eq_destruct_map]; rw [h]
  rfl

@[simp]

Depends on / 依赖: Seq.destruct_eq_cons, Stream, destruct_eq_cons, destruct_eq_destruct_map
-/
theorem destruct_eq_cons {basis_hd : Real -> Real} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    {exp : Real} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : destruct ms = some (exp, coef, tl)) : ms = cons exp coef tl := by
  apply Stream'.Seq.destruct_eq_cons
  rw [destruct_eq_destruct_map]; rw [h]
  rfl

@[simp]
/--
theorem `head_nil` / 定理 `head_nil`

English:
theorem head_nil
  given: {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: by
  simp [head, nil]

中文:
定理 head_nil
  条件: {basis_hd : 实数 -> 实数} {basis_tl : Basis}
  证明: by
  simp [head, nil]
-/
theorem head_nil {basis_hd : Real -> Real} {basis_tl : Basis} :
    (nil : Multiseries basis_hd basis_tl).head = none := by
  simp [head, nil]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `head_cons` / 定理 `head_cons`

English:
theorem head_cons
  statement: {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real}
  proof: by
  simp [head, cons]

中文:
定理 head_cons
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {exp : 实数}
  证明: by
  simp [head, cons]
-/
theorem head_cons {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).head = some (exp, coef) := by
  simp [head, cons]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `tail_nil` / 定理 `tail_nil`

English:
theorem tail_nil
  given: {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: by
  simp [tail, nil]

中文:
定理 tail_nil
  条件: {basis_hd : 实数 -> 实数} {basis_tl : Basis}
  证明: by
  simp [tail, nil]
-/
theorem tail_nil {basis_hd : Real -> Real} {basis_tl : Basis} :
    (nil : Multiseries basis_hd basis_tl).tail = nil := by
  simp [tail, nil]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `tail_cons` / 定理 `tail_cons`

English:
theorem tail_cons
  statement: {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real}
  proof: by
  simp [tail, cons]

中文:
定理 tail_cons
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {exp : 实数}
  证明: by
  simp [tail, cons]
-/
theorem tail_cons {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).tail = tl := by
  simp [tail, cons]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_nil` / 定理 `map_nil`

English:
theorem map_nil
  statement: {basis_hd basis_tl basis_hd' basis_tl'} (f : Real -> Real)
  proof: by
  simp [map, nil]

中文:
定理 map_nil
  结论: {basis_hd basis_tl basis_hd' basis_tl'} (f : 实数 -> 实数)
  证明: by
  simp [map, nil]
-/
theorem map_nil {basis_hd basis_tl basis_hd' basis_tl'} (f : Real -> Real)
    (g : MultiseriesExpansion basis_tl -> MultiseriesExpansion basis_tl') :
    (nil : Multiseries basis_hd basis_tl).map f g = (nil : Multiseries basis_hd' basis_tl') := by
  simp [map, nil]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_cons` / 定理 `map_cons`

English:
theorem map_cons
  statement: {basis_hd basis_tl basis_hd' basis_tl'} (f : Real -> Real)
  proof: by
  simp [map, cons]

@[simp]

中文:
定理 map_cons
  结论: {basis_hd basis_tl basis_hd' basis_tl'} (f : 实数 -> 实数)
  证明: by
  simp [map, cons]

@[simp]

Depends on / 依赖: basis_hd
-/
theorem map_cons {basis_hd basis_tl basis_hd' basis_tl'} (f : Real -> Real)
    (g : MultiseriesExpansion basis_tl -> MultiseriesExpansion basis_tl') {exp : Real}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).map f g = cons (basis_hd := basis_hd')
      (f exp) (g coef) (map f g tl) := by
  simp [map, cons]

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl)
  proof: Stream'.Seq.map_id ms

中文:
定理 map_id
  条件: {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl)
  证明: Stream'.Seq.map_id ms

Depends on / 依赖: Seq.map_id, Stream, map_id
-/
theorem map_id {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    ms.map (fun exp => exp) (fun coef => coef) = ms :=
  Stream'.Seq.map_id ms

set_option backward.isDefEq.respectTransparency false in
@[simp← ]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: {b₁ b₂ b₃ bs₁ bs₂ bs₃}
  proof: by
  simp [map, ← Stream'.Seq.map_comp]
  rfl

@[simp]

中文:
定理 map_comp
  结论: {b₁ b₂ b₃ bs₁ bs₂ bs₃}
  证明: by
  simp [map, ← Stream'.Seq.map_comp]
  rfl

@[simp]

Depends on / 依赖: Seq.map_comp, Stream, map_comp
-/
theorem map_comp {b₁ b₂ b₃ bs₁ bs₂ bs₃}
    (f₁ : Real -> Real) (g₁ : MultiseriesExpansion bs₁ -> MultiseriesExpansion bs₂)
    (f₂ : Real -> Real) (g₂ : MultiseriesExpansion bs₂ -> MultiseriesExpansion bs₃)
    (ms : Multiseries b₁ bs₁) :
    (ms.map (f₂ ∘ f₁) (g₂ ∘ g₁) : Multiseries b₃ bs₃) =
    (ms.map f₁ g₁ : Multiseries b₂ bs₂).map f₂ g₂ := by
  simp [map, ← Stream'.Seq.map_comp]
  rfl

@[simp]
/--
theorem `notMem_nil` / 定理 `notMem_nil`

English:
theorem notMem_nil
  given: {basis_hd : Real -> Real} {basis_tl : Basis} {x : Real × MultiseriesExpansion basis_tl}
  proof: Seq.notMem_nil _

@[simp]

中文:
定理 notMem_nil
  条件: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {x : 实数 × MultiseriesExpansion basis_tl}
  证明: Seq.notMem_nil _

@[simp]

Depends on / 依赖: Seq.notMem_nil, notMem_nil
-/
theorem notMem_nil {basis_hd : Real -> Real} {basis_tl : Basis} {x : Real × MultiseriesExpansion basis_tl} :
    x ∉ (nil : Multiseries basis_hd basis_tl) :=
  Seq.notMem_nil _

@[simp]
/--
theorem `mem_cons_iff` / 定理 `mem_cons_iff`

English:
theorem mem_cons_iff
  statement: {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real}
  proof: Seq.mem_cons_iff

@[simp]

中文:
定理 mem_cons_iff
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {exp : 实数}
  证明: Seq.mem_cons_iff

@[simp]

Depends on / 依赖: Seq.mem_cons_iff, mem_cons_iff
-/
theorem mem_cons_iff {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {x : Real × MultiseriesExpansion basis_tl} :
    x in cons exp coef tl ↔ x = (exp, coef) ∨ x in tl :=
  Seq.mem_cons_iff

@[simp]
/--
theorem `Pairwise_nil` / 定理 `Pairwise_nil`

English:
theorem Pairwise_nil
  given: {basis_hd : Real -> Real} {basis_tl : Basis} {R}
  proof: by
  simp [nil]

@[simp]

中文:
定理 Pairwise_nil
  条件: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {R}
  证明: by
  simp [nil]

@[simp]
-/
theorem Pairwise_nil {basis_hd : Real -> Real} {basis_tl : Basis} {R} :
    Seq.Pairwise R (nil : Multiseries basis_hd basis_tl) := by
  simp [nil]

@[simp]
/--
theorem `Pairwise_cons_nil` / 定理 `Pairwise_cons_nil`

English:
theorem Pairwise_cons_nil
  given: {basis_hd : Real -> Real} {basis_tl : Basis} {R exp coef}
  proof: by
  simp [cons, nil]

中文:
定理 Pairwise_cons_nil
  条件: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {R exp coef}
  证明: by
  simp [cons, nil]
-/
theorem Pairwise_cons_nil {basis_hd : Real -> Real} {basis_tl : Basis} {R exp coef} :
    Seq.Pairwise R (cons exp coef (nil : Multiseries basis_hd basis_tl)) := by
  simp [cons, nil]

end simp

end Multiseries

/--
Definition of `ofReal` / `ofReal` 的定义

English:
definition ofReal
  signature: (c : Real)
  body: c

中文:
定义 ofReal
  签名: (c : 实数)
  定义体: c
-/
def ofReal (c : Real) : MultiseriesExpansion [] := c

/--
Definition of `toReal` / `toReal` 的定义

English:
definition toReal
  signature: (ms : MultiseriesExpansion [])
  body: ms

中文:
定义 toReal
  签名: (ms : MultiseriesExpansion [])
  定义体: ms
-/
def toReal (ms : MultiseriesExpansion []) : Real := ms

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl))
  body: ms.1

中文:
定义 seq
  签名: {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl))
  定义体: ms.1
-/
def seq {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl)) :
    Multiseries basis_hd basis_tl :=
  ms.1

/--
Definition of `toFun` / `toFun` 的定义

English:
definition toFun
  signature: {basis : Basis} (ms : MultiseriesExpansion basis)
  body: match basis with
  | [] => fun _ => ms.toReal
  | .cons _ _ => ms.2

中文:
定义 toFun
  签名: {basis : Basis} (ms : MultiseriesExpansion basis)
  定义体: match basis with
  | [] => fun _ => ms.toReal
  | .cons _ _ => ms.2

Depends on / 依赖: ms.toReal, toReal
-/
def toFun {basis : Basis} (ms : MultiseriesExpansion basis) : Real -> Real :=
  match basis with
  | [] => fun _ => ms.toReal
  | .cons _ _ => ms.2

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f : Real -> Real)
  body: (s, f)

中文:
定义 mk
  签名: {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f : 实数 -> 实数)
  定义体: (s, f)
-/
def mk {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f : Real -> Real) :
    MultiseriesExpansion (basis_hd :: basis_tl) :=
  (s, f)

/-- Recursion principle for `MultiseriesExpansion (basis_hd :: basis_tl)`. -/
@[cases_eliminator]
/--
Definition of `recOn` / `recOn` 的定义

English:
definition recOn
  signature: {basis_hd basis_tl} {motive : MultiseriesExpansion (basis_hd :: basis_tl) -> Sort*}
  body: by
  let ⟨s, f⟩ := ms
  cases s with
  | nil => apply nil
  | cons hd tl => apply cons

中文:
定义 recOn
  签名: {basis_hd basis_tl} {motive : MultiseriesExpansion (basis_hd :: basis_tl) -> Sort*}
  定义体: by
  let ⟨s, f⟩ := ms
  cases s with
  | nil => apply nil
  | cons hd tl => apply cons
-/
def recOn {basis_hd basis_tl} {motive : MultiseriesExpansion (basis_hd :: basis_tl) -> Sort*}
    (nil : forall f, motive (mk .nil f))
    (cons : forall exp coef tl f, motive (.mk (.cons exp coef tl) f))
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : motive ms := by
  let ⟨s, f⟩ := ms
  cases s with
  | nil => apply nil
  | cons hd tl => apply cons

instance (basis : Basis) : Inhabited (MultiseriesExpansion basis) :=
  match basis with
  | [] => ⟨(default : Real)⟩
  | List.cons basis_hd basis_tl => ⟨(default : Multiseries basis_hd basis_tl × (Real -> Real))⟩

/--
theorem `eq_mk` / 定理 `eq_mk`

English:
theorem eq_mk
  given: {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl))
  proof: rfl

中文:
定理 eq_mk
  条件: {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl))
  证明: rfl

Depends on / 依赖: Finset, Finset.sup, _apply, finset_sup
-/
theorem eq_mk {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl)) :
    ms = mk ms.seq ms.toFun := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mk_eq_mk_iff` / 定理 `mk_eq_mk_iff`

English:
theorem mk_eq_mk_iff
  given: {basis_hd basis_tl} (s t : Multiseries basis_hd basis_tl) (f g : Real -> Real)
  proof: by rwa [mk, mk, Prod.mk_inj] at h
  mpr h := by simp [h]

@[simp]

中文:
定理 mk_eq_mk_iff
  条件: {basis_hd basis_tl} (s t : Multiseries basis_hd basis_tl) (f g : 实数 -> 实数)
  证明: by rwa [mk, mk, Prod.mk_inj] at h
  mpr h := by simp [h]

@[simp]

Depends on / 依赖: basis_hd
-/
theorem mk_eq_mk_iff {basis_hd basis_tl} (s t : Multiseries basis_hd basis_tl) (f g : Real -> Real) :
    mk (basis_hd := basis_hd) s f = mk (basis_hd := basis_hd) t g ↔ s = t ∧ f = g where
  mp h := by rwa [mk, mk, Prod.mk_inj] at h
  mpr h := by simp [h]

@[simp]
/--
theorem `ms_eq_mk_iff` / 定理 `ms_eq_mk_iff`

English:
theorem ms_eq_mk_iff
  statement: {basis_hd basis_tl}
  proof: by
  conv => lhs; lhs; rw [eq_mk ms]
  rw [mk_eq_mk_iff]

@[simp]

中文:
定理 ms_eq_mk_iff
  结论: {basis_hd basis_tl}
  证明: by
  conv => lhs; lhs; rw [eq_mk ms]
  rw [mk_eq_mk_iff]

@[simp]

Depends on / 依赖: Finset, Finset.sup, _apply, eq_mk, finset_sup, mk_eq_mk_iff
-/
theorem ms_eq_mk_iff {basis_hd basis_tl}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl))
    (s : Multiseries basis_hd basis_tl) (f : Real -> Real) : ms = mk s f ↔ ms.seq = s ∧ ms.toFun = f := by
  conv => lhs; lhs; rw [eq_mk ms]
  rw [mk_eq_mk_iff]

@[simp]
/--
theorem `mk_eq_mk_iff_iff` / 定理 `mk_eq_mk_iff_iff`

English:
theorem mk_eq_mk_iff_iff
  statement: {basis_hd basis_tl}
  proof: by
  rw [@Eq.comm _ (mk s f) ms]; rw [ms_eq_mk_iff]

中文:
定理 mk_eq_mk_iff_iff
  结论: {basis_hd basis_tl}
  证明: by
  rw [@Eq.comm _ (mk s f) ms]; rw [ms_eq_mk_iff]

Depends on / 依赖: Eq.comm, ms_eq_mk_iff
-/
theorem mk_eq_mk_iff_iff {basis_hd basis_tl}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl))
    (s : Multiseries basis_hd basis_tl) (f : Real -> Real) :
    mk s f = ms ↔ ms.seq = s ∧ ms.toFun = f := by
  rw [@Eq.comm _ (mk s f) ms]; rw [ms_eq_mk_iff]

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  statement: {basis_hd basis_tl}
  proof: by simp [h]
  mpr h := by
    rw [eq_mk ms₁]; rw [eq_mk ms₂]
    simp [h]

@[simp]

中文:
定理 ext_iff
  结论: {basis_hd basis_tl}
  证明: by simp [h]
  mpr h := by
    rw [eq_mk ms₁]; rw [eq_mk ms₂]
    simp [h]

@[simp]

Depends on / 依赖: eq_mk
-/
theorem ext_iff {basis_hd basis_tl}
    (ms₁ ms₂ : MultiseriesExpansion (basis_hd :: basis_tl)) :
    ms₁ = ms₂ ↔ ms₁.seq = ms₂.seq ∧ ms₁.toFun = ms₂.toFun where
  mp h := by simp [h]
  mpr h := by
    rw [eq_mk ms₁]; rw [eq_mk ms₂]
    simp [h]

@[simp]
/--
theorem `ofReal_toReal` / 定理 `ofReal_toReal`

English:
theorem ofReal_toReal
  given: (x : Real)
  statement: (ofReal x).toReal = x
  proof: rfl

@[simp]

中文:
定理 ofReal_toReal
  条件: (x : 实数)
  结论: (of实数 x).to实数 = x
  证明: rfl

@[simp]
-/
theorem ofReal_toReal (x : Real) : (ofReal x).toReal = x := rfl

@[simp]
/--
theorem `toReal_ofReal` / 定理 `toReal_ofReal`

English:
theorem toReal_ofReal
  given: (ms : MultiseriesExpansion [])
  statement: ofReal ms.toReal = ms
  proof: rfl

@[simp]

中文:
定理 toReal_ofReal
  条件: (ms : MultiseriesExpansion [])
  结论: of实数 ms.to实数 = ms
  证明: rfl

@[simp]

Depends on / 依赖: ContinuousAt, ContinuousAt.finset_sup, continuousAt, continuous_iff_continuousAt, finset_sup
-/
theorem toReal_ofReal (ms : MultiseriesExpansion []) : ofReal ms.toReal = ms := rfl

@[simp]
/--
theorem `const_toFun` / 定理 `const_toFun`

English:
theorem const_toFun
  given: (ms : MultiseriesExpansion [])
  statement: ms.toFun = fun _ => ms.toReal
  proof: rfl

@[simp]

中文:
定理 const_toFun
  条件: (ms : MultiseriesExpansion [])
  结论: ms.toFun = fun _ => ms.to实数
  证明: rfl

@[simp]
-/
theorem const_toFun (ms : MultiseriesExpansion []) : ms.toFun = fun _ => ms.toReal := rfl

@[simp]
/--
theorem `mk_toFun` / 定理 `mk_toFun`

English:
theorem mk_toFun
  given: {basis_hd basis_tl} {s : Multiseries basis_hd basis_tl} {f : Real -> Real}
  proof: rfl

@[simp]

中文:
定理 mk_toFun
  条件: {basis_hd basis_tl} {s : Multiseries basis_hd basis_tl} {f : 实数 -> 实数}
  证明: rfl

@[simp]

Depends on / 依赖: basis_hd
-/
theorem mk_toFun {basis_hd basis_tl} {s : Multiseries basis_hd basis_tl} {f : Real -> Real} :
    (mk (basis_hd := basis_hd) s f).toFun = f := rfl

@[simp]
/--
theorem `mk_seq` / 定理 `mk_seq`

English:
theorem mk_seq
  given: {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f : Real -> Real)
  proof: rfl

中文:
定理 mk_seq
  条件: {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f : 实数 -> 实数)
  证明: rfl

Depends on / 依赖: basis_hd
-/
theorem mk_seq {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f : Real -> Real) :
    (mk (basis_hd := basis_hd) s f).seq = s := rfl

/--
Definition of `replaceFun` / `replaceFun` 的定义

English:
definition replaceFun
  signature: {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl))
  body: mk ms.seq f

@[simp]

中文:
定义 replaceFun
  签名: {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl))
  定义体: mk ms.seq f

@[simp]

Depends on / 依赖: ms.seq
-/
def replaceFun {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl))
    (f : Real -> Real) : MultiseriesExpansion (basis_hd :: basis_tl) :=
  mk ms.seq f

@[simp]
/--
theorem `mk_replaceFun` / 定理 `mk_replaceFun`

English:
theorem mk_replaceFun
  statement: {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl)
  proof: rfl

@[simp]

中文:
定理 mk_replaceFun
  结论: {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl)
  证明: rfl

@[simp]

Depends on / 依赖: basis_hd, replaceFun
-/
theorem mk_replaceFun {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl)
    (f g : Real -> Real) :
    (mk (basis_hd := basis_hd) s f).replaceFun g = mk (basis_hd := basis_hd) s g :=
  rfl

@[simp]
/--
theorem `replaceFun_toFun` / 定理 `replaceFun_toFun`

English:
theorem replaceFun_toFun
  statement: {basis_hd basis_tl}
  proof: rfl

@[simp]

中文:
定理 replaceFun_toFun
  结论: {basis_hd basis_tl}
  证明: rfl

@[simp]
-/
theorem replaceFun_toFun {basis_hd basis_tl}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) (f : Real -> Real) :
    (ms.replaceFun f).toFun = f := rfl

@[simp]
/--
theorem `replaceFun_seq` / 定理 `replaceFun_seq`

English:
theorem replaceFun_seq
  statement: {basis_hd basis_tl}
  proof: rfl

中文:
定理 replaceFun_seq
  结论: {basis_hd basis_tl}
  证明: rfl
-/
theorem replaceFun_seq {basis_hd basis_tl}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) (f : Real -> Real) :
    (ms.replaceFun f).seq = ms.seq := rfl

section leadingExp

variable {basis_hd : Real -> Real} {basis_tl : Basis}
  {ms : MultiseriesExpansion (basis_hd :: basis_tl)}

namespace Multiseries

/--
Definition of `leadingExp` / `leadingExp` 的定义

English:
definition leadingExp
  signature: (s : Multiseries basis_hd basis_tl)
  body: match s.head with
  | none => ⊥
  | some (exp, _) => exp

@[simp]

中文:
定义 leadingExp
  签名: (s : Multiseries basis_hd basis_tl)
  定义体: match s.head with
  | none => ⊥
  | some (exp, _) => exp

@[simp]

Depends on / 依赖: s.head
-/
def leadingExp (s : Multiseries basis_hd basis_tl) : WithBot Real :=
  match s.head with
  | none => ⊥
  | some (exp, _) => exp

@[simp]
/--
theorem `leadingExp_nil` / 定理 `leadingExp_nil`

English:
theorem leadingExp_nil
  statement: (nil : Multiseries basis_hd basis_tl).leadingExp = ⊥
  proof: rfl

@[simp]

中文:
定理 leadingExp_nil
  结论: (nil : Multiseries basis_hd basis_tl).leadingExp = ⊥
  证明: rfl

@[simp]
-/
theorem leadingExp_nil : (nil : Multiseries basis_hd basis_tl).leadingExp = ⊥ :=
  rfl

@[simp]
/--
theorem `leadingExp_cons` / 定理 `leadingExp_cons`

English:
theorem leadingExp_cons
  statement: {exp : Real} {coef : MultiseriesExpansion basis_tl}
  proof: rfl

中文:
定理 leadingExp_cons
  结论: {exp : 实数} {coef : MultiseriesExpansion basis_tl}
  证明: rfl

Depends on / 依赖: Finset, Finset.inf, _apply, finset_inf
-/
theorem leadingExp_cons {exp : Real} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).leadingExp = exp :=
  rfl

/-- `ms.leadingExp = ⊥` iff `ms = []`. -/
@[simp]
/--
theorem `leadingExp_eq_bot` / 定理 `leadingExp_eq_bot`

English:
theorem leadingExp_eq_bot
  given: (s : Multiseries basis_hd basis_tl)
  proof: by
  cases s <;> simp

中文:
定理 leadingExp_eq_bot
  条件: (s : Multiseries basis_hd basis_tl)
  证明: by
  cases s <;> simp
-/
theorem leadingExp_eq_bot (s : Multiseries basis_hd basis_tl) :
    s.leadingExp = ⊥ ↔ s = nil := by
  cases s <;> simp

end Multiseries

/--
Definition of `leadingExp` / `leadingExp` 的定义

English:
definition leadingExp
  signature: (ms : MultiseriesExpansion (basis_hd :: basis_tl))
  body: ms.seq.leadingExp

@[simp]

中文:
定义 leadingExp
  签名: (ms : MultiseriesExpansion (basis_hd :: basis_tl))
  定义体: ms.seq.leadingExp

@[simp]

Depends on / 依赖: Finset, Finset.inf, _apply, finset_inf, leadingExp, ms.seq.leadingExp
-/
def leadingExp (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : WithBot Real :=
  ms.seq.leadingExp

@[simp]
/--
theorem `leadingExp_def` / 定理 `leadingExp_def`

English:
theorem leadingExp_def
  given: (ms : MultiseriesExpansion (basis_hd :: basis_tl))
  proof: rfl

中文:
定理 leadingExp_def
  条件: (ms : MultiseriesExpansion (basis_hd :: basis_tl))
  证明: rfl
-/
theorem leadingExp_def (ms : MultiseriesExpansion (basis_hd :: basis_tl)) :
    leadingExp ms = ms.seq.leadingExp := rfl

end leadingExp

section Sorted

/-- Auxiliary instance for the order on pairs `(exp, coef)` used below to define `Sorted` in terms
of `Stream'.Seq.Pairwise`. `(exp₁, coef₁) ≤ (exp₂, coef₂)` iff `exp₁ ≤ exp₂`. -/
scoped instance {basis} : Preorder (Real × MultiseriesExpansion basis) := Preorder.lift Prod.fst

/--
theorem `lt_iff_lt` / 定理 `lt_iff_lt`

English:
theorem lt_iff_lt
  given: {basis} {exp1 exp2 : Real} {coef1 coef2 : MultiseriesExpansion basis}
  proof: by
  rfl

中文:
定理 lt_iff_lt
  条件: {basis} {exp1 exp2 : 实数} {coef1 coef2 : MultiseriesExpansion basis}
  证明: by
  rfl
-/
private theorem lt_iff_lt {basis} {exp1 exp2 : Real} {coef1 coef2 : MultiseriesExpansion basis} :
    (exp1, coef1) < (exp2, coef2) ↔ exp1 < exp2 := by
  rfl

/--
Inductive type `Sorted` / 归纳类型 `Sorted`

English:
inductive Sorted
  parameters: : {basis : Basis} -> (MultiseriesExpansion basis) -> Prop
  constructors (2):
    - const: (ms : MultiseriesExpansion []) : ms.Sorted
    - seq: {hd} {tl} (ms : MultiseriesExpansion (hd :: tl)) (h_coef : forall x in ms.seq, x.2.Sorted) (h_Pairwise : Seq.Pairwise (· > ·) ms.seq) : ms.Sorted

中文:
归纳类型 Sorted
  参数: : {basis : Basis} -> (MultiseriesExpansion basis) -> 命题
  构造子 (2 个):
    - const: (ms : MultiseriesExpansion []) : ms.Sorted
    - seq: {hd} {tl} (ms : MultiseriesExpansion (hd :: tl)) (h_coef : 对任意 x in ms.seq, x.2.Sorted) (h_Pairwise : Seq.Pairwise (· > ·) ms.seq) : ms.Sorted
-/
inductive Sorted : {basis : Basis} -> (MultiseriesExpansion basis) -> Prop
| const (ms : MultiseriesExpansion []) : ms.Sorted
| seq {hd} {tl} (ms : MultiseriesExpansion (hd :: tl))
    (h_coef : forall x in ms.seq, x.2.Sorted)
    (h_Pairwise : Seq.Pairwise (· > ·) ms.seq) : ms.Sorted

/--
Definition of `Multiseries.Sorted` / `Multiseries.Sorted` 的定义

English:
definition Multiseries.Sorted
  signature: {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl)
  body: (mk s 0).Sorted (basis := basis_hd :: basis_tl)

中文:
定义 Multiseries.Sorted
  签名: {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl)
  定义体: (mk s 0).Sorted (basis := basis_hd :: basis_tl)

Depends on / 依赖: ContinuousAt, ContinuousAt.finset_inf, Sorted, basis_hd, basis_tl, continuousAt, continuous_iff_continuousAt, finset_inf
-/
def Multiseries.Sorted {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) : Prop :=
  (mk s 0).Sorted (basis := basis_hd :: basis_tl)

variable {basis_hd : Real -> Real} {basis_tl : Basis}

@[simp]
/--
theorem `sorted_iff_seq_sorted` / 定理 `sorted_iff_seq_sorted`

English:
theorem sorted_iff_seq_sorted
  given: {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
  proof: by
    cases h with | seq _ h_coef h_Pairwise =>
    constructor
    · simpa using h_coef
    · simpa using h_Pairwise
  mpr h := by
    cases h with | seq _ h_coef h_Pairwise =>
    constructor
    · simpa using h_coef
    · simpa using h_Pairwise

中文:
定理 sorted_iff_seq_sorted
  条件: {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
  证明: by
    cases h with | seq _ h_coef h_Pairwise =>
    constructor
    · simpa using h_coef
    · simpa using h_Pairwise
  mpr h := by
    cases h with | seq _ h_coef h_Pairwise =>
    constructor
    · simpa using h_coef
    · simpa using h_Pairwise

Depends on / 依赖: h_Pairwise, h_coef
-/
theorem sorted_iff_seq_sorted {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    ms.Sorted ↔ ms.seq.Sorted where
  mp h := by
    cases h with | seq _ h_coef h_Pairwise =>
    constructor
    · simpa using h_coef
    · simpa using h_Pairwise
  mpr h := by
    cases h with | seq _ h_coef h_Pairwise =>
    constructor
    · simpa using h_coef
    · simpa using h_Pairwise

namespace Multiseries.Sorted

@[simp]
/--
theorem `nil` / 定理 `nil`

English:
theorem nil
  statement: Sorted (nil : Multiseries basis_hd basis_tl)
  proof: by
  constructor <;> simp

中文:
定理 nil
  结论: Sorted (nil : Multiseries basis_hd basis_tl)
  证明: by
  constructor <;> simp
-/
theorem nil : Sorted (nil : Multiseries basis_hd basis_tl) := by
  constructor <;> simp

/--
theorem `cons_nil` / 定理 `cons_nil`

English:
theorem cons_nil
  statement: {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl}
  proof: by
  constructor
  · simpa
  · simp

中文:
定理 cons_nil
  结论: {basis_hd basis_tl} {exp : 实数} {coef : MultiseriesExpansion basis_tl}
  证明: by
  constructor
  · simpa
  · simp
-/
theorem cons_nil {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl}
    (h_coef : coef.Sorted) :
    Sorted (cons exp coef (.nil : Multiseries basis_hd basis_tl)) := by
  constructor
  · simpa
  · simp

/--
theorem `cons` / 定理 `cons`

English:
theorem cons
  statement: {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl}
  proof: by
  cases h_tl with | seq _ h_tl_coef h_tl_tl =>
  constructor
  · simp at h_tl_coef ⊢
    grind
  · cases tl
    · exact Seq.Pairwise_cons_nil
    · exact h_tl_tl.cons_cons_of_trans (by simpa [lt_iff_lt] using h_comp)

中文:
定理 cons
  结论: {basis_hd basis_tl} {exp : 实数} {coef : MultiseriesExpansion basis_tl}
  证明: by
  cases h_tl with | seq _ h_tl_coef h_tl_tl =>
  constructor
  · simp at h_tl_coef ⊢
    grind
  · cases tl
    · exact Seq.Pairwise_cons_nil
    · exact h_tl_tl.cons_cons_of_trans (by simpa [lt_iff_lt] using h_comp)

Depends on / 依赖: Pairwise_cons_nil, Seq.Pairwise_cons_nil, cons_cons_of_trans, h_comp, h_tl, h_tl_coef, h_tl_tl, h_tl_tl.cons_cons_of_trans, lt_iff_lt
-/
theorem cons {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl}
    (h_coef : coef.Sorted)
    (h_comp : leadingExp tl < exp)
    (h_tl : tl.Sorted) :
    Sorted (cons exp coef tl) := by
  cases h_tl with | seq _ h_tl_coef h_tl_tl =>
  constructor
  · simp at h_tl_coef ⊢
    grind
  · cases tl
    · exact Seq.Pairwise_cons_nil
    · exact h_tl_tl.cons_cons_of_trans (by simpa [lt_iff_lt] using h_comp)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `elim_cons` / 定理 `elim_cons`

English:
theorem elim_cons
  statement: {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl}
  proof: by
  cases h with | seq _ h_coef h_Pairwise =>
  constructor
  · simpa using h_coef (exp, coef) (by simp)
  cases tl with
  | nil => simp
  | cons tl_exp tl_coef tl_tl =>
  obtain ⟨h_all, h_Pairwise⟩ := h_Pairwise.cons_elim
  constructor
  · simp only [leadingExp_cons, WithBot.coe_lt_coe]
    exact 

中文:
定理 elim_cons
  结论: {basis_hd basis_tl} {exp : 实数} {coef : MultiseriesExpansion basis_tl}
  证明: by
  cases h with | seq _ h_coef h_Pairwise =>
  constructor
  · simpa using h_coef (exp, coef) (by simp)
  cases tl with
  | nil => simp
  | cons tl_exp tl_coef tl_tl =>
  obtain ⟨h_all, h_Pairwise⟩ := h_Pairwise.cons_elim
  constructor
  · simp only [leadingExp_cons, WithBot.coe_lt_coe]
    exact 

Depends on / 依赖: Multiseries, Multiseries.cons, Sorted, Sorted.seq, WithBot, WithBot.coe_lt_coe, coe_lt_coe, cons_elim, h_Pairwise, h_Pairwise.cons_elim, h_all, h_coef, leadingExp_cons, tl_coef, tl_exp, tl_tl
-/
theorem elim_cons {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} (h : (Multiseries.cons exp coef tl).Sorted) :
    coef.Sorted ∧ leadingExp tl < exp ∧ tl.Sorted := by
  cases h with | seq _ h_coef h_Pairwise =>
  constructor
  · simpa using h_coef (exp, coef) (by simp)
  cases tl with
  | nil => simp
  | cons tl_exp tl_coef tl_tl =>
  obtain ⟨h_all, h_Pairwise⟩ := h_Pairwise.cons_elim
  constructor
  · simp only [leadingExp_cons, WithBot.coe_lt_coe]
    exact h_all (tl_exp, tl_coef) (by simp [Multiseries.cons])
  · exact Sorted.seq _ (fun x hx => h_coef _ (by simp_all)) h_Pairwise

/--
theorem `tail` / 定理 `tail`

English:
theorem tail
  given: {ms : Multiseries basis_hd basis_tl} (h : ms.Sorted)
  proof: by
  cases ms with
  | nil => simp
  | cons exp coef tl => simpa using h.elim_cons.right.right

中文:
定理 tail
  条件: {ms : Multiseries basis_hd basis_tl} (h : ms.Sorted)
  证明: by
  cases ms with
  | nil => simp
  | cons exp coef tl => simpa using h.elim_cons.right.right

Depends on / 依赖: elim_cons, h.elim_cons.right.right
-/
theorem tail {ms : Multiseries basis_hd basis_tl} (h : ms.Sorted) :
    ms.tail.Sorted := by
  cases ms with
  | nil => simp
  | cons exp coef tl => simpa using h.elim_cons.right.right

/--
theorem `coind` / 定理 `coind`

English:
theorem coind
  statement: {s : Multiseries basis_hd basis_tl}
  proof: by
  constructor
  · apply Seq.all_coind
    · exact h_base
    · intro (exp, coef) tl h
      grind [h_step exp coef tl h]
  · apply Seq.Pairwise.coind_trans
    · exact h_base
    · intro (exp, coef) tl h
      constructor
      · intro (tl_exp, tl_coef) h_tl
        rw [gt_iff_lt]; rw [lt_iff_lt]

中文:
定理 coind
  结论: {s : Multiseries basis_hd basis_tl}
  证明: by
  constructor
  · apply Seq.all_coind
    · exact h_base
    · intro (exp, coef) tl h
      grind [h_step exp coef tl h]
  · apply Seq.Pairwise.coind_trans
    · exact h_base
    · intro (exp, coef) tl h
      constructor
      · intro (tl_exp, tl_coef) h_tl
        rw [gt_iff_lt]; rw [lt_iff_lt]

Depends on / 依赖: Pairwise, Seq.Pairwise.coind_trans, Seq.all_coind, all_coind, coind_trans, gt_iff_lt, h_base, h_step, h_tl, leadingExp, lt_iff_lt, replace, right.left, tl_coef, tl_exp
-/
theorem coind {s : Multiseries basis_hd basis_tl}
    (motive : (ms : Multiseries basis_hd basis_tl) -> Prop)
    (h_base : motive s)
    (h_step : forall exp coef tl, motive (.cons exp coef tl) ->
        coef.Sorted ∧
        leadingExp tl < exp ∧
        motive tl) :
    s.Sorted := by
  constructor
  · apply Seq.all_coind
    · exact h_base
    · intro (exp, coef) tl h
      grind [h_step exp coef tl h]
  · apply Seq.Pairwise.coind_trans
    · exact h_base
    · intro (exp, coef) tl h
      constructor
      · intro (tl_exp, tl_coef) h_tl
        rw [gt_iff_lt]; rw [lt_iff_lt]
        replace h_step := (h_step exp coef tl h).right.left
        cases tl <;> simp [leadingExp, head] at h_tl h_step
        grind
      · grind [h_step exp coef tl h]

end Multiseries.Sorted

namespace Sorted

/--
theorem `nil` / 定理 `nil`

English:
theorem nil
  given: (f : Real -> Real)
  statement: Sorted (basis := basis_hd :: basis_tl) (mk .nil f)
  proof: by
  simp

中文:
定理 nil
  条件: (f : 实数 -> 实数)
  结论: Sorted (basis := basis_hd :: basis_tl) (mk .nil f)
  证明: by
  simp

Depends on / 依赖: basis_hd, basis_tl
-/
theorem nil (f : Real -> Real) : Sorted (basis := basis_hd :: basis_tl) (mk .nil f) := by
  simp

/--
theorem `cons_nil` / 定理 `cons_nil`

English:
theorem cons_nil
  statement: {exp : Real} {coef : MultiseriesExpansion basis_tl} {f : Real -> Real}
  proof: by
  simp [Multiseries.Sorted.cons_nil h_coef]

中文:
定理 cons_nil
  结论: {exp : 实数} {coef : MultiseriesExpansion basis_tl} {f : 实数 -> 实数}
  证明: by
  simp [Multiseries.Sorted.cons_nil h_coef]

Depends on / 依赖: Multiseries, Multiseries.Sorted.cons_nil, Sorted, basis_hd, basis_tl, cons_nil, h_coef
-/
theorem cons_nil {exp : Real} {coef : MultiseriesExpansion basis_tl} {f : Real -> Real}
    (h_coef : coef.Sorted) :
    Sorted (basis := basis_hd :: basis_tl) (mk (.cons exp coef .nil) f) := by
  simp [Multiseries.Sorted.cons_nil h_coef]

/--
theorem `cons` / 定理 `cons`

English:
theorem cons
  statement: {exp : Real} {coef : MultiseriesExpansion basis_tl}
  proof: by
  simp [Multiseries.Sorted.cons h_coef h_comp h_tl]

中文:
定理 cons
  结论: {exp : 实数} {coef : MultiseriesExpansion basis_tl}
  证明: by
  simp [Multiseries.Sorted.cons h_coef h_comp h_tl]

Depends on / 依赖: Multiseries, Multiseries.Sorted.cons, Sorted, basis_hd, basis_tl, h_coef, h_comp, h_tl
-/
theorem cons {exp : Real} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl}
    {f : Real -> Real}
    (h_coef : coef.Sorted)
    (h_comp : tl.leadingExp < exp)
    (h_tl : tl.Sorted) :
    Sorted (basis := basis_hd :: basis_tl) (mk (.cons exp coef tl) f) := by
  simp [Multiseries.Sorted.cons h_coef h_comp h_tl]

/--
theorem `elim_cons` / 定理 `elim_cons`

English:
theorem elim_cons
  statement: {exp : Real} {coef : MultiseriesExpansion basis_tl}
  proof: by
  apply Multiseries.Sorted.elim_cons (by simpa using h)

中文:
定理 elim_cons
  结论: {exp : 实数} {coef : MultiseriesExpansion basis_tl}
  证明: by
  apply Multiseries.Sorted.elim_cons (by simpa using h)

Depends on / 依赖: basis_hd, basis_tl
-/
theorem elim_cons {exp : Real} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : Real -> Real}
    (h : Sorted (basis := basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) :
    coef.Sorted ∧ tl.leadingExp < exp ∧ tl.Sorted := by
  apply Multiseries.Sorted.elim_cons (by simpa using h)

/--
theorem `replaceFun` / 定理 `replaceFun`

English:
theorem replaceFun
  statement: {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
  proof: by
  simpa using h_sorted

中文:
定理 replaceFun
  结论: {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
  证明: by
  simpa using h_sorted

Depends on / 依赖: h_sorted
-/
theorem replaceFun {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    {f : Real -> Real} (h_sorted : ms.Sorted) :
    (ms.replaceFun f).Sorted := by
  simpa using h_sorted

end Sorted

end Sorted

section Approximates

/-- Coinductive predicate stating that `ms` approximates its attached function on `basis`.
* If `basis = []`, i.e. `ms` is just a real number, `Approximates` holds unconditionally.
* If `basis = basis_hd :: basis_tl` and `ms = nil`, then `f =ᶠ[atTop] 0`.
* If `basis = basis_hd :: basis_tl` and `ms = cons exp coef tl`, then
  `f` is `Majorized` with exponent `exp` by `basis_hd`,
  `coef` approximates its attached function, and
  `tl` approximates `f - basis_hd ^ exp * coef.toFun`.
-/
coinductive Approximates : {basis : Basis} -> (ms : MultiseriesExpansion basis) -> Prop
/-- Constant multiseries always approximates its attached function. -/
| const (ms : MultiseriesExpansion []) : Approximates ms
/-- Empty multiseries approximates (eventually) zero function. -/
| nil {basis_hd : Real -> Real} {basis_tl : Basis} {f : Real -> Real} (hf : f =ᶠ[atTop] 0) :
  Approximates (mk (@Multiseries.nil basis_hd basis_tl) f)
/-- `cons (exp, coef) tl` approximates `f` when `coef` approximates some function `fC`, `f` is
majorized with exponent `exp` by `basis_hd`, and `tl` approximates `f - fC * basis_hd ^ exp`. -/
| cons {basis_hd f : Real -> Real} {basis_tl : Basis} {exp : Real} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl}
    (h_coef : Approximates coef) (h_maj : Majorized f basis_hd exp)
    (h_tl : Approximates (mk tl (f - basis_hd ^ exp * coef.toFun))) :
  Approximates (mk (.cons exp coef tl) f)

variable {f basis_hd : Real -> Real} {basis_tl : Basis}

attribute [simp] Approximates.const

namespace Approximates

/--
theorem `coind` / 定理 `coind`

English:
theorem coind
  statement: {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
  proof: by
  apply coinduct fun {basis} ms =>
    ms.Approximates ∨ exists (h_basis : basis = basis_hd :: basis_tl), (motive (h_basis ▸ ms))
  · rintro basis ms (h_ms | ⟨rfl, h_ms⟩)
    · cases h_ms <;> grind
    simp only [reduceCtorEq, List.cons.injEq, ↓existsAndEq, and_true, heq_eq_eq, ms_eq_mk_iff,
    

中文:
定理 coind
  结论: {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
  证明: by
  apply coinduct fun {basis} ms =>
    ms.Approximates ∨ exists (h_basis : basis = basis_hd :: basis_tl), (motive (h_basis ▸ ms))
  · rintro basis ms (h_ms | ⟨rfl, h_ms⟩)
    · cases h_ms <;> grind
    simp only [reduceCtorEq, List.cons.injEq, ↓existsAndEq, and_true, heq_eq_eq, ms_eq_mk_iff,
    

Depends on / 依赖: basis_hd, coef.toFun, ms.toFun
-/
theorem coind {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    (motive : MultiseriesExpansion (basis_hd :: basis_tl) -> Prop)
    (h_base : motive ms)
    (h_step : forall ms, motive ms ->
      (ms.seq = .nil ∧ ms.toFun =ᶠ[atTop] 0) ∨
      (exists exp coef tl, ms.seq = .cons exp coef tl ∧
        coef.Approximates ∧
        Majorized ms.toFun basis_hd exp ∧
        motive (mk (basis_hd := basis_hd) tl (ms.toFun - basis_hd ^ exp * coef.toFun)))) :
    ms.Approximates := by
  apply coinduct fun {basis} ms =>
    ms.Approximates ∨ exists (h_basis : basis = basis_hd :: basis_tl), (motive (h_basis ▸ ms))
  · rintro basis ms (h_ms | ⟨rfl, h_ms⟩)
    · cases h_ms <;> grind
    simp only [reduceCtorEq, List.cons.injEq, ↓existsAndEq, and_true, heq_eq_eq, ms_eq_mk_iff,
      true_and, exists_eq_right_right', exists_and_left, false_or] at h_ms ⊢
    rcases h_step _ h_ms with h_step | ⟨exp, coef, tl, h_seq, h_coef, h_maj, h_tl⟩
    · grind
    · refine .inr ⟨basis_hd, ms.toFun, basis_tl, exp, coef, by simpa, ‹_›, tl, ?_⟩
      simp
      grind
  · grind

/--
theorem `elim_nil` / 定理 `elim_nil`

English:
theorem elim_nil
  given: (h : @Approximates (basis_hd :: basis_tl) (mk .nil f))
  proof: by
  generalize h_ms : (mk .nil f) = ms at h
  cases h <;> simp at h_ms; grind

@[simp]

中文:
定理 elim_nil
  条件: (h : @Approximates (basis_hd :: basis_tl) (mk .nil f))
  证明: by
  generalize h_ms : (mk .nil f) = ms at h
  cases h <;> simp at h_ms; grind

@[simp]

Depends on / 依赖: generalize, h_ms
-/
theorem elim_nil (h : @Approximates (basis_hd :: basis_tl) (mk .nil f)) :
    f =ᶠ[atTop] 0 := by
  generalize h_ms : (mk .nil f) = ms at h
  cases h <;> simp at h_ms; grind

@[simp]
/--
theorem `nil_iff` / 定理 `nil_iff`

English:
theorem nil_iff
  given: {f : Real -> Real}
  proof: ⟨elim_nil, nil⟩

中文:
定理 nil_iff
  条件: {f : 实数 -> 实数}
  证明: ⟨elim_nil, nil⟩

Depends on / 依赖: Approximates, basis_hd, basis_tl
-/
theorem nil_iff {f : Real -> Real} :
    (mk (basis_hd := basis_hd) (basis_tl := basis_tl) .nil f).Approximates ↔ f =ᶠ[atTop] 0 :=
  ⟨elim_nil, nil⟩

/--
theorem `elim_cons` / 定理 `elim_cons`

English:
theorem elim_cons
  statement: {exp : Real}
  proof: by
  generalize h_ms : (mk (.cons exp coef tl) f) = ms at h
  cases h <;> simp at h_ms; grind

中文:
定理 elim_cons
  结论: {exp : 实数}
  证明: by
  generalize h_ms : (mk (.cons exp coef tl) f) = ms at h
  cases h <;> simp at h_ms; grind

Depends on / 依赖: basis_hd, basis_tl
-/
theorem elim_cons {exp : Real}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : Approximates (basis := basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) :
    coef.Approximates ∧
    Majorized f basis_hd exp ∧
    (mk (basis_hd := basis_hd) tl (f - basis_hd ^ exp * coef.toFun)).Approximates := by
  generalize h_ms : (mk (.cons exp coef tl) f) = ms at h
  cases h <;> simp at h_ms; grind

/--
theorem `replaceFun` / 定理 `replaceFun`

English:
theorem replaceFun
  statement: {ms : MultiseriesExpansion (basis_hd :: basis_tl)} {f : Real -> Real}
  proof: by
  let motive (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : Prop :=
      exists (ms' : MultiseriesExpansion (basis_hd :: basis_tl)) (f' : Real -> Real),
      ms = ms'.replaceFun f' ∧ ms'.Approximates ∧ ms'.toFun =ᶠ[atTop] f'
  apply Approximates.coind motive ⟨ms, f, by grind⟩
  rintro _ ⟨

中文:
定理 replaceFun
  结论: {ms : MultiseriesExpansion (basis_hd :: basis_tl)} {f : 实数 -> 实数}
  证明: by
  let motive (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : Prop :=
      exists (ms' : MultiseriesExpansion (basis_hd :: basis_tl)) (f' : Real -> Real),
      ms = ms'.replaceFun f' ∧ ms'.Approximates ∧ ms'.toFun =ᶠ[atTop] f'
  apply Approximates.coind motive ⟨ms, f, by grind⟩
  rintro _ ⟨

Depends on / 依赖: Approximates, Approximates.coind, Multiseries, Multiseries.nil_ne_cons, MultiseriesExpansion, basis_hd, basis_tl, exists_const, false_and, h_approx, h_eq, mk_replaceFun, mk_seq, mk_toFun, motive, nil_iff, nil_ne_cons, or_false, replaceFun, true_and
-/
theorem replaceFun {ms : MultiseriesExpansion (basis_hd :: basis_tl)} {f : Real -> Real}
    (h_equiv : ms.toFun =ᶠ[atTop] f) (h_approx : ms.Approximates) :
    (ms.replaceFun f).Approximates := by
  let motive (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : Prop :=
      exists (ms' : MultiseriesExpansion (basis_hd :: basis_tl)) (f' : Real -> Real),
      ms = ms'.replaceFun f' ∧ ms'.Approximates ∧ ms'.toFun =ᶠ[atTop] f'
  apply Approximates.coind motive ⟨ms, f, by grind⟩
  rintro _ ⟨ms, f, rfl, h_approx, h_eq⟩
  cases ms with
  | nil g =>
    simp only [nil_iff, mk_toFun, mk_replaceFun, mk_seq, true_and,
      Multiseries.nil_ne_cons, false_and, exists_const, or_false] at h_approx h_eq ⊢
    grw [← h_eq, h_approx]
  | cons exp coef tl g =>
    obtain ⟨h_coef, h_maj, h_tl⟩ := h_approx.elim_cons
    refine .inr ⟨exp, coef, tl, ?_⟩
    simp only [mk_replaceFun, mk_seq, h_coef, mk_toFun, true_and]
    simp only [mk_toFun] at h_eq
    refine ⟨h_maj.of_eventuallyEq h_eq.symm, mk tl (g - basis_hd ^ exp * coef.toFun), _, rfl,
      h_tl, ?_⟩
    grw [mk_toFun, h_eq]

/--
theorem `neg_leadingExp_tendsto_zero` / 定理 `neg_leadingExp_tendsto_zero`

English:
theorem neg_leadingExp_tendsto_zero
  statement: {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: by
  cases ms
  · exact Tendsto.congr' h_approx.elim_nil.symm tendsto_const_nhds
  · obtain ⟨h_coef, h_maj, h_tl⟩ := h_approx.elim_cons
    simp only [leadingExp_def, mk_seq, Multiseries.leadingExp_cons, WithBot.coe_lt_zero] at h_neg
    exact Majorized.tendsto_zero_of_neg h_neg h_maj

中文:
定理 neg_leadingExp_tendsto_zero
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis}
  证明: by
  cases ms
  · exact Tendsto.congr' h_approx.elim_nil.symm tendsto_const_nhds
  · obtain ⟨h_coef, h_maj, h_tl⟩ := h_approx.elim_cons
    simp only [leadingExp_def, mk_seq, Multiseries.leadingExp_cons, WithBot.coe_lt_zero] at h_neg
    exact Majorized.tendsto_zero_of_neg h_neg h_maj

Depends on / 依赖: Majorized, Majorized.tendsto_zero_of_neg, Multiseries, Multiseries.leadingExp_cons, Tendsto, Tendsto.congr, WithBot, WithBot.coe_lt_zero, coe_lt_zero, elim_cons, elim_nil, h_approx, h_approx.elim_cons, h_approx.elim_nil.symm, h_coef, h_maj, h_neg, h_tl, leadingExp_cons, leadingExp_def
-/
theorem neg_leadingExp_tendsto_zero {basis_hd : Real -> Real} {basis_tl : Basis}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    (h_neg : ms.leadingExp < 0) (h_approx : ms.Approximates) :
    Tendsto ms.toFun atTop (𝓝 0) := by
  cases ms
  · exact Tendsto.congr' h_approx.elim_nil.symm tendsto_const_nhds
  · obtain ⟨h_coef, h_maj, h_tl⟩ := h_approx.elim_cons
    simp only [leadingExp_def, mk_seq, Multiseries.leadingExp_cons, WithBot.coe_lt_zero] at h_neg
    exact Majorized.tendsto_zero_of_neg h_neg h_maj

/--
theorem `nil_tendsto_zero` / 定理 `nil_tendsto_zero`

English:
theorem nil_tendsto_zero
  statement: {basis_hd : Real -> Real} {basis_tl : Basis} {f : Real -> Real}
  proof: neg_leadingExp_tendsto_zero (by simp) h

中文:
定理 nil_tendsto_zero
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis} {f : 实数 -> 实数}
  证明: neg_leadingExp_tendsto_zero (by simp) h

Depends on / 依赖: basis_hd, basis_tl
-/
theorem nil_tendsto_zero {basis_hd : Real -> Real} {basis_tl : Basis} {f : Real -> Real}
    (h : MultiseriesExpansion.Approximates (basis := basis_hd :: basis_tl) (mk .nil f)) :
    Tendsto f atTop (𝓝 0) :=
  neg_leadingExp_tendsto_zero (by simp) h

end Approximates

instance (basis_hd : Real -> Real) (basis_tl : Basis) :
    Setoid (MultiseriesExpansion (basis_hd :: basis_tl)) where
  r x y := x.seq = y.seq ∧ x.toFun =ᶠ[atTop] y.toFun
  iseqv := ⟨by simp, by grind [EventuallyEq.symm], by grind [EventuallyEq.trans]⟩

@[simp]
/--
theorem `equiv_def` / 定理 `equiv_def`

English:
theorem equiv_def
  given: {x y : MultiseriesExpansion (basis_hd :: basis_tl)}
  proof: by
  rfl

中文:
定理 equiv_def
  条件: {x y : MultiseriesExpansion (basis_hd :: basis_tl)}
  证明: by
  rfl
-/
theorem equiv_def {x y : MultiseriesExpansion (basis_hd :: basis_tl)} :
    x ≈ y ↔ x.seq = y.seq ∧ x.toFun =ᶠ[atTop] y.toFun := by
  rfl

end Approximates

end MultiseriesExpansion

end Tactic.ComputeAsymptotics
