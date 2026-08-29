/-
Copyright (c) 2022 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, Yaël Dillies
-/
module

public meta import Mathlib.Control.Basic
public import Mathlib.Algebra.Order.Invertible
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Tactic.HaveI
public import Mathlib.Tactic.NormNum.Core

/-!
## `positivity` core functionality

This file sets up the `positivity` tactic and the `@[positivity]` attribute,
which allow for plugging in new positivity functionality around a positivity-based driver.
The actual behavior is in `@[positivity]`-tagged definitions in `Tactic.Positivity.Basic`
and elsewhere.
-/

public meta section

open Lean
open Lean.Meta Qq Lean.Elab Term

/-- A definition of type `PositivityExt` tagged `@[positivity t]` extends the `positivity` tactic.
The term (with underscores) `t` indicates which expressions this extension accepts.
An extension will be given an expression `e : α`, together with hypotheses
`[Zero α] [PartialOrder α]` and attempts to prove `e > 0`, `e ≥ 0`, or `e ≠ 0`.

When `Positivity.core` calls this extension on an expression `e`, it does not guarantee that `e`
matches `t` perfectly: validate the form of the expression (using e.g.
`match_expr (← withReducible (whnf e))`) before building a proof. See also the
`let .app ... ← withReducible (whnf e) | throwError ...` lines in the example below.

An extension can call `Mathlib.Meta.Positivity.core` to recursively solve subgoals.

Example:
```lean
@[positivity ite _ _ _] def evalIte : PositivityExt where eval {u α} zα pα e := do
  let .app (.app (.app (.app f (p : Q(Prop))) (_ : Q(Decidable $p))) (a : Q($α))) (b : Q($α))
    ← withReducible (whnf e) | throwError "not ite"
  haveI' : $e =Q ite $p $a $b := ⟨⟩
  guard <| ← withDefault <| withNewMCtxDepth <| isDefEq f q(ite (α := $α))
  let ra ← core zα pα a; let rb ← core zα pα b
  ...
```
-/
syntax (name := positivity) "positivity " term,+ : attr

/--
lemma `ne_of_ne_of_eq'` / 引理 `ne_of_ne_of_eq'`

English:
lemma ne_of_ne_of_eq'
  given: {α : Sort*} {a c b : α} (hab : (a : α) != c) (hbc : a = b)
  statement: b != c
  proof: hbc ▸ hab

中文:
引理 ne_of_ne_of_eq'
  条件: {α : 类型层*} {a c b : α} (hab : (a : α) != c) (hbc : a = b)
  结论: b != c
  证明: hbc ▸ hab
-/
lemma ne_of_ne_of_eq' {α : Sort*} {a c b : α} (hab : (a : α) != c) (hbc : a = b) : b != c := hbc ▸ hab

namespace Mathlib.Meta.Positivity

variable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α))

/--
Inductive type `Strictness` / 归纳类型 `Strictness`

English:
inductive Strictness
  parameters: (e : Q($α))
  constructors (4):
    - positive: {pα : Q(PartialOrder $α)} (pf : Q(0 < $e)) : Strictness e pα
    - nonnegative: {pα : Q(PartialOrder $α)} (pf : Q(0 <= $e)) : Strictness e pα
    - nonzero: {pα?} (pf : Q($e != 0)) : Strictness e pα?
    - none: {pα?} : Strictness e pα?

中文:
归纳类型 Strictness
  参数: (e : Q($α))
  构造子 (4 个):
    - positive: {pα : Q(偏序 $α)} (pf : Q(0 < $e)) : Strictness e pα
    - nonnegative: {pα : Q(偏序 $α)} (pf : Q(0 <= $e)) : Strictness e pα
    - nonzero: {pα?} (pf : Q($e != 0)) : Strictness e pα?
    - none: {pα?} : Strictness e pα?
-/
inductive Strictness (e : Q($α)) : Option Q(PartialOrder $α) -> Type where
  | positive {pα : Q(PartialOrder $α)} (pf : Q(0 < $e)) : Strictness e pα
  | nonnegative {pα : Q(PartialOrder $α)} (pf : Q(0 <= $e)) : Strictness e pα
  | nonzero {pα?} (pf : Q($e != 0)) : Strictness e pα?
  | none {pα?} : Strictness e pα?

/--
Definition of `Strictness.toString` / `Strictness.toString` 的定义

English:
definition Strictness.toString
  signature: {e pα?}

中文:
定义 Strictness.toString
  签名: {e pα?}
-/
def Strictness.toString {e pα?} : Strictness zα e pα? -> String
  | positive _ => "positive"
  | nonnegative _ => "nonnegative"
  | nonzero _ => "nonzero"
  | none => "none"

/--
Definition of `Strictness.toPositive` / `Strictness.toPositive` 的定义

English:
definition Strictness.toPositive
  signature: {e pα}

中文:
定义 Strictness.toPositive
  签名: {e pα}
-/
def Strictness.toPositive {e pα} : Strictness zα e (some pα) -> Option Q(0 < $e)
  | .positive pf => some pf
  | _ => .none

/--
Definition of `Strictness.toNonneg` / `Strictness.toNonneg` 的定义

English:
definition Strictness.toNonneg
  signature: {e pα}

中文:
定义 Strictness.toNonneg
  签名: {e pα}
-/
def Strictness.toNonneg {e pα} : Strictness zα e (some pα) -> Option Q(0 <= $e)
  | .positive pf => some q(le_of_lt $pf)
  | .nonnegative pf => some pf
  | _ => .none

/--
Definition of `Strictness.toNonzero` / `Strictness.toNonzero` 的定义

English:
definition Strictness.toNonzero
  signature: {e pα?}

中文:
定义 Strictness.toNonzero
  签名: {e pα?}
-/
def Strictness.toNonzero {e pα?} : Strictness zα e pα? -> Option Q($e != 0)
  | .positive pf => some q(ne_of_gt $pf)
  | .nonzero pf => some pf
  | _ => .none

/--
Definition of `PositivityExt` / `PositivityExt` 的定义

English:
structure PositivityExt
  parameters: where
  axioms and operations (1):
    - eval({u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (pα? : Option Q(PartialOrder $α)) (e : Q($α))) : MetaM (Strictness zα e pα?)

中文:
结构 PositivityExt
  参数: where
  公理与运算 (1 个):
    - eval({u : Level} {α : Q(类型u)} (zα : Q(零 $α)) (pα? : 选项类型 Q(偏序 $α)) (e : Q($α))) : MetaM (Strictness zα e pα?)
-/
structure PositivityExt where
  /-- Attempts to prove an expression `e : α` is `>0`, `≥0`, or `≠0`. -/
  eval {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (pα? : Option Q(PartialOrder $α)) (e : Q($α)) :
    MetaM (Strictness zα e pα?)

/--
Definition of `mkPositivityExt` / `mkPositivityExt` 的定义

English:
definition mkPositivityExt
  signature: (n : Name)
  body: do
  let { env, opts, .. } ← read
IO.ofExcept unsafe env.evalConstCheck PositivityExt opts ``PositivityExt n

中文:
定义 mkPositivityExt
  签名: (n : Name)
  定义体: do
  let { env, opts, .. } ← read
IO.ofExcept unsafe env.evalConstCheck PositivityExt opts ``PositivityExt n
-/
def mkPositivityExt (n : Name) : ImportM PositivityExt := do
  let { env, opts, .. } ← read
IO.ofExcept unsafe env.evalConstCheck PositivityExt opts ``PositivityExt n

/--
Definition of `Entry` / `Entry` 的定义

English:
abbreviation Entry
  body: Array (Array DiscrTree.Key) × Name

中文:
缩写 Entry
  定义体: Array (Array DiscrTree.Key) × Name

Depends on / 依赖: DiscrTree, DiscrTree.Key
-/
abbrev Entry := Array (Array DiscrTree.Key) × Name

/-- Environment extensions for `positivity` declarations -/
initialize positivityExt : PersistentEnvExtension Entry (Entry × PositivityExt)
    (List Entry × DiscrTree PositivityExt) ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq PositivityExt := ⟨fun _ _ => false⟩
  let insert kss v dt := kss.foldl (fun dt ks => dt.insertKeyValue ks v) dt
  registerPersistentEnvExtension {
    mkInitial := pure ([], {})
    addImportedFn := fun s => do
      let dt ← s.foldlM (init := {}) fun dt s => s.foldlM (init := dt) fun dt (kss, n) => do
        pure (insert kss (← mkPositivityExt n) dt)
      pure ([], dt)
    addEntryFn := fun (entries, s) ((kss, n), ext) => ((kss, n) :: entries, insert kss ext s)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

initialize registerBuiltinAttribute {
  name := `positivity
  descr := "adds a positivity extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| positivity $es,*) => do
      ensureAttrDeclIsMeta `positivity declName kind
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'positivity', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'positivity', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkPositivityExt declName
let keys ← MetaM.run' es.getElems.mapM fun stx => do
let e ← TermElabM.run' withSaveInfoContext withAutoBoundImplicit
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
setEnv positivityExt.addEntry env ((keys, declName), ext)
      -- TODO: track what `[positivity]` decls are actually used at use sites
      recordExtraRevUseOfCurrentModule
    | _ => throwUnsupportedSyntax
}

variable {A : Type*} {e : A}

/--
lemma `pos_of_isNat` / 引理 `pos_of_isNat`

English:
lemma pos_of_isNat
  statement: {n : Nat} [Semiring A] [PartialOrder A] [IsOrderedRing A] [Nontrivial A]
  proof: by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Nat.cast_pos.2
  simpa using! w

中文:
引理 pos_of_is自然数
  结论: {n : 自然数} [半环 A] [偏序 A] [是Ordered环 A] [非平凡 A]
  证明: by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Nat.cast_pos.2
  simpa using! w

Depends on / 依赖: Nat.cast_pos, NormNum, NormNum.IsNat.to_eq, cast_pos, to_eq
-/
lemma pos_of_isNat {n : Nat} [Semiring A] [PartialOrder A] [IsOrderedRing A] [Nontrivial A]
    (h : NormNum.IsNat e n) (w : Nat.ble 1 n = true) : 0 < (e : A) := by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Nat.cast_pos.2
  simpa using! w

/--
lemma `pos_of_isNat'` / 引理 `pos_of_isNat'`

English:
lemma pos_of_isNat'
  statement: {n : Nat}
  proof: by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Nat.cast_pos'.2
  simpa using! w

中文:
引理 pos_of_is自然数'
  结论: {n : 自然数}
  证明: by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Nat.cast_pos'.2
  simpa using! w

Depends on / 依赖: Nat.cast_pos, NormNum, NormNum.IsNat.to_eq, cast_pos, to_eq
-/
lemma pos_of_isNat' {n : Nat}
    [AddMonoidWithOne A] [PartialOrder A] [AddLeftMono A] [ZeroLEOneClass A] [h'' : NeZero (1 : A)]
    (h : NormNum.IsNat e n) (w : Nat.ble 1 n = true) : 0 < (e : A) := by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Nat.cast_pos'.2
  simpa using! w

/--
lemma `nonneg_of_isNat` / 引理 `nonneg_of_isNat`

English:
lemma nonneg_of_isNat
  statement: {n : Nat} [Semiring A] [PartialOrder A] [IsOrderedRing A]
  proof: by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Nat.cast_nonneg n

中文:
引理 nonneg_of_is自然数
  结论: {n : 自然数} [半环 A] [偏序 A] [是Ordered环 A]
  证明: by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Nat.cast_nonneg n

Depends on / 依赖: Nat.cast_nonneg, NormNum, NormNum.IsNat.to_eq, cast_nonneg, to_eq
-/
lemma nonneg_of_isNat {n : Nat} [Semiring A] [PartialOrder A] [IsOrderedRing A]
    (h : NormNum.IsNat e n) : 0 <= (e : A) := by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Nat.cast_nonneg n

/--
lemma `nonneg_of_isNat'` / 引理 `nonneg_of_isNat'`

English:
lemma nonneg_of_isNat'
  statement: {n : Nat}
  proof: by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Nat.cast_nonneg' n

中文:
引理 nonneg_of_is自然数'
  结论: {n : 自然数}
  证明: by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Nat.cast_nonneg' n

Depends on / 依赖: Nat.cast_nonneg, NormNum, NormNum.IsNat.to_eq, cast_nonneg, to_eq
-/
lemma nonneg_of_isNat' {n : Nat}
    [AddMonoidWithOne A] [PartialOrder A] [AddLeftMono A] [ZeroLEOneClass A]
    (h : NormNum.IsNat e n) : 0 <= (e : A) := by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Nat.cast_nonneg' n

/--
lemma `nz_of_isNegNat` / 引理 `nz_of_isNegNat`

English:
lemma nz_of_isNegNat
  statement: {n : Nat} [Ring A] [PartialOrder A] [IsStrictOrderedRing A]
  proof: by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  simp only [ne_eq, neg_eq_zero]
  apply ne_of_gt
  simpa using! w

中文:
引理 nz_of_isNeg自然数
  结论: {n : 自然数} [环 A] [偏序 A] [是StrictOrdered环 A]
  证明: by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  simp only [ne_eq, neg_eq_zero]
  apply ne_of_gt
  simpa using! w

Depends on / 依赖: NormNum, NormNum.IsInt.neg_to_eq, ne_eq, ne_of_gt, neg_eq_zero, neg_to_eq
-/
lemma nz_of_isNegNat {n : Nat} [Ring A] [PartialOrder A] [IsStrictOrderedRing A]
    (h : NormNum.IsInt e (.negOfNat n)) (w : Nat.ble 1 n = true) : (e : A) != 0 := by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  simp only [ne_eq, neg_eq_zero]
  apply ne_of_gt
  simpa using! w

/--
lemma `pos_of_isNNRat` / 引理 `pos_of_isNNRat`

English:
lemma pos_of_isNNRat
  given: {n d : Nat} [Semiring A] [LinearOrder A] [IsStrictOrderedRing A]
  proof: pos_invOf_of_invertible_cast d
.2 (of_decide_eq_true h) have pos_n : (0 < (n : A)) := Nat.cast_pos (n := n)
    rw [eq]
    exact mul_pos pos_n pos_invOf_d

中文:
引理 pos_of_isNNRat
  条件: {n d : 自然数} [半环 A] [线性序 A] [是StrictOrdered环 A]
  证明: pos_invOf_of_invertible_cast d
.2 (of_decide_eq_true h) have pos_n : (0 < (n : A)) := Nat.cast_pos (n := n)
    rw [eq]
    exact mul_pos pos_n pos_invOf_d

Depends on / 依赖: pos_invOf_of_invertible_cast
-/
lemma pos_of_isNNRat {n d : Nat} [Semiring A] [LinearOrder A] [IsStrictOrderedRing A] :
    (NormNum.IsNNRat e n d) -> (decide (0 < n)) -> ((0 : A) < (e : A))
  | ⟨inv, eq⟩, h => by
    have pos_invOf_d : (0 < ⅟ (d : A)) := pos_invOf_of_invertible_cast d
.2 (of_decide_eq_true h) have pos_n : (0 < (n : A)) := Nat.cast_pos (n := n)
    rw [eq]
    exact mul_pos pos_n pos_invOf_d

/--
lemma `pos_of_isRat` / 引理 `pos_of_isRat`

English:
lemma pos_of_isRat
  given: {n : Int} {d : Nat} [Ring A] [LinearOrder A] [IsStrictOrderedRing A]
  proof: pos_invOf_of_invertible_cast d
.2 (of_decide_eq_true h) have pos_n : (0 < (n : A)) := Int.cast_pos (n := n)
    rw [eq]
    exact mul_pos pos_n pos_invOf_d

中文:
引理 pos_of_isRat
  条件: {n : 整数} {d : 自然数} [环 A] [线性序 A] [是StrictOrdered环 A]
  证明: pos_invOf_of_invertible_cast d
.2 (of_decide_eq_true h) have pos_n : (0 < (n : A)) := Int.cast_pos (n := n)
    rw [eq]
    exact mul_pos pos_n pos_invOf_d

Depends on / 依赖: pos_invOf_of_invertible_cast
-/
lemma pos_of_isRat {n : Int} {d : Nat} [Ring A] [LinearOrder A] [IsStrictOrderedRing A] :
    (NormNum.IsRat e n d) -> (decide (0 < n)) -> ((0 : A) < (e : A))
  | ⟨inv, eq⟩, h => by
    have pos_invOf_d : (0 < ⅟(d : A)) := pos_invOf_of_invertible_cast d
.2 (of_decide_eq_true h) have pos_n : (0 < (n : A)) := Int.cast_pos (n := n)
    rw [eq]
    exact mul_pos pos_n pos_invOf_d

/--
lemma `nonneg_of_isNNRat` / 引理 `nonneg_of_isNNRat`

English:
lemma nonneg_of_isNNRat
  given: {n d : Nat} [Semiring A] [LinearOrder A]

中文:
引理 nonneg_of_isNNRat
  条件: {n d : 自然数} [半环 A] [线性序 A]
-/
lemma nonneg_of_isNNRat {n d : Nat} [Semiring A] [LinearOrder A] :
    (NormNum.IsNNRat e n d) -> (decide (n = 0)) -> (0 <= (e : A))
  | ⟨inv, eq⟩, h => by rw [eq, of_decide_eq_true h]; simp

/--
lemma `nonneg_of_isRat` / 引理 `nonneg_of_isRat`

English:
lemma nonneg_of_isRat
  given: {n : Int} {d : Nat} [Ring A] [LinearOrder A]

中文:
引理 nonneg_of_isRat
  条件: {n : 整数} {d : 自然数} [环 A] [线性序 A]
-/
lemma nonneg_of_isRat {n : Int} {d : Nat} [Ring A] [LinearOrder A] :
    (NormNum.IsRat e n d) -> (decide (n = 0)) -> (0 <= (e : A))
  | ⟨inv, eq⟩, h => by rw [eq, of_decide_eq_true h]; simp

/--
lemma `nz_of_isRat` / 引理 `nz_of_isRat`

English:
lemma nz_of_isRat
  given: {n : Int} {d : Nat} [Ring A] [LinearOrder A] [IsStrictOrderedRing A]
  proof: pos_invOf_of_invertible_cast d
.2 (of_decide_eq_true h) have neg_n : ((n : A) < 0) := Int.cast_lt_zero (n := n)
    have neg := mul_neg_of_neg_of_pos neg_n pos_invOf_d
    rw [eq]
    exact ne_iff_lt_or_gt.2 (Or.inl neg)

中文:
引理 nz_of_isRat
  条件: {n : 整数} {d : 自然数} [环 A] [线性序 A] [是StrictOrdered环 A]
  证明: pos_invOf_of_invertible_cast d
.2 (of_decide_eq_true h) have neg_n : ((n : A) < 0) := Int.cast_lt_zero (n := n)
    have neg := mul_neg_of_neg_of_pos neg_n pos_invOf_d
    rw [eq]
    exact ne_iff_lt_or_gt.2 (Or.inl neg)

Depends on / 依赖: pos_invOf_of_invertible_cast
-/
lemma nz_of_isRat {n : Int} {d : Nat} [Ring A] [LinearOrder A] [IsStrictOrderedRing A] :
    (NormNum.IsRat e n d) -> (decide (n < 0)) -> ((e : A) != 0)
  | ⟨inv, eq⟩, h => by
    have pos_invOf_d : (0 < ⅟(d : A)) := pos_invOf_of_invertible_cast d
.2 (of_decide_eq_true h) have neg_n : ((n : A) < 0) := Int.cast_lt_zero (n := n)
    have neg := mul_neg_of_neg_of_pos neg_n pos_invOf_d
    rw [eq]
    exact ne_iff_lt_or_gt.2 (Or.inl neg)

variable {zα} in
/--
Definition of `catchNone` / `catchNone` 的定义

English:
definition catchNone
  signature: {e pα?} (t : MetaM (Strictness zα e pα?))
  body: try t catch e =>
    trace[Tactic.positivity.failure] "{e.toMessageData}"
    pure .none

中文:
定义 catchNone
  签名: {e pα?} (t : MetaM (Strictness zα e pα?))
  定义体: try t catch e =>
    trace[Tactic.positivity.failure] "{e.toMessageData}"
    pure .none

Depends on / 依赖: Tactic, Tactic.positivity.failure, e.toMessageData, failure, toMessageData
-/
def catchNone {e pα?} (t : MetaM (Strictness zα e pα?)) : MetaM (Strictness zα e pα?) :=
  try t catch e =>
    trace[Tactic.positivity.failure] "{e.toMessageData}"
    pure .none

variable {zα} in
/--
Definition of `throwNone` / `throwNone` 的定义

English:
definition throwNone
  signature: {e pα?} (t : MetaM (Strictness zα e pα?))
  body: do
  match ← t with
  | .none => throwError "Strictness result was `{.ofConstName ``Strictness.none}`."
  | r => pure r

中文:
定义 throwNone
  签名: {e pα?} (t : MetaM (Strictness zα e pα?))
  定义体: do
  match ← t with
  | .none => throwError "Strictness result was `{.ofConstName ``Strictness.none}`."
  | r => pure r
-/
def throwNone {e pα?} (t : MetaM (Strictness zα e pα?)) : MetaM (Strictness zα e pα?) := do
  match ← t with
  | .none => throwError "Strictness result was `{.ofConstName ``Strictness.none}`."
  | r => pure r

/--
Definition of `normNumPositivity` / `normNumPositivity` 的定义

English:
definition normNumPositivity
  signature: (pα : Q(PartialOrder $α)) (e : Q($α))
  body: catchNone do
  match ← NormNum.derive e with
  | .isBool .. => failure
  | .isNat _ lit p =>
    if 0 < lit.natLit! then
      -- NB. The `try` branch is actually a special case of the `catch` branch,
      -- hence is not strictly necessary. However, this makes a small but measurable performance
  

中文:
定义 normNumPositivity
  签名: (pα : Q(偏序 $α)) (e : Q($α))
  定义体: catchNone do
  match ← NormNum.derive e with
  | .isBool .. => failure
  | .isNat _ lit p =>
    if 0 < lit.natLit! then
      -- NB. The `try` branch is actually a special case of the `catch` branch,
      -- hence is not strictly necessary. However, this makes a small but measurable performance
  

Depends on / 依赖: catchNone
-/
def normNumPositivity (pα : Q(PartialOrder $α)) (e : Q($α))
    : MetaM (Strictness zα e (some pα)) := catchNone do
  match ← NormNum.derive e with
  | .isBool .. => failure
  | .isNat _ lit p =>
    if 0 < lit.natLit! then
      -- NB. The `try` branch is actually a special case of the `catch` branch,
      -- hence is not strictly necessary. However, this makes a small but measurable performance
      -- difference, as synthesising the `try` classes is a bit faster.
      try
        let _a ← synthInstanceQ q(Semiring $α)
        let _a ← synthInstanceQ q(PartialOrder $α)
        let _a ← synthInstanceQ q(IsOrderedRing $α)
        let _a ← synthInstanceQ q(Nontrivial $α)
        assumeInstancesCommute
        have p : Q(NormNum.IsNat $e $lit) := p
haveI' p' : Nat.ble 1 lit =Q true := ⟨⟩
        pure (.positive q(pos_of_isNat (A := $α) $p $p'))
      catch e : Exception =>
        trace[Tactic.positivity.failure] "{e.toMessageData}"
        let _a ← synthInstanceQ q(AddMonoidWithOne $α)
        let _a ← synthInstanceQ q(PartialOrder $α)
        let _a ← synthInstanceQ q(AddLeftMono $α)
        let _a ← synthInstanceQ q(ZeroLEOneClass $α)
        let _a ← synthInstanceQ q(NeZero (1 : $α))
        assumeInstancesCommute
        have p : Q(NormNum.IsNat $e $lit) := p
haveI' p' : Nat.ble 1 lit =Q true := ⟨⟩
        pure (.positive q(pos_of_isNat' (A := $α) $p $p'))
    else
      -- NB. The `try` branch is actually a special case of the `catch` branch,
      -- hence is not strictly necessary. However, this makes a small but measurable performance
      -- difference, as synthesising the `try` classes is a bit faster.
      try
        let _a ← synthInstanceQ q(Semiring $α)
        let _a ← synthInstanceQ q(PartialOrder $α)
        let _a ← synthInstanceQ q(IsOrderedRing $α)
        assumeInstancesCommute
        have p : Q(NormNum.IsNat $e $lit) := p
        pure (.nonnegative q(nonneg_of_isNat $p))
      catch e : Exception =>
        trace[Tactic.positivity.failure] "{e.toMessageData}"
        let _a ← synthInstanceQ q(AddMonoidWithOne $α)
        let _a ← synthInstanceQ q(PartialOrder $α)
        let _a ← synthInstanceQ q(AddLeftMono $α)
        let _a ← synthInstanceQ q(ZeroLEOneClass $α)
        assumeInstancesCommute
        have p : Q(NormNum.IsNat $e $lit) := p
        pure (.nonnegative q(nonneg_of_isNat' $p))
  | .isNegNat _ lit p =>
    let _a ← synthInstanceQ q(Ring $α)
    let _a ← synthInstanceQ q(PartialOrder $α)
    let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    have p : Q(NormNum.IsInt $e (Int.negOfNat $lit)) := p
haveI' p' : Nat.ble 1 lit =Q true := ⟨⟩
    pure (.nonzero q(nz_of_isNegNat $p $p'))
  | .isNNRat _i q n d p =>
    let _a ← synthInstanceQ q(Semiring $α)
    let _a ← synthInstanceQ q(LinearOrder $α)
    let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    have p : Q(NormNum.IsNNRat $e $n $d) := p
    if 0 < q then
      haveI' w : decide (0 < $n) =Q true := ⟨⟩
      pure (.positive q(pos_of_isNNRat $p $w))
    else -- should not be reachable, but just in case
      haveI' w : decide ($n = 0) =Q true := ⟨⟩
      pure (.nonnegative q(nonneg_of_isNNRat $p $w))
  | .isNegNNRat _i q n d p =>
    let _a ← synthInstanceQ q(Ring $α)
    let _a ← synthInstanceQ q(LinearOrder $α)
    let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    have p : Q(NormNum.IsRat $e (.negOfNat $n) $d) := p
    if q < 0 then
      haveI' w : decide (Int.negOfNat $n < 0) =Q true := ⟨⟩
      pure (.nonzero q(nz_of_isRat $p $w))
    else -- should not be reachable, but just in case
      haveI' w : decide (Int.negOfNat $n = 0) =Q true := ⟨⟩
      pure (.nonnegative q(nonneg_of_isRat $p $w))

/--
Definition of `positivityCanon` / `positivityCanon` 的定义

English:
definition positivityCanon
  signature: (pα : Q(PartialOrder $α)) (e : Q($α))
  body: do
  let _add ← synthInstanceQ q(AddMonoid $α)
  let _le ← synthInstanceQ q(PartialOrder $α)
  let _i ← synthInstanceQ q(CanonicallyOrderedAdd $α)
  assumeInstancesCommute
  pure (.nonnegative q(zero_le (a := $e)))

中文:
定义 positivityCanon
  签名: (pα : Q(偏序 $α)) (e : Q($α))
  定义体: do
  let _add ← synthInstanceQ q(AddMonoid $α)
  let _le ← synthInstanceQ q(PartialOrder $α)
  let _i ← synthInstanceQ q(CanonicallyOrderedAdd $α)
  assumeInstancesCommute
  pure (.nonnegative q(zero_le (a := $e)))
-/
def positivityCanon (pα : Q(PartialOrder $α)) (e : Q($α)) : MetaM (Strictness zα e (some pα)) := do
  let _add ← synthInstanceQ q(AddMonoid $α)
  let _le ← synthInstanceQ q(PartialOrder $α)
  let _i ← synthInstanceQ q(CanonicallyOrderedAdd $α)
  assumeInstancesCommute
  pure (.nonnegative q(zero_le (a := $e)))

/--
Definition of `compareHypLE` / `compareHypLE` 的定义

English:
definition compareHypLE
  signature: (pα : Q(PartialOrder $α)) (lo e : Q($α)) (p₂ : Q($lo <= $e))
  body: do
  match ← normNumPositivity zα pα lo with
  | .positive p₁ => pure (.positive q(lt_of_lt_of_le $p₁ $p₂))
  | .nonnegative p₁ => pure (.nonnegative q(le_trans $p₁ $p₂))
  | _ => pure .none

中文:
定义 compareHypLE
  签名: (pα : Q(偏序 $α)) (lo e : Q($α)) (p₂ : Q($lo <= $e))
  定义体: do
  match ← normNumPositivity zα pα lo with
  | .positive p₁ => pure (.positive q(lt_of_lt_of_le $p₁ $p₂))
  | .nonnegative p₁ => pure (.nonnegative q(le_trans $p₁ $p₂))
  | _ => pure .none
-/
def compareHypLE (pα : Q(PartialOrder $α)) (lo e : Q($α)) (p₂ : Q($lo <= $e))
    : MetaM (Strictness zα e pα) := do
  match ← normNumPositivity zα pα lo with
  | .positive p₁ => pure (.positive q(lt_of_lt_of_le $p₁ $p₂))
  | .nonnegative p₁ => pure (.nonnegative q(le_trans $p₁ $p₂))
  | _ => pure .none

/--
Definition of `compareHypLT` / `compareHypLT` 的定义

English:
definition compareHypLT
  signature: (pα : Q(PartialOrder $α)) (lo e : Q($α)) (p₂ : Q($lo < $e))
  body: do
  match ← normNumPositivity zα pα lo with
  | .positive p₁ => pure (.positive q(lt_trans $p₁ $p₂))
  | .nonnegative p₁ => pure (.positive q(lt_of_le_of_lt $p₁ $p₂))
  | _ => pure .none

中文:
定义 compareHypLT
  签名: (pα : Q(偏序 $α)) (lo e : Q($α)) (p₂ : Q($lo < $e))
  定义体: do
  match ← normNumPositivity zα pα lo with
  | .positive p₁ => pure (.positive q(lt_trans $p₁ $p₂))
  | .nonnegative p₁ => pure (.positive q(lt_of_le_of_lt $p₁ $p₂))
  | _ => pure .none
-/
def compareHypLT (pα : Q(PartialOrder $α)) (lo e : Q($α)) (p₂ : Q($lo < $e)) :
    MetaM (Strictness zα e pα) := do
  match ← normNumPositivity zα pα lo with
  | .positive p₁ => pure (.positive q(lt_trans $p₁ $p₂))
  | .nonnegative p₁ => pure (.positive q(lt_of_le_of_lt $p₁ $p₂))
  | _ => pure .none

/--
Definition of `compareHypEq` / `compareHypEq` 的定义

English:
definition compareHypEq
  signature: (pα : Q(PartialOrder $α)) (e x : Q($α)) (p₂ : Q($x = $e))
  body: do
  match ← normNumPositivity zα pα x with
  | .positive p₁ => pure (.positive q(lt_of_lt_of_eq $p₁ $p₂))
  | .nonnegative p₁ => pure (.nonnegative q(le_of_le_of_eq $p₁ $p₂))
  | .nonzero p₁ => pure (.nonzero q(ne_of_ne_of_eq' $p₁ $p₂))
  | .none => pure .none

中文:
定义 compareHypEq
  签名: (pα : Q(偏序 $α)) (e x : Q($α)) (p₂ : Q($x = $e))
  定义体: do
  match ← normNumPositivity zα pα x with
  | .positive p₁ => pure (.positive q(lt_of_lt_of_eq $p₁ $p₂))
  | .nonnegative p₁ => pure (.nonnegative q(le_of_le_of_eq $p₁ $p₂))
  | .nonzero p₁ => pure (.nonzero q(ne_of_ne_of_eq' $p₁ $p₂))
  | .none => pure .none
-/
def compareHypEq (pα : Q(PartialOrder $α)) (e x : Q($α)) (p₂ : Q($x = $e)) :
    MetaM (Strictness zα e pα) := do
  match ← normNumPositivity zα pα x with
  | .positive p₁ => pure (.positive q(lt_of_lt_of_eq $p₁ $p₂))
  | .nonnegative p₁ => pure (.nonnegative q(le_of_le_of_eq $p₁ $p₂))
  | .nonzero p₁ => pure (.nonzero q(ne_of_ne_of_eq' $p₁ $p₂))
  | .none => pure .none

initialize registerTraceClass `Tactic.positivity
initialize registerTraceClass `Tactic.positivity.failure

/--
Definition of `compareHyp` / `compareHyp` 的定义

English:
definition compareHyp
  signature: (pα : Q(PartialOrder $α)) (e : Q($α)) (ldecl : LocalDecl)
  body: do
  unless ← isProp ldecl.type do return .none
  have e' : Q(Prop) := ldecl.type
  let p : Q($e') := .fvar ldecl.fvarId
  match e' with
  | ~q(@LE.le.{u} $β $_le $lo $hi) =>
    let .defEq (_ : $α =Q $β) ← isDefEqQ α β | return .none
    let .defEq _ ← isDefEqQ e hi | return .none
    match lo with

中文:
定义 compareHyp
  签名: (pα : Q(偏序 $α)) (e : Q($α)) (ldecl : LocalDecl)
  定义体: do
  unless ← isProp ldecl.type do return .none
  have e' : Q(Prop) := ldecl.type
  let p : Q($e') := .fvar ldecl.fvarId
  match e' with
  | ~q(@LE.le.{u} $β $_le $lo $hi) =>
    let .defEq (_ : $α =Q $β) ← isDefEqQ α β | return .none
    let .defEq _ ← isDefEqQ e hi | return .none
    match lo with
-/
def compareHyp (pα : Q(PartialOrder $α)) (e : Q($α)) (ldecl : LocalDecl) :
    MetaM (Strictness zα e pα) := do
  unless ← isProp ldecl.type do return .none
  have e' : Q(Prop) := ldecl.type
  let p : Q($e') := .fvar ldecl.fvarId
  match e' with
  | ~q(@LE.le.{u} $β $_le $lo $hi) =>
    let .defEq (_ : $α =Q $β) ← isDefEqQ α β | return .none
    let .defEq _ ← isDefEqQ e hi | return .none
    match lo with
    | ~q(0) =>
      assertInstancesCommute
      return .nonnegative q($p)
    | _ => compareHypLE zα pα lo e p
  | ~q(@LT.lt.{u} $β $_lt $lo $hi) =>
    let .defEq (_ : $α =Q $β) ← isDefEqQ α β | return .none
    let .defEq _ ← isDefEqQ e hi | return .none
    match lo with
    | ~q(0) =>
      assertInstancesCommute
      return .positive q($p)
    | _ => compareHypLT zα pα lo e p
  | ~q(@Eq.{u+1} $α' $lhs $rhs) =>
    let .defEq (_ : $α =Q $α') ← isDefEqQ α α' | pure .none
    match ← isDefEqQ e rhs with
    | .defEq _ =>
      match lhs with
| ~q(0) => pure .nonnegative q(le_of_eq $p)
      | _ => compareHypEq zα pα e lhs q($p)
    | .notDefEq =>
      let .defEq _ ← isDefEqQ e lhs | pure .none
      match rhs with
| ~q(0) => pure .nonnegative q(ge_of_eq $p)
      | _ => compareHypEq zα pα e rhs q(Eq.symm $p)
  | ~q(@Ne.{u+1} $α' $lhs $rhs) =>
    let .defEq (_ : $α =Q $α') ← isDefEqQ α α' | pure .none
    match lhs, rhs with
    | ~q(0), _ =>
      let .defEq _ ← isDefEqQ e rhs | pure .none
pure .nonzero q(Ne.symm $p)
    | _, ~q(0) =>
      let .defEq _ ← isDefEqQ e lhs | pure .none
pure .nonzero q($p)
    | _, _ => pure .none
  | _ => pure .none

/--
Definition of `compareHypNonzero` / `compareHypNonzero` 的定义

English:
definition compareHypNonzero
  signature: {pα?} (e : Q($α)) (ldecl : LocalDecl)
  body: do
  unless ← isProp ldecl.type do return .none
  have e' : Q(Prop) := ldecl.type
  let p : Q($e') := .fvar ldecl.fvarId
  match e' with
  | ~q(@Ne.{u+1} $α' $lhs $rhs) =>
    let .defEq (_ : $α =Q $α') ← isDefEqQ α α' | pure .none
    match lhs, rhs with
    | ~q(0), _ =>
      let .defEq _ ← isDef

中文:
定义 compareHypNonzero
  签名: {pα?} (e : Q($α)) (ldecl : LocalDecl)
  定义体: do
  unless ← isProp ldecl.type do return .none
  have e' : Q(Prop) := ldecl.type
  let p : Q($e') := .fvar ldecl.fvarId
  match e' with
  | ~q(@Ne.{u+1} $α' $lhs $rhs) =>
    let .defEq (_ : $α =Q $α') ← isDefEqQ α α' | pure .none
    match lhs, rhs with
    | ~q(0), _ =>
      let .defEq _ ← isDef
-/
def compareHypNonzero {pα?} (e : Q($α)) (ldecl : LocalDecl) : MetaM (Strictness zα e pα?) := do
  unless ← isProp ldecl.type do return .none
  have e' : Q(Prop) := ldecl.type
  let p : Q($e') := .fvar ldecl.fvarId
  match e' with
  | ~q(@Ne.{u+1} $α' $lhs $rhs) =>
    let .defEq (_ : $α =Q $α') ← isDefEqQ α α' | pure .none
    match lhs, rhs with
    | ~q(0), _ =>
      let .defEq _ ← isDefEqQ e rhs | pure .none
pure .nonzero q(Ne.symm $p)
    | _, ~q(0) =>
      let .defEq _ ← isDefEqQ e lhs | pure .none
pure .nonzero q($p)
    | _, _ => pure .none
  | _ => pure .none

variable {zα} in
/--
Definition of `orElse` / `orElse` 的定义

English:
definition orElse
  signature: {pα?} {e : Q($α)} (t₁ : Strictness zα e pα?) (t₂ : MetaM (Strictness zα e pα?))
  body: match t₁ with
  | .none => catchNone t₂
  | p@(.positive _) => pure p
  | .nonnegative p₁ => do
    match ← catchNone t₂ with
    | p@(.positive _) => pure p
    | .nonzero p₂ => pure (.positive q(lt_of_le_of_ne' $p₁ $p₂))
    | _ => pure (.nonnegative p₁)
  | .nonzero p₁ => do
    match (dependent 

中文:
定义 orElse
  签名: {pα?} {e : Q($α)} (t₁ : Strictness zα e pα?) (t₂ : MetaM (Strictness zα e pα?))
  定义体: match t₁ with
  | .none => catchNone t₂
  | p@(.positive _) => pure p
  | .nonnegative p₁ => do
    match ← catchNone t₂ with
    | p@(.positive _) => pure p
    | .nonzero p₂ => pure (.positive q(lt_of_le_of_ne' $p₁ $p₂))
    | _ => pure (.nonnegative p₁)
  | .nonzero p₁ => do
    match (dependent 

Depends on / 依赖: catchNone, dependent, lt_of_le_of_ne, nonnegative, nonzero, positive
-/
def orElse {pα?} {e : Q($α)} (t₁ : Strictness zα e pα?) (t₂ : MetaM (Strictness zα e pα?)) :
    MetaM (Strictness zα e pα?) :=
  match t₁ with
  | .none => catchNone t₂
  | p@(.positive _) => pure p
  | .nonnegative p₁ => do
    match ← catchNone t₂ with
    | p@(.positive _) => pure p
    | .nonzero p₂ => pure (.positive q(lt_of_le_of_ne' $p₁ $p₂))
    | _ => pure (.nonnegative p₁)
  | .nonzero p₁ => do
    match (dependent := true) ← catchNone t₂ with
    | p@(.positive _) => pure p
    | .nonnegative p₂ => pure (.positive q(lt_of_le_of_ne' $p₂ $p₁))
    | _ => pure (.nonzero p₁)

/--
Definition of `core` / `core` 的定义

English:
definition core
  signature: (pα? : Option Q(PartialOrder $α)) (e : Q($α))
  body: do
  let mut result := .none
  trace[Tactic.positivity] "trying to prove positivity of {e}"
  for ext in ← (positivityExt.getState (← getEnv)).2.getMatch e do
    try
result ← orElse result ext.eval zα pα? e
    catch err =>
      trace[Tactic.positivity] "{e} failed: {err.toMessageData}"
  trace[Ta

中文:
定义 core
  签名: (pα? : 选项类型 Q(偏序 $α)) (e : Q($α))
  定义体: do
  let mut result := .none
  trace[Tactic.positivity] "trying to prove positivity of {e}"
  for ext in ← (positivityExt.getState (← getEnv)).2.getMatch e do
    try
result ← orElse result ext.eval zα pα? e
    catch err =>
      trace[Tactic.positivity] "{e} failed: {err.toMessageData}"
  trace[Ta
-/
def core (pα? : Option Q(PartialOrder $α)) (e : Q($α)) : MetaM (Strictness zα e pα?) := do
  let mut result := .none
  trace[Tactic.positivity] "trying to prove positivity of {e}"
  for ext in ← (positivityExt.getState (← getEnv)).2.getMatch e do
    try
result ← orElse result ext.eval zα pα? e
    catch err =>
      trace[Tactic.positivity] "{e} failed: {err.toMessageData}"
  trace[Tactic.positivity] "current result from positivity extensions: {result.toString}"
  match h : pα?, result with
  | some pα, res =>
    trace[Tactic.positivity] "{α} has some {pα}"
let mut res ← orElse res normNumPositivity zα pα e
    trace[Tactic.positivity] "current result from normNum: {res.toString}"
res ← orElse res positivityCanon zα pα e
    trace[Tactic.positivity] "current result from canonicity: {res.toString}"
    if let .positive _ := res then
      trace[Tactic.positivity] "{e} => {res.toString}"
      return h ▸ res
    for ldecl in ← getLCtx do
      if !ldecl.isImplementationDetail then
res ← orElse res compareHyp zα pα e ldecl
    trace[Tactic.positivity] "{e} => {res.toString}"
    throwNone (pure (h ▸ res))
  | .none, _ =>
    trace[Tactic.positivity] "{α} has no PartialOrder"
    if let .nonzero _ := result then
      trace[Tactic.positivity] "{e} => {result.toString}"
      return result
    for ldecl in ← getLCtx do
      if !ldecl.isImplementationDetail then
result ← orElse result compareHypNonzero zα e ldecl
    trace[Tactic.positivity] "{e} => {result.toString}"
    throwNone (pure result)


/--
Inductive type `OrderRel` / 归纳类型 `OrderRel`

English:
inductive OrderRel
  parameters: : Type
  constructors (4):
    - le: OrderRel -- `0 ≤ a`
    - lt: OrderRel -- `0 < a`
    - ne: OrderRel -- `a ≠ 0`
    - ne': OrderRel -- `0 ≠ a`

中文:
归纳类型 OrderRel
  参数: : 类型
  构造子 (4 个):
    - le: OrderRel -- `0 ≤ a`
    - lt: OrderRel -- `0 < a`
    - ne: OrderRel -- `a ≠ 0`
    - ne': OrderRel -- `0 ≠ a`
-/
private inductive OrderRel : Type
| le : OrderRel -- `0 ≤ a`
| lt : OrderRel -- `0 < a`
| ne : OrderRel -- `a ≠ 0`
| ne' : OrderRel -- `0 ≠ a`

end Meta.Positivity
namespace Meta.Positivity

/--
Definition of `bestResult` / `bestResult` 的定义

English:
definition bestResult
  signature: (e : Expr)
  body: do
  let ⟨u, α, _⟩ ← inferTypeQ' e
  let zα ← synthInstanceQ q(Zero $α)
let pα? ← try? synthInstanceQ q(PartialOrder $α)
  assumeInstancesCommute
  match pα?, ← try? (Meta.Positivity.core zα pα? e) with
  | _, some (.positive pf) => pure (true, pf)
  | _, some (.nonnegative pf) => pure (false, pf)
 

中文:
定义 bestResult
  签名: (e : Expr)
  定义体: do
  let ⟨u, α, _⟩ ← inferTypeQ' e
  let zα ← synthInstanceQ q(Zero $α)
let pα? ← try? synthInstanceQ q(PartialOrder $α)
  assumeInstancesCommute
  match pα?, ← try? (Meta.Positivity.core zα pα? e) with
  | _, some (.positive pf) => pure (true, pf)
  | _, some (.nonnegative pf) => pure (false, pf)
 
-/
def bestResult (e : Expr) : MetaM (Bool × Expr) := do
  let ⟨u, α, _⟩ ← inferTypeQ' e
  let zα ← synthInstanceQ q(Zero $α)
let pα? ← try? synthInstanceQ q(PartialOrder $α)
  assumeInstancesCommute
  match pα?, ← try? (Meta.Positivity.core zα pα? e) with
  | _, some (.positive pf) => pure (true, pf)
  | _, some (.nonnegative pf) => pure (false, pf)
  | _, _ => throwError "could not establish the nonnegativity of {e}"

/--
Definition of `proveNonneg` / `proveNonneg` 的定义

English:
definition proveNonneg
  signature: (e : Expr)
  body: do
  let (strict, pf) ← bestResult e
  if strict then mkAppM ``le_of_lt #[pf] else pure pf

中文:
定义 proveNonneg
  签名: (e : Expr)
  定义体: do
  let (strict, pf) ← bestResult e
  if strict then mkAppM ``le_of_lt #[pf] else pure pf
-/
def proveNonneg (e : Expr) : MetaM Expr := do
  let (strict, pf) ← bestResult e
  if strict then mkAppM ``le_of_lt #[pf] else pure pf

/--
Definition of `solve` / `solve` 的定义

English:
definition solve
  signature: (t : Q(Prop))
  body: do
  let rest {u : Level} (α : Q(Type u)) z e (relDesired : OrderRel) : MetaM Expr := do
    let zα ← synthInstanceQ q(Zero $α)
    let .true ← isDefEq z q(0 : $α) | throwError "not a positivity goal"
let pα? ← try? synthInstanceQ q(PartialOrder $α)
let r ← catchNone Meta.Positivity.core zα pα? e
  

中文:
定义 solve
  签名: (t : Q(命题))
  定义体: do
  let rest {u : Level} (α : Q(Type u)) z e (relDesired : OrderRel) : MetaM Expr := do
    let zα ← synthInstanceQ q(Zero $α)
    let .true ← isDefEq z q(0 : $α) | throwError "not a positivity goal"
let pα? ← try? synthInstanceQ q(PartialOrder $α)
let r ← catchNone Meta.Positivity.core zα pα? e
  
-/
def solve (t : Q(Prop)) : MetaM Expr := do
  let rest {u : Level} (α : Q(Type u)) z e (relDesired : OrderRel) : MetaM Expr := do
    let zα ← synthInstanceQ q(Zero $α)
    let .true ← isDefEq z q(0 : $α) | throwError "not a positivity goal"
let pα? ← try? synthInstanceQ q(PartialOrder $α)
let r ← catchNone Meta.Positivity.core zα pα? e
    let throw (a b : String) : MetaM Expr := throwError
      "failed to prove {a}, but it would be possible to prove {b} if desired"
    match (dependent := true) pα? with
    | some _ =>
      match relDesired, r with
      | .lt, .positive p
      | .le, .nonnegative p
      | .ne, .nonzero p => pure p
      | .le, .positive p => pure q(le_of_lt $p)
      | .ne, .positive p => pure q(ne_of_gt $p)
      | .ne', .positive p => pure q(ne_of_lt $p)
      | .ne', .nonzero p => pure q(Ne.symm $p)
      | .lt, .nonnegative _ => throw "strict positivity" "nonnegativity"
      | .lt, .nonzero _ => throw "strict positivity" "nonzeroness"
      | .le, .nonzero _ => throw "nonnegativity" "nonzeroness"
      | .ne, .nonnegative _
      | .ne', .nonnegative _ => throw "nonzeroness" "nonnegativity"
      | _, .none => throwError "failed to prove positivity/nonnegativity/nonzeroness"
    | none =>
      match relDesired, r with
      | .ne, .nonzero p => pure p
      | .ne', .nonzero p => pure q(Ne.symm $p)
      | .lt, .nonzero _ => throw "strict positivity" "nonzeroness"
      | .le, .nonzero _ => throw "nonnegativity" "nonzeroness"
      | _, _ => throwError "failed to prove nonzeroness"
  match t with
  | ~q(@LE.le $α $_a $z $e) => rest α z e .le
  | ~q(@LT.lt $α $_a $z $e) => rest α z e .lt
  | ~q($a != ($b : ($α : Type _))) =>
    let _zα ← synthInstanceQ q(Zero $α)
    if ← isDefEq b q((0 : $α)) then
      rest α b a .ne
    else
      let .true ← isDefEq a q((0 : $α)) | throwError "not a positivity goal"
      rest α a b .ne'
  | _ => throwError "not a positivity goal"

/--
Definition of `positivity` / `positivity` 的定义

English:
definition positivity
  signature: (goal : MVarId)
  body: do
  let t : Q(Prop) ← withReducible goal.getType'
  let p ← solve t
  goal.assign p

中文:
定义 positivity
  签名: (goal : MVarId)
  定义体: do
  let t : Q(Prop) ← withReducible goal.getType'
  let p ← solve t
  goal.assign p
-/
def positivity (goal : MVarId) : MetaM Unit := do
  let t : Q(Prop) ← withReducible goal.getType'
  let p ← solve t
  goal.assign p

end Meta.Positivity

namespace Tactic.Positivity

open Tactic

/-- `positivity` solves goals of the form `0 ≤ x`, `0 < x` and `x ≠ 0`. The tactic works recursively
according to the syntax of the expression `x`, by attempting to prove subexpressions are
positive/nonnegative/nonzero and combining this into a final proof. This tactic either closes the
goal or fails.

For each subexpression `e`, `positivity` will try to:
* try `@[positivity]`-tagged extensions to recursively prove `e` is positive/nonnegative/nonzero
  based on its subexpressions (see the `positivity` attribute for more details), or
* try the `norm_num` tactic to prove `e` is positive/nonnegative/nonzero, or
* try showing `e : t` is nonnegative because there is a `CanonicallyOrderedAdd t` instance, or
* use a local hypothesis of the form `0 ≤ e`, `0 < e` or `e ≠ 0`.

This tactic is extensible. See the `positivity` attribute documentation for more details.

* `positivity [t₁, …, tₙ]` first executes `have := t₁; …; have := tₙ` in the current goal,
  then runs `positivity`. This is useful when `positivity` needs derived premises such as `0 < y`
  for division/reciprocal, or `0 ≤ x` for real powers.

Examples:
```
example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by positivity

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity

example {a b c d : ℝ} (hab : 0 < a * b) (hb : 0 ≤ b) (hcd : c < d) :
    0 < a ^ c + 1 / (d - c) := by
  positivity [sub_pos_of_lt hcd, pos_of_mul_pos_left hab hb]
```
-/
syntax (name := positivity) "positivity" (" [" term,* "]")? : tactic

elab_rules : tactic
| `(tactic| positivity) => liftMetaTactic fun g => do Meta.Positivity.positivity g; pure []

macro_rules
| `(tactic| positivity [$h,*]) => `(tactic| · ($[have := $h];*); positivity)

end Positivity

end Mathlib.Tactic

/-!
We set up `positivity` as a first-pass discharger for `gcongr` side goals.
-/

macro_rules | `(tactic| gcongr_discharger) => `(tactic| positivity)

/-!
We register `positivity` with the `hint` tactic.
-/

register_hint 1000 positivity
register_try?_tactic (priority := 1000) positivity
