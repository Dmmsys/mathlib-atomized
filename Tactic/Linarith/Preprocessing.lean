/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public meta import Mathlib.Control.Basic
public meta import Mathlib.Lean.Meta.Tactic.Rewrite
public meta import Mathlib.Tactic.Linarith.Datatypes
public meta import Mathlib.Util.AtomM
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Datatypes
public import Mathlib.Tactic.Zify

/-!
# Linarith preprocessing

This file contains methods used to preprocess inputs to `linarith`.

In particular, `linarith` works over comparisons of the form `t R 0`, where `R ∈ {<,≤,=}`.
It assumes that expressions in `t` have integer coefficients and that the type of `t` has
well-behaved subtraction.

## Implementation details

A `GlobalPreprocessor` is a function `List Expr → TacticM (List Expr)`. Users can add custom
preprocessing steps by adding them to the `LinarithConfig` object. `Linarith.defaultPreprocessors`
is the main list, and generally none of these should be skipped unless you know what you're doing.
-/

public meta section

namespace Mathlib.Tactic.Linarith

/-! ### Preprocessing -/

open Lean
open Elab Tactic Meta
open Qq
open Std (TreeSet)

/--
Definition of `splitConjunctions` / `splitConjunctions` 的定义

English:
definition splitConjunctions
  signature: : Preprocessor where
  body: "split conjunctions"
  transform := aux

中文:
定义 splitConjunctions
  签名: : Preprocessor where
  定义体: "split conjunctions"
  transform := aux
-/
partial def splitConjunctions : Preprocessor where
  description := "split conjunctions"
  transform := aux
where
  /-- Implementation of the `splitConjunctions` preprocessor. -/
  aux (proof : Expr) : MetaM (List Expr) := do
    match (← instantiateMVars (← inferType proof)).getAppFnArgs with
    | (``And, #[_, _]) =>
      pure ((← aux (← mkAppM ``And.left #[proof])) ++
        (← aux (← mkAppM ``And.right #[proof])))
    | _ => pure [proof]

/--
Definition of `filterComparisons` / `filterComparisons` 的定义

English:
definition filterComparisons
  signature: : Preprocessor where
  body: "filter terms that are not proofs of comparisons"
  transform h := do
    let tp ← instantiateMVars (← inferType h)
    try
      match tp.not? with
      | some p => match (← p.ineq?).1 with
        | .le => return [← mkAppM ``lt_of_not_ge #[h]]
        | .lt => return [← mkAppM ``le_of_not_gt #[h]

中文:
定义 filterComparisons
  签名: : Preprocessor where
  定义体: "filter terms that are not proofs of comparisons"
  transform h := do
    let tp ← instantiateMVars (← inferType h)
    try
      match tp.not? with
      | some p => match (← p.ineq?).1 with
        | .le => return [← mkAppM ``lt_of_not_ge #[h]]
        | .lt => return [← mkAppM ``le_of_not_gt #[h]
-/
partial def filterComparisons : Preprocessor where
  description := "filter terms that are not proofs of comparisons"
  transform h := do
    let tp ← instantiateMVars (← inferType h)
    try
      match tp.not? with
      | some p => match (← p.ineq?).1 with
        | .le => return [← mkAppM ``lt_of_not_ge #[h]]
        | .lt => return [← mkAppM ``le_of_not_gt #[h]]
        | .eq => return []
      | none =>
        _ ← tp.ineq?
        return [h]
    catch _ =>
      return []

section natToInt

open Zify

/--
Definition of `isNatProp` / `isNatProp` 的定义

English:
definition isNatProp
  signature: (e : Expr)
  body: succeeds do
  let (_, _, .const ``Nat [], _, _) ← e.ineqOrNotIneq? | failure

中文:
定义 isNatProp
  签名: (e : Expr)
  定义体: succeeds do
  let (_, _, .const ``Nat [], _, _) ← e.ineqOrNotIneq? | failure
-/
partial def isNatProp (e : Expr) : MetaM Bool := succeeds do
  let (_, _, .const ``Nat [], _, _) ← e.ineqOrNotIneq? | failure

/--
Definition of `isNatCoe` / `isNatCoe` 的定义

English:
definition isNatCoe
  signature: (e : Expr)
  body: match e.getAppFnArgs with
  | (``Nat.cast, #[target, _, n]) => some ⟨n, target⟩
  | _ => none

中文:
定义 isNatCoe
  签名: (e : Expr)
  定义体: match e.getAppFnArgs with
  | (``Nat.cast, #[target, _, n]) => some ⟨n, target⟩
  | _ => none

Depends on / 依赖: Nat.cast, e.getAppFnArgs, getAppFnArgs, target
-/
def isNatCoe (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Nat.cast, #[target, _, n]) => some ⟨n, target⟩
  | _ => none

/--
Definition of `getNatComparisons` / `getNatComparisons` 的定义

English:
definition getNatComparisons
  signature: (e : Expr)
  body: match isNatCoe e with
  | some x => [x]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``HSub.hSub, #[_, _, _, _, a, b]) => getN

中文:
定义 getNatComparisons
  签名: (e : Expr)
  定义体: match isNatCoe e with
  | some x => [x]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``HSub.hSub, #[_, _, _, _, a, b]) => getN
-/
partial def getNatComparisons (e : Expr) : List (Expr × Expr) :=
  match isNatCoe e with
  | some x => [x]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``HSub.hSub, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``Neg.neg, #[_, _, a]) => getNatComparisons a
    | _ => []

/--
Definition of `mkNatCastNonnegProof?` / `mkNatCastNonnegProof?` 的定义

English:
definition mkNatCastNonnegProof?
  signature: (p : Expr × Expr)
  body: match p with
  | ⟨e, target⟩ => try commitIfNoEx (mkAppM ``natCast_nonneg #[target, e])
    catch e => do
      trace[linarith] "Got exception when using cast {e.toMessageData}"
      return none

@[deprecated (since := "2026-05-27")] alias mk_natCast_nonneg_prf := mkNatCastNonnegProof?

中文:
定义 mkNatCastNonnegProof?
  签名: (p : Expr × Expr)
  定义体: match p with
  | ⟨e, target⟩ => try commitIfNoEx (mkAppM ``natCast_nonneg #[target, e])
    catch e => do
      trace[linarith] "Got exception when using cast {e.toMessageData}"
      return none

@[deprecated (since := "2026-05-27")] alias mk_natCast_nonneg_prf := mkNatCastNonnegProof?

Depends on / 依赖: commitIfNoEx, e.toMessageData, exception, mkAppM, natCast_nonneg, return, target, toMessageData
-/
def mkNatCastNonnegProof? (p : Expr × Expr) : MetaM (Option Expr) :=
  match p with
  | ⟨e, target⟩ => try commitIfNoEx (mkAppM ``natCast_nonneg #[target, e])
    catch e => do
      trace[linarith] "Got exception when using cast {e.toMessageData}"
      return none

@[deprecated (since := "2026-05-27")] alias mk_natCast_nonneg_prf := mkNatCastNonnegProof?

/--
Definition of `natToInt` / `natToInt` 的定义

English:
definition natToInt
  signature: : GlobalBranchingPreprocessor where
  body: "move nats to ints"
  transform g l := do
    let l ← l.mapM fun h => do
      let t ← whnfR (← instantiateMVars (← inferType h))
      if ← isNatProp t then
        let (some (h', t'), _) ← Term.TermElabM.run' (run_for g (zifyProof none h t))
          | throwError "zifyProof failed on {h}"
       

中文:
定义 natToInt
  签名: : GlobalBranchingPreprocessor where
  定义体: "move nats to ints"
  transform g l := do
    let l ← l.mapM fun h => do
      let t ← whnfR (← instantiateMVars (← inferType h))
      if ← isNatProp t then
        let (some (h', t'), _) ← Term.TermElabM.run' (run_for g (zifyProof none h t))
          | throwError "zifyProof failed on {h}"
       
-/
def natToInt : GlobalBranchingPreprocessor where
  description := "move nats to ints"
  transform g l := do
    let l ← l.mapM fun h => do
      let t ← whnfR (← instantiateMVars (← inferType h))
      if ← isNatProp t then
        let (some (h', t'), _) ← Term.TermElabM.run' (run_for g (zifyProof none h t))
          | throwError "zifyProof failed on {h}"
        if ← succeeds t'.ineqOrNotIneq? then
          pure h'
        else
          -- `zifyProof` turned our comparison into something that wasn't a comparison
          -- probably replacing `n = n` with `True`, because of
          -- https://github.com/leanprover-community/mathlib4/issues/741
          -- so we just keep the original hypothesis.
          pure h
      else
        pure h
withNewMCtxDepth AtomM.run .reducible do
    let nonnegs ← l.foldlM (init := ∅) fun (es : TreeSet (Nat × Nat) lexOrd.compare) h => do
      try
        let (_, _, a, b) ← (← inferType h).ineq?
        let getIndices (p : Expr × Expr) : AtomM (Nat × Nat) := do
          return ((← AtomM.addAtom p.1).1, (← AtomM.addAtom p.2).1)
        let indices_a ← (getNatComparisons a).mapM getIndices
        let indices_b ← (getNatComparisons b).mapM getIndices
pure (es.insertMany indices_a).insertMany indices_b
      catch _ => pure es
    let atoms : Array Expr := (← get).atoms
    let nonnegProofs : List Expr ← nonnegs.toList.filterMapM fun p => do
      mkNatCastNonnegProof? (atoms[p.1]!, atoms[p.2]!)
    pure [(g, nonnegProofs ++ l)]

end natToInt

section strengthenStrictInt

/--
Definition of `mkNonstrictIntProof?` / `mkNonstrictIntProof?` 的定义

English:
definition mkNonstrictIntProof?
  signature: (pf : Expr)
  body: do
  match ← (← inferType pf).ineqOrNotIneq? with
  | (true, Ineq.lt, .const ``Int [], a, b) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[a, b]]) pf
  | (false, Ineq.le, .const ``Int [], a, b) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff 

中文:
定义 mkNonstrictIntProof?
  签名: (pf : Expr)
  定义体: do
  match ← (← inferType pf).ineqOrNotIneq? with
  | (true, Ineq.lt, .const ``Int [], a, b) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[a, b]]) pf
  | (false, Ineq.le, .const ``Int [], a, b) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff 
-/
def mkNonstrictIntProof? (pf : Expr) : MetaM (Option Expr) := do
  match ← (← inferType pf).ineqOrNotIneq? with
  | (true, Ineq.lt, .const ``Int [], a, b) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[a, b]]) pf
  | (false, Ineq.le, .const ``Int [], a, b) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[b, a]])
      (← mkAppM ``lt_of_not_ge #[pf])
  | _ => return none

@[deprecated (since := "2026-05-27")] alias mkNonstrictIntProof := mkNonstrictIntProof?

/--
Definition of `strengthenStrictInt` / `strengthenStrictInt` 的定义

English:
definition strengthenStrictInt
  signature: : Preprocessor where
  body: "strengthen strict inequalities over int"
  transform h := return [(← mkNonstrictIntProof? h).getD h]

中文:
定义 strengthenStrictInt
  签名: : Preprocessor where
  定义体: "strengthen strict inequalities over int"
  transform h := return [(← mkNonstrictIntProof? h).getD h]

Depends on / 依赖: inequalities, strengthen, strict
-/
def strengthenStrictInt : Preprocessor where
  description := "strengthen strict inequalities over int"
  transform h := return [(← mkNonstrictIntProof? h).getD h]

end strengthenStrictInt

section compWithZero

/--
Definition of `rearrangeComparison?` / `rearrangeComparison?` 的定义

English:
definition rearrangeComparison?
  signature: (e : Expr)
  body: do
  match ← (← inferType e).ineq? with
| (Ineq.le, _) => try? mkAppM ``Linarith.sub_nonpos_of_le #[e]
| (Ineq.lt, _) => try? mkAppM ``Linarith.sub_neg_of_lt #[e]
| (Ineq.eq, _) => try? mkAppM ``sub_eq_zero_of_eq #[e]

@[deprecated (since := "2026-05-27")] alias rearrangeComparison := rearrangeCompa

中文:
定义 rearrangeComparison?
  签名: (e : Expr)
  定义体: do
  match ← (← inferType e).ineq? with
| (Ineq.le, _) => try? mkAppM ``Linarith.sub_nonpos_of_le #[e]
| (Ineq.lt, _) => try? mkAppM ``Linarith.sub_neg_of_lt #[e]
| (Ineq.eq, _) => try? mkAppM ``sub_eq_zero_of_eq #[e]

@[deprecated (since := "2026-05-27")] alias rearrangeComparison := rearrangeCompa
-/
partial def rearrangeComparison? (e : Expr) : MetaM (Option Expr) := do
  match ← (← inferType e).ineq? with
| (Ineq.le, _) => try? mkAppM ``Linarith.sub_nonpos_of_le #[e]
| (Ineq.lt, _) => try? mkAppM ``Linarith.sub_neg_of_lt #[e]
| (Ineq.eq, _) => try? mkAppM ``sub_eq_zero_of_eq #[e]

@[deprecated (since := "2026-05-27")] alias rearrangeComparison := rearrangeComparison?

/--
Definition of `compWithZero` / `compWithZero` 的定义

English:
definition compWithZero
  signature: : Preprocessor where
  body: "make comparisons with zero"
  transform e := return (← rearrangeComparison? e).toList

中文:
定义 compWithZero
  签名: : Preprocessor where
  定义体: "make comparisons with zero"
  transform e := return (← rearrangeComparison? e).toList

Depends on / 依赖: comparisons
-/
def compWithZero : Preprocessor where
  description := "make comparisons with zero"
  transform e := return (← rearrangeComparison? e).toList

end compWithZero

section cancelDenoms

/--
theorem `without_one_mul` / 定理 `without_one_mul`

English:
theorem without_one_mul
  given: {M : Type*} [MulOneClass M] {a b : M} (h : 1 * a = b)
  statement: a = b
  proof: by
  rwa [one_mul] at h

中文:
定理 without_one_mul
  条件: {M : 类型} [MulOneClass M] {a b : M} (h : 1 * a = b)
  结论: a = b
  证明: by
  rwa [one_mul] at h

Depends on / 依赖: one_mul
-/
theorem without_one_mul {M : Type*} [MulOneClass M] {a b : M} (h : 1 * a = b) : a = b := by
  rwa [one_mul] at h

/--
Definition of `normalizeDenominatorsLHS` / `normalizeDenominatorsLHS` 的定义

English:
definition normalizeDenominatorsLHS
  signature: (h lhs : Expr)
  body: do
  let mut (v, lhs') ← CancelDenoms.derive lhs
  if v = 1 then
    -- `lhs'` has a `1 *` out front, but `mkSingleCompZeroOf` has a special case
    -- where it does not produce `1 *`. We strip it off here:
    lhs' ← mkAppM ``without_one_mul #[lhs']
  let (_, h'') ← mkSingleCompZeroOf v h
  try
  

中文:
定义 normalizeDenominatorsLHS
  签名: (h lhs : Expr)
  定义体: do
  let mut (v, lhs') ← CancelDenoms.derive lhs
  if v = 1 then
    -- `lhs'` has a `1 *` out front, but `mkSingleCompZeroOf` has a special case
    -- where it does not produce `1 *`. We strip it off here:
    lhs' ← mkAppM ``without_one_mul #[lhs']
  let (_, h'') ← mkSingleCompZeroOf v h
  try
  
-/
def normalizeDenominatorsLHS (h lhs : Expr) : MetaM Expr := do
  let mut (v, lhs') ← CancelDenoms.derive lhs
  if v = 1 then
    -- `lhs'` has a `1 *` out front, but `mkSingleCompZeroOf` has a special case
    -- where it does not produce `1 *`. We strip it off here:
    lhs' ← mkAppM ``without_one_mul #[lhs']
  let (_, h'') ← mkSingleCompZeroOf v h
  try
    h''.rewriteType lhs'
  catch e =>
    dbg_trace
      s!"Error in Linarith.normalizeDenominatorsLHS: {← e.toMessageData.toString}"
    throw e

/--
Definition of `cancelDenoms` / `cancelDenoms` 的定义

English:
definition cancelDenoms
  signature: : Preprocessor where
  body: "cancel denominators"
  transform := fun pf => (do
      let (_, lhs) ← parseCompAndExpr (← inferType pf)
guard lhs.containsConst fun n =>
        n = ``HDiv.hDiv || n = ``Div.div || n = ``Inv.inv || n == ``OfScientific.ofScientific
      pure [← normalizeDenominatorsLHS pf lhs])
 > return [pf]

中文:
定义 cancelDenoms
  签名: : Preprocessor where
  定义体: "cancel denominators"
  transform := fun pf => (do
      let (_, lhs) ← parseCompAndExpr (← inferType pf)
guard lhs.containsConst fun n =>
        n = ``HDiv.hDiv || n = ``Div.div || n = ``Inv.inv || n == ``OfScientific.ofScientific
      pure [← normalizeDenominatorsLHS pf lhs])
 > return [pf]

Depends on / 依赖: cancel, denominators
-/
def cancelDenoms : Preprocessor where
  description := "cancel denominators"
  transform := fun pf => (do
      let (_, lhs) ← parseCompAndExpr (← inferType pf)
guard lhs.containsConst fun n =>
        n = ``HDiv.hDiv || n = ``Div.div || n = ``Inv.inv || n == ``OfScientific.ofScientific
      pure [← normalizeDenominatorsLHS pf lhs])
 > return [pf]
end cancelDenoms

section nlinarith
/--
Definition of `findSquares` / `findSquares` 的定义

English:
definition findSquares
  signature: (s : TreeSet (Nat × Bool) lexOrd.compare) (e : Expr)
  body: -- Completely traversing the expression is non-ideal,
  -- as we can descend into expressions that could not possibly be seen by `linarith`.
  -- As a result we visit expressions with bvars, which then cause panics.
  -- Ideally this preprocessor would be reimplemented so it only visits things that 

中文:
定义 findSquares
  签名: (s : TreeSet (自然数 × 布尔) lexOrd.compare) (e : Expr)
  定义体: -- Completely traversing the expression is non-ideal,
  -- as we can descend into expressions that could not possibly be seen by `linarith`.
  -- As a result we visit expressions with bvars, which then cause panics.
  -- Ideally this preprocessor would be reimplemented so it only visits things that 
-/
partial def findSquares (s : TreeSet (Nat × Bool) lexOrd.compare) (e : Expr) :
    AtomM (TreeSet (Nat × Bool) lexOrd.compare) :=
  -- Completely traversing the expression is non-ideal,
  -- as we can descend into expressions that could not possibly be seen by `linarith`.
  -- As a result we visit expressions with bvars, which then cause panics.
  -- Ideally this preprocessor would be reimplemented so it only visits things that could be atoms.
  -- In the meantime we just bail out if we ever encounter loose bvars.
  if e.hasLooseBVars then return s else
  match e.getAppFnArgs with
  | (``HPow.hPow, #[_, _, _, _, a, b]) => match b.numeral? with
    | some 2 => do
      let s ← findSquares s a
      let (ai, _) ← AtomM.addAtom a
      return (s.insert (ai, true))
    | _ => e.foldlM findSquares s
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
    let (ai, _) ← AtomM.addAtom a
    let (bi, _) ← AtomM.addAtom b
    if ai = bi then do
      let s ← findSquares s a
      return (s.insert (ai, false))
    else
      e.foldlM findSquares s
  | _ => e.foldlM findSquares s

/--
Definition of `nlinarithGetSquareProofs` / `nlinarithGetSquareProofs` 的定义

English:
definition nlinarithGetSquareProofs
  signature: (ls : List Expr)
  body: withTraceNode `linarith (fun _ => return m!" finding squares") do
  -- find the squares in `AtomM` to ensure deterministic behavior
  let s ← AtomM.run .reducible do
    let si ← ls.foldrM (fun h s' => do findSquares s' (← instantiateMVars (← inferType h))) ∅
    si.toList.mapM fun (i, is_sq) => ret

中文:
定义 nlinarithGetSquareProofs
  签名: (ls : List Expr)
  定义体: withTraceNode `linarith (fun _ => return m!" finding squares") do
  -- find the squares in `AtomM` to ensure deterministic behavior
  let s ← AtomM.run .reducible do
    let si ← ls.foldrM (fun h s' => do findSquares s' (← instantiateMVars (← inferType h))) ∅
    si.toList.mapM fun (i, is_sq) => ret
-/
private def nlinarithGetSquareProofs (ls : List Expr) : MetaM (List Expr) :=
  withTraceNode `linarith (fun _ => return m!" finding squares") do
  -- find the squares in `AtomM` to ensure deterministic behavior
  let s ← AtomM.run .reducible do
    let si ← ls.foldrM (fun h s' => do findSquares s' (← instantiateMVars (← inferType h))) ∅
    si.toList.mapM fun (i, is_sq) => return ((← get).atoms[i]!, is_sq)
  let new_es ← s.filterMapM fun (e, is_sq) =>
observing? mkAppM (if is_sq then ``sq_nonneg else ``mul_self_nonneg) #[e]
  let new_es ← compWithZero.globalize.transform new_es
  trace[linarith] "found:{indentD <| toMessageData s}"
  linarithTraceProofs "so we added proofs" new_es
  return new_es

/--
Definition of `nlinarithGetProductsProofs` / `nlinarithGetProductsProofs` 的定义

English:
definition nlinarithGetProductsProofs
  signature: (ls : List Expr)
  body: withTraceNode `linarith (fun _ => return m!" adding product terms") do
  let with_comps ← ls.mapM (fun e => do
    let tp ← inferType e
    try
      let ⟨ine, _⟩ ← parseCompAndExpr tp
      pure (ine, e)
    catch _ => pure (Ineq.lt, e))
  let products ← with_comps.mapDiagM fun (⟨posa, a⟩ : Ineq × 

中文:
定义 nlinarithGetProductsProofs
  签名: (ls : List Expr)
  定义体: withTraceNode `linarith (fun _ => return m!" adding product terms") do
  let with_comps ← ls.mapM (fun e => do
    let tp ← inferType e
    try
      let ⟨ine, _⟩ ← parseCompAndExpr tp
      pure (ine, e)
    catch _ => pure (Ineq.lt, e))
  let products ← with_comps.mapDiagM fun (⟨posa, a⟩ : Ineq × 
-/
private def nlinarithGetProductsProofs (ls : List Expr) : MetaM (List Expr) :=
  withTraceNode `linarith (fun _ => return m!" adding product terms") do
  let with_comps ← ls.mapM (fun e => do
    let tp ← inferType e
    try
      let ⟨ine, _⟩ ← parseCompAndExpr tp
      pure (ine, e)
    catch _ => pure (Ineq.lt, e))
  let products ← with_comps.mapDiagM fun (⟨posa, a⟩ : Ineq × Expr) ⟨posb, b⟩ =>
    try
      (some <$> match posa, posb with
        | Ineq.eq, _ => mkAppM ``zero_mul_eq #[a, b]
        | _, Ineq.eq => mkAppM ``mul_zero_eq #[a, b]
        | Ineq.lt, Ineq.lt => mkAppM ``mul_pos_of_neg_of_neg #[a, b]
        | Ineq.lt, Ineq.le => do
            let a ← mkAppM ``le_of_lt #[a]
            mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, b]
        | Ineq.le, Ineq.lt => do
            let b ← mkAppM ``le_of_lt #[b]
            mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, b]
        | Ineq.le, Ineq.le => mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, b])
    catch _ => pure none
  compWithZero.globalize.transform products.reduceOption

/--
Definition of `nlinarithExtras` / `nlinarithExtras` 的定义

English:
definition nlinarithExtras
  signature: : GlobalPreprocessor where
  body: "nonlinear arithmetic extras"
  transform ls := do
    let new_es ← nlinarithGetSquareProofs ls
    let products ← nlinarithGetProductsProofs (new_es ++ ls)
    return (new_es ++ ls ++ products)

中文:
定义 nlinarithExtras
  签名: : GlobalPreprocessor where
  定义体: "nonlinear arithmetic extras"
  transform ls := do
    let new_es ← nlinarithGetSquareProofs ls
    let products ← nlinarithGetProductsProofs (new_es ++ ls)
    return (new_es ++ ls ++ products)

Depends on / 依赖: arithmetic, extras, nonlinear
-/
def nlinarithExtras : GlobalPreprocessor where
  description := "nonlinear arithmetic extras"
  transform ls := do
    let new_es ← nlinarithGetSquareProofs ls
    let products ← nlinarithGetProductsProofs (new_es ++ ls)
    return (new_es ++ ls ++ products)

end nlinarith

section removeNe
/--
Definition of `removeNeAux` / `removeNeAux` 的定义

English:
definition removeNeAux
  signature: : MVarId -> List Expr -> MetaM (List Branch)
  body: fun g hs => do
  let some (e, α, a, b) ← hs.findSomeM? (fun e : Expr => do
    let some (α, a, b) := (← instantiateMVars (← inferType e)).ne?' | return none
    unless (← synthInstance? (← mkAppM ``LinearOrder #[α])).isSome do return none
    return some (e, α, a, b)) | return [(g, hs)]
  let [ng1, 

中文:
定义 removeNeAux
  签名: : MVarId -> List Expr -> MetaM (List Branch)
  定义体: fun g hs => do
  let some (e, α, a, b) ← hs.findSomeM? (fun e : Expr => do
    let some (α, a, b) := (← instantiateMVars (← inferType e)).ne?' | return none
    unless (← synthInstance? (← mkAppM ``LinearOrder #[α])).isSome do return none
    return some (e, α, a, b)) | return [(g, hs)]
  let [ng1, 
-/
partial def removeNeAux : MVarId -> List Expr -> MetaM (List Branch) := fun g hs => do
  let some (e, α, a, b) ← hs.findSomeM? (fun e : Expr => do
    let some (α, a, b) := (← instantiateMVars (← inferType e)).ne?' | return none
    unless (← synthInstance? (← mkAppM ``LinearOrder #[α])).isSome do return none
    return some (e, α, a, b)) | return [(g, hs)]
  let [ng1, ng2] ← g.apply (← mkAppOptM ``Or.elim #[none, none, ← g.getType,
      ← mkAppOptM ``lt_or_gt_of_ne #[α, none, a, b, e]]) | failure
  let do_goal : MVarId -> MetaM (List Branch) := fun g => do
    let (f, h) ← g.intro1
    h.withContext do
let ls ← removeNeAux h hs.removeAll [e]
      return ls.map (fun b : Branch => (b.1, (.fvar f)::b.2))
  return ((← do_goal ng1) ++ (← do_goal ng2))

@[deprecated (since := "2026-06-06")] alias removeNe_aux := removeNeAux

/--
Definition of `removeNe` / `removeNe` 的定义

English:
definition removeNe
  signature: : GlobalBranchingPreprocessor where
  body: "case split on !="
  transform := removeNeAux

中文:
定义 removeNe
  签名: : GlobalBranchingPreprocessor where
  定义体: "case split on !="
  transform := removeNeAux
-/
def removeNe : GlobalBranchingPreprocessor where
  description := "case split on !="
  transform := removeNeAux
end removeNe

/-- Definition overridden in `Mathlib.Tactic.Linarith.NNRealPreprocessor`. -/
initialize nnrealToRealTransform : IO.Ref (List Expr -> MetaM (List Expr)) ← IO.mkRef pure

/--
Definition of `nnrealToReal` / `nnrealToReal` 的定义

English:
definition nnrealToReal
  signature: : GlobalPreprocessor where
  body: "move nnreals to reals"
  transform l := do (← nnrealToRealTransform.get) l

中文:
定义 nnrealToReal
  签名: : GlobalPreprocessor where
  定义体: "move nnreals to reals"
  transform l := do (← nnrealToRealTransform.get) l

Depends on / 依赖: nnreals
-/
def nnrealToReal : GlobalPreprocessor where
  description := "move nnreals to reals"
  transform l := do (← nnrealToRealTransform.get) l

/--
Definition of `defaultPreprocessors` / `defaultPreprocessors` 的定义

English:
definition defaultPreprocessors
  signature: : List GlobalBranchingPreprocessor
  body: [filterComparisons, nnrealToReal, natToInt, strengthenStrictInt,
    compWithZero, cancelDenoms]

中文:
定义 defaultPreprocessors
  签名: : List GlobalBranchingPreprocessor
  定义体: [filterComparisons, nnrealToReal, natToInt, strengthenStrictInt,
    compWithZero, cancelDenoms]

Depends on / 依赖: cancelDenoms, compWithZero, filterComparisons, natToInt, nnrealToReal, strengthenStrictInt
-/
def defaultPreprocessors : List GlobalBranchingPreprocessor :=
  [filterComparisons, nnrealToReal, natToInt, strengthenStrictInt,
    compWithZero, cancelDenoms]

/--
Definition of `preprocess` / `preprocess` 的定义

English:
definition preprocess
  signature: (pps : List GlobalBranchingPreprocessor) (g : MVarId) (l : List Expr)
  body: do
withTraceNode `linarith (fun _ => return m!"Running preprocessors")
g.withContext
      pps.foldlM (init := [(g, l)]) fun ls pp => do
        return (← ls.mapM fun (g, l) => do pp.process g l).flatten

中文:
定义 preprocess
  签名: (pps : List GlobalBranchingPreprocessor) (g : MVarId) (l : List Expr)
  定义体: do
withTraceNode `linarith (fun _ => return m!"Running preprocessors")
g.withContext
      pps.foldlM (init := [(g, l)]) fun ls pp => do
        return (← ls.mapM fun (g, l) => do pp.process g l).flatten
-/
def preprocess (pps : List GlobalBranchingPreprocessor) (g : MVarId) (l : List Expr) :
    MetaM (List Branch) := do
withTraceNode `linarith (fun _ => return m!"Running preprocessors")
g.withContext
      pps.foldlM (init := [(g, l)]) fun ls pp => do
        return (← ls.mapM fun (g, l) => do pp.process g l).flatten

end Mathlib.Tactic.Linarith
