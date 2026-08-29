/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Damiano Testa
-/
module

public meta import Mathlib.Lean.Meta
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Order.Defs.LinearOrder
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual

/-!

# `move_add` a tactic for moving summands in expressions

The tactic `move_add` rearranges summands in expressions.

The tactic takes as input a list of terms, each one optionally preceded by `←`.
A term preceded by `←` gets moved to the left, while a term without `←` gets moved to the right.

* Empty input: `move_add []`

  In this case, the effect of `move_add []` is equivalent to `simp only [← add_assoc]`:
  essentially the tactic removes all visible parentheses.

* Singleton input: `move_add [a]` and `move_add [← a]`

  If `⊢ b + a + c` is (a summand in) the goal, then
  * `move_add [← a]` changes the goal to `a + b + c` (effectively, `a` moved to the left).
  * `move_add [a]` changes the goal to `b + c + a` (effectively, `a` moved to the right);

  The tactic reorders *all* sub-expressions of the target at the same time.
  For instance, if `⊢ 0 < if b + a < b + a + c then a + b else b + a` is the goal, then
  * `move_add [a]` changes the goal to `0 < if b + a < b + c + a then b + a else b + a`
    (`a` moved to the right in three sums);
  * `move_add [← a]` changes the goal to `0 < if a + b < a + b + c then a + b else a + b`
    (`a` again moved to the left in three sums).

* Longer inputs: `move_add [..., a, ..., ← b, ...]`

  If the list contains more than one term, the tactic effectively tries to move each term preceded
  by `←` to the left, each term not preceded by `←` to the right
  *maintaining the relative order in the call*.
  Thus, applying `move_add [a, b, c, ← d, ← e]` returns summands of the form
  `d + e + [...] + a + b + c`, i.e. `d` and `e` have the same relative position in the input list
  and in the final rearrangement (and similarly for `a, b, c`).
  In particular, `move_add [a, b]` likely has the same effect as
  `move_add [a]; move_add [b]`: first, we move `a` to the right, then we move `b` also to the
  right, *after* `a`.
  However, if the terms matched by `a` and `b` do not overlap, then `move_add [← a, ← b]`
  has the same effect as `move_add [b]; move_add [a]`:
  first, we move `b` to the left, then we move `a` also to the left, *before* `b`.
  The behaviour in the situation where `a` and `b` overlap is unspecified: `move_add`
  will descend into subexpressions, but the order in which they are visited depends
  on which rearrangements have already happened.
  Also note, though, that `move_add [a, b]` may differ from `move_add [a]; move_add [b]`,
  for instance when `a` and `b` are `DefEq`.

* Unification of inputs and repetitions: `move_add [_, ← _, a * _]`

  The matching of the user inputs with the atoms of the summands in the target expression
  is performed via checking `DefEq` and selecting the first, still available match.
  Thus, if a sum in the target is `2 * 3 + 4 * (5 + 6) + 4 * 7 + 10 * 10`, then
  `move_add [4 * _]` moves the summand `4 * (5 + 6)` to the right.

  The unification of later terms only uses the atoms in the target that have not yet been unified.
  Thus, if again the target contains `2 * 3 + 4 * (5 + 6) + 4 * 7 + 10 * 10`, then
  `move_add [_, ← _, 4 * _]`
  matches
  * the first input (`_`) with `2 * 3`;
  * the second input (`_`) with `4 * (5 + 6)`;
  * the third input (`4 * _`) with `4 * 7`.

  The resulting permutation therefore places `2 * 3` and `4 * 7` to the left (in this order) and
  `4 * (5 + 6)` to the right: `2 * 3 + 4 * 7 + 10 * 10 + 4 * (5 + 6)`.

For the technical description, look at `Mathlib.MoveAdd.weight` and `Mathlib.MoveAdd.reorderUsing`.

`move_add` is the specialization of a more general `move_oper` tactic that takes a binary,
associative, commutative operation and a list of "operand atoms" and rearranges the operation.

## Extension notes

To work with a general associative, commutative binary operation, `move_oper`
needs to have inbuilt the lemmas asserting the analogues of
`add_comm, add_assoc, add_left_comm` for the new operation.
Currently, `move_oper` supports `HAdd.hAdd`, `HMul.hMul`, `And`, `Or`, `Max.max`, `Min.min`.

These lemmas should be added to `Mathlib.MoveAdd.moveOperSimpCtx`.

See `MathlibTest/MoveAdd.lean` for sample usage of `move_oper`.

## Implementation notes

The main driver behind the tactic is `Mathlib.MoveAdd.reorderAndSimp`.

The tactic takes the target, replaces the maximal subexpressions whose head symbol is the given
operation and replaces them by their reordered versions.
Once that is done, it tries to replace the initial goal with the permuted one by using `simp`.

Currently, no attempt is made at guiding `simp` by doing a `congr`-like destruction of the goal.
This will be the content of a later PR.
-/

public meta section

open Lean Expr

/--
Definition of `Lean.Expr.getExprInputs` / `Lean.Expr.getExprInputs` 的定义

English:
definition Lean.Expr.getExprInputs
  signature: : Expr -> Array Expr

中文:
定义 Lean.Expr.getExprInputs
  签名: : Expr -> 数组 Expr
-/
def Lean.Expr.getExprInputs : Expr -> Array Expr
  | app fn arg => #[fn, arg]
  | lam _ bt bb _ => #[bt, bb]
  | forallE _ bt bb _ => #[bt, bb]
  | letE _ t v b _ => #[t, v, b]
  | mdata _ e => #[e]
  | proj _ _ e => #[e]
  | _ => #[]

namespace Mathlib.MoveAdd

section ExprProcessing

section reorder
variable {α : Type*} [BEq α]

/-!
## Reordering the variables

This section produces the permutations of the variables for `move_add`.

The user controls the final order by passing a list of terms to the tactic.
Each term can be preceded by `←` or not.
In the final ordering,
* terms preceded by `←` appear first,
* terms not preceded by `←` appear last,
* all remaining terms remain in their current relative order.
-/

/--
Definition of `uniquify` / `uniquify` 的定义

English:
definition uniquify
  signature: : List α -> List (α × Nat)
  body: uniquify ms
    (m, 0) :: (lms.map fun (x, n) => if x == m then (x, n + 1) else (x, n))

中文:
定义 uniquify
  签名: : 列表 α -> 列表 (α × 自然数)
  定义体: uniquify ms
    (m, 0) :: (lms.map fun (x, n) => if x == m then (x, n + 1) else (x, n))

Depends on / 依赖: uniquify
-/
def uniquify : List α -> List (α × Nat)
  | [] => []
  | m::ms =>
    let lms := uniquify ms
    (m, 0) :: (lms.map fun (x, n) => if x == m then (x, n + 1) else (x, n))

/--
Definition of `weight` / `weight` 的定义

English:
definition weight
  signature: (L : List (α × Bool)) (a : α)
  body: let l := L.length
  match L.find? (Prod.fst · == a) with
    | some (_, b) => if b then - l + (L.idxOf (a, b) : Int) else (L.idxOf (a, b) + 1 : Int)
    | none => 0

中文:
定义 weight
  签名: (L : 列表 (α × 布尔值)) (a : α)
  定义体: let l := L.length
  match L.find? (Prod.fst · == a) with
    | some (_, b) => if b then - l + (L.idxOf (a, b) : Int) else (L.idxOf (a, b) + 1 : Int)
    | none => 0

Depends on / 依赖: L.find, L.idxOf, L.length, Prod.fst, length
-/
def weight (L : List (α × Bool)) (a : α) : Int :=
  let l := L.length
  match L.find? (Prod.fst · == a) with
    | some (_, b) => if b then - l + (L.idxOf (a, b) : Int) else (L.idxOf (a, b) + 1 : Int)
    | none => 0

/--
Definition of `reorderUsing` / `reorderUsing` 的定义

English:
definition reorderUsing
  signature: (toReorder : List α) (instructions : List (α × Bool))
  body: let uInstructions :=
    let (as, as?) := instructions.unzip
    (uniquify as).zip as?
  let uToReorder := (uniquify toReorder).toArray
  let reorder := uToReorder.qsort fun x y =>
    match uInstructions.find? (Prod.fst · == x), uInstructions.find? (Prod.fst · == y) with
      | none, none =>
     

中文:
定义 reorderUsing
  签名: (toReorder : 列表 α) (instructions : 列表 (α × 布尔值))
  定义体: let uInstructions :=
    let (as, as?) := instructions.unzip
    (uniquify as).zip as?
  let uToReorder := (uniquify toReorder).toArray
  let reorder := uToReorder.qsort fun x y =>
    match uInstructions.find? (Prod.fst · == x), uInstructions.find? (Prod.fst · == y) with
      | none, none =>
     

Depends on / 依赖: Prod.fst, instructions, instructions.unzip, reorder, reorder.map, toArray, toList, toReorder, uInstructions, uInstructions.find, uToReorder, uToReorder.idxOf, uToReorder.qsort, uniquify, weight
-/
def reorderUsing (toReorder : List α) (instructions : List (α × Bool)) : List α :=
  let uInstructions :=
    let (as, as?) := instructions.unzip
    (uniquify as).zip as?
  let uToReorder := (uniquify toReorder).toArray
  let reorder := uToReorder.qsort fun x y =>
    match uInstructions.find? (Prod.fst · == x), uInstructions.find? (Prod.fst · == y) with
      | none, none =>
        (uToReorder.idxOf? x).get! <= (uToReorder.idxOf? y).get!
      | _, _ => weight uInstructions x <= weight uInstructions y
  (reorder.map Prod.fst).toList

end reorder

/--
Definition of `prepareOp` / `prepareOp` 的定义

English:
definition prepareOp
  signature: (sum : Expr)
  body: let opargs := sum.getAppArgs
  (opargs.toList.take (opargs.size - 2)).foldl (fun x y => Expr.app x y) sum.getAppFn

中文:
定义 prepareOp
  签名: (求和 : Expr)
  定义体: let opargs := sum.getAppArgs
  (opargs.toList.take (opargs.size - 2)).foldl (fun x y => Expr.app x y) sum.getAppFn

Depends on / 依赖: Expr.app, IsInducing, IsInducing.subtypeVal.r0Space, getAppArgs, getAppFn, opargs, opargs.size, opargs.toList.take, r0Space, subtypeVal, sum.getAppArgs, sum.getAppFn, toList
-/
def prepareOp (sum : Expr) : Expr :=
  let opargs := sum.getAppArgs
  (opargs.toList.take (opargs.size - 2)).foldl (fun x y => Expr.app x y) sum.getAppFn

/-- `sumList prepOp left_assoc? exs` assumes that `prepOp` is an `Expr`ession representing a
binary operation already fully applied up until its last two arguments and assumes that the
last two arguments are the operands of the operation.
Such an expression is the result of `prepareOp`.

If `exs` is the list `[e₁, e₂, ..., eₙ]` of `Expr`essions, then `sumList prepOp left_assoc? exs`
returns
* `prepOp (prepOp( ... prepOp (prepOp e₁ e₂) e₃) ... eₙ)`, if `left_assoc?` is `false`, and
* `prepOp e₁ (prepOp e₂ (... prepOp (prepOp eₙ₋₁ eₙ))`, if `left_assoc?` is `true`.
-/
partial
/--
Definition of `sumList` / `sumList` 的定义

English:
definition sumList
  signature: (prepOp : Expr) (left_assoc? : Bool)

中文:
定义 sumList
  签名: (prepOp : Expr) (left_assoc? : 布尔值)
-/
def sumList (prepOp : Expr) (left_assoc? : Bool) : List Expr -> Expr
  | [] => default
  | [a] => a
  | a::as =>
    if left_assoc? then
      Expr.app (prepOp.app a) (sumList prepOp true as)
    else
      as.foldl (fun x y => Expr.app (prepOp.app x) y) a

end ExprProcessing

open Meta

variable (op : Name)

variable (R : Expr) in
/--
Definition of `getAddends` / `getAddends` 的定义

English:
definition getAddends
  signature: (sum : Expr)
  body: do
  if sum.isAppOf op then
    let inR ← sum.getAppArgs.filterM fun r => do isDefEq R (← inferType r <|> pure R)
    let new ← inR.mapM (getAddends ·)
    return new.foldl Array.append #[]
  else return #[sum]

中文:
定义 getAddends
  签名: (求和 : Expr)
  定义体: do
  if sum.isAppOf op then
    let inR ← sum.getAppArgs.filterM fun r => do isDefEq R (← inferType r <|> pure R)
    let new ← inR.mapM (getAddends ·)
    return new.foldl Array.append #[]
  else return #[sum]

Depends on / 依赖: specializes_pi
-/
partial def getAddends (sum : Expr) : MetaM (Array Expr) := do
  if sum.isAppOf op then
    let inR ← sum.getAppArgs.filterM fun r => do isDefEq R (← inferType r <|> pure R)
    let new ← inR.mapM (getAddends ·)
    return new.foldl Array.append #[]
  else return #[sum]

/--
Definition of `getOps` / `getOps` 的定义

English:
definition getOps
  signature: (sum : Expr)
  body: do
  let summands ← getAddends op (← inferType sum <|> return sum) sum
  let (first, rest) := if summands.size == 1 then (#[], sum.getExprInputs) else
    (#[(summands, sum)], summands)
  let rest ← rest.mapM getOps
  return rest.foldl Array.append first

中文:
定义 getOps
  签名: (求和 : Expr)
  定义体: do
  let summands ← getAddends op (← inferType sum <|> return sum) sum
  let (first, rest) := if summands.size == 1 then (#[], sum.getExprInputs) else
    (#[(summands, sum)], summands)
  let rest ← rest.mapM getOps
  return rest.foldl Array.append first
-/
partial def getOps (sum : Expr) : MetaM (Array ((Array Expr) × Expr)) := do
  let summands ← getAddends op (← inferType sum <|> return sum) sum
  let (first, rest) := if summands.size == 1 then (#[], sum.getExprInputs) else
    (#[(summands, sum)], summands)
  let rest ← rest.mapM getOps
  return rest.foldl Array.append first

/--
Definition of `rankSums` / `rankSums` 的定义

English:
definition rankSums
  signature: (tgt : Expr) (instructions : List (Expr × Bool))
  body: do
  let sums ← getOps op (← instantiateMVars tgt)
  let candidates := sums.map fun (addends, sum) => do
    let reord := reorderUsing addends.toList instructions
    let left_assoc? := sum.getAppFn.isConstOf `And || sum.getAppFn.isConstOf `Or
    let resummed := sumList (prepareOp sum) left_assoc? 

中文:
定义 rankSums
  签名: (tgt : Expr) (instructions : 列表 (Expr × 布尔值))
  定义体: do
  let sums ← getOps op (← instantiateMVars tgt)
  let candidates := sums.map fun (addends, sum) => do
    let reord := reorderUsing addends.toList instructions
    let left_assoc? := sum.getAppFn.isConstOf `And || sum.getAppFn.isConstOf `Or
    let resummed := sumList (prepareOp sum) left_assoc? 
-/
def rankSums (tgt : Expr) (instructions : List (Expr × Bool)) : MetaM (List (Expr × Expr)) := do
  let sums ← getOps op (← instantiateMVars tgt)
  let candidates := sums.map fun (addends, sum) => do
    let reord := reorderUsing addends.toList instructions
    let left_assoc? := sum.getAppFn.isConstOf `And || sum.getAppFn.isConstOf `Or
    let resummed := sumList (prepareOp sum) left_assoc? reord
    if (resummed != sum) then some (sum, resummed) else none
  return (candidates.toList.reduceOption.toArray.qsort
    (fun x y : Expr × Expr => (y.1.sizeWithoutSharing <= x.1.sizeWithoutSharing))).toList

/--
Definition of `permuteExpr` / `permuteExpr` 的定义

English:
definition permuteExpr
  signature: (tgt : Expr) (instructions : List (Expr × Bool))
  body: do
  let permInstructions ← rankSums op tgt instructions
  if permInstructions == [] then throwError "The goal is already in the required form"
  let mut permTgt := tgt
  -- We cannot do `Expr.replace` all at once here, we need to follow
  -- the order of the instructions.
  for (old, new) in permIn

中文:
定义 permuteExpr
  签名: (tgt : Expr) (instructions : 列表 (Expr × 布尔值))
  定义体: do
  let permInstructions ← rankSums op tgt instructions
  if permInstructions == [] then throwError "The goal is already in the required form"
  let mut permTgt := tgt
  -- We cannot do `Expr.replace` all at once here, we need to follow
  -- the order of the instructions.
  for (old, new) in permIn
-/
def permuteExpr (tgt : Expr) (instructions : List (Expr × Bool)) : MetaM Expr := do
  let permInstructions ← rankSums op tgt instructions
  if permInstructions == [] then throwError "The goal is already in the required form"
  let mut permTgt := tgt
  -- We cannot do `Expr.replace` all at once here, we need to follow
  -- the order of the instructions.
  for (old, new) in permInstructions do
    permTgt := permTgt.replace (if · == old then new else none)
  return permTgt

/-- `pairUp L R` takes two lists `L R : List Expr` as inputs.
It scans the elements of `L`, looking for a corresponding `DefEq` `Expr`ession in `R`.
If it finds one such element `d`, then it sets the element `d : R` aside, removing it from `R`, and
it continues with the matching on the remainder of `L` and on `R.erase d`.

At the end, it returns the sublist of `R` of the elements that were matched to some element of `L`,
in the order in which they appeared in `L`,
as well as the sublist of `L` of elements that were not matched, also in the order in which they
appeared in `L`.

Example:
```lean
#eval do
  let L := [mkNatLit 0, (← mkFreshExprMVar (some (mkConst ``Nat))), mkNatLit 0] -- i.e. [0, _, 0]
  let R := [mkNatLit 0, mkNatLit 0, mkNatLit 1] -- i.e. [0, 1]
  dbg_trace f!"{(← pairUp L R)}"
/--
Definition of `pairUp` / `pairUp` 的定义

English:
definition pairUp
  signature: : List (Expr × Bool × Syntax) -> List Expr ->

中文:
定义 pairUp
  签名: : 列表 (Expr × 布尔值 × Syntax) -> 列表 Expr ->
-/
def pairUp : List (Expr × Bool × Syntax) -> List Expr ->
    MetaM ((List (Expr × Bool)) × List (Expr × Bool × Syntax))
  | (m::ms), l => do
    match ← l.findM? (isDefEq · m.1) with
      | none => let (found, unfound) ← pairUp ms l; return (found, m::unfound)
      | some d => let (found, unfound) ← pairUp ms (l.erase d)
                  return ((d, m.2.1)::found, unfound)
  | _, _ => return ([], [])

/--
Definition of `moveOperSimpCtx` / `moveOperSimpCtx` 的定义

English:
definition moveOperSimpCtx
  signature: : MetaM Simp.Context
  body: do
  let simpNames := Elab.Tactic.simpOnlyBuiltins ++ [
    ``add_comm, ``add_assoc, ``add_left_comm, -- for `HAdd.hAdd`
    ``mul_comm, ``mul_assoc, ``mul_left_comm, -- for `HMul.hMul`
    ``and_comm, ``and_assoc, ``and_left_comm, -- for `and`
    ``or_comm, ``or_assoc, ``or_left_comm, -- for `or`


中文:
定义 moveOperSimpCtx
  签名: : MetaM Simp.余ntext
  定义体: do
  let simpNames := Elab.Tactic.simpOnlyBuiltins ++ [
    ``add_comm, ``add_assoc, ``add_left_comm, -- for `HAdd.hAdd`
    ``mul_comm, ``mul_assoc, ``mul_left_comm, -- for `HMul.hMul`
    ``and_comm, ``and_assoc, ``and_left_comm, -- for `and`
    ``or_comm, ``or_assoc, ``or_left_comm, -- for `or`

-/
def moveOperSimpCtx : MetaM Simp.Context := do
  let simpNames := Elab.Tactic.simpOnlyBuiltins ++ [
    ``add_comm, ``add_assoc, ``add_left_comm, -- for `HAdd.hAdd`
    ``mul_comm, ``mul_assoc, ``mul_left_comm, -- for `HMul.hMul`
    ``and_comm, ``and_assoc, ``and_left_comm, -- for `and`
    ``or_comm, ``or_assoc, ``or_left_comm, -- for `or`
    ``max_comm, ``max_assoc, ``max_left_comm, -- for `max`
    ``min_comm, ``min_assoc, ``min_left_comm -- for `min`
    ]
  let simpThms ← simpNames.foldlM (·.addConst ·) ({} : SimpTheorems)
  Simp.mkContext {} (simpTheorems := #[simpThms])

/--
Definition of `reorderAndSimp` / `reorderAndSimp` 的定义

English:
definition reorderAndSimp
  signature: (mv : MVarId) (instr : List (Expr × Bool))
  body: mv.withContext do
  let permExpr ← permuteExpr op (← mv.getType'') instr
  -- generate the implication `permutedMv → mv = permutedMv → mv`
  let eqmpr ← mkAppM ``Eq.mpr #[← mkFreshExprMVar (← mkEq (← mv.getType) permExpr)]
  let twoGoals ← mv.apply eqmpr
guard (twoGoals.length == 2) >
    throwError

中文:
定义 reorderAndSimp
  签名: (mv : MVarId) (instr : 列表 (Expr × 布尔值))
  定义体: mv.withContext do
  let permExpr ← permuteExpr op (← mv.getType'') instr
  -- generate the implication `permutedMv → mv = permutedMv → mv`
  let eqmpr ← mkAppM ``Eq.mpr #[← mkFreshExprMVar (← mkEq (← mv.getType) permExpr)]
  let twoGoals ← mv.apply eqmpr
guard (twoGoals.length == 2) >
    throwError

Depends on / 依赖: mv.withContext, withContext
-/
def reorderAndSimp (mv : MVarId) (instr : List (Expr × Bool)) :
    MetaM (List MVarId) := mv.withContext do
  let permExpr ← permuteExpr op (← mv.getType'') instr
  -- generate the implication `permutedMv → mv = permutedMv → mv`
  let eqmpr ← mkAppM ``Eq.mpr #[← mkFreshExprMVar (← mkEq (← mv.getType) permExpr)]
  let twoGoals ← mv.apply eqmpr
guard (twoGoals.length == 2) >
    throwError m!"There should only be 2 goals, instead of {twoGoals.length}"
  -- `permGoal` is the single goal `mv_permuted`, possibly more operations will be permuted later on
  let permGoal ← twoGoals.filterM fun v => return !(← v.isAssigned)
  match ← (simpGoal (permGoal[1]!) (← moveOperSimpCtx)) with
    | (some x, _) => throwError m!"'move_oper' could not solve {indentD x.2}"
    | (none, _) => return permGoal

/--
Definition of `unifyMovements` / `unifyMovements` 的定义

English:
definition unifyMovements
  signature: (data : Array (Expr × Bool × Syntax)) (tgt : Expr)
  body: do
  let ops ← getOps op tgt
  let atoms := (ops.map Prod.fst).flatten.toList.filter (!isBVar ·)
  -- `instr` are the unified user-provided terms, `neverMatched` are non-unified ones
  let (instr, neverMatched) ← pairUp data.toList atoms
  let dbgMsg := #[m!"Matching of input variables:\n\
    * pre

中文:
定义 unifyMovements
  签名: (data : 数组 (Expr × 布尔值 × Syntax)) (tgt : Expr)
  定义体: do
  let ops ← getOps op tgt
  let atoms := (ops.map Prod.fst).flatten.toList.filter (!isBVar ·)
  -- `instr` are the unified user-provided terms, `neverMatched` are non-unified ones
  let (instr, neverMatched) ← pairUp data.toList atoms
  let dbgMsg := #[m!"Matching of input variables:\n\
    * pre
-/
def unifyMovements (data : Array (Expr × Bool × Syntax)) (tgt : Expr) :
    MetaM (List (Expr × Bool) × (List MessageData × List Syntax) × Array MessageData) := do
  let ops ← getOps op tgt
  let atoms := (ops.map Prod.fst).flatten.toList.filter (!isBVar ·)
  -- `instr` are the unified user-provided terms, `neverMatched` are non-unified ones
  let (instr, neverMatched) ← pairUp data.toList atoms
  let dbgMsg := #[m!"Matching of input variables:\n\
    * pre-match: {data.map (Prod.snd ∘ Prod.snd)}\n\
    * post-match: {instr}",
    m!"\nMaximum number of iterations: {ops.size}"]
  -- if there are `neverMatched` terms, return the parsed terms and the syntax
  let errMsg := neverMatched.map fun (t, a, stx) => (if a then m!"← {t}" else m!"{t}", stx)
  return (instr, errMsg.unzip, dbgMsg)

section parsing
open Elab Parser Tactic

/--
Definition of `parseArrows` / `parseArrows` 的定义

English:
definition parseArrows
  signature: : TSyntax `Lean.Parser.Tactic.rwRuleSeq -> TermElabM (Array (Expr × Bool × Syntax))
  body: rstx
      return (← Term.elabTerm r[1]! none, ! r[0]!.isNone, rstx)
  | _ => failure

中文:
定义 parseArrows
  签名: : TSyntax `Lean.Parser.Tactic.rwRuleSeq -> TermElabM (数组 (Expr × 布尔值 × Syntax))
  定义体: rstx
      return (← Term.elabTerm r[1]! none, ! r[0]!.isNone, rstx)
  | _ => failure
-/
def parseArrows : TSyntax `Lean.Parser.Tactic.rwRuleSeq -> TermElabM (Array (Expr × Bool × Syntax))
  | `(rwRuleSeq| [$rs,*]) => do
    rs.getElems.mapM fun rstx => do
      let r : Syntax := rstx
      return (← Term.elabTerm r[1]! none, ! r[0]!.isNone, rstx)
  | _ => failure

initialize registerTraceClass `Tactic.move_oper

/-- `move_oper op [a]` repeatedly moves `a` to the far right hand side in applications of `op`.
Here the constant `op` refers to a binary associative commutative operation, and `a` is any term
(potentially with underscores).

If `a` contains underscores, they are filled in by unification with the first matching occurrence.
Subterms with different values for the underscores are not matched, unless you repeat `a`.

Currently, `move_oper` supports the operators `HAdd.hAdd` (`· + ·`), `HMul.hMul` (`· * ·`),
`And` (`· ∧ ·`), `Or` (`· ∨ ·`), `Max.max` and `Min.min`. To support more operations, add them to
`Mathlib.MoveAdd.moveOperSimpCtx`.

* `move_add [...]` uses addition as the operation: it abbreviates `move_oper HAdd.add [...]`.
* `move_mul [...]` uses multiplication as the operation: it abbreviates `move_oper HMul.mul [...]`.
* `move_oper op [← a]` moves the atoms matching `a` to the far left hand side instead of the right.
* `move_oper op [a, b, ← c, ← d, ...]` moves multiple atoms simultaneously, in the order indicated
  by the arguments: `c` will appear to the left of `d` and `a` will appear to the left of `b`.
-/
elab (name := moveOperTac) "move_oper" id:ident rws:rwRuleSeq : tactic => withMainContext do
  -- parse the operation
  let op := id.getId
  -- parse the list of terms
  let (instr, (unmatched, stxs), dbgMsg) ← unifyMovements op (← parseArrows rws)
                                                              (← instantiateMVars (← getMainTarget))
  unless unmatched.length = 0 do
    let _ ← stxs.mapM (logErrorAt · "") -- underline all non-matching terms
    trace[Tactic.move_oper] dbgMsg.foldl (fun x y => (x.compose y).compose "\n\n---\n") ""
    throwErrorAt stxs[0]! m!"Errors:\nThe terms in '{unmatched}' were not matched to any atom"
  -- move around the operands
  replaceMainGoal (← reorderAndSimp op (← getMainGoal) instr)

@[tactic_alt moveOperTac]
elab "move_add" rws:rwRuleSeq : tactic => do
  let hadd := mkIdent ``HAdd.hAdd
  evalTactic (← `(tactic| move_oper $hadd $rws))

@[tactic_alt moveOperTac]
elab "move_mul" rws:rwRuleSeq : tactic => do
  let hmul := mkIdent ``HMul.hMul
  evalTactic (← `(tactic| move_oper $hmul $rws))

end parsing

end MoveAdd

end Mathlib
