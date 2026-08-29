/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Meta.Tactic.TryThis
public meta import Lean.Server.InfoUtils
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header -- shake: keep
public import Lean.Parser.Term

/-!
# The "flexible" linter

The "flexible" linter makes sure that a "rigid" tactic (such as `rw`) does not act on the
output of a "flexible" tactic (such as `simp`).

For example, this ensures that, if you want to use `simp [...]` in the middle of a proof,
then you should replace `simp [...]` by one of
* a `suffices \"expr after simp\" by simpa` line;
* the output of `simp? [...]`, so that the final code contains `simp only [...]`;
* something else that does not involve `simp`!

Otherwise, the linter will complain.

Simplifying and appealing to a geometric intuition, you can imagine a (tactic) proof like a
directed graph, where
* each node is a local hypothesis or a goal in some metavariable and
* two hypotheses/goals are connected by an arrow if there is a tactic that modifies the source
  of the arrow into the target (this does not apply well to all tactics, but it does apply to
  a large number of them).

With this in mind, a tactic like `rw [lemma]` takes a *very specific* input and return a
*very predictable* output.
Such a tactic is "rigid". Any tactic is rigid, unless it is in `flexible` or `stoppers`.
Conversely, a tactic like `simp` acts on a wide variety of inputs and returns an output that
is possibly unpredictable: if later modifications adds a `simp`-lemma or some internals of
`simp` changes, the output of `simp` may change as well.
Such a tactic is `flexible`. Other examples are `split`, `abel`, `norm_cast`,...
Let's go back to the graph picture above.
* ✅️ [`rigid` --> `flexible`]
  A sequence `rw [lemma]; simp` is unlikely to break, since `rw [lemma]` produces the same output
  unless some *really major* change happens!
* ❌️ [`flexible` --> `rigid`]
  A sequence `simp; rw [lemma]` is instead more likely to break, since the goal after `simp` is
  subject to change by even a small, likely, modification of the `simp` set.
* ✅️ [`flexible` --> `flexible`]
  A sequence `simp; linarith` is also quite stable, since if `linarith` was able to close the
  goal with a "weaker" `simp`, it will likely still be able to close the goal with a `simp`
  that takes one further step.
* ✅️ [`flexible` --> `stopper`]
  Finally, a sequence `simp; ring_nf` is stable and, moreover, the output of `ring_nf` is a
  "normal form", which means that it is likely to produce an unchanged result, even if the initial
  input is different from the proof in its initial form.
  A stopper can be followed by a rigid tactic, "stopping" the spread of the flexible reach.

What the linter does is keeping track of nodes that are connected by `flexible` tactics and
makes sure that only `flexible` or `stoppers` follow them.
Such nodes are `Stained`.
Whenever it reaches a `stopper` edge, the target node is no longer `Stained` and it is
available again to `rigid` tactics.

Currently, the only tactics that "start" the bookkeeping are most forms of non-`only` `simp`s.
These are encoded by the `flexible?` predicate.
Future modifications of the linter may increase the scope of the `flexible?` predicate and
forbid a wider range of combinations.

## TODO
The example
```lean
example (h : 0 = 0) : True := by
  simp at h
  assumption
```
should trigger the linter, since `assumption` uses `h` that has been "stained" by `simp at h`.
However, `assumption` contains no syntax information for the location `h`, so the linter in its
current form does not catch this.

## Implementation notes

A large part of the code is devoted to tracking `FVar`s and `MVar`s between tactics.

For the `FVar`s, this follows the following heuristic:
* if the unique name of the `FVar` is preserved, then we use that;
* otherwise, if the `userName` of the `FVar` is preserved, then we use that;
* if neither is preserved, we drop the ball and stop tracking the `FVarId`.

For the `MVar`s, we use the information of `Lean.Elab.TacticInfo.goalsBefore` and
`Lean.Elab.TacticInfo.goalsAfter`.
By looking at the `mvar`s that are either only "before" or only "after", we focus on the
"active" goals.
We then propagate all the `FVarId`s that were present in the "before" goals to the "after" goals,
while leaving untouched the ones in the "inert" goals.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- The flexible linter makes sure that "rigid" tactics do not follow "flexible" tactics. -/
public register_option linter.flexible : Bool := {
  defValue := false
  descr := "enable the flexible linter"
}

-- TODO: adding more entries here, allows to consider more tactics to be flexible
/--
Definition of `flexible?` / `flexible?` 的定义

English:
definition flexible?
  signature: : Syntax -> Bool

中文:
定义 flexible?
  签名: : Syntax -> 布尔
-/
def flexible? : Syntax -> Bool
  | .node _ ``Lean.Parser.Tactic.simp #[_, _, _, only?, _, _] => only?[0].getAtomVal != "only"
  | .node _ ``Lean.Parser.Tactic.simpAll #[_, _, _, only?, _] => only?[0].getAtomVal != "only"
  | _ => false

end Mathlib.Linter

section goals_heuristic
namespace Lean.Elab.TacticInfo

/-!
### Heuristics for determining goals that a tactic modifies and what they become

The two definitions `goalsTargetedBy`, `goalsCreatedBy` extract a list of
`MVarId`s attempting to determine on which goals the tactic `t` is acting and what are the
resulting modified goals.
This is mostly based on the heuristic that the tactic will "change" an `MVarId`.
-/

/--
Definition of `goalsTargetedBy` / `goalsTargetedBy` 的定义

English:
definition goalsTargetedBy
  signature: (t : TacticInfo)
  body: t.goalsBefore.filter (·.name ∉ t.goalsAfter.map (·.name))

中文:
定义 goalsTargetedBy
  签名: (t : TacticInfo)
  定义体: t.goalsBefore.filter (·.name ∉ t.goalsAfter.map (·.name))

Depends on / 依赖: filter, goalsAfter, goalsBefore, t.goalsAfter.map, t.goalsBefore.filter
-/
def goalsTargetedBy (t : TacticInfo) : List MVarId :=
  t.goalsBefore.filter (·.name ∉ t.goalsAfter.map (·.name))

/--
Definition of `goalsCreatedBy` / `goalsCreatedBy` 的定义

English:
definition goalsCreatedBy
  signature: (t : TacticInfo)
  body: t.goalsAfter.filter (·.name ∉ t.goalsBefore.map (·.name))

中文:
定义 goalsCreatedBy
  签名: (t : TacticInfo)
  定义体: t.goalsAfter.filter (·.name ∉ t.goalsBefore.map (·.name))

Depends on / 依赖: filter, goalsAfter, goalsBefore, t.goalsAfter.filter, t.goalsBefore.map
-/
def goalsCreatedBy (t : TacticInfo) : List MVarId :=
  t.goalsAfter.filter (·.name ∉ t.goalsBefore.map (·.name))

end Lean.Elab.TacticInfo
end goals_heuristic

namespace Mathlib.Linter.Flexible

/--
Definition of `TacticData` / `TacticData` 的定义

English:
structure TacticData
  parameters: where
  axioms and operations (6):
    - stx : Syntax
    - ci : ContextInfo
    - mctxBefore : MetavarContext
    - mctxAfter : MetavarContext
    - goalsTargetedBy : List MVarId
    - goalsCreatedBy : List MVarId

中文:
结构 TacticData
  参数: where
  公理与运算 (6 个):
    - stx : Syntax
    - ci : ContextInfo
    - mctxBefore : MetavarContext
    - mctxAfter : MetavarContext
    - goalsTargetedBy : List MVarId
    - goalsCreatedBy : List MVarId
-/
structure TacticData where
  /-- The tactic syntax -/
  stx : Syntax
  /-- ContextInfo for running MetaM -/
  ci : ContextInfo
  /-- MetavarContext before the tactic -/
  mctxBefore : MetavarContext
  /-- MetavarContext after the tactic -/
  mctxAfter : MetavarContext
  /-- Goals targeted by the tactic -/
  goalsTargetedBy : List MVarId
  /-- Goals created by the tactic -/
  goalsCreatedBy : List MVarId

/--
Definition of `extractTacticData` / `extractTacticData` 的定义

English:
definition extractTacticData
  signature: (tree : InfoTree)
  body: tree.foldInfo (init := #[]) fun ci info acc =>
    match info with
    | .ofTacticInfo i =>
      if (i.stx.getRange? true).isSome then
        acc.push {
          stx := i.stx
          ci := ci
          mctxBefore := i.mctxBefore
          mctxAfter := i.mctxAfter
          goalsTargetedBy := i.

中文:
定义 extractTacticData
  签名: (tree : InfoTree)
  定义体: tree.foldInfo (init := #[]) fun ci info acc =>
    match info with
    | .ofTacticInfo i =>
      if (i.stx.getRange? true).isSome then
        acc.push {
          stx := i.stx
          ci := ci
          mctxBefore := i.mctxBefore
          mctxAfter := i.mctxAfter
          goalsTargetedBy := i.

Depends on / 依赖: acc.push, foldInfo, getRange, goalsCreatedBy, goalsTargetedBy, i.goalsCreatedBy, i.goalsTargetedBy, i.mctxAfter, i.mctxBefore, i.stx, i.stx.getRange, isSome, mctxAfter, mctxBefore, ofTacticInfo, tree.foldInfo
-/
def extractTacticData (tree : InfoTree) : Array TacticData :=
  tree.foldInfo (init := #[]) fun ci info acc =>
    match info with
    | .ofTacticInfo i =>
      if (i.stx.getRange? true).isSome then
        acc.push {
          stx := i.stx
          ci := ci
          mctxBefore := i.mctxBefore
          mctxAfter := i.mctxAfter
          goalsTargetedBy := i.goalsTargetedBy
          goalsCreatedBy := i.goalsCreatedBy
        }
      else acc
    | _ => acc

/--
Inductive type `Stained` / 归纳类型 `Stained`

English:
inductive Stained
  constructors (3):
    - name: Name -> Stained
    - goal: Stained
    - wildcard: Stained

中文:
归纳类型 Stained
  构造子 (3 个):
    - name: Name -> Stained
    - goal: Stained
    - wildcard: Stained
-/
inductive Stained
  | name : Name -> Stained
  | goal : Stained
  | wildcard : Stained
  deriving Repr, Inhabited, DecidableEq, Hashable

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString Stained

中文:
实例 :
  签名: ToString Stained
-/
instance : ToString Stained where
  toString | .name n => n.toString | .goal => "⊢" | .wildcard => "*"

/--
Definition of `toStained` / `toStained` 的定义

English:
definition toStained
  signature: : Syntax -> Std.HashSet Stained

中文:
定义 toStained
  签名: : Syntax -> Std.HashSet Stained
-/
partial def toStained : Syntax -> Std.HashSet Stained
  | .node _ _ arg => (arg.map toStained).foldl (.union) {}
  | .ident _ _ val _ => {.name val}
  | .atom _ val => match val with
                  | "*" => {.wildcard}
                  | "⊢" => {.goal}
                  | "|" => {.goal}
                  | _ => {}
  | _ => {}

/-- `getStained stx` expects `stx` to be an argument of a node of `SyntaxNodeKind`
`Lean.Parser.Tactic.location`.
Typically, we apply `getStained` to the output of `getLocs`.

See `getStained!` for a similar function. -/
partial
/--
Definition of `getStained` / `getStained` 的定义

English:
definition getStained
  signature: (stx : Syntax) (all? : Syntax -> Bool := fun _ => false)
  body: match stx with
    | stx@(.node _ ``Lean.Parser.Tactic.location loc) =>
      if all? stx then {} else (loc.map toStained).foldl (·.union) {}
    | .node _ _ args => (args.map (getStained · all?)).foldl (·.union) {}
    | _ => default

中文:
定义 getStained
  签名: (stx : Syntax) (all? : Syntax -> 布尔 := fun _ => false)
  定义体: match stx with
    | stx@(.node _ ``Lean.Parser.Tactic.location loc) =>
      if all? stx then {} else (loc.map toStained).foldl (·.union) {}
    | .node _ _ args => (args.map (getStained · all?)).foldl (·.union) {}
    | _ => default

Depends on / 依赖: HashSet, Stained, Std.HashSet
-/
def getStained (stx : Syntax) (all? : Syntax -> Bool := fun _ => false) : Std.HashSet Stained :=
  match stx with
    | stx@(.node _ ``Lean.Parser.Tactic.location loc) =>
      if all? stx then {} else (loc.map toStained).foldl (·.union) {}
    | .node _ _ args => (args.map (getStained · all?)).foldl (·.union) {}
    | _ => default

/--
Definition of `getStained!` / `getStained!` 的定义

English:
definition getStained!
  signature: (stx : Syntax) (all? : Syntax -> Bool := fun _ => false)
  body: let out := getStained stx all?
  if out.size == 0 then {.goal} else out

中文:
定义 getStained!
  签名: (stx : Syntax) (all? : Syntax -> 布尔 := fun _ => false)
  定义体: let out := getStained stx all?
  if out.size == 0 then {.goal} else out
-/
def getStained! (stx : Syntax) (all? : Syntax -> Bool := fun _ => false) : Std.HashSet Stained :=
  let out := getStained stx all?
  if out.size == 0 then {.goal} else out

/--
Definition of `Stained.toFMVarId` / `Stained.toFMVarId` 的定义

English:
definition Stained.toFMVarId
  signature: (mv : MVarId) (lctx: LocalContext)

中文:
定义 Stained.toFMVarId
  签名: (mv : MVarId) (lctx: LocalContext)
-/
def Stained.toFMVarId (mv : MVarId) (lctx: LocalContext) : Stained -> Array (FVarId × MVarId)
  | name n => match lctx.findFromUserName? n with
                  | none => #[]
                  | some decl => #[(decl.fvarId, mv)]
  | goal => #[(default, mv)]
  | wildcard => (lctx.getFVarIds.push default).map (·, mv)

/--
Definition of `stoppers` / `stoppers` 的定义

English:
definition stoppers
  signature: : Std.HashSet Name
  body: { -- "properly stopper tactics": the effect of these tactics is to return a normal form
    -- (or possibly be finishing tactics -- the ultimate normal form!
    -- finishing tactics could equally well be considered as `flexible`, but as there is
    -- no possibility of a follower anyway, it does n

中文:
定义 stoppers
  签名: : Std.HashSet Name
  定义体: { -- "properly stopper tactics": the effect of these tactics is to return a normal form
    -- (or possibly be finishing tactics -- the ultimate normal form!
    -- finishing tactics could equally well be considered as `flexible`, but as there is
    -- no possibility of a follower anyway, it does n

Depends on / 依赖: effect, normal, properly, return, stopper, tactics
-/
def stoppers : Std.HashSet Name :=
  { -- "properly stopper tactics": the effect of these tactics is to return a normal form
    -- (or possibly be finishing tactics -- the ultimate normal form!
    -- finishing tactics could equally well be considered as `flexible`, but as there is
    -- no possibility of a follower anyway, it does not make a big difference.)
    ``Lean.Parser.Tactic.tacticSorry,
    ``Lean.Parser.Tactic.tacticRepeat_,
    ``Lean.Parser.Tactic.tacticStop_,
    `Mathlib.Tactic.Abel.abelNF,
    `Mathlib.Tactic.Abel.tacticAbel_nf!__,
    `Mathlib.Tactic.RingNF.ringNF,
    `Mathlib.Tactic.RingNF.tacticRing_nf!__,
    `Mathlib.Tactic.Group.group,
    `Mathlib.Tactic.FieldSimp.fieldSimp,
    `Mathlib.Tactic.FieldSimp.field,
    `finiteness_nonterminal,
    -- "continuators": the *effect* of these tactics is similar the "properly stoppers" above,
    -- though they typically wrap other tactics inside them.
    -- The linter ignores the wrapper, but does recurse into the enclosed tactics
    ``Lean.Parser.Tactic.tacticSeq1Indented,
    ``Lean.Parser.Tactic.tacticSeq,
    ``Lean.Parser.Term.byTactic,
    `by,
    ``Lean.Parser.Tactic.tacticTry_,
    `choice, -- involved in `first`
    ``Lean.Parser.Tactic.allGoals,
    `Std.Tactic.«tacticOn_goal-_=>_»,
    ``Lean.Parser.Tactic.«tactic_<;>_»,
    ``cdotTk,
    ``cdot }

/--
Definition of `flexible` / `flexible` 的定义

English:
definition flexible
  signature: : Std.HashSet Name
  body: { ``Lean.Parser.Tactic.simp,
    ``Lean.Parser.Tactic.simpAll,
    ``Lean.Parser.Tactic.simpa,
    ``Lean.Parser.Tactic.simpaUsingBang,
    ``Lean.Parser.Tactic.dsimp,
    ``Lean.Parser.Tactic.constructor,
    ``Lean.Parser.Tactic.congr,
    ``Lean.Parser.Tactic.done,
    ``Lean.Parser.Tactic.tactic

中文:
定义 flexible
  签名: : Std.HashSet Name
  定义体: { ``Lean.Parser.Tactic.simp,
    ``Lean.Parser.Tactic.simpAll,
    ``Lean.Parser.Tactic.simpa,
    ``Lean.Parser.Tactic.simpaUsingBang,
    ``Lean.Parser.Tactic.dsimp,
    ``Lean.Parser.Tactic.constructor,
    ``Lean.Parser.Tactic.congr,
    ``Lean.Parser.Tactic.done,
    ``Lean.Parser.Tactic.tactic

Depends on / 依赖: Lean.Parser.Tactic.acRfl, Lean.Parser.Tactic.congr, Lean.Parser.Tactic.constructor, Lean.Parser.Tactic.done, Lean.Parser.Tactic.dsimp, Lean.Parser.Tactic.omega, Lean.Parser.Tactic.simp, Lean.Parser.Tactic.simpAll, Lean.Parser.Tactic.simpa, Lean.Parser.Tactic.simpaUsingBang, Lean.Parser.Tactic.tacticRfl, Mathlib, Mathlib.Tactic, Mathlib.Tactic.Abel.abel, Mathlib.Tactic.Abel.tacticAbel, Mathlib.Tactic.Group.group, Mathlib.Tactic.RingNF.ring, Mathlib.Tactic.RingNF.tacticRing, Parser, RingNF
-/
def flexible : Std.HashSet Name :=
  { ``Lean.Parser.Tactic.simp,
    ``Lean.Parser.Tactic.simpAll,
    ``Lean.Parser.Tactic.simpa,
    ``Lean.Parser.Tactic.simpaUsingBang,
    ``Lean.Parser.Tactic.dsimp,
    ``Lean.Parser.Tactic.constructor,
    ``Lean.Parser.Tactic.congr,
    ``Lean.Parser.Tactic.done,
    ``Lean.Parser.Tactic.tacticRfl,
    ``Lean.Parser.Tactic.acRfl,
    ``Lean.Parser.Tactic.omega,
    `Mathlib.Tactic.Abel.abel,
    `Mathlib.Tactic.Abel.tacticAbel!,
    `Mathlib.Tactic.Group.group,
    `Mathlib.Tactic.RingNF.ring,
    `Mathlib.Tactic.RingNF.tacticRing!,
    `Mathlib.Tactic.Ring.ring1,
    `Mathlib.Tactic.Ring.tacticRing1!,
    `Mathlib.Tactic.RingNF.ring1NF,
    `Mathlib.Tactic.RingNF.tacticRing1_nf!_,
    `Mathlib.Tactic.RingNF.ring1NF!,
    `Mathlib.Tactic.Module.tacticModule,
    `Mathlib.Tactic.FieldSimp.fieldSimp,
    `Mathlib.Tactic.FieldSimp.field,
    ``Lean.Parser.Tactic.grind,
    ``Lean.Parser.Tactic.grobner,
    ``Lean.Parser.Tactic.lia,
    `Mathlib.Tactic.normNum,
    `Mathlib.Tactic.linarith,
    `Mathlib.Tactic.nlinarith,
    `Mathlib.Tactic.tacticNlinarith!_,
    `Mathlib.Tactic.LinearCombination.linearCombination,
    ``Lean.Parser.Tactic.tacticNorm_cast__,
    `Aesop.Frontend.Parser.aesopTactic,
    -- `cfc_tac` and `cfc_zero_tac` use `aesop` under the hood,
    -- `cfc_cont_tactic` uses `fun_prop`: in practice, this should be robust enough.
    `cfcTac,
    `cfcZeroTac,
    `cfcContTac,
    -- `continuity` and `measurability` also use `aesop` under the hood.
    `tacticContinuity,
    `Mathlib.Tactic.measurability,
    `finiteness,
    `finiteness?,
    `Mathlib.Tactic.Tauto.tauto,
    `Lean.Parser.Tactic.split,
    `Mathlib.Tactic.splitIfs }

/--
Definition of `usesGoal?` / `usesGoal?` 的定义

English:
definition usesGoal?
  signature: : SyntaxNodeKind -> Bool

中文:
定义 usesGoal?
  签名: : SyntaxNodeKind -> 布尔
-/
def usesGoal? : SyntaxNodeKind -> Bool
  | ``Lean.Parser.Tactic.cases => false
  | `Mathlib.Tactic.cases' => false
  | ``Lean.Parser.Tactic.obtain => false
  | ``Lean.Parser.Tactic.tacticHave__ => false
  | ``Lean.Parser.Tactic.rcases => false
  | ``Lean.Parser.Tactic.specialize => false
  | ``Lean.Parser.Tactic.subst => false
  | ``«tacticBy_cases_:_» => false
  | ``Lean.Parser.Tactic.induction => false
  | _ => true

/--
Definition of `getFVarIdCandidates` / `getFVarIdCandidates` 的定义

English:
definition getFVarIdCandidates
  signature: (fv : FVarId) (name : Name) (lctx : LocalContext)
  body: #[lctx.find? fv, lctx.findFromUserName? name].reduceOption.map (·.fvarId)

中文:
定义 getFVarIdCandidates
  签名: (fv : FVarId) (name : Name) (lctx : LocalContext)
  定义体: #[lctx.find? fv, lctx.findFromUserName? name].reduceOption.map (·.fvarId)

Depends on / 依赖: findFromUserName, fvarId, lctx.find, lctx.findFromUserName, reduceOption, reduceOption.map
-/
def getFVarIdCandidates (fv : FVarId) (name : Name) (lctx : LocalContext) : Array FVarId :=
  #[lctx.find? fv, lctx.findFromUserName? name].reduceOption.map (·.fvarId)

/-!
Tactics often change the name of the current `MVarId`, as well as the names of the `FVarId`s
appearing in their local contexts.
The function `reallyPersist` makes an attempt at "tracking" pairs `(fvar, mvar)` across a
simultaneous change represented by an "old" list of `MVarId`s and the corresponding
`MetavarContext` and a new one.

This arises in the context of the information encoded in the `InfoTree`s when processing a
tactic proof.
-/

/--
Definition of `persistFVars` / `persistFVars` 的定义

English:
definition persistFVars
  signature: (fv : FVarId) (before after : LocalContext)
  body: let ldecl := (before.find? fv).getD default
  (getFVarIdCandidates fv ldecl.userName after).getD 0 default

中文:
定义 persistFVars
  签名: (fv : FVarId) (before after : LocalContext)
  定义体: let ldecl := (before.find? fv).getD default
  (getFVarIdCandidates fv ldecl.userName after).getD 0 default

Depends on / 依赖: before, before.find, getFVarIdCandidates, ldecl.userName, userName
-/
def persistFVars (fv : FVarId) (before after : LocalContext) : FVarId :=
  let ldecl := (before.find? fv).getD default
  (getFVarIdCandidates fv ldecl.userName after).getD 0 default

/--
Definition of `reallyPersist` / `reallyPersist` 的定义

English:
definition reallyPersist
  body: Id.run do
  -- split the input `fmvars` into
  -- * the `active` ones, whose `mvar` appears in `mvs0` and
  -- * the `inert` ones, the rest.
  -- `inert` gets copied unchanged, while we transform `active`
  let (active, inert) := fmvars.partition fun (_, mv) => mvs0.contains mv
  let mut new := #[]


中文:
定义 reallyPersist
  定义体: Id.run do
  -- split the input `fmvars` into
  -- * the `active` ones, whose `mvar` appears in `mvs0` and
  -- * the `inert` ones, the rest.
  -- `inert` gets copied unchanged, while we transform `active`
  let (active, inert) := fmvars.partition fun (_, mv) => mvs0.contains mv
  let mut new := #[]


Depends on / 依赖: Id.run
-/
def reallyPersist
    (fmvars : Array (FVarId × MVarId)) (mvs0 mvs1 : List MVarId) (ctx0 ctx1 : MetavarContext) :
    Array (FVarId × MVarId) := Id.run do
  -- split the input `fmvars` into
  -- * the `active` ones, whose `mvar` appears in `mvs0` and
  -- * the `inert` ones, the rest.
  -- `inert` gets copied unchanged, while we transform `active`
  let (active, inert) := fmvars.partition fun (_, mv) => mvs0.contains mv
  let mut new := #[]
  for (fvar, mvar) in active do -- for each `active` pair `(fvar, mvar)`
    match ctx0.decls.find? mvar with -- check if `mvar` is managed by `ctx0` (it should be)
      | none => -- the `mvar` is not managed by `ctx0`: no change
        new := new.push (fvar, mvar)
      | some mvDecl0 => -- the `mvar` *is* managed by `ctx0`: push the pair `(fvar, mvar)` through
        for mv1 in mvs1 do -- for each new `MVarId` in `mvs1`
          match ctx1.decls.find? mv1 with -- check if `mv1` is managed by `ctx1` (it should be)
            | none => dbg_trace "'really_persist' could this happen?" default -- ??? maybe `.push`?
            | some mvDecl1 => -- we found a "new" declaration
              let persisted_fv := persistFVars fvar mvDecl0.lctx mvDecl1.lctx -- persist `fv`
              new := new.push (persisted_fv, mv1)
  return inert ++ new

/--
Definition of `StainData` / `StainData` 的定义

English:
structure StainData
  parameters: where
  axioms and operations (5):
    - stained : Stained
    - stx : Syntax
    - ci : ContextInfo
    - mctx : MetavarContext
    - goals : List MVarId

中文:
结构 StainData
  参数: where
  公理与运算 (5 个):
    - stained : Stained
    - stx : Syntax
    - ci : ContextInfo
    - mctx : MetavarContext
    - goals : List MVarId
-/
structure StainData where
  /-- The stained location -/
  stained : Stained
  /-- The syntax of the flexible tactic that caused the stain -/
  stx : Syntax
  /-- ContextInfo for running MetaM -/
  ci : ContextInfo
  /-- MetavarContext before the flexible tactic -/
  mctx : MetavarContext
  /-- Goals before the flexible tactic -/
  goals : List MVarId

/--
Definition of `generateSimpSuggestion` / `generateSimpSuggestion` 的定义

English:
definition generateSimpSuggestion
  signature: (stainData : StainData) (stainStx : Syntax)
  body: do
  match stainStx.getKind with
  | ``Lean.Parser.Tactic.simp | ``Lean.Parser.Tactic.simpAll => try
    let some mv := stainData.goals[0]? | return none
    let some mvDecl := stainData.mctx.decls.find? mv | return none
    stainData.ci.runMetaM mvDecl.lctx do
      Lean.Meta.withMCtx stainData.mct

中文:
定义 generateSimpSuggestion
  签名: (stainData : StainData) (stainStx : Syntax)
  定义体: do
  match stainStx.getKind with
  | ``Lean.Parser.Tactic.simp | ``Lean.Parser.Tactic.simpAll => try
    let some mv := stainData.goals[0]? | return none
    let some mvDecl := stainData.mctx.decls.find? mv | return none
    stainData.ci.runMetaM mvDecl.lctx do
      Lean.Meta.withMCtx stainData.mct
-/
def generateSimpSuggestion (stainData : StainData) (stainStx : Syntax) :
    CoreM (Option Syntax) := do
  match stainStx.getKind with
  | ``Lean.Parser.Tactic.simp | ``Lean.Parser.Tactic.simpAll => try
    let some mv := stainData.goals[0]? | return none
    let some mvDecl := stainData.mctx.decls.find? mv | return none
    stainData.ci.runMetaM mvDecl.lctx do
      Lean.Meta.withMCtx stainData.mctx do
        let ctx ← Lean.Meta.Simp.Context.mkDefault
        let simprocs ← Lean.Meta.Simp.getSimprocs
        let (_, stats) ← Lean.Meta.simpGoal mv ctx #[simprocs]
        if stats.usedTheorems.map.isEmpty then
          return none
        let suggStx ← Lean.Elab.Tactic.mkSimpOnly stainStx stats.usedTheorems
        return some suggStx
  catch _ => return none
  | _ => return none

/--
Definition of `flexibleLinter` / `flexibleLinter` 的定义

English:
definition flexibleLinter
  signature: : Linter where run
  body: withSetOptionIn fun _stx => do
  unless getLinterValue linter.flexible (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let tacticData := trees.foldl (init := #[]) fun acc tree => acc ++ extractTact

中文:
定义 flexibleLinter
  签名: : Linter where run
  定义体: withSetOptionIn fun _stx => do
  unless getLinterValue linter.flexible (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let tacticData := trees.foldl (init := #[]) fun acc tree => acc ++ extractTact

Depends on / 依赖: _stx, withSetOptionIn
-/
def flexibleLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterValue linter.flexible (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let tacticData := trees.foldl (init := #[]) fun acc tree => acc ++ extractTacticData tree
  -- `stains` records pairs `(location, mvar)`, where
  -- * `location` is either a hypothesis or the main goal modified by a flexible tactic and
  -- * `mvar` is the metavariable containing the modified location
  -- We also track the ContextInfo and MetavarContext for generating suggestions
  let mut stains : Array ((FVarId × MVarId) × StainData) := #[]
  let mut msgs : Array (Syntax × StainData) := #[]
  for td in tacticData do
    let s := td.stx
    let ctx0 := td.mctxBefore
    let ctx1 := td.mctxAfter
    let mvs0 := td.goalsTargetedBy
    let mvs1 := td.goalsCreatedBy
    let skind := s.getKind
    if stoppers.contains skind then continue
    let shouldStain? := flexible? s && mvs1.length == mvs0.length
    for d in getStained! s do
      if shouldStain? then
        for currMVar1 in mvs1 do
          let lctx1 := (ctx1.decls.findD currMVar1 default).lctx
          let locsAfter := d.toFMVarId currMVar1 lctx1
          -- Store ContextInfo, mctxBefore, and goals for generating suggestions later
          let stainData : StainData := {
            stained := d, stx := s, ci := td.ci, mctx := ctx0, goals := mvs0
          }
          stains := stains ++ locsAfter.map (fun l => (l, stainData))
      else
        let stained_in_syntax := if usesGoal? skind then (toStained s).insert d else toStained s
        if !flexible.contains skind then
          for currMv0 in mvs0 do
            let lctx0 := (ctx0.decls.findD currMv0 default).lctx
            let mut foundFvs : Std.HashSet (FVarId × MVarId):= {}
            for st in stained_in_syntax do
              for d in st.toFMVarId currMv0 lctx0 do
                if !foundFvs.contains d then foundFvs := foundFvs.insert d
            for l in foundFvs do
              if let some (_stdLoc, stainData) := stains.find? (Prod.fst · == l) then
                msgs := msgs.push (s, stainData)

      -- tactics often change the name of the current `MVarId`, so we migrate the `FvarId`s
      -- in the "old" `mvars` to the "same" `FVarId` in the "new" `mvars`
      let mut new : Array ((FVarId × MVarId) × StainData) := .empty
      for (fv, stainData) in stains do
        let psisted := reallyPersist #[fv] mvs0 mvs1 ctx0 ctx1
        if psisted == #[] && mvs1 != [] then
          new := new.push (fv, stainData)
          dbg_trace "lost {((fv.1.name, fv.2.name), stainData.stained, stainData.stx)}"
        for p in psisted do new := new.push (p, stainData)
      stains := new

  for (s, stainData) in msgs do
    let stainStx := stainData.stx
    let d := stainData.stained
    let stainStr := (stainStx.reprint.getD s!"{stainStx}").trimAscii
let suggestion? ← liftCoreM generateSimpSuggestion stainData stainStx
    -- Emit warning and suggestion
    let msg := match stainStx.getKind with
      | ``Lean.Parser.Tactic.simp => match d with
        | .wildcard => m!"`{stainStr}` is a flexible tactic that potentially modifies all \
          hypotheses and the current goal with a wildcard `*`. \
          Try `simp?` and use the suggested `simp only [...]`. \
          Alternatively, use `suffices` to explicitly state the simplified form."
        | _ => m!"`{stainStr}` is a flexible tactic modifying `{d}`. \
          Try `simp?` and use the suggested `simp only [...]`. \
          Alternatively, use `suffices` to explicitly state the simplified form."
      | ``Lean.Parser.Tactic.simpAll =>
        m!"`{stainStr}` is a flexible tactic modifying `{d}`. \
          Try `simp_all?` and use the suggested `simp_all only [...]`. \
          Alternatively, use `suffices` to explicitly state the simplified form."
      | `Aesop.Frontend.Parser.aesopTactic =>
        m!"`{stainStr}` is a flexible tactic modifying `{d}`. \
          Try `aesop?` and use the suggested proof."
      | _ =>
        m!"`{stainStr}` is a flexible tactic modifying `{d}`."
    Linter.logLint linter.flexible stainStx msg
    if let some suggStx := suggestion? then
liftCoreM Lean.Meta.Tactic.TryThis.addSuggestion stainStx
        { suggestion := .tsyntax (kind := `tactic) ⟨suggStx⟩ } (origSpan? := stainStx)
    let fm ← getFileMap
    let stainLine? := stainStx.getPos?.map (Position.line ∘ fm.toPosition)
    let lineStr := if let some line := stainLine? then s!" on line {line}" else ""
    let atomStr := match stainStx[0] with
      | .atom _ val => "the flexible tactic " ++ m!"`{val}`"
      | _ => "a flexible tactic"
logInfoAt s match d with
    | .name _ => m!"`{.group s}`\nuses `{d}`, which was modified by {atomStr}{lineStr}!"
    | .goal =>
      m!"`{.group s}`\nmodifies the current goal, which was modified by {atomStr}{lineStr}!"
    | .wildcard => m!"`{.group s}`\nuses a rigid tactic. Previously, {atomStr}, which \
        potentially modified all hypotheses and the goal with a wildcard `*`, was used{lineStr}."

initialize addLinter flexibleLinter

end Mathlib.Linter.Flexible
