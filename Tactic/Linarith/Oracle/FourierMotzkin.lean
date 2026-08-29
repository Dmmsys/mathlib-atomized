/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public meta import Std.Data.HashMap.AdditionalOperations
public meta import Batteries.Lean.HashMap
public import Mathlib.Tactic.Linarith.Datatypes

/-!
# The Fourier-Motzkin elimination procedure

The Fourier-Motzkin procedure is a variable elimination method for linear inequalities.
<https://en.wikipedia.org/wiki/Fourier%E2%80%93Motzkin_elimination>

Given a set of linear inequalities `comps = {tᵢ Rᵢ 0}`,
we aim to eliminate a single variable `a` from the set.
We partition `comps` into `comps_pos`, `comps_neg`, and `comps_zero`,
where `comps_pos` contains the comparisons `tᵢ Rᵢ 0` in which
the coefficient of `a` in `tᵢ` is positive, and similar.

For each pair of comparisons `tᵢ Rᵢ 0 ∈ comps_pos`, `tⱼ Rⱼ 0 ∈ comps_neg`,
we compute coefficients `vᵢ, vⱼ ∈ ℕ` such that `vᵢ*tᵢ + vⱼ*tⱼ` cancels out `a`.
We collect these sums `vᵢ*tᵢ + vⱼ*tⱼ R' 0` in a set `S` and set `comps' = S ∪ comps_zero`,
a new set of comparisons in which `a` has been eliminated.

Theorem: `comps` and `comps'` are equisatisfiable.

We recursively eliminate all variables from the system. If we derive an empty clause `0 < 0`,
we conclude that the original system was unsatisfiable.
-/

public meta section

open Batteries
open Std (format ToFormat TreeSet)

namespace Mathlib.Tactic.Linarith

/-!
### Datatypes

The `CompSource` and `PComp` datatypes are specific to the FM elimination routine;
they are not shared with other components of `linarith`.
-/

/--
Inductive type `CompSource` / 归纳类型 `CompSource`

English:
inductive CompSource
  parameters: : Type
  constructors (3):
    - assump: Nat -> CompSource
    - add: CompSource -> CompSource -> CompSource
    - scale: Nat -> CompSource -> CompSource

中文:
归纳类型 CompSource
  参数: : Type
  构造子 (3 个):
    - assump: 自然数 -> CompSource
    - add: CompSource -> CompSource -> CompSource
    - scale: 自然数 -> CompSource -> CompSource
-/
inductive CompSource : Type
  | assump : Nat -> CompSource
  | add : CompSource -> CompSource -> CompSource
  | scale : Nat -> CompSource -> CompSource
deriving Inhabited

/--
Definition of `CompSource.flatten` / `CompSource.flatten` 的定义

English:
definition CompSource.flatten
  signature: : CompSource -> Std.HashMap Nat Nat

中文:
定义 CompSource.flatten
  签名: : CompSource -> Std.HashMap 自然数 自然数
-/
def CompSource.flatten : CompSource -> Std.HashMap Nat Nat
  | (CompSource.assump n) => (∅ : Std.HashMap Nat Nat).insert n 1
  | (CompSource.add c1 c2) =>
      (CompSource.flatten c1).mergeWith (fun _ b b' => b + b') (CompSource.flatten c2)
  | (CompSource.scale n c) => (CompSource.flatten c).map (fun _ v => v * n)

/--
Definition of `CompSource.toString` / `CompSource.toString` 的定义

English:
definition CompSource.toString
  signature: : CompSource -> String

中文:
定义 CompSource.toString
  签名: : CompSource -> String
-/
def CompSource.toString : CompSource -> String
  | (CompSource.assump e) => ToString.toString e
  | (CompSource.add c1 c2) => CompSource.toString c1 ++ " + " ++ CompSource.toString c2
  | (CompSource.scale n c) => ToString.toString n ++ " * " ++ CompSource.toString c

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToFormat CompSource
  body: ⟨fun a => CompSource.toString a⟩

中文:
实例 :
  签名: ToFormat CompSource
  定义体: ⟨fun a => CompSource.toString a⟩

Depends on / 依赖: CompSource, CompSource.toString, toString
-/
instance : ToFormat CompSource :=
  ⟨fun a => CompSource.toString a⟩

/--
Definition of `PComp` / `PComp` 的定义

English:
structure PComp
  parameters: : Type where
  axioms and operations (6):
    - c : Comp
    - src : CompSource
    - history : TreeSet Nat Ord.compare
    - effective : TreeSet Nat Ord.compare
    - implicit : TreeSet Nat Ord.compare
    - vars : TreeSet Nat Ord.compare

中文:
结构 PComp
  参数: : Type where
  公理与运算 (6 个):
    - c : Comp
    - src : CompSource
    - history : TreeSet 自然数 Ord.compare
    - effective : TreeSet 自然数 Ord.compare
    - implicit : TreeSet 自然数 Ord.compare
    - vars : TreeSet 自然数 Ord.compare
-/
structure PComp : Type where
  /-- The comparison `Σ cᵢ*xᵢ R 0`. -/
  c : Comp
  /-- We track how the comparison was constructed by adding and scaling previous comparisons,
  back to the original assumptions. -/
  src : CompSource
  /-- The set of original assumptions which have been used in constructing this comparison. -/
  history : TreeSet Nat Ord.compare
  /-- The variables which have been *effectively eliminated*,
  i.e. by running the elimination algorithm on that variable. -/
  effective : TreeSet Nat Ord.compare
  /-- The variables which have been *implicitly eliminated*.
  These are variables that appear in the historical set,
  do not appear in `c` itself, and are not in `effective`. -/
  implicit : TreeSet Nat Ord.compare
  /-- The union of all variables appearing in those original assumptions
  which appear in the `history` set. -/
  vars : TreeSet Nat Ord.compare

/--
Definition of `PComp.maybeMinimal` / `PComp.maybeMinimal` 的定义

English:
definition PComp.maybeMinimal
  signature: (c : PComp) (elimedGE : Nat)
  body: c.history.size <= 1 + ((c.implicit.filter (· >= elimedGE)).union c.effective).size

中文:
定义 PComp.maybeMinimal
  签名: (c : PComp) (elimedGE : 自然数)
  定义体: c.history.size <= 1 + ((c.implicit.filter (· >= elimedGE)).union c.effective).size

Depends on / 依赖: c.effective, c.history.size, c.implicit.filter, effective, elimedGE, filter, history, implicit
-/
def PComp.maybeMinimal (c : PComp) (elimedGE : Nat) : Bool :=
  c.history.size <= 1 + ((c.implicit.filter (· >= elimedGE)).union c.effective).size

/--
Definition of `PComp.cmp` / `PComp.cmp` 的定义

English:
definition PComp.cmp
  signature: (p1 p2 : PComp)
  body: p1.c.cmp p2.c

中文:
定义 PComp.cmp
  签名: (p1 p2 : PComp)
  定义体: p1.c.cmp p2.c

Depends on / 依赖: p1.c.cmp, p2.c
-/
def PComp.cmp (p1 p2 : PComp) : Ordering := p1.c.cmp p2.c

/--
Definition of `PComp.scale` / `PComp.scale` 的定义

English:
definition PComp.scale
  signature: (c : PComp) (n : Nat)
  body: { c with c := c.c.scale n, src := c.src.scale n }

中文:
定义 PComp.scale
  签名: (c : PComp) (n : 自然数)
  定义体: { c with c := c.c.scale n, src := c.src.scale n }

Depends on / 依赖: c.c.scale, c.src.scale
-/
def PComp.scale (c : PComp) (n : Nat) : PComp :=
  { c with c := c.c.scale n, src := c.src.scale n }

/--
Definition of `PComp.add` / `PComp.add` 的定义

English:
definition PComp.add
  signature: (c1 c2 : PComp) (elimVar : Nat)
  body: let c := c1.c.add c2.c
  let src := c1.src.add c2.src
  let history := c1.history.union c2.history
  let vars := c1.vars.union c2.vars
  let effective := (c1.effective.union c2.effective).insert elimVar
  let implicit := (vars.diff (.ofList c.vars _)).diff effective
  ⟨c, src, history, effective, im

中文:
定义 PComp.add
  签名: (c1 c2 : PComp) (elimVar : 自然数)
  定义体: let c := c1.c.add c2.c
  let src := c1.src.add c2.src
  let history := c1.history.union c2.history
  let vars := c1.vars.union c2.vars
  let effective := (c1.effective.union c2.effective).insert elimVar
  let implicit := (vars.diff (.ofList c.vars _)).diff effective
  ⟨c, src, history, effective, im

Depends on / 依赖: c.vars, c1.c.add, c1.effective.union, c1.history.union, c1.src.add, c1.vars.union, c2.c, c2.effective, c2.history, c2.src, c2.vars, effective, elimVar, history, implicit, insert, ofList, vars.diff
-/
def PComp.add (c1 c2 : PComp) (elimVar : Nat) : PComp :=
  let c := c1.c.add c2.c
  let src := c1.src.add c2.src
  let history := c1.history.union c2.history
  let vars := c1.vars.union c2.vars
  let effective := (c1.effective.union c2.effective).insert elimVar
  let implicit := (vars.diff (.ofList c.vars _)).diff effective
  ⟨c, src, history, effective, implicit, vars⟩

/--
Definition of `PComp.assump` / `PComp.assump` 的定义

English:
definition PComp.assump
  signature: (c : Comp) (n : Nat)
  body: c
  src := CompSource.assump n
  history := {n}
  effective := .empty
  implicit := .empty
  vars := .ofList c.vars _

中文:
定义 PComp.assump
  签名: (c : Comp) (n : 自然数)
  定义体: c
  src := CompSource.assump n
  history := {n}
  effective := .empty
  implicit := .empty
  vars := .ofList c.vars _
-/
def PComp.assump (c : Comp) (n : Nat) : PComp where
  c := c
  src := CompSource.assump n
  history := {n}
  effective := .empty
  implicit := .empty
  vars := .ofList c.vars _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToFormat PComp
  body: ⟨fun p => format p.c.coeffs ++ toString p.c.str ++ "0"⟩

中文:
实例 :
  签名: ToFormat PComp
  定义体: ⟨fun p => format p.c.coeffs ++ toString p.c.str ++ "0"⟩

Depends on / 依赖: coeffs, format, p.c.coeffs, p.c.str, toString
-/
instance : ToFormat PComp :=
  ⟨fun p => format p.c.coeffs ++ toString p.c.str ++ "0"⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString PComp
  body: ⟨fun p => toString p.c.coeffs ++ toString p.c.str ++ "0"⟩

中文:
实例 :
  签名: ToString PComp
  定义体: ⟨fun p => toString p.c.coeffs ++ toString p.c.str ++ "0"⟩

Depends on / 依赖: coeffs, p.c.coeffs, p.c.str, toString
-/
instance : ToString PComp :=
  ⟨fun p => toString p.c.coeffs ++ toString p.c.str ++ "0"⟩

/--
Definition of `PCompSet` / `PCompSet` 的定义

English:
abbreviation PCompSet
  body: TreeSet PComp PComp.cmp

中文:
缩写 PCompSet
  定义体: TreeSet PComp PComp.cmp

Depends on / 依赖: PComp.cmp, TreeSet
-/
abbrev PCompSet := TreeSet PComp PComp.cmp

/-! ### Elimination procedure -/

/--
Definition of `elimVar` / `elimVar` 的定义

English:
definition elimVar
  signature: (c1 c2 : Comp) (a : Nat)
  body: let v1 := c1.coeffOf a
  let v2 := c2.coeffOf a
  if v1 * v2 < 0 then
    let vlcm := Nat.lcm v1.natAbs v2.natAbs
    some ⟨vlcm / v1.natAbs, vlcm / v2.natAbs⟩
  else none

中文:
定义 elimVar
  签名: (c1 c2 : Comp) (a : 自然数)
  定义体: let v1 := c1.coeffOf a
  let v2 := c2.coeffOf a
  if v1 * v2 < 0 then
    let vlcm := Nat.lcm v1.natAbs v2.natAbs
    some ⟨vlcm / v1.natAbs, vlcm / v2.natAbs⟩
  else none

Depends on / 依赖: Nat.lcm, c1.coeffOf, c2.coeffOf, coeffOf, natAbs, v1.natAbs, v2.natAbs
-/
def elimVar (c1 c2 : Comp) (a : Nat) : Option (Nat × Nat) :=
  let v1 := c1.coeffOf a
  let v2 := c2.coeffOf a
  if v1 * v2 < 0 then
    let vlcm := Nat.lcm v1.natAbs v2.natAbs
    some ⟨vlcm / v1.natAbs, vlcm / v2.natAbs⟩
  else none

/--
Definition of `pelimVar` / `pelimVar` 的定义

English:
definition pelimVar
  signature: (p1 p2 : PComp) (a : Nat)
  body: do
  let (n1, n2) ← elimVar p1.c p2.c a
  return (p1.scale n1).add (p2.scale n2) a

中文:
定义 pelimVar
  签名: (p1 p2 : PComp) (a : 自然数)
  定义体: do
  let (n1, n2) ← elimVar p1.c p2.c a
  return (p1.scale n1).add (p2.scale n2) a

Depends on / 依赖: foobar
-/
def pelimVar (p1 p2 : PComp) (a : Nat) : Option PComp := do
  let (n1, n2) ← elimVar p1.c p2.c a
  return (p1.scale n1).add (p2.scale n2) a

/--
Definition of `PComp.isContr` / `PComp.isContr` 的定义

English:
definition PComp.isContr
  signature: (p : PComp)
  body: p.c.isContr

中文:
定义 PComp.isContr
  签名: (p : PComp)
  定义体: p.c.isContr

Depends on / 依赖: isContr, p.c.isContr
-/
def PComp.isContr (p : PComp) : Bool := p.c.isContr

/--
Definition of `elimWithSet` / `elimWithSet` 的定义

English:
definition elimWithSet
  signature: (a : Nat) (p : PComp) (comps : PCompSet)
  body: comps.foldl (fun s pc =>
  match pelimVar p pc a with
  | some pc => if pc.maybeMinimal a then s.insert pc else s
  | none => s) TreeSet.empty

中文:
定义 elimWithSet
  签名: (a : 自然数) (p : PComp) (comps : PCompSet)
  定义体: comps.foldl (fun s pc =>
  match pelimVar p pc a with
  | some pc => if pc.maybeMinimal a then s.insert pc else s
  | none => s) TreeSet.empty

Depends on / 依赖: TreeSet, TreeSet.empty, comps.foldl, insert, maybeMinimal, pc.maybeMinimal, pelimVar, s.insert
-/
def elimWithSet (a : Nat) (p : PComp) (comps : PCompSet) : PCompSet :=
  comps.foldl (fun s pc =>
  match pelimVar p pc a with
  | some pc => if pc.maybeMinimal a then s.insert pc else s
  | none => s) TreeSet.empty

/--
Definition of `LinarithData` / `LinarithData` 的定义

English:
structure LinarithData
  parameters: : Type where
  axioms and operations (2):
    - maxVar : Nat
    - comps : PCompSet

中文:
结构 LinarithData
  参数: : Type where
  公理与运算 (2 个):
    - maxVar : 自然数
    - comps : PCompSet
-/
structure LinarithData : Type where
  /-- The largest variable index that has not been (officially) eliminated. -/
  maxVar : Nat
  /-- The set of comparisons. -/
  comps : PCompSet

/--
Definition of `LinarithM` / `LinarithM` 的定义

English:
abbreviation LinarithM
  signature: : Type -> Type
  body: StateT LinarithData (ExceptT PComp Lean.Core.CoreM)

中文:
缩写 LinarithM
  签名: : Type -> Type
  定义体: StateT LinarithData (ExceptT PComp Lean.Core.CoreM)

Depends on / 依赖: ExceptT, Lean.Core.CoreM, LinarithData, StateT
-/
abbrev LinarithM : Type -> Type :=
  StateT LinarithData (ExceptT PComp Lean.Core.CoreM)

/--
Definition of `getMaxVar` / `getMaxVar` 的定义

English:
definition getMaxVar
  signature: : LinarithM Nat
  body: LinarithData.maxVar < > get

中文:
定义 getMaxVar
  签名: : LinarithM 自然数
  定义体: LinarithData.maxVar < > get

Depends on / 依赖: LinarithData, LinarithData.maxVar, maxVar
-/
def getMaxVar : LinarithM Nat :=
LinarithData.maxVar < > get

/--
Definition of `getPCompSet` / `getPCompSet` 的定义

English:
definition getPCompSet
  signature: : LinarithM PCompSet
  body: LinarithData.comps < > get

中文:
定义 getPCompSet
  签名: : LinarithM PCompSet
  定义体: LinarithData.comps < > get

Depends on / 依赖: LinarithData, LinarithData.comps
-/
def getPCompSet : LinarithM PCompSet :=
LinarithData.comps < > get

/--
Definition of `validate` / `validate` 的定义

English:
definition validate
  signature: : LinarithM Unit
  body: do
  match (← getPCompSet).toList.find? (fun p : PComp => p.isContr) with
  | none => return ()
  | some c => throwThe _ c

中文:
定义 validate
  签名: : LinarithM Unit
  定义体: do
  match (← getPCompSet).toList.find? (fun p : PComp => p.isContr) with
  | none => return ()
  | some c => throwThe _ c

Depends on / 依赖: e.symm
-/
def validate : LinarithM Unit := do
  match (← getPCompSet).toList.find? (fun p : PComp => p.isContr) with
  | none => return ()
  | some c => throwThe _ c

/--
Definition of `update` / `update` 的定义

English:
definition update
  signature: (maxVar : Nat) (comps : PCompSet)
  body: do
  StateT.set ⟨maxVar, comps⟩
  validate

中文:
定义 update
  签名: (maxVar : 自然数) (comps : PCompSet)
  定义体: do
  StateT.set ⟨maxVar, comps⟩
  validate
-/
def update (maxVar : Nat) (comps : PCompSet) : LinarithM Unit := do
  StateT.set ⟨maxVar, comps⟩
  validate

/--
Definition of `splitSetByVarSign` / `splitSetByVarSign` 的定义

English:
definition splitSetByVarSign
  signature: (a : Nat) (comps : PCompSet)
  body: comps.foldl (fun ⟨pos, neg, notPresent⟩ pc =>
    let n := pc.c.coeffOf a
    if n > 0 then ⟨pos.insert pc, neg, notPresent⟩
    else if n < 0 then ⟨pos, neg.insert pc, notPresent⟩
    else ⟨pos, neg, notPresent.insert pc⟩)
    ⟨TreeSet.empty, TreeSet.empty, TreeSet.empty⟩

中文:
定义 splitSetByVarSign
  签名: (a : 自然数) (comps : PCompSet)
  定义体: comps.foldl (fun ⟨pos, neg, notPresent⟩ pc =>
    let n := pc.c.coeffOf a
    if n > 0 then ⟨pos.insert pc, neg, notPresent⟩
    else if n < 0 then ⟨pos, neg.insert pc, notPresent⟩
    else ⟨pos, neg, notPresent.insert pc⟩)
    ⟨TreeSet.empty, TreeSet.empty, TreeSet.empty⟩

Depends on / 依赖: TreeSet, TreeSet.empty, coeffOf, comps.foldl, insert, neg.insert, notPresent, notPresent.insert, pc.c.coeffOf, pos.insert
-/
def splitSetByVarSign (a : Nat) (comps : PCompSet) : PCompSet × PCompSet × PCompSet :=
  comps.foldl (fun ⟨pos, neg, notPresent⟩ pc =>
    let n := pc.c.coeffOf a
    if n > 0 then ⟨pos.insert pc, neg, notPresent⟩
    else if n < 0 then ⟨pos, neg.insert pc, notPresent⟩
    else ⟨pos, neg, notPresent.insert pc⟩)
    ⟨TreeSet.empty, TreeSet.empty, TreeSet.empty⟩

/--
Definition of `elimVarM` / `elimVarM` 的定义

English:
definition elimVarM
  signature: (a : Nat)
  body: do
  let vs ← getMaxVar
  if (a <= vs) then
    Lean.Core.checkSystem decl_name%.toString
    let ⟨pos, neg, notPresent⟩ := splitSetByVarSign a (← getPCompSet)
    update (vs - 1) (← pos.foldlM (fun s p => do
      Lean.Core.checkSystem decl_name%.toString
      -- FIXME: `.foldl .insert` should be 

中文:
定义 elimVarM
  签名: (a : 自然数)
  定义体: do
  let vs ← getMaxVar
  if (a <= vs) then
    Lean.Core.checkSystem decl_name%.toString
    let ⟨pos, neg, notPresent⟩ := splitSetByVarSign a (← getPCompSet)
    update (vs - 1) (← pos.foldlM (fun s p => do
      Lean.Core.checkSystem decl_name%.toString
      -- FIXME: `.foldl .insert` should be 
-/
def elimVarM (a : Nat) : LinarithM Unit := do
  let vs ← getMaxVar
  if (a <= vs) then
    Lean.Core.checkSystem decl_name%.toString
    let ⟨pos, neg, notPresent⟩ := splitSetByVarSign a (← getPCompSet)
    update (vs - 1) (← pos.foldlM (fun s p => do
      Lean.Core.checkSystem decl_name%.toString
      -- FIXME: `.foldl .insert` should be equivalent to `.union`, but this breaks the test from
      -- https://github.com/leanprover-community/mathlib4/issues/8875
      pure ((elimWithSet a p neg).foldl .insert s)) notPresent)
  else
    pure ()

/--
Definition of `elimAllVarsM` / `elimAllVarsM` 的定义

English:
definition elimAllVarsM
  signature: : LinarithM Unit
  body: do
  for i in (List.range ((← getMaxVar) + 1)).reverse do
    elimVarM i

中文:
定义 elimAllVarsM
  签名: : LinarithM Unit
  定义体: do
  for i in (List.range ((← getMaxVar) + 1)).reverse do
    elimVarM i
-/
def elimAllVarsM : LinarithM Unit := do
  for i in (List.range ((← getMaxVar) + 1)).reverse do
    elimVarM i

/--
Definition of `mkLinarithData` / `mkLinarithData` 的定义

English:
definition mkLinarithData
  signature: (hyps : List Comp) (maxVar : Nat)
  body: ⟨maxVar, .ofList (hyps.mapIdx fun n cmp => PComp.assump cmp n) _⟩

中文:
定义 mkLinarithData
  签名: (hyps : List Comp) (maxVar : 自然数)
  定义体: ⟨maxVar, .ofList (hyps.mapIdx fun n cmp => PComp.assump cmp n) _⟩

Depends on / 依赖: PComp.assump, assump, hyps.mapIdx, mapIdx, maxVar, ofList
-/
def mkLinarithData (hyps : List Comp) (maxVar : Nat) : LinarithData :=
  ⟨maxVar, .ofList (hyps.mapIdx fun n cmp => PComp.assump cmp n) _⟩

/--
Definition of `CertificateOracle.fourierMotzkin` / `CertificateOracle.fourierMotzkin` 的定义

English:
definition CertificateOracle.fourierMotzkin
  signature: : CertificateOracle where
  body: do
    let linarithData := mkLinarithData hyps maxVar
    let result ←
      (ExceptT.run (StateT.run (do validate; elimAllVarsM : LinarithM Unit) linarithData) :)
    match result with
    | (Except.ok _) => failure
    | (Except.error contr) => return contr.src.flatten

中文:
定义 CertificateOracle.fourierMotzkin
  签名: : CertificateOracle where
  定义体: do
    let linarithData := mkLinarithData hyps maxVar
    let result ←
      (ExceptT.run (StateT.run (do validate; elimAllVarsM : LinarithM Unit) linarithData) :)
    match result with
    | (Except.ok _) => failure
    | (Except.error contr) => return contr.src.flatten
-/
def CertificateOracle.fourierMotzkin : CertificateOracle where
  produceCertificate hyps maxVar := do
    let linarithData := mkLinarithData hyps maxVar
    let result ←
      (ExceptT.run (StateT.run (do validate; elimAllVarsM : LinarithM Unit) linarithData) :)
    match result with
    | (Except.ok _) => failure
    | (Except.error contr) => return contr.src.flatten

end Mathlib.Tactic.Linarith
