/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
module

public import Mathlib.Util.AtomM

/-!
# Running `AtomM` metaprograms recursively

Tactics such as `ring` and `abel` are implemented using the `AtomM` monad, which tracks "atoms" --
expressions which cannot be further parsed according to the arithmetic operations they handle --
to allow for consistent normalization relative to these atoms.

This file provides methods to allow for such normalization to run recursively: the atoms themselves
will have the normalization run on any of their subterms for which this makes sense. For example,
given an implementation of ring-normalization, the methods in this file implement the bottom-to-top
recursive ring-normalization in which `sin (x + y) + sin (y + x)` is normalized first to
`sin (x + y) + sin (x + y)` and then to `2 * sin (x + y)`.

## Main declarations

* `Mathlib.Tactic.AtomM.RecurseM.run`: run a metaprogram (in `AtomM` or its slight extension
  `AtomM.RecurseM`), with atoms normalized according to a provided normalization operation (in
  `AtomM`), run recursively.

* `Mathlib.Tactic.AtomM.recurse`: run a normalization operation (in `AtomM`) recursively on an
  expression.

-/

public meta section

namespace Mathlib.Tactic.AtomM
open Lean Meta

/--
Definition of `Recurse.Config` / `Recurse.Config` 的定义

English:
structure Recurse.Config
  parameters: where
  axioms and operations (3):
    - red : = TransparencyMode.reducible
    - zetaDelta : = false
    - contextual : = false

中文:
结构 Recurse.余nfig
  参数: where
  公理与运算 (3 个):
    - red : = TransparencyMode.reducible
    - zetaDelta : = false
    - contextual : = false

Depends on / 依赖: TransparencyMode, TransparencyMode.reducible, reducible
-/
structure Recurse.Config where
  /-- the reducibility setting to use when comparing atoms for defeq -/
  red := TransparencyMode.reducible
  /-- if true, local let variables can be unfolded -/
  zetaDelta := false
  /-- if true, implication hypotheses are added to the local context of the discharger -/
  contextual := false
deriving Inhabited, BEq, Repr

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] Mathlib.Tactic.AtomM.Recurse.instReprConfig.repr

/--
Definition of `Recurse.Context` / `Recurse.Context` 的定义

English:
structure Recurse.Context
  parameters: where
  axioms and operations (2):
    - ctx : Simp.Context
    - simp : Simp.Result -> MetaM Simp.Result

中文:
结构 Recurse.余ntext
  参数: where
  公理与运算 (2 个):
    - ctx : Simp.余ntext
    - simp : Simp.Result -> MetaM Simp.Result
-/
structure Recurse.Context where
  /-- A basically empty simp context, passed to the `simp` traversal in `AtomM.onSubexpressions`.
  -/
  ctx : Simp.Context
  /-- A cleanup routine, which simplifies evaluation results to a more human-friendly format. -/
  simp : Simp.Result -> MetaM Simp.Result

/--
Definition of `RecurseM` / `RecurseM` 的定义

English:
abbreviation RecurseM
  body: ReaderT Recurse.Context AtomM

中文:
缩写 RecurseM
  定义体: ReaderT Recurse.Context AtomM

Depends on / 依赖: Context, ReaderT, Recurse, Recurse.Context
-/
abbrev RecurseM := ReaderT Recurse.Context AtomM

/--
Definition of `onSubexpressions` / `onSubexpressions` 的定义

English:
definition onSubexpressions
  signature: (eval : Expr -> AtomM Simp.Result) (parent : Expr)
  body: fun nctx rctx s => do
    let pre : Simp.Simproc := fun e =>
      try
guard root || parent != e-- recursion guard
        let r' ← eval e rctx s
        let r ← nctx.simp r'
if ← withReducible isDefEq r.expr e then return .done { expr := r.expr }
        pure (.done r)
catch _ => pure .continue
    let post := Simp.postDefault #[]
(·.1) < > Simp.main parent nctx.ctx (methods := { pre, post, wellBehavedDischarge })

中文:
定义 onSubexpressions
  签名: (eval : Expr -> AtomM Simp.Result) (parent : Expr)
  定义体: fun nctx rctx s => do
    let pre : Simp.Simproc := fun e =>
      try
guard root || parent != e-- recursion guard
        let r' ← eval e rctx s
        let r ← nctx.simp r'
if ← withReducible isDefEq r.expr e then return .done { expr := r.expr }
        pure (.done r)
catch _ => pure .continue
    let post := Simp.postDefault #[]
(·.1) < > Simp.main parent nctx.ctx (methods := { pre, post, wellBehavedDischarge })
-/
def onSubexpressions (eval : Expr -> AtomM Simp.Result) (parent : Expr)
    (wellBehavedDischarge : Bool) (root := true) :
    RecurseM Simp.Result :=
  fun nctx rctx s => do
    let pre : Simp.Simproc := fun e =>
      try
guard root || parent != e-- recursion guard
        let r' ← eval e rctx s
        let r ← nctx.simp r'
if ← withReducible isDefEq r.expr e then return .done { expr := r.expr }
        pure (.done r)
catch _ => pure .continue
    let post := Simp.postDefault #[]
(·.1) < > Simp.main parent nctx.ctx (methods := { pre, post, wellBehavedDischarge })

/--
Definition of `RecurseM.run` / `RecurseM.run` 的定义

English:
definition RecurseM.run
  body: do
  let ctx ← Simp.mkContext
    { zetaDelta := cfg.zetaDelta, singlePass := true, contextual := cfg.contextual }
    (simpTheorems := #[← Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}])
    (congrTheorems := ← getSimpCongrTheorems)
  let nctx := { ctx, simp }
  let rec
    /-- The recursive context. -/
    rctx := { red := cfg.red, evalAtom },
    /-- The atom evaluator calls `AtomM.onSubexpressions` recursively. -/
    evalAtom e := onSubexpressions eval e wellBehavedDischarge false nctx rctx s
withConfig ({ · with zetaDelta := cfg.zetaDelta }) x nctx rctx s

中文:
定义 RecurseM.run
  定义体: do
  let ctx ← Simp.mkContext
    { zetaDelta := cfg.zetaDelta, singlePass := true, contextual := cfg.contextual }
    (simpTheorems := #[← Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}])
    (congrTheorems := ← getSimpCongrTheorems)
  let nctx := { ctx, simp }
  let rec
    /-- The recursive context. -/
    rctx := { red := cfg.red, evalAtom },
    /-- The atom evaluator calls `AtomM.onSubexpressions` recursively. -/
    evalAtom e := onSubexpressions eval e wellBehavedDischarge false nctx rctx s
withConfig ({ · with zetaDelta := cfg.zetaDelta }) x nctx rctx s
-/
partial def RecurseM.run
    {α : Type} (s : IO.Ref State) (cfg : Recurse.Config) (wellBehavedDischarge : Bool)
    (eval : Expr -> AtomM Simp.Result) (simp : Simp.Result -> MetaM Simp.Result) (x : RecurseM α) :
    MetaM α := do
  let ctx ← Simp.mkContext
    { zetaDelta := cfg.zetaDelta, singlePass := true, contextual := cfg.contextual }
    (simpTheorems := #[← Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}])
    (congrTheorems := ← getSimpCongrTheorems)
  let nctx := { ctx, simp }
  let rec
    /-- The recursive context. -/
    rctx := { red := cfg.red, evalAtom },
    /-- The atom evaluator calls `AtomM.onSubexpressions` recursively. -/
    evalAtom e := onSubexpressions eval e wellBehavedDischarge false nctx rctx s
withConfig ({ · with zetaDelta := cfg.zetaDelta }) x nctx rctx s

/--
Definition of `recurse` / `recurse` 的定义

English:
definition recurse
  signature: (s : IO.Ref State) (cfg : Recurse.Config) (wellBehavedDischarge : Bool)
  body: do
  RecurseM.run s cfg wellBehavedDischarge eval simp
 onSubexpressions eval tgt wellBehavedDischarge

中文:
定义 recurse
  签名: (s : IO.Ref State) (cfg : Recurse.余nfig) (wellBehavedDischarge : 布尔值)
  定义体: do
  RecurseM.run s cfg wellBehavedDischarge eval simp
 onSubexpressions eval tgt wellBehavedDischarge
-/
def recurse (s : IO.Ref State) (cfg : Recurse.Config) (wellBehavedDischarge : Bool)
    (eval : Expr -> AtomM Simp.Result)
    (simp : Simp.Result -> MetaM Simp.Result) (tgt : Expr) :
    MetaM Simp.Result := do
  RecurseM.run s cfg wellBehavedDischarge eval simp
 onSubexpressions eval tgt wellBehavedDischarge

end Mathlib.Tactic.AtomM
