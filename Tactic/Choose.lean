/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Mario Carneiro, Reid Barton, Johan Commelin
-/
module

public import Mathlib.Logic.Function.Basic

/-!
# `choose` tactic

Performs Skolemization, that is, given `h : ∀ a:α, ∃ b:β, p a b |- G` produces
`f : α → β, hf: ∀ a, p a (f a) |- G`.

TODO: switch to `rcases` syntax: `choose ⟨i, j, h₁ -⟩ := expr`.
-/

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.Choose

/--
Definition of `mkSometimes` / `mkSometimes` 的定义

English:
definition mkSometimes
  signature: (u : Level) (α nonemp p : Expr)
  body: mkSometimes

中文:
定义 mkSometimes
  签名: (u : Level) (α nonemp p : Expr)
  定义体: mkSometimes
-/
def mkSometimes (u : Level) (α nonemp p : Expr) :
    List Expr -> Expr × Expr -> MetaM (Expr × Expr)
| [], (val, spec) => pure (val, spec)
| (e :: ctx), (val, spec) => do
  let (val, spec) ← mkSometimes u α nonemp p ctx (val, spec)
  let t ← inferType e
  let b ← isProp t
  if b then do
    let val' ← mkLambdaFVars #[e] val
    pure
      (mkApp4 (Expr.const ``Function.sometimes [Level.zero, u]) t α nonemp val',
      mkApp7 (Expr.const ``Function.sometimes_spec [u]) t α nonemp p val' e spec)
  else pure (val, spec)

@[deprecated (since := "2026-05-27")] alias mk_sometimes := mkSometimes

/--
Inductive type `ElimStatus` / 归纳类型 `ElimStatus`

English:
inductive ElimStatus
  constructors (2):
    - success: 
    - failure: (ts : List Expr)

中文:
归纳类型 ElimStatus
  构造子 (2 个):
    - success: 
    - failure: (ts : List Expr)
-/
inductive ElimStatus
  | success
  | failure (ts : List Expr)

/--
Definition of `ElimStatus.merge` / `ElimStatus.merge` 的定义

English:
definition ElimStatus.merge
  signature: : ElimStatus -> ElimStatus -> ElimStatus

中文:
定义 ElimStatus.merge
  签名: : ElimStatus -> ElimStatus -> ElimStatus
-/
def ElimStatus.merge : ElimStatus -> ElimStatus -> ElimStatus
  | success, _ => success
  | _, success => success
  | failure ts₁, failure ts₂ => failure (ts₁ ++ ts₂)

/--
Definition of `mkFreshNameFrom` / `mkFreshNameFrom` 的定义

English:
definition mkFreshNameFrom
  signature: (orig base : Name)
  body: if orig = `_ then mkFreshUserName base else pure orig

中文:
定义 mkFreshNameFrom
  签名: (orig base : Name)
  定义体: if orig = `_ then mkFreshUserName base else pure orig

Depends on / 依赖: mkFreshUserName
-/
def mkFreshNameFrom (orig base : Name) : CoreM Name :=
  if orig = `_ then mkFreshUserName base else pure orig

/--
Definition of `ChooseArg` / `ChooseArg` 的定义

English:
structure ChooseArg
  parameters: where
  axioms and operations (3):
    - ref : Syntax
    - name : Name
    - expectedType? : Option Term

中文:
结构 ChooseArg
  参数: where
  公理与运算 (3 个):
    - ref : Syntax
    - name : Name
    - expectedType? : Option Term

Depends on / 依赖: Batteries, Batteries.ExtendedBinder.extBinderParenthesized, ExtendedBinder, binderIdent, extBinderParenthesized
-/
structure ChooseArg where
  /-- The syntax reference for the identifier (for hover info) -/
  ref : Syntax
  /-- The name to use for the introduced variable -/
  name : Name
  /-- Optional expected type annotation -/
  expectedType? : Option Term
  deriving Inhabited

/-- A `choose` argument is either a bare identifier or a parenthesized extended binder -/
syntax chooseBinder := binderIdent > Batteries.ExtendedBinder.extBinderParenthesized

open Batteries.ExtendedBinder in
/--
Definition of `parseChooseArg` / `parseChooseArg` 的定义

English:
definition parseChooseArg
  signature: (stx : TSyntax ``chooseBinder)
  body: do
  match stx with
  | `(chooseBinder| $id:binderIdent) => return parseBinderIdent id
  | `(chooseBinder| ($id:binderIdent : $ty:term)) =>
    return { parseBinderIdent id with expectedType? := some ty }
  | `(chooseBinder| ($_id:binderIdent $bp:binderPred)) =>
    throwErrorAt bp "binder predicate

中文:
定义 parseChooseArg
  签名: (stx : TSyntax ``chooseBinder)
  定义体: do
  match stx with
  | `(chooseBinder| $id:binderIdent) => return parseBinderIdent id
  | `(chooseBinder| ($id:binderIdent : $ty:term)) =>
    return { parseBinderIdent id with expectedType? := some ty }
  | `(chooseBinder| ($_id:binderIdent $bp:binderPred)) =>
    throwErrorAt bp "binder predicate
-/
def parseChooseArg (stx : TSyntax ``chooseBinder) : MetaM ChooseArg := do
  match stx with
  | `(chooseBinder| $id:binderIdent) => return parseBinderIdent id
  | `(chooseBinder| ($id:binderIdent : $ty:term)) =>
    return { parseBinderIdent id with expectedType? := some ty }
  | `(chooseBinder| ($_id:binderIdent $bp:binderPred)) =>
    throwErrorAt bp "binder predicates like '< n' are not supported by choose; \
      use a type annotation like '(h : x < n)' instead"
  | _ => return ⟨stx, `_, none⟩
where
  parseBinderIdent (id : TSyntax ``Lean.binderIdent) : ChooseArg :=
    match id with
    | `(binderIdent| $h:ident) => ⟨h, h.getId, none⟩
    | _ => ⟨id, `_, none⟩

/--
Definition of `choose1` / `choose1` 的定义

English:
definition choose1
  signature: (g : MVarId) (nondep : Bool) (h : Option Expr) (data : Name)
  body: do
  let (g, h) ← match h with
  | some e => pure (g, e)
  | none => do
    let (e, g) ← g.intro1P
    pure (g, .fvar e)
  g.withContext do
    let h ← instantiateMVars h
    let t ← inferType h
    forallTelescopeReducing t fun ctx t => do
      (← withTransparency .all (whnf t)).withApp fun
      

中文:
定义 choose1
  签名: (g : MVarId) (nondep : 布尔) (h : Option Expr) (data : Name)
  定义体: do
  let (g, h) ← match h with
  | some e => pure (g, e)
  | none => do
    let (e, g) ← g.intro1P
    pure (g, .fvar e)
  g.withContext do
    let h ← instantiateMVars h
    let t ← inferType h
    forallTelescopeReducing t fun ctx t => do
      (← withTransparency .all (whnf t)).withApp fun
      
-/
def choose1 (g : MVarId) (nondep : Bool) (h : Option Expr) (data : Name) :
    MetaM (ElimStatus × Expr × MVarId) := do
  let (g, h) ← match h with
  | some e => pure (g, e)
  | none => do
    let (e, g) ← g.intro1P
    pure (g, .fvar e)
  g.withContext do
    let h ← instantiateMVars h
    let t ← inferType h
    forallTelescopeReducing t fun ctx t => do
      (← withTransparency .all (whnf t)).withApp fun
      | .const ``Exists [u], #[α, p] => do
        let data ← mkFreshNameFrom data ((← p.getBinderName).getD `h)
        let ((neFail : ElimStatus), (nonemp : Option Expr)) ← if nondep then
          let ne := (Expr.const ``Nonempty [u]).app α
          let m ← mkFreshExprMVar ne
          let mut g' := m.mvarId!
          for e in ctx do
            if (← isProof e) then continue
            let ty ← whnf (← inferType e)
            let nety := (Expr.const ``Nonempty [u]).app ty
            let neval := mkApp2 (Expr.const ``Nonempty.intro [u]) ty e
            g' ← g'.assert .anonymous nety neval
          (_, g') ← g'.intros
          g'.withContext do
            match ← synthInstance? (← g'.getType) with
            | some e => do
              g'.assign e
              let m ← instantiateMVars m
              pure (.success, some m)
            | none => pure (.failure [ne], none)
        else pure (.failure [], none)
        let ctx' ← if nonemp.isSome then ctx.filterM (not <$> isProof ·) else pure ctx
        let dataTy ← mkForallFVars ctx' α
        let mut dataVal := mkApp3 (.const ``Classical.choose [u]) α p (mkAppN h ctx)
        let mut specVal := mkApp3 (.const ``Classical.choose_spec [u]) α p (mkAppN h ctx)
        if let some nonemp := nonemp then
          (dataVal, specVal) ← mkSometimes u α nonemp p ctx.toList (dataVal, specVal)
        dataVal ← mkLambdaFVars ctx' dataVal
        specVal ← mkLambdaFVars ctx specVal
        let (fvar, g) ← withLocalDeclD .anonymous dataTy fun d => do
          let specTy ← mkForallFVars ctx (p.app (mkAppN d ctx')).headBeta
g.withContext withLocalDeclD data dataTy fun d' => do
            let mvarTy ← mkArrow (specTy.replaceFVar d d') (← g.getType)
            let newMVar ← mkFreshExprSyntheticOpaqueMVar mvarTy (← g.getTag)
g.assign mkApp2 (← mkLambdaFVars #[d'] newMVar) dataVal specVal
            pure (d', newMVar.mvarId!)
        let g ← match h with
        | .fvar v => g.clear v
        | _ => pure g
        return (neFail, fvar, g)
      | .const ``And _, #[p, q] => do
        let data ← mkFreshNameFrom data `h
let e1 ← mkLambdaFVars ctx mkApp3 (.const ``And.left []) p q (mkAppN h ctx)
let e2 ← mkLambdaFVars ctx mkApp3 (.const ``And.right []) p q (mkAppN h ctx)
        let t1 ← inferType e1
        let t2 ← inferType e2
        let (fvar, g) ← (← (← g.assert .anonymous t2 e2).assert data t1 e1).intro1P
        let g ← match h with
        | .fvar v => g.clear v
        | _ => pure g
        return (.success, .fvar fvar, g)
      -- TODO: support Σ, ×, or even any inductive type with 1 constructor ?
      | _, _ => throwError "expected a term of the shape `forall xs, exists a, p xs a` or `forall xs, p xs ∧ q xs`"

/--
Definition of `choose1WithInfo` / `choose1WithInfo` 的定义

English:
definition choose1WithInfo
  signature: (g : MVarId) (nondep : Bool) (h : Option Expr) (arg : ChooseArg)
  body: do
  let (status, fvar, g) ← choose1 g nondep h arg.name
  let g ← g.withContext do
    Term.addLocalVarInfo arg.ref fvar
    -- Check type annotation if provided, and use the user-specified type
    if let some expectedTypeStx := arg.expectedType? then
      let actualType ← inferType fvar
      le

中文:
定义 choose1WithInfo
  签名: (g : MVarId) (nondep : 布尔) (h : Option Expr) (arg : ChooseArg)
  定义体: do
  let (status, fvar, g) ← choose1 g nondep h arg.name
  let g ← g.withContext do
    Term.addLocalVarInfo arg.ref fvar
    -- Check type annotation if provided, and use the user-specified type
    if let some expectedTypeStx := arg.expectedType? then
      let actualType ← inferType fvar
      le
-/
def choose1WithInfo (g : MVarId) (nondep : Bool) (h : Option Expr) (arg : ChooseArg) :
    TermElabM (ElimStatus × MVarId) := do
  let (status, fvar, g) ← choose1 g nondep h arg.name
  let g ← g.withContext do
    Term.addLocalVarInfo arg.ref fvar
    -- Check type annotation if provided, and use the user-specified type
    if let some expectedTypeStx := arg.expectedType? then
      let actualType ← inferType fvar
      let expectedType ← Term.elabType expectedTypeStx
      unless ← isDefEq actualType expectedType do
        throwErrorAt arg.ref m!"type mismatch for '{arg.name}'\n\
          {← mkHasTypeButIsExpectedMsg actualType expectedType}"
      -- Change the local declaration to use the user-specified type
      return ← g.changeLocalDecl fvar.fvarId! expectedType
    return g
  pure (status, g)

/--
Definition of `elabChoose` / `elabChoose` 的定义

English:
definition elabChoose
  signature: (nondep : Bool) (h : Option Expr)
  body: m!"choose!: failed to synthesize any nonempty instances"
      for ty in tys do
        msg := msg ++ m!"{(← mkFreshExprMVar ty).mvarId!}"
      throwError msg
    | _, _ => do
      let (fvar, g) ← if arg.name == `_ then g.intro1 else g.intro arg.name
      g.withContext do
        Term.addLocalVar

中文:
定义 elabChoose
  签名: (nondep : 布尔) (h : Option Expr)
  定义体: m!"choose!: failed to synthesize any nonempty instances"
      for ty in tys do
        msg := msg ++ m!"{(← mkFreshExprMVar ty).mvarId!}"
      throwError msg
    | _, _ => do
      let (fvar, g) ← if arg.name == `_ then g.intro1 else g.intro arg.name
      g.withContext do
        Term.addLocalVar

Depends on / 依赖: failed, instances, nonempty, synthesize
-/
def elabChoose (nondep : Bool) (h : Option Expr) :
    List ChooseArg -> ElimStatus -> MVarId -> TermElabM MVarId
  | [], _, _ => throwError "expect list of variables"
  | [arg], status, g =>
    match nondep, status with
    | true, .failure tys => do -- We expected some elimination, but it didn't happen.
      let mut msg := m!"choose!: failed to synthesize any nonempty instances"
      for ty in tys do
        msg := msg ++ m!"{(← mkFreshExprMVar ty).mvarId!}"
      throwError msg
    | _, _ => do
      let (fvar, g) ← if arg.name == `_ then g.intro1 else g.intro arg.name
      g.withContext do
        Term.addLocalVarInfo arg.ref (.fvar fvar)
        -- Check type annotation if provided, and use the user-specified type
        if let some expectedTypeStx := arg.expectedType? then
          let actualType ← inferType (.fvar fvar)
          let expectedType ← Term.elabType expectedTypeStx
          unless ← isDefEq actualType expectedType do
            throwErrorAt arg.ref m!"type mismatch for '{arg.name}'\n\
              {← mkHasTypeButIsExpectedMsg actualType expectedType}"
          -- Change the local declaration to use the user-specified type
          return ← g.changeLocalDecl fvar expectedType
        return g
  | arg::args, status, g => do
    let (status', g) ← choose1WithInfo g nondep h arg
    elabChoose nondep none args (status.merge status') g

/--
* `choose a b h h' using hyp` takes a hypothesis `hyp` of the form
  `∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b`
  for some `P Q : X → Y → A → B → Prop` and outputs
  into context a function `a : X → Y → A`, `b : X → Y → B` and two assumptions:
  `h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`. It also works with dependent versions.

* `choose! a b h h' using hyp` does the same, except that it will remove dependency of
  the functions on propositional arguments if possible. For example if `Y` is a proposition
  and `A` and `B` are nonempty in the above example then we will instead get
  `a : X → A`, `b : X → B`, and the assumptions
  `h : ∀ (x : X) (y : Y), P x y (a x) (b x)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x) (b x)`.

The `using hyp` part can be omitted,
which will effectively cause `choose` to start with an `intro hyp`.

Like `intro`, the `choose` tactic supports type annotations to specify the expected type
of the introduced variables. This is useful for documentation and for catching mistakes early:
```
example (h : ∃ n : ℕ, n > 0) : True := by
  choose (n : ℕ) (hn : n > 0) using h
  trivial
```
If the provided type does not match the actual type, an error is raised.

Examples:

```
example (h : ∀ n m : ℕ, ∃ i j, m = n + i ∨ m + j = n) : True := by
  choose i j h using h
  guard_hyp i : ℕ → ℕ → ℕ
  guard_hyp j : ℕ → ℕ → ℕ
  guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n
  trivial
```

```
example (h : ∀ i : ℕ, i < 7 → ∃ j, i < j ∧ j < i+i) : True := by
  choose! f h h' using h
  guard_hyp f : ℕ → ℕ
  guard_hyp h : ∀ (i : ℕ), i < 7 → i < f i
  guard_hyp h' : ∀ (i : ℕ), i < 7 → f i < i + i
  trivial
```
-/
syntax (name := choose) "choose" "!"? (ppSpace colGt chooseBinder)+ (" using " term)? : tactic

elab_rules : tactic
| `(tactic| choose $[!%$b]? $[$ids:chooseBinder]* $[using $h]?) => withMainContext do
  let h ← h.mapM (Elab.Tactic.elabTerm · none)
  let args ← ids.toList.mapM (liftM <| parseChooseArg ·)
  Term.withoutErrToSorry do
    let g ← elabChoose b.isSome h args (.failure []) (← getMainGoal)
    replaceMainGoal [g]

@[tactic_alt choose]
syntax "choose!" (ppSpace colGt chooseBinder)+ (" using " term)? : tactic

macro_rules
  | `(tactic| choose! $[$ids:chooseBinder]* $[using $h]?) =>
    `(tactic| choose ! $[$ids]* $[using $h]?)

end Mathlib.Tactic.Choose
