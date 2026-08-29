/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Wojciech Nawrocki
-/
module

public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.Tactic.Conv.Basic
public meta import Lean.Elab.Tactic.Rewrite
public import Mathlib.Init
public import Lean.Elab.ConfigEval

/-! ## Dependent rewrite tactic -/

public meta section

namespace Mathlib.Tactic.DepRewrite
open Lean Meta

/--
theorem `dcongrArg.` / 定理 `dcongrArg.`

English:
theorem dcongrArg.{u,
  given: v} {α
  statement: Sort u} {a a' : α} {β : (a' : α) -> a = a' -> Sort v}
  proof: by
  cases h; rfl

中文:
定理 dcongrArg.{u,
  条件: v} {α
  结论: Sort u} {a a' : α} {β : (a' : α) -> a = a' -> Sort v}
  证明: by
  cases h; rfl

Depends on / 依赖: h.symm, h.trans
-/
theorem dcongrArg.{u, v} {α : Sort u} {a a' : α} {β : (a' : α) -> a = a' -> Sort v}
    (h : a = a') (f : (a' : α) -> (h : a = a') -> β a' h) :
    f a rfl = Eq.rec (motive := fun x h' => β x (h.trans h')) (f a' h) h.symm := by
  cases h; rfl

/--
theorem `hdcongrArg.` / 定理 `hdcongrArg.`

English:
theorem hdcongrArg.{u,
  given: v} {α
  statement: Sort u} {a a' : α} {β : (a' : α) -> a = a' -> Sort v}
  proof: by
  cases h; rfl

中文:
定理 hdcongrArg.{u,
  条件: v} {α
  结论: Sort u} {a a' : α} {β : (a' : α) -> a = a' -> Sort v}
  证明: by
  cases h; rfl
-/
theorem hdcongrArg.{u, v} {α : Sort u} {a a' : α} {β : (a' : α) -> a = a' -> Sort v}
    (h : a = a') (f : (a' : α) -> (h : a = a') -> β a' h) :
    f a rfl ≍ f a' h := by
  cases h; rfl

/--
theorem `eq_of_heq.` / 定理 `eq_of_heq.`

English:
theorem eq_of_heq.{u}
  given: {α : Sort u} {a a' : α} (h : a ≍ a')
  statement: a = a'
  proof: by
  cases h; rfl

中文:
定理 eq_of_heq.{u}
  条件: {α : Sort u} {a a' : α} (h : a ≍ a')
  结论: a = a'
  证明: by
  cases h; rfl
-/
theorem eq_of_heq.{u} {α : Sort u} {a a' : α} (h : a ≍ a') : a = a' := by
  cases h; rfl

/--
theorem `heqL.` / 定理 `heqL.`

English:
theorem heqL.{u}
  given: {α β : Sort u} {a : α} {b : β} (h : HEq a b)
  proof: by
  cases h; rfl

中文:
定理 heqL.{u}
  条件: {α β : Sort u} {a : α} {b : β} (h : HEq a b)
  证明: by
  cases h; rfl
-/
theorem heqL.{u} {α β : Sort u} {a : α} {b : β} (h : HEq a b) :
    a = cast (type_eq_of_heq h).symm b := by
  cases h; rfl

/--
theorem `heqR.` / 定理 `heqR.`

English:
theorem heqR.{u}
  given: {α β : Sort u} {a : α} {b : β} (h : HEq a b)
  proof: by
  cases h; rfl

中文:
定理 heqR.{u}
  条件: {α β : Sort u} {a : α} {b : β} (h : HEq a b)
  证明: by
  cases h; rfl
-/
theorem heqR.{u} {α β : Sort u} {a : α} {b : β} (h : HEq a b) :
    cast (type_eq_of_heq h) a = b := by
  cases h; rfl

/--
Definition of `traceCls` / `traceCls` 的定义

English:
definition traceCls
  signature: : Name
  body: `Tactic.depRewrite

中文:
定义 traceCls
  签名: : Name
  定义体: `Tactic.depRewrite
-/
private def traceCls : Name := `Tactic.depRewrite
/--
Definition of `traceClsVisit` / `traceClsVisit` 的定义

English:
definition traceClsVisit
  signature: : Name
  body: `Tactic.depRewrite.visit

中文:
定义 traceClsVisit
  签名: : Name
  定义体: `Tactic.depRewrite.visit
-/
private def traceClsVisit : Name := `Tactic.depRewrite.visit
/--
Definition of `traceClsCast` / `traceClsCast` 的定义

English:
definition traceClsCast
  signature: : Name
  body: `Tactic.depRewrite.cast

中文:
定义 traceClsCast
  签名: : Name
  定义体: `Tactic.depRewrite.cast
-/
private def traceClsCast : Name := `Tactic.depRewrite.cast
/--
Definition of `traceClsClean` / `traceClsClean` 的定义

English:
definition traceClsClean
  signature: : Name
  body: `Tactic.depRewrite.cleanupCasts

中文:
定义 traceClsClean
  签名: : Name
  定义体: `Tactic.depRewrite.cleanupCasts
-/
private def traceClsClean : Name := `Tactic.depRewrite.cleanupCasts

initialize
  registerTraceClass traceCls
  registerTraceClass traceClsVisit
  registerTraceClass traceClsCast
  registerTraceClass traceClsClean

/--
Inductive type `CastMode` / 归纳类型 `CastMode`

English:
inductive CastMode
  parameters: where
  constructors (2):
    - proofs: 
    - all: 

中文:
归纳类型 CastMode
  参数: where
  构造子 (2 个):
    - proofs: 
    - all: 
-/
inductive CastMode where
  /-- Only insert casts on proofs.

  In this mode, it is *not* permitted to cast subterms of proofs that are not themselves proofs. -/
  -- TODO: should we relax this restriction and switch `castMode` when visiting a proof?
  | proofs
  /- TODO: `proofs` plus "good" user-defined casts such as `Fin.cast`.
  See https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/dependent.20rewrite.20tactic/near/497185687 -/
  -- | userDef
  /-- Insert casts whenever necessary. -/
  | all
deriving BEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString CastMode
  body: ⟨fun
  | .proofs => "proofs"
  | .all => "all"⟩

中文:
实例 :
  签名: ToString CastMode
  定义体: ⟨fun
  | .proofs => "proofs"
  | .all => "all"⟩
-/
instance : ToString CastMode := ⟨fun
  | .proofs => "proofs"
  | .all => "all"⟩

/--
Definition of `CastMode.toNat` / `CastMode.toNat` 的定义

English:
definition CastMode.toNat
  signature: : CastMode -> Nat

中文:
定义 CastMode.toNat
  签名: : CastMode -> 自然数
-/
def CastMode.toNat : CastMode -> Nat
  | .proofs => 0
  | .all => 1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE CastMode
  body: a.toNat <= b.toNat

中文:
实例 :
  签名: LE CastMode
  定义体: a.toNat <= b.toNat

Depends on / 依赖: a.toNat, b.toNat
-/
instance : LE CastMode where
  le a b := a.toNat <= b.toNat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableLE CastMode
  body: fun a b => inferInstanceAs (Decidable (a.toNat <= b.toNat))

中文:
实例 :
  签名: DecidableLE CastMode
  定义体: fun a b => inferInstanceAs (Decidable (a.toNat <= b.toNat))

Depends on / 依赖: Decidable, a.toNat, b.toNat
-/
instance : DecidableLE CastMode :=
  fun a b => inferInstanceAs (Decidable (a.toNat <= b.toNat))

/--
Definition of `Config` / `Config` 的定义

English:
structure Config
  parameters: where
  axioms and operations (4):
    - transparency : TransparencyMode  [default: .reducible]
    - occs : Occurrences  [default: .all]
    - castMode : CastMode  [default: .proofs]
    - castTransparency : TransparencyMode  [default: .default]

中文:
结构 Config
  参数: where
  公理与运算 (4 个):
    - transparency : TransparencyMode  [默认: .reducible]
    - occs : Occurrences  [默认: .all]
    - castMode : CastMode  [默认: .proofs]
    - castTransparency : TransparencyMode  [默认: .default]

Depends on / 依赖: reducible
-/
structure Config where
  /-- Which transparency level to use when unifying the rewrite rule's LHS
  against subterms of the term being rewritten. -/
  transparency : TransparencyMode := .reducible
  /-- Which occurrences to rewrite. -/
  occs : Occurrences := .all
  /-- The cast mode specifies when `rewrite!` is permitted to insert casts
  in order to correct subterms that become type-incorrect
  as a result of rewriting.

  For example, given `P : Nat → Prop`, `f : (n : Nat) → P n → Nat` and `h : P n₀`,
  rewriting `f n₀ h` by `eq : n₀ = n₁` produces `f n₁ h`,
  where `h` does not typecheck at `P n₁`.
  The tactic will cast `h` to `eq ▸ h : P n₁` iff `.proofs ≤ castMode`. -/
  castMode : CastMode := .proofs
  /-- Which transparency level to use when cleaning up casts to decide if a cast is a refl-cast. -/
  castTransparency : TransparencyMode := .default

/--
Definition of `Context` / `Context` 的定义

English:
structure Context
  parameters: where
  axioms and operations (8):
    - cfg : DepRewrite.Config
    - p : Expr
    - x : Expr
    - h : Expr
    - Δ : Array (FVarId × Expr)
    - δ : Std.HashSet FVarId
    - pHeadIdx : HeadIndex  [default: p.toHeadIndex]
    - pNumArgs : Nat  [default: p.headNumArgs]

中文:
结构 Context
  参数: where
  公理与运算 (8 个):
    - cfg : DepRewrite.Config
    - p : Expr
    - x : Expr
    - h : Expr
    - Δ : Array (FVarId × Expr)
    - δ : Std.HashSet FVarId
    - pHeadIdx : HeadIndex  [默认: p.toHeadIndex]
    - pNumArgs : 自然数  [默认: p.headNumArgs]
-/
structure Context where
  /-- Configuration. -/
  cfg : DepRewrite.Config
  /-- The pattern to generalize over. -/
  p : Expr
  /-- The free variable to substitute for `p`. -/
  x : Expr
  /-- A proof of `p = x`. Must be an fvar. -/
  h : Expr
  /-- The list of *value-less* binders (`cdecl`s and nondependent `ldecl`s)
  that we have introduced.
  Together with each binder, we store its type abstracted over `x` and `h`,
  and with all occurrences of previous entries in `Δ`
  casted along the abstracting equation.

  E.g., if the local context is `a : T, b : U`,
  we store `(a, Ma)` where `Ma := fun (x' : α) (h' : x = x') => T[x'/x, h'/h]`
  and `(b, fun (x' : α) (h' : x = x') => U[x'/x, h'/h, (Eq.rec (motive := Ma) a h)/a])`
  See the docstring on `visitAndCast`. -/
  Δ : Array (FVarId × Expr)
  /-- The set of all *dependent* `ldecl`s that we have introduced. -/
  δ : Std.HashSet FVarId
  -- TODO: use `@[computed_field]`s below when `structure` supports that
  /-- Cached `p.toHeadIndex`. -/
  pHeadIdx : HeadIndex := p.toHeadIndex
  /-- Cached `p.toNumArgs`. -/
  pNumArgs : Nat := p.headNumArgs

/--
Definition of `canUseCache` / `canUseCache` 的定义

English:
definition canUseCache
  signature: (cacheOcc dCacheOcc currOcc : Nat)
  body: #[]
    let mut currOccs := #[]
    for p in l.toArray.qsort do
      if cacheOcc <= p && p < cacheOcc + dCacheOcc then
        prevOccs := prevOccs.push (p - cacheOcc)
      if currOcc <= p && p < currOcc + dCacheOcc then
        currOccs := currOccs.push (p - currOcc)
    return prevOccs == currOc

中文:
定义 canUseCache
  签名: (cacheOcc dCacheOcc currOcc : 自然数)
  定义体: #[]
    let mut currOccs := #[]
    for p in l.toArray.qsort do
      if cacheOcc <= p && p < cacheOcc + dCacheOcc then
        prevOccs := prevOccs.push (p - cacheOcc)
      if currOcc <= p && p < currOcc + dCacheOcc then
        currOccs := currOccs.push (p - currOcc)
    return prevOccs == currOc
-/
def canUseCache (cacheOcc dCacheOcc currOcc : Nat) : Occurrences -> Bool
  | .all => true
  | .pos l | .neg l => Id.run do
    let mut prevOccs := #[]
    let mut currOccs := #[]
    for p in l.toArray.qsort do
      if cacheOcc <= p && p < cacheOcc + dCacheOcc then
        prevOccs := prevOccs.push (p - cacheOcc)
      if currOcc <= p && p < currOcc + dCacheOcc then
        currOccs := currOccs.push (p - currOcc)
    return prevOccs == currOccs

/--
Definition of `M` / `M` 的定义

English:
abbreviation M
  body: ReaderT Context MonadCacheT ExprStructEq (Expr × Nat × Nat)
  StateRefT Nat MetaM

中文:
缩写 M
  定义体: ReaderT Context MonadCacheT ExprStructEq (Expr × Nat × Nat)
  StateRefT Nat MetaM

Depends on / 依赖: Context, ExprStructEq, MonadCacheT, ReaderT
-/
abbrev M := ReaderT Context MonadCacheT ExprStructEq (Expr × Nat × Nat)
  StateRefT Nat MetaM

/--
Definition of `checkCastAllowed` / `checkCastAllowed` 的定义

English:
definition checkCastAllowed
  signature: (e t : Expr) (castMode : CastMode)
  body: do
  let throwMismatch : Unit -> MetaM Unit := fun _ => do
    throwError m!"\
      Will not cast{indentExpr e}\nin cast mode '{castMode}'. \
      If inserting more casts is acceptable, use `rw! (castMode := .all)`."
  if castMode == .proofs then
    if !(← isProp t) then
      throwMismatch ()

中文:
定义 checkCastAllowed
  签名: (e t : Expr) (castMode : CastMode)
  定义体: do
  let throwMismatch : Unit -> MetaM Unit := fun _ => do
    throwError m!"\
      Will not cast{indentExpr e}\nin cast mode '{castMode}'. \
      If inserting more casts is acceptable, use `rw! (castMode := .all)`."
  if castMode == .proofs then
    if !(← isProp t) then
      throwMismatch ()
-/
def checkCastAllowed (e t : Expr) (castMode : CastMode) : MetaM Unit := do
  let throwMismatch : Unit -> MetaM Unit := fun _ => do
    throwError m!"\
      Will not cast{indentExpr e}\nin cast mode '{castMode}'. \
      If inserting more casts is acceptable, use `rw! (castMode := .all)`."
  if castMode == .proofs then
    if !(← isProp t) then
      throwMismatch ()

/--
Definition of `zetaDelta` / `zetaDelta` 的定义

English:
definition zetaDelta
  signature: (e : Expr) (fvars : Std.HashSet FVarId)
  body: let unfold? (fvarId : FVarId) : MetaM (Option Expr) := do
    if fvars.contains fvarId then
      fvarId.getValue?
    else
      return none
  let pre (e : Expr) : MetaM TransformStep := do
    let .fvar fvarId := e | return .continue
    let some val ← unfold? fvarId | return .continue
    return 

中文:
定义 zetaDelta
  签名: (e : Expr) (fvars : Std.HashSet FVarId)
  定义体: let unfold? (fvarId : FVarId) : MetaM (Option Expr) := do
    if fvars.contains fvarId then
      fvarId.getValue?
    else
      return none
  let pre (e : Expr) : MetaM TransformStep := do
    let .fvar fvarId := e | return .continue
    let some val ← unfold? fvarId | return .continue
    return 

Depends on / 依赖: FVarId, TransformStep, contains, continue, fvarId, fvarId.getValue, fvars.contains, getValue, return, transform
-/
def zetaDelta (e : Expr) (fvars : Std.HashSet FVarId) : MetaM Expr :=
  let unfold? (fvarId : FVarId) : MetaM (Option Expr) := do
    if fvars.contains fvarId then
      fvarId.getValue?
    else
      return none
  let pre (e : Expr) : MetaM TransformStep := do
    let .fvar fvarId := e | return .continue
    let some val ← unfold? fvarId | return .continue
    return .visit val
  transform e (pre := pre)

/--
Definition of `castMData` / `castMData` 的定义

English:
definition castMData
  signature: : MData
  body: .mk [(`depRewrite, .ofBool true)]

中文:
定义 castMData
  签名: : MData
  定义体: .mk [(`depRewrite, .ofBool true)]

Depends on / 依赖: depRewrite, ofBool
-/
def castMData : MData :=
  .mk [(`depRewrite, .ofBool true)]

/--
Definition of `castBack?` / `castBack?` 的定义

English:
definition castBack?
  signature: (e te x h : Expr) (Δ : Array (FVarId × Expr)) (δ : Std.HashSet FVarId)
  body: do
  if !te.hasAnyFVar (fun f => f == x.fvarId! || f == h.fvarId! ||
      Δ.any (·.1 == f) || δ.contains f) then
    return none
  let e' := .mdata castMData (← mkEqRec (← motive) e (← mkEqSymm h))
  trace[Tactic.depRewrite.cast] "casting (x => p):{indentExpr e'}"
  return some e'

中文:
定义 castBack?
  签名: (e te x h : Expr) (Δ : Array (FVarId × Expr)) (δ : Std.HashSet FVarId)
  定义体: do
  if !te.hasAnyFVar (fun f => f == x.fvarId! || f == h.fvarId! ||
      Δ.any (·.1 == f) || δ.contains f) then
    return none
  let e' := .mdata castMData (← mkEqRec (← motive) e (← mkEqSymm h))
  trace[Tactic.depRewrite.cast] "casting (x => p):{indentExpr e'}"
  return some e'
-/
def castBack? (e te x h : Expr) (Δ : Array (FVarId × Expr)) (δ : Std.HashSet FVarId) :
    MetaM (Option Expr) := do
  if !te.hasAnyFVar (fun f => f == x.fvarId! || f == h.fvarId! ||
      Δ.any (·.1 == f) || δ.contains f) then
    return none
  let e' := .mdata castMData (← mkEqRec (← motive) e (← mkEqSymm h))
  trace[Tactic.depRewrite.cast] "casting (x => p):{indentExpr e'}"
  return some e'
where
  /-- Compute the motive that casts `e` back to `te[p/x, rfl/h, …]`. -/
  motive : MetaM Expr := do
    withLocalDeclD `x' (← inferType x) fun x' => do
    withLocalDeclD `h' (← mkEq x x') fun h' => do
      /- The motive computation below operates syntactically, i.e.,
      it looks for the fvars `x` and `h`.
      This breaks in the presence of `let`-binders:
      if we traverse into `b` in `let a := n; b` with `n` as the pattern,
      we will have `a := x` in the local context.
      If the type-correctness of `b` depends on the defeq `a ≡ n`,
      because `b` does not depend on `x` syntactically,
      a `replaceFVars` substitution will not suffice to fix `b`.
      Thus we unfold the necessary dependent `ldecl`s when computing motives.
      If their values depend on `x`,
      this will be visible in the syntactic form of `te`. -/
      let te ← zetaDelta te δ
      let mut fs := #[x, h]
      let mut es := #[x', ← mkEqTrans h h']
      for (f, M) in Δ do
        fs := fs.push (.fvar f)
        es := es.push (.mdata castMData (← mkEqRec M (.fvar f) h'))
      let te := te.replaceFVars fs es
      mkLambdaFVars #[x', h'] te

/--
Definition of `castFwd` / `castFwd` 的定义

English:
definition castFwd
  signature: (e te p x h : Expr) (Δ : Array (FVarId × Expr)) (δ : Std.HashSet FVarId)
  body: do
  if !te.hasAnyFVar (fun f => f == x.fvarId! || f == h.fvarId! ||
      Δ.any (·.1 == f) || δ.contains f) then
    return e
  let motive ← do
    withLocalDeclD `x' (← inferType x) fun x' => do
    withLocalDeclD `h' (← mkEq p x') fun h' => do
      let te ← zetaDelta te δ
      let mut fs := #[x

中文:
定义 castFwd
  签名: (e te p x h : Expr) (Δ : Array (FVarId × Expr)) (δ : Std.HashSet FVarId)
  定义体: do
  if !te.hasAnyFVar (fun f => f == x.fvarId! || f == h.fvarId! ||
      Δ.any (·.1 == f) || δ.contains f) then
    return e
  let motive ← do
    withLocalDeclD `x' (← inferType x) fun x' => do
    withLocalDeclD `h' (← mkEq p x') fun h' => do
      let te ← zetaDelta te δ
      let mut fs := #[x
-/
def castFwd (e te p x h : Expr) (Δ : Array (FVarId × Expr)) (δ : Std.HashSet FVarId) :
    MetaM Expr := do
  if !te.hasAnyFVar (fun f => f == x.fvarId! || f == h.fvarId! ||
      Δ.any (·.1 == f) || δ.contains f) then
    return e
  let motive ← do
    withLocalDeclD `x' (← inferType x) fun x' => do
    withLocalDeclD `h' (← mkEq p x') fun h' => do
      let te ← zetaDelta te δ
      let mut fs := #[x, h]
      let mut es := #[x', h']
      for (f, M) in Δ do
        fs := fs.push (.fvar f)
        es := es.push (.mdata castMData (← mkEqRec M (.fvar f) (← mkEqTrans (← mkEqSymm h) h')))
      let te := te.replaceFVars fs es
      mkLambdaFVars #[x', h'] te
  let e' := .mdata castMData (← mkEqRec motive e h)
  trace[Tactic.depRewrite.cast] "casting (p => x):{indentExpr e'}"
  return e'

mutual

/--
Definition of `visitAndCast` / `visitAndCast` 的定义

English:
definition visitAndCast
  signature: (e : Expr) (et? : Option Expr)
  body: do
  let e' ← visit e et?
  let some et := et? | return e'
  let te' ← inferType e'
  -- Increase transparency to avoid inserting unnecessary casts
  -- between definientia and definienda (δ reductions).
if ← withAtLeastTransparency .default withNewMCtxDepth isDefEq te' et then
    return e'
  trace

中文:
定义 visitAndCast
  签名: (e : Expr) (et? : Option Expr)
  定义体: do
  let e' ← visit e et?
  let some et := et? | return e'
  let te' ← inferType e'
  -- Increase transparency to avoid inserting unnecessary casts
  -- between definientia and definienda (δ reductions).
if ← withAtLeastTransparency .default withNewMCtxDepth isDefEq te' et then
    return e'
  trace
-/
partial def visitAndCast (e : Expr) (et? : Option Expr) : M Expr := do
  let e' ← visit e et?
  let some et := et? | return e'
  let te' ← inferType e'
  -- Increase transparency to avoid inserting unnecessary casts
  -- between definientia and definienda (δ reductions).
if ← withAtLeastTransparency .default withNewMCtxDepth isDefEq te' et then
    return e'
  trace[Tactic.depRewrite.cast] "casting{indentExpr e'}\nto expected type{indentExpr et}"
  let ctx ← read
  checkCastAllowed e' te' ctx.cfg.castMode

  /- Try casting from the inferred type (x ↦ p),
  and to the expected type (p ↦ x).
  In certain cases we need to cast in both directions (see `bool_dep_test`). -/
  match ← castBack? e' te' ctx.x ctx.h ctx.Δ ctx.δ with
  | some e'' =>
    let te'' ← inferType e''
if ← withAtLeastTransparency .default withNewMCtxDepth isDefEq te'' et then
      return e''

    castFwd e'' et ctx.p ctx.x ctx.h ctx.Δ ctx.δ
  | none =>
    castFwd e' et ctx.p ctx.x ctx.h ctx.Δ ctx.δ

/--
Definition of `visit` / `visit` 的定义

English:
definition visit
  signature: (e : Expr) (et? : Option Expr)
  body: withTraceNode traceClsVisit (fun
    | .ok e' => pure m!"{e} => {e'} (et: {et?})"
    | .error _ => pure m!"{e} => ??") <| Meta.withIncRecDepth do
  let ctx ← read
  if let some (eup, cacheOcc, dCacheOcc) ← MonadCache.findCached? { val := e : ExprStructEq } then
    if canUseCache cacheOcc dCacheOcc

中文:
定义 visit
  签名: (e : Expr) (et? : Option Expr)
  定义体: withTraceNode traceClsVisit (fun
    | .ok e' => pure m!"{e} => {e'} (et: {et?})"
    | .error _ => pure m!"{e} => ??") <| Meta.withIncRecDepth do
  let ctx ← read
  if let some (eup, cacheOcc, dCacheOcc) ← MonadCache.findCached? { val := e : ExprStructEq } then
    if canUseCache cacheOcc dCacheOcc
-/
partial def visit (e : Expr) (et? : Option Expr) : M Expr :=
  withTraceNode traceClsVisit (fun
    | .ok e' => pure m!"{e} => {e'} (et: {et?})"
    | .error _ => pure m!"{e} => ??") <| Meta.withIncRecDepth do
  let ctx ← read
  if let some (eup, cacheOcc, dCacheOcc) ← MonadCache.findCached? { val := e : ExprStructEq } then
    if canUseCache cacheOcc dCacheOcc (← get) ctx.cfg.occs then
      modify (· + dCacheOcc)
      return eup
  let initOccs ← get
  let eup ← visitInner e et?
  MonadCache.cache { val := e : ExprStructEq } (eup, initOccs, (← get) - initOccs)
  return eup

-- TODO(WN): further speedup might come from returning whether anything
-- was rewritten inside a `visit`,
-- and then skipping the type correctness check if it wasn't.
/--
Definition of `visitInner` / `visitInner` 的定义

English:
definition visitInner
  signature: (e : Expr) (et? : Option Expr)
  body: do
  let ctx ← read
  if e.hasLooseBVars then
    throwError "internal error: forgot to instantiate"
  if e.toHeadIndex == ctx.pHeadIdx && e.headNumArgs == ctx.pNumArgs then
    -- We save the metavariable context here,
    -- so that it can be rolled back unless `occs.contains i`.
    let mctx ← ge

中文:
定义 visitInner
  签名: (e : Expr) (et? : Option Expr)
  定义体: do
  let ctx ← read
  if e.hasLooseBVars then
    throwError "internal error: forgot to instantiate"
  if e.toHeadIndex == ctx.pHeadIdx && e.headNumArgs == ctx.pNumArgs then
    -- We save the metavariable context here,
    -- so that it can be rolled back unless `occs.contains i`.
    let mctx ← ge
-/
partial def visitInner (e : Expr) (et? : Option Expr) : M Expr := do
  let ctx ← read
  if e.hasLooseBVars then
    throwError "internal error: forgot to instantiate"
  if e.toHeadIndex == ctx.pHeadIdx && e.headNumArgs == ctx.pNumArgs then
    -- We save the metavariable context here,
    -- so that it can be rolled back unless `occs.contains i`.
    let mctx ← getMCtx
    -- Note that the pattern `ctx.p` is created in the outer lctx,
    -- so bvars from the visited term will not be unified into the pattern.
if ← withTransparency ctx.cfg.transparency isDefEq e ctx.p then
      let i ← modifyGet fun i => (i, i+1)
      if ctx.cfg.occs.contains i then
        return ctx.x
      else
        -- Revert the metavariable context,
        -- so that other matches are still possible.
        setMCtx mctx
  match e with
  | .mdata d b => return .mdata d (← visitAndCast b et?)
  | .app f a =>
    let (fup, tr) ← do
      let fup ← visit f none
      let tfup ← inferType fup
withAtLeastTransparency .default forallBoundedTelescope tfup (some 1) fun xs _ => do
        match xs with
        | #[r] => return (fup, ← inferType r)
        | _ =>
          -- The term in function position was rewritten to a non-function,
          -- so cast it back to one.
          let some fup' ← castBack? fup tfup ctx.x ctx.h ctx.Δ ctx.δ
            | throwError "internal error: unexpected castBack failure on{indentExpr fup}"
          let tfup' ← inferType fup'
withAtLeastTransparency .default forallBoundedTelescope tfup' (some 1) fun xs _ => do
            let #[r] := xs | throwError "internal error: function expected, got{indentExpr fup'}"
            return (fup', ← inferType r)

    let aup ← visitAndCast a tr
    return .app fup aup
  | .proj n i b =>
    let bup ← visit b none
    let tbup ← inferType bup
    if (← withAtLeastTransparency .default <| whnf tbup).isAppOf n then
      return .proj n i bup

    /- Otherwise the term in structure position was rewritten to have a different type,
    so cast it back to the original type.
    (While the other type may itself be a structure type,
    we can't assume that its projections are the same as those of the original.) -/
    let some bup' ← castBack? bup tbup ctx.x ctx.h ctx.Δ ctx.δ
      | throwError "internal error: could not cast back in{indentExpr bup}"
    return .proj n i bup'
  | .letE n t v b nondep =>
    let tup ← visit t none
    let vup ← visitAndCast v tup
    if nondep || !vup.hasAnyFVar (fun f => f == ctx.x.fvarId! || f == ctx.h.fvarId! ||
        ctx.Δ.any (·.1 == f) || ctx.δ.contains f) then
      return ← withLetDecl n tup vup (nondep := nondep) fun r => do
        let motive ← castBack?.motive tup ctx.x ctx.h ctx.Δ ctx.δ
        let bup ← withReader (fun ctx => { ctx with Δ := ctx.Δ.push (r.fvarId!, motive) })
          (visitAndCast (b.instantiate1 r) et?)
        return .letE n tup vup (bup.abstract #[r]) nondep

    withLetDecl n tup vup (nondep := nondep) fun r => do
      let bup ← withReader (fun ctx => { ctx with δ := ctx.δ.insert r.fvarId! })
        (visitAndCast (b.instantiate1 r) et?)
      return .letE n tup vup (bup.abstract #[r]) nondep
  | .lam n t b bi =>
    let tup ← visit t none
    withLocalDecl n bi tup fun r => do
      -- NOTE(WN): there should be some way to propagate the expected type here,
      -- but it is not easy to do correctly (see `lam (as argument)` tests).
      let motive ← castBack?.motive tup ctx.x ctx.h ctx.Δ ctx.δ
      let bup ← withReader (fun ctx => { ctx with Δ := ctx.Δ.push (r.fvarId!, motive) })
        (visit (b.instantiate1 r) none)
      return .lam n tup (bup.abstract #[r]) bi
  | .forallE n t b bi =>
    let tup ← visit t none
    withLocalDecl n bi tup fun r => do
      let motive ← castBack?.motive tup ctx.x ctx.h ctx.Δ ctx.δ
      let bup ← withReader (fun ctx => { ctx with Δ := ctx.Δ.push (r.fvarId!, motive) })
        (visit (b.instantiate1 r) none)
      return .forallE n tup (bup.abstract #[r]) bi
  | _ => return e

end

/--
Definition of `dabstract` / `dabstract` 的定义

English:
definition dabstract
  signature: (e : Expr) (p : Expr) (cfg : DepRewrite.Config)
  body: do
  let e ← instantiateMVars e
  let tp ← inferType p
  withTraceNode traceCls (fun
    -- Message shows unified pattern (without mvars) b/c it is constructed after the body runs
    | .ok motive => pure m!"{e} =[x/{p}]=> {motive}"
    | .error (err : Lean.Exception) => pure m!"{e} =[x/{p}]=> {inde

中文:
定义 dabstract
  签名: (e : Expr) (p : Expr) (cfg : DepRewrite.Config)
  定义体: do
  let e ← instantiateMVars e
  let tp ← inferType p
  withTraceNode traceCls (fun
    -- Message shows unified pattern (without mvars) b/c it is constructed after the body runs
    | .ok motive => pure m!"{e} =[x/{p}]=> {motive}"
    | .error (err : Lean.Exception) => pure m!"{e} =[x/{p}]=> {inde
-/
def dabstract (e : Expr) (p : Expr) (cfg : DepRewrite.Config) : MetaM Expr := do
  let e ← instantiateMVars e
  let tp ← inferType p
  withTraceNode traceCls (fun
    -- Message shows unified pattern (without mvars) b/c it is constructed after the body runs
    | .ok motive => pure m!"{e} =[x/{p}]=> {motive}"
    | .error (err : Lean.Exception) => pure m!"{e} =[x/{p}]=> {indentD err.toMessageData}") do
  withLocalDeclD `x tp fun x => do
  withLocalDeclD `h (← mkEq p x) fun h => do
.run.run' 1 .run { cfg, p, x, h, Δ := ∅, δ := ∅ } let e' ← visit e none
    mkLambdaFVars #[x, h] e'

/--
Definition of `_root_.Lean.MVarId.depRewrite` / `_root_.Lean.MVarId.depRewrite` 的定义

English:
definition _root_.Lean.MVarId.depRewrite
  signature: (mvarId : MVarId) (e : Expr) (heq : Expr)
  body: mvarId.withContext do
    mvarId.checkNotAssigned `depRewrite
    let heqIn := heq
    let heqType ← instantiateMVars (← inferType heq)
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    let cont (heq heqType : Expr) : MetaM RewriteR

中文:
定义 _root_.Lean.MVarId.depRewrite
  签名: (mvarId : MVarId) (e : Expr) (heq : Expr)
  定义体: mvarId.withContext do
    mvarId.checkNotAssigned `depRewrite
    let heqIn := heq
    let heqType ← instantiateMVars (← inferType heq)
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    let cont (heq heqType : Expr) : MetaM RewriteR

Depends on / 依赖: Config, DepRewrite, DepRewrite.Config, RewriteResult, config
-/
def _root_.Lean.MVarId.depRewrite (mvarId : MVarId) (e : Expr) (heq : Expr)
    (symm : Bool := false) (config := { : DepRewrite.Config }) : MetaM RewriteResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `depRewrite
    let heqIn := heq
    let heqType ← instantiateMVars (← inferType heq)
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    let cont (heq heqType : Expr) : MetaM RewriteResult := do
      match (← matchEq? heqType) with
      | none => throwTacticEx `depRewrite mvarId
                  m!"equality or iff proof expected{indentExpr heqType}"
      | some (α, lhs, rhs) =>
        let cont (heq lhs rhs : Expr) : MetaM RewriteResult := do
          if lhs.getAppFn.isMVar then
            throwTacticEx `depRewrite mvarId
              m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr heqType}"
          let e ← instantiateMVars e
let eAbst ← withConfig (fun oldConfig => { config, oldConfig with })
            dabstract e lhs config
          let .lam _ _ (.lam _ _ eBody _) _ := eAbst |
            throwTacticEx `depRewrite mvarId
              m!"internal error: output{indentExpr eAbst}\nof dabstract is not a lambda"
          /-
          This error message may not show up in cases that it could reasonably be expected
          to show up in while using `rw!`.
          In the case that the `depRewrite` step finds an
          instance of the pattern to rewrite with, and it does the rewrite, but then the
          `cleanupCasts` step happens and the result of the `cleanupCasts` step is
          syntactically equal to the original expression.
          Then the error message would be skipped, because `depRewrite` found instances
          of the pattern to rewrite, even though the final result of the `rw!` call
          is the same as the original expression.
          -/
          if !eBody.hasLooseBVars then
            throwTacticEx `depRewrite mvarId
              m!"did not find instance of the pattern in the target expression{indentExpr lhs}"
          try
            check eAbst
          catch e : Lean.Exception =>
throwTacticEx `depRewrite mvarId m!"\
              motive{indentExpr eAbst}\nis not type correct:{indentD e.toMessageData}\n\
              unlike with rw/rewrite, this error should NOT happen in rw!/rewrite!: \
              please report it on the Lean Zulip"
          -- construct rewrite proof
          let eType ← inferType e
          -- `eNew ≡ eAbst rhs heq`
          let eNew := eBody.instantiateRev #[rhs, heq]
          -- Has the type of the term that we rewrote changed?
          -- (Checking whether the motive depends on `x` is overly conservative:
          -- when rewriting by a definitional equality,
          -- the motive may use `x` while the type remains the same.)
let isDep ← withNewMCtxDepth not < > (inferType eNew >>= isDefEq eType)
          let u1 ← getLevel α
          let u2 ← getLevel eType
          -- `eqPrf : eAbst lhs rfl = eNew`
          -- `eAbst lhs rfl ≡ e`
          let (eNew, eqPrf) ← do
            lambdaBoundedTelescope eAbst 2 fun xs eBody => do
              let #[x, h] := xs | throwError
                "internal error: expected 2 arguments in{indentExpr eAbst}"
              let eBodyTyp ← inferType eBody
              let motive ← mkLambdaFVars xs eBodyTyp
              if isDep then
                checkCastAllowed eBody eBodyTyp config.castMode
                let some eBody ← castBack? eBody eBodyTyp x h ∅ ∅ | throwError
                  "internal error: body{indentExpr eBody}\nshould mention '{x}' or '{h}'"
                pure (
                  eBody.replaceFVars #[x, h] #[rhs, heq],
                  mkApp6 (.const ``dcongrArg [u1, u2]) α lhs rhs motive heq eAbst)
              else
                let heqPrf := mkApp6 (.const ``hdcongrArg [u1, u2]) α lhs rhs motive heq eAbst
                pure (eNew, mkApp4 (.const ``eq_of_heq [u2]) eType e eNew heqPrf)
          postprocessAppMVars `depRewrite mvarId newMVars binderInfos
            (synthAssignedInstances := !tactic.skipAssignedInstances.get (← getOptions))
.filterM fun mvarId => let newMVarIds ← newMVars.map Expr.mvarId!
not < > mvarId.isAssigned
          let otherMVarIds ← getMVarsNoDelayed heqIn
          let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
          let newMVarIds := newMVarIds ++ otherMVarIds
          pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVarIds.toList }
        match symm with
        | false => cont heq lhs rhs
        | true => do
          cont (← mkEqSymm heq) rhs lhs
    match heqType.iff? with
    | some (lhs, rhs) =>
      let heqType ← mkEq lhs rhs
      let heq := mkApp3 (mkConst ``propext) lhs rhs heq
      cont heq heqType
    | none => match heqType.heq? with
      | some (α, lhs, β, rhs) =>
        let heq ← mkAppOptM (if symm then ``heqR else ``heqL) #[α, β, lhs, rhs, heq]
        cont heq (← inferType heq)
      | none =>
        cont heq heqType

/--
Definition of `cleanupCasts` / `cleanupCasts` 的定义

English:
definition cleanupCasts
  signature: (e : Expr)
  body: transform (input := e) (skipConstInApp := true) (pre := fun e =>
    -- since the `pre` method returns a result instead of calling itself recursively,
    -- the tracing creates many parallel nodes instead of nesting them
    -- unfortunately, there does not seem to be a way to nest the trace nodes


中文:
定义 cleanupCasts
  签名: (e : Expr)
  定义体: transform (input := e) (skipConstInApp := true) (pre := fun e =>
    -- since the `pre` method returns a result instead of calling itself recursively,
    -- the tracing creates many parallel nodes instead of nesting them
    -- unfortunately, there does not seem to be a way to nest the trace nodes


Depends on / 依赖: skipConstInApp, transform
-/
def cleanupCasts (e : Expr) : MetaM Expr :=
  transform (input := e) (skipConstInApp := true) (pre := fun e =>
    -- since the `pre` method returns a result instead of calling itself recursively,
    -- the tracing creates many parallel nodes instead of nesting them
    -- unfortunately, there does not seem to be a way to nest the trace nodes
    -- within the bounds of the `Lean.Meta.transform` API
    withTraceNode traceClsClean (fun
      | .ok (.visit e') => pure m!"{e} => visit {e'}"
      | .ok (.continue e'?) => pure m!"{e} => continue {e'?.getD e}"
      | .ok (.done e') => pure m!"{e} => done {e'}"
      | .error _ => pure m!"{e} => ??") <| do
    let .mdata mdata e := e | return .continue
    if mdata != castMData then return .continue
    trace[Tactic.depRewrite.cleanupCasts] "found potential cast{indentExpr e}"
    unless e.isAppOfArity ``Eq.rec 6 do
      trace[Tactic.depRewrite.cleanupCasts]
        "cast candidate{indentExpr e}\nis not {.ofConstName ``Eq.rec} application"
      return .visit e
    e.withApp fun _ args => do
      let lhs := args[1]!
      let rhs := args[4]!
      let refl := args[3]!
unless ← withNewMCtxDepth isDefEq lhs rhs do
        trace[Tactic.depRewrite.cleanupCasts]
          "lhs{indentExpr lhs}\nis not definitionally equal to rhs{indentExpr rhs}"
        return .continue
unless ← withNewMCtxDepth isDefEq e refl do
        trace[Tactic.depRewrite.cleanupCasts]
          "refl-cast expression{indentExpr e} is not definitionally equal to{indentExpr refl}"
        return .continue
      return .visit refl)

open Parser Elab Tactic

/--
`rewrite!` is like `rewrite`,
but can also insert casts to adjust types that depend on the LHS of a rewrite.
It is available as an ordinary tactic and a `conv` tactic.

The sort of casts that are inserted is controlled by the `castMode` configuration option.
By default, only proof terms are casted;
by proof irrelevance, this adds no observable complexity.

With `rewrite! +letAbs (castMode := .all)`, casts are inserted whenever necessary.
This means that the 'motive is not type correct' error never occurs,
at the expense of creating potentially complicated terms.
-/
syntax (name := depRewriteSeq) "rewrite!" optConfig rwRuleSeq (location)? : tactic

/--
`rw!` is like `rewrite!`, but also cleans up introduced refl-casts after every substitution.
It is available as an ordinary tactic and a `conv` tactic.
-/
syntax (name := depRwSeq) "rw!" optConfig rwRuleSeq (location)? : tactic

/--
Definition of `depRewriteTarget` / `depRewriteTarget` 的定义

English:
definition depRewriteTarget
  signature: (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {})
  body: do
Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

中文:
定义 depRewriteTarget
  签名: (stx : Syntax) (symm : 布尔) (config : DepRewrite.Config := {})
  定义体: do
Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)
-/
def depRewriteTarget (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {}) :
    TacticM Unit := do
Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

/--
Definition of `depRwTarget` / `depRwTarget` 的定义

English:
definition depRwTarget
  signature: (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {})
  body: do
Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    let mvarId'' ← mvarId'.change (← withTransparency config.castTranspar

中文:
定义 depRwTarget
  签名: (stx : Syntax) (symm : 布尔) (config : DepRewrite.Config := {})
  定义体: do
Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    let mvarId'' ← mvarId'.change (← withTransparency config.castTranspar
-/
def depRwTarget (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {}) :
    TacticM Unit := do
Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    let mvarId'' ← mvarId'.change (← withTransparency config.castTransparency
      (mvarId'.withContext <| cleanupCasts (← mvarId'.getType)))
    replaceMainGoal (mvarId'' :: r.mvarIds)

/--
Definition of `depRewriteLocalDecl` / `depRewriteLocalDecl` 的定义

English:
definition depRewriteLocalDecl
  signature: (stx : Syntax) (symm : Bool) (fvarId : FVarId)
  body: withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues https://github.com/leanprover-community/mathlib4/issues/2711 and https://github.com/leanprover-community/mathlib4/issues/2727.
let rwResult ← Term.withSynthesize withMainContext do
    le

中文:
定义 depRewriteLocalDecl
  签名: (stx : Syntax) (symm : 布尔) (fvarId : FVarId)
  定义体: withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues https://github.com/leanprover-community/mathlib4/issues/2711 and https://github.com/leanprover-community/mathlib4/issues/2727.
let rwResult ← Term.withSynthesize withMainContext do
    le

Depends on / 依赖: TacticM, withMainContext
-/
def depRewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId)
    (config : DepRewrite.Config := {}) : TacticM Unit := withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues https://github.com/leanprover-community/mathlib4/issues/2711 and https://github.com/leanprover-community/mathlib4/issues/2727.
let rwResult ← Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let localDecl ← fvarId.getDecl
    (← getMainGoal).depRewrite localDecl.type e symm (config := config)
  let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
  replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

/--
Definition of `depRwLocalDecl` / `depRwLocalDecl` 的定义

English:
definition depRwLocalDecl
  signature: (stx : Syntax) (symm : Bool) (fvarId : FVarId)
  body: withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues https://github.com/leanprover-community/mathlib4/issues/2711 and https://github.com/leanprover-community/mathlib4/issues/2727.
let rwResult ← Term.withSynthesize withMainContext do
    le

中文:
定义 depRwLocalDecl
  签名: (stx : Syntax) (symm : 布尔) (fvarId : FVarId)
  定义体: withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues https://github.com/leanprover-community/mathlib4/issues/2711 and https://github.com/leanprover-community/mathlib4/issues/2727.
let rwResult ← Term.withSynthesize withMainContext do
    le

Depends on / 依赖: TacticM, withMainContext
-/
def depRwLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId)
    (config : DepRewrite.Config := {}) : TacticM Unit := withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues https://github.com/leanprover-community/mathlib4/issues/2711 and https://github.com/leanprover-community/mathlib4/issues/2727.
let rwResult ← Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let localDecl ← fvarId.getDecl
    (← getMainGoal).depRewrite localDecl.type e symm (config := config)
  let r ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
  let mvarId' ← r.mvarId.changeLocalDecl r.fvarId (← withTransparency config.castTransparency
    (r.mvarId.withContext do cleanupCasts (← r.fvarId.getType)))
  replaceMainGoal (mvarId' :: rwResult.mvarIds)

/-- Elaborate `DepRewrite.Config`. -/
declare_config_elab elabDepRewriteConfig Config

@[tactic depRewriteSeq, inherit_doc depRewriteSeq]
/--
Definition of `evalDepRewriteSeq` / `evalDepRewriteSeq` 的定义

English:
definition evalDepRewriteSeq
  signature: : Tactic
  body: fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  let loc := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `depRewrite · "did not find inst

中文:
定义 evalDepRewriteSeq
  签名: : Tactic
  定义体: fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  let loc := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `depRewrite · "did not find inst
-/
def evalDepRewriteSeq : Tactic := fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  let loc := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `depRewrite · "did not find instance of the pattern in the current goal")

@[tactic depRwSeq, inherit_doc depRwSeq]
/--
Definition of `evalDepRwSeq` / `evalDepRwSeq` 的定义

English:
definition evalDepRwSeq
  signature: : Tactic
  body: fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  let loc := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRwLocalDecl term symm · cfg)
      (depRwTarget term symm cfg)
      (throwTacticEx `depRewrite · "did not find instance of th

中文:
定义 evalDepRwSeq
  签名: : Tactic
  定义体: fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  let loc := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRwLocalDecl term symm · cfg)
      (depRwTarget term symm cfg)
      (throwTacticEx `depRewrite · "did not find instance of th
-/
def evalDepRwSeq : Tactic := fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  let loc := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRwLocalDecl term symm · cfg)
      (depRwTarget term symm cfg)
      (throwTacticEx `depRewrite · "did not find instance of the pattern in the current goal")

namespace Conv
open Conv

@[inherit_doc depRewriteSeq]
syntax (name := depRewrite) "rewrite!" optConfig rwRuleSeq : conv

@[inherit_doc depRwSeq]
syntax (name := depRw) "rw!" optConfig rwRuleSeq : conv

/--
Definition of `depRewriteTarget` / `depRewriteTarget` 的定义

English:
definition depRewriteTarget
  signature: (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {})
  body: do
Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    replaceMainGoal ((← getMainGoal) :: r.mvarIds)

中文:
定义 depRewriteTarget
  签名: (stx : Syntax) (symm : 布尔) (config : DepRewrite.Config := {})
  定义体: do
Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    replaceMainGoal ((← getMainGoal) :: r.mvarIds)
-/
def depRewriteTarget (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {}) :
    TacticM Unit := do
Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    replaceMainGoal ((← getMainGoal) :: r.mvarIds)

/--
Definition of `depRwTarget` / `depRwTarget` 的定义

English:
definition depRwTarget
  signature: (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {})
  body: do
Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    changeLhs (← withTransparency config.castTransparency
      (withMainContext <| cleanupCasts (← getLhs)))
    re

中文:
定义 depRwTarget
  签名: (stx : Syntax) (symm : 布尔) (config : DepRewrite.Config := {})
  定义体: do
Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    changeLhs (← withTransparency config.castTransparency
      (withMainContext <| cleanupCasts (← getLhs)))
    re

Depends on / 依赖: TacticM
-/
def depRwTarget (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {}) : TacticM Unit := do
Term.withSynthesize withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    changeLhs (← withTransparency config.castTransparency
      (withMainContext <| cleanupCasts (← getLhs)))
    replaceMainGoal ((← getMainGoal) :: r.mvarIds)

@[tactic depRewrite, inherit_doc depRewriteSeq]
/--
Definition of `evalDepRewriteSeq` / `evalDepRewriteSeq` 的定义

English:
definition evalDepRewriteSeq
  signature: : Tactic
  body: fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  withRWRulesSeq stx[0] stx[2] fun symm term => depRewriteTarget term symm cfg

@[tactic depRw, inherit_doc depRwSeq]

中文:
定义 evalDepRewriteSeq
  签名: : Tactic
  定义体: fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  withRWRulesSeq stx[0] stx[2] fun symm term => depRewriteTarget term symm cfg

@[tactic depRw, inherit_doc depRwSeq]
-/
def evalDepRewriteSeq : Tactic := fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  withRWRulesSeq stx[0] stx[2] fun symm term => depRewriteTarget term symm cfg

@[tactic depRw, inherit_doc depRwSeq]
/--
Definition of `evalDepRwSeq` / `evalDepRwSeq` 的定义

English:
definition evalDepRwSeq
  signature: : Tactic
  body: fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  withRWRulesSeq stx[0] stx[2] fun symm term => depRwTarget term symm cfg

中文:
定义 evalDepRwSeq
  签名: : Tactic
  定义体: fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  withRWRulesSeq stx[0] stx[2] fun symm term => depRwTarget term symm cfg
-/
def evalDepRwSeq : Tactic := fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  withRWRulesSeq stx[0] stx[2] fun symm term => depRwTarget term symm cfg

end Conv
end Mathlib.Tactic.DepRewrite
