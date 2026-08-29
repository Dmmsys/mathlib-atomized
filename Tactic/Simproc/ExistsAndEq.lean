/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Init
public meta import Qq
public import Qq
public import Qq.MatchImpl
public import Qq.Typ

/-!
# Simproc for `∃ a', ... ∧ a' = a ∧ ...`

This module implements the `existsAndEq` simproc, which triggers on goals of the form `∃ a, P`.
It checks whether `P` allows only one possible value for `a`, and if so, substitutes it, eliminating
the leading quantifier.

The procedure traverses the body, branching at each `∧` and entering existential quantifiers,
searching for a subexpression of the form `a = a'` or `a' = a` for `a'` that is independent of `a`.
If such an expression is found, all occurrences of `a` are replaced with `a'`. If `a'` depends on
variables bound by existential quantifiers, those quantifiers are moved outside.

For example, `∃ a, p a ∧ ∃ b, a = f b ∧ q b` will be rewritten as `∃ b, p (f b) ∧ q b`.
-/

public meta section

open Lean Meta Qq

namespace ExistsAndEq

/--
Inductive type `GoTo` / 归纳类型 `GoTo`

English:
inductive GoTo
  constructors (1):
    - left: | right

中文:
归纳类型 GoTo
  构造子 (1 个):
    - left: | right
-/
inductive GoTo
| left | right
deriving BEq, Inhabited

/--
Definition of `Path` / `Path` 的定义

English:
abbreviation Path
  body: List GoTo

中文:
缩写 道路
  定义体: List GoTo

Depends on / 依赖: Algebra, F.obj, G.obj, Localization
-/
abbrev Path := List GoTo

/--
Definition of `VarQ` / `VarQ` 的定义

English:
abbreviation VarQ
  body: (u : Level) × (α : Q(Sort u)) × Q($α)

中文:
缩写 VarQ
  定义体: (u : Level) × (α : Q(Sort u)) × Q($α)

Depends on / 依赖: G.obj, IsLocalization, Localization
-/
abbrev VarQ := (u : Level) × (α : Q(Sort u)) × Q($α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited VarQ
  body: ⟨default, default, default⟩

中文:
实例 :
  签名: 可居 VarQ
  定义体: ⟨default, default, default⟩
-/
instance : Inhabited VarQ where
  default := ⟨default, default, default⟩

/--
Definition of `HypQ` / `HypQ` 的定义

English:
abbreviation HypQ
  body: (P : Q(Prop)) × Q($P)

中文:
缩写 HypQ
  定义体: (P : Q(Prop)) × Q($P)
-/
abbrev HypQ := (P : Q(Prop)) × Q($P)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited HypQ
  body: ⟨default, default⟩

中文:
实例 :
  签名: 可居 HypQ
  定义体: ⟨default, default⟩
-/
instance : Inhabited HypQ where
  default := ⟨default, default⟩

/--
Definition of `assertUnreachable` / `assertUnreachable` 的定义

English:
definition assertUnreachable
  signature: {α : Type} (context : String)
  body: do
  let e := s!"existsAndEq: internal error, unreachable case has occurred:\n{context}."
  logError e
  -- the following error will be caught by `simp` so we additionally log it above
  throwError e

中文:
定义 assertUnreachable
  签名: {α : 类型} (context : String)
  定义体: do
  let e := s!"existsAndEq: internal error, unreachable case has occurred:\n{context}."
  logError e
  -- the following error will be caught by `simp` so we additionally log it above
  throwError e
-/
private def assertUnreachable {α : Type} (context : String) : MetaM α := do
  let e := s!"existsAndEq: internal error, unreachable case has occurred:\n{context}."
  logError e
  -- the following error will be caught by `simp` so we additionally log it above
  throwError e

/--
Definition of `mkNestedExists` / `mkNestedExists` 的定义

English:
definition mkNestedExists
  signature: (fvars : List VarQ) (body : Q(Prop))
  body: do
  match fvars with
  | [] => pure body
  | ⟨_, β, b⟩ :: tl =>
    let res ← mkNestedExists tl body
.get!.userName let name := (← getLCtx).findFVar? b
    let p : Q($β -> Prop) ← Impl.mkLambdaQ name b res
    pure q(Exists $p)

中文:
定义 mkNestedExists
  签名: (fvars : 列表 VarQ) (body : Q(命题))
  定义体: do
  match fvars with
  | [] => pure body
  | ⟨_, β, b⟩ :: tl =>
    let res ← mkNestedExists tl body
.get!.userName let name := (← getLCtx).findFVar? b
    let p : Q($β -> Prop) ← Impl.mkLambdaQ name b res
    pure q(Exists $p)
-/
def mkNestedExists (fvars : List VarQ) (body : Q(Prop)) : MetaM Q(Prop) := do
  match fvars with
  | [] => pure body
  | ⟨_, β, b⟩ :: tl =>
    let res ← mkNestedExists tl body
.get!.userName let name := (← getLCtx).findFVar? b
    let p : Q($β -> Prop) ← Impl.mkLambdaQ name b res
    pure q(Exists $p)

/--
Definition of `findEqPath` / `findEqPath` 的定义

English:
definition findEqPath
  signature: {u : Level} {α : Q(Sort u)} (a : Q($α)) (P : Q(Prop))
  body: do
  match_expr P with
  | Eq _ x y =>
    if a == x && !(y.containsFVar a.fvarId!) then
      return some []
    if a == y && !(x.containsFVar a.fvarId!) then
      return some []
    return none
  | And L R =>
    if let some path ← findEqPath a L then
      return some (.left :: path)
    if let some path ← findEqPath a R then
      return some (.right :: path)
    return none
  | Exists tb pb =>
    if (tb.containsFVar a.fvarId!) then
      return none
    let .lam _ _ body _ := pb | return none
    findEqPath a body
  | _ => return none

中文:
定义 findEqPath
  签名: {u : Level} {α : Q(类型层 u)} (a : Q($α)) (P : Q(命题))
  定义体: do
  match_expr P with
  | Eq _ x y =>
    if a == x && !(y.containsFVar a.fvarId!) then
      return some []
    if a == y && !(x.containsFVar a.fvarId!) then
      return some []
    return none
  | And L R =>
    if let some path ← findEqPath a L then
      return some (.left :: path)
    if let some path ← findEqPath a R then
      return some (.right :: path)
    return none
  | Exists tb pb =>
    if (tb.containsFVar a.fvarId!) then
      return none
    let .lam _ _ body _ := pb | return none
    findEqPath a body
  | _ => return none
-/
partial def findEqPath {u : Level} {α : Q(Sort u)} (a : Q($α)) (P : Q(Prop)) :
MetaM Option Path := do
  match_expr P with
  | Eq _ x y =>
    if a == x && !(y.containsFVar a.fvarId!) then
      return some []
    if a == y && !(x.containsFVar a.fvarId!) then
      return some []
    return none
  | And L R =>
    if let some path ← findEqPath a L then
      return some (.left :: path)
    if let some path ← findEqPath a R then
      return some (.right :: path)
    return none
  | Exists tb pb =>
    if (tb.containsFVar a.fvarId!) then
      return none
    let .lam _ _ body _ := pb | return none
    findEqPath a body
  | _ => return none

/--
Definition of `findEq` / `findEq` 的定义

English:
definition findEq
  signature: {u : Level} {α : Q(Sort u)} (a : Q($α)) (P : Q(Prop)) (path : Path)
  body: do
   go a P path

中文:
定义 findEq
  签名: {u : Level} {α : Q(类型层 u)} (a : Q($α)) (P : Q(命题)) (path : 道路)
  定义体: do
   go a P path

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_of_injective, NatTrans, NatTrans.mono_of_mono_app, allowSynthFailures, mono_of_injective, mono_of_mono_app, toTotalQuotientPresheaf
-/
partial def findEq {u : Level} {α : Q(Sort u)} (a : Q($α)) (P : Q(Prop)) (path : Path) :
    MetaM (List VarQ × LocalContext × Q(Prop) × Q($α)) := do
   go a P path
where
  /-- Recursive part of `findEq`. -/
  go {u : Level} {α : Q(Sort u)} (a : Q($α)) (P : Q(Prop)) (path : Path) :
    MetaM (List VarQ × LocalContext × Q(Prop) × Q($α)) := do
  match P with
  | ~q(@Eq.{u} $γ $x $y) =>
    if a == x && !(y.containsFVar a.fvarId!) then
      return ([], ← getLCtx, P, y)
    if a == y && !(x.containsFVar a.fvarId!) then
      return ([], ← getLCtx, P, x)
    assertUnreachable
      "findEq: some side of equality must be `a`, and the other must not depend on `a`"
  | ~q($L ∧ $R) =>
    match path with
    | [] => assertUnreachable "findEq: P is conjunction but path is empty"
    | .left :: tl =>
      let (fvars, lctx, P', a') ← go a q($L) tl
      return (fvars, lctx, q($P' ∧ $R), a')
    | .right :: tl =>
      let (fvars, lctx, P', a') ← go a q($R) tl
      return (fvars, lctx, q($L ∧ $P'), a')
  | ~q(@Exists $β $pb) =>
    lambdaBoundedTelescope pb 1 fun bs (body : Q(Prop)) => do
      let #[(b : Q($β))] := bs | unreachable!
      let (fvars, lctx, P', a') ← go a q($body) path
      return (⟨_, _, b⟩ :: fvars, lctx, P', a')
  | _ => assertUnreachable s!"findEq: unexpected P = {← ppExpr P}"

/--
Definition of `withNestedExistsElim` / `withNestedExistsElim` 的定义

English:
definition withNestedExistsElim
  signature: {P body goal : Q(Prop)} (exs : List VarQ) (h : Q($P))
  body: do
  match exs with
  | [] =>
let _ : P =Q body := ⟨⟩
    act q($h)
  | ⟨u, β, b⟩ :: tl =>
    let ~q(@Exists.{u} $γ $p) := P
| assertUnreachable "withNestedExistsElim: exs is not empty but P is not `Exists`.\n" ++
          s!"P = {← ppExpr P}"
let _ : β =Q γ := ⟨⟩
    withLocalDeclQ .anonymous .default q($p $b) fun hb => do
      let pf1 ← withNestedExistsElim tl hb act
      let pf2 : Q(forall b, $p b -> $goal) ← mkLambdaFVars #[b, hb] pf1
      return q(Exists.elim $h $pf2)

中文:
定义 withNestedExistsElim
  签名: {P body goal : Q(命题)} (exs : 列表 VarQ) (h : Q($P))
  定义体: do
  match exs with
  | [] =>
let _ : P =Q body := ⟨⟩
    act q($h)
  | ⟨u, β, b⟩ :: tl =>
    let ~q(@Exists.{u} $γ $p) := P
| assertUnreachable "withNestedExistsElim: exs is not empty but P is not `Exists`.\n" ++
          s!"P = {← ppExpr P}"
let _ : β =Q γ := ⟨⟩
    withLocalDeclQ .anonymous .default q($p $b) fun hb => do
      let pf1 ← withNestedExistsElim tl hb act
      let pf2 : Q(forall b, $p b -> $goal) ← mkLambdaFVars #[b, hb] pf1
      return q(Exists.elim $h $pf2)
-/
def withNestedExistsElim {P body goal : Q(Prop)} (exs : List VarQ) (h : Q($P))
    (act : Q($body) -> MetaM Q($goal)) : MetaM Q($goal) := do
  match exs with
  | [] =>
let _ : P =Q body := ⟨⟩
    act q($h)
  | ⟨u, β, b⟩ :: tl =>
    let ~q(@Exists.{u} $γ $p) := P
| assertUnreachable "withNestedExistsElim: exs is not empty but P is not `Exists`.\n" ++
          s!"P = {← ppExpr P}"
let _ : β =Q γ := ⟨⟩
    withLocalDeclQ .anonymous .default q($p $b) fun hb => do
      let pf1 ← withNestedExistsElim tl hb act
      let pf2 : Q(forall b, $p b -> $goal) ← mkLambdaFVars #[b, hb] pf1
      return q(Exists.elim $h $pf2)

/--
Definition of `mkAfterToBefore` / `mkAfterToBefore` 的定义

English:
definition mkAfterToBefore
  signature: {u : Level} {α : Q(Sort u)} {p : Q($α -> Prop)}
  body: do
  withLocalDeclQ .anonymous .default P' fun (h : Q($P')) => do
    let pf : Q(exists a, $p a) ← withNestedExistsElim fvars h fun (h : Q($newBody)) => do
      let pf1 : Q($p $a') ← go h fvars path
      return q(Exists.intro $a' $pf1)
    mkLambdaFVars #[h] pf

中文:
定义 mkAfterToBefore
  签名: {u : Level} {α : Q(类型层 u)} {p : Q($α -> 命题)}
  定义体: do
  withLocalDeclQ .anonymous .default P' fun (h : Q($P')) => do
    let pf : Q(exists a, $p a) ← withNestedExistsElim fvars h fun (h : Q($newBody)) => do
      let pf1 : Q($p $a') ← go h fvars path
      return q(Exists.intro $a' $pf1)
    mkLambdaFVars #[h] pf
-/
partial def mkAfterToBefore {u : Level} {α : Q(Sort u)} {p : Q($α -> Prop)}
    {P' : Q(Prop)} (a' : Q($α)) (newBody : Q(Prop)) (fvars : List VarQ) (path : Path) :
MetaM Q($P' -> (exists a, $p a)) := do
  withLocalDeclQ .anonymous .default P' fun (h : Q($P')) => do
    let pf : Q(exists a, $p a) ← withNestedExistsElim fvars h fun (h : Q($newBody)) => do
      let pf1 : Q($p $a') ← go h fvars path
      return q(Exists.intro $a' $pf1)
    mkLambdaFVars #[h] pf
where
  /-- Traverses `P` and `goal` simultaneously, proving `goal`. -/
  go {goal P : Q(Prop)} (h : Q($P)) (exs : List VarQ) (path : Path) :
    MetaM Q($goal) := do
  match goal with
  | ~q(@Exists $β $pb) =>
    match exs with
    | [] => assertUnreachable "mkAfterToBefore: goal is `Exists` but `exs` is empty"
    | ⟨v, γ, c⟩ :: exsTail =>
    let _ : u_1 =QL v := ⟨⟩
let _ : γ =Q β := ⟨⟩
    let pf1 : Q($pb $c) ← go h exsTail path
    return q(Exists.intro $c $pf1)
  | ~q(And $L $R) =>
    let ~q($L' ∧ $R') := P
      | assertUnreachable "mkAfterToBefore: goal is `And` but `P` is not `And`"
    match path with
    | [] => assertUnreachable "mkAfterToBefore: goal is `And` but `exs` is empty"
    | .left :: tl =>
let _ : R =Q R' := ⟨⟩
      let pfRight : Q($R) := q(And.right $h)
      let pfLeft : Q($L) ← go q(And.left $h) exs tl
      return q(And.intro $pfLeft $pfRight)
    | .right :: tl =>
let _ : L =Q L' := ⟨⟩
      let pfLeft : Q($L) := q(And.left $h)
      let pfRight : Q($R) ← go q(And.right $h) exs tl
      return q(And.intro $pfLeft $pfRight)
  | _ =>
    let ~q($x = $y) := goal
      | assertUnreachable "mkAfterToBefore: unexpected goal: {← ppExpr goal}"
    if !path.isEmpty then
      assertUnreachable "mkAfterToBefore: `goal` is equality but `path` is not empty"
let _ : x =Q y := ⟨⟩
    return q(rfl)

/--
Definition of `withExistsElimAlongPathImp` / `withExistsElimAlongPathImp` 的定义

English:
definition withExistsElimAlongPathImp
  signature: {u : Level} {α : Q(Sort u)}
  body: do
  match P with
  | ~q(@Exists $β $pb) =>
    match exs with
    | [] => assertUnreachable "withExistsElimAlongPathImp: `P` is `Exists` but `exs` is empty"
    | ⟨v, γ, b⟩ :: exsTail =>
    let _ : u_1 =QL v := ⟨⟩
let _ : γ =Q β := ⟨⟩
    withLocalDeclQ .anonymous .default q($pb $b) fun hb => do
      let newHs := hs ++ [⟨_, hb⟩]
      let pf1 ← withExistsElimAlongPathImp (P := q($pb $b)) hb exsTail path newHs act
      let pf2 : Q(forall b, $pb b -> $goal) ← mkLambdaFVars #[b, hb] pf1
      return q(Exists.elim $h $pf2)
  | ~q(And $L' $R') =>
      match path with
      | [] => assertUnreachable "withExistsElimAlongPathImp: `P` is `And` but `path` is empty"
      | .left :: tl =>
        withExistsElimAlongPathImp q(And.left $h) exs tl hs act
      | .right :: tl =>
        withExistsElimAlongPathImp q(And.right $h) exs tl hs act
  | ~q(@Eq.{u} $γ $x $y) =>
let _ : γ =Q α := ⟨⟩
    if !path.isEmpty then
      assertUnreachable "withExistsElimAlongPathImp: `P` is equality but `path` is not empty"
    if a == x then
let _ : a =Q x := ⟨⟩
let _ : a' =Q y := ⟨⟩
      act q($h) hs
    else if a == y then
let _ : a =Q y := ⟨⟩
let _ : a' =Q x := ⟨⟩
      act q(Eq.symm $h) hs
    else
      assertUnreachable "withExistsElimAlongPathImp: `P` is equality but neither of sides is `a`"
  | _ => assertUnreachable s!"withExistsElimAlongPathImp: unexpected P = {← ppExpr P}"

中文:
定义 withExistsElimAlongPathImp
  签名: {u : Level} {α : Q(类型层 u)}
  定义体: do
  match P with
  | ~q(@Exists $β $pb) =>
    match exs with
    | [] => assertUnreachable "withExistsElimAlongPathImp: `P` is `Exists` but `exs` is empty"
    | ⟨v, γ, b⟩ :: exsTail =>
    let _ : u_1 =QL v := ⟨⟩
let _ : γ =Q β := ⟨⟩
    withLocalDeclQ .anonymous .default q($pb $b) fun hb => do
      let newHs := hs ++ [⟨_, hb⟩]
      let pf1 ← withExistsElimAlongPathImp (P := q($pb $b)) hb exsTail path newHs act
      let pf2 : Q(forall b, $pb b -> $goal) ← mkLambdaFVars #[b, hb] pf1
      return q(Exists.elim $h $pf2)
  | ~q(And $L' $R') =>
      match path with
      | [] => assertUnreachable "withExistsElimAlongPathImp: `P` is `And` but `path` is empty"
      | .left :: tl =>
        withExistsElimAlongPathImp q(And.left $h) exs tl hs act
      | .right :: tl =>
        withExistsElimAlongPathImp q(And.right $h) exs tl hs act
  | ~q(@Eq.{u} $γ $x $y) =>
let _ : γ =Q α := ⟨⟩
    if !path.isEmpty then
      assertUnreachable "withExistsElimAlongPathImp: `P` is equality but `path` is not empty"
    if a == x then
let _ : a =Q x := ⟨⟩
let _ : a' =Q y := ⟨⟩
      act q($h) hs
    else if a == y then
let _ : a =Q y := ⟨⟩
let _ : a' =Q x := ⟨⟩
      act q(Eq.symm $h) hs
    else
      assertUnreachable "withExistsElimAlongPathImp: `P` is equality but neither of sides is `a`"
  | _ => assertUnreachable s!"withExistsElimAlongPathImp: unexpected P = {← ppExpr P}"
-/
partial def withExistsElimAlongPathImp {u : Level} {α : Q(Sort u)}
    {P goal : Q(Prop)} (h : Q($P)) {a a' : Q($α)} (exs : List VarQ) (path : Path)
    (hs : List HypQ)
    (act : Q($a = $a') -> List HypQ -> MetaM Q($goal)) :
    MetaM Q($goal) := do
  match P with
  | ~q(@Exists $β $pb) =>
    match exs with
    | [] => assertUnreachable "withExistsElimAlongPathImp: `P` is `Exists` but `exs` is empty"
    | ⟨v, γ, b⟩ :: exsTail =>
    let _ : u_1 =QL v := ⟨⟩
let _ : γ =Q β := ⟨⟩
    withLocalDeclQ .anonymous .default q($pb $b) fun hb => do
      let newHs := hs ++ [⟨_, hb⟩]
      let pf1 ← withExistsElimAlongPathImp (P := q($pb $b)) hb exsTail path newHs act
      let pf2 : Q(forall b, $pb b -> $goal) ← mkLambdaFVars #[b, hb] pf1
      return q(Exists.elim $h $pf2)
  | ~q(And $L' $R') =>
      match path with
      | [] => assertUnreachable "withExistsElimAlongPathImp: `P` is `And` but `path` is empty"
      | .left :: tl =>
        withExistsElimAlongPathImp q(And.left $h) exs tl hs act
      | .right :: tl =>
        withExistsElimAlongPathImp q(And.right $h) exs tl hs act
  | ~q(@Eq.{u} $γ $x $y) =>
let _ : γ =Q α := ⟨⟩
    if !path.isEmpty then
      assertUnreachable "withExistsElimAlongPathImp: `P` is equality but `path` is not empty"
    if a == x then
let _ : a =Q x := ⟨⟩
let _ : a' =Q y := ⟨⟩
      act q($h) hs
    else if a == y then
let _ : a =Q y := ⟨⟩
let _ : a' =Q x := ⟨⟩
      act q(Eq.symm $h) hs
    else
      assertUnreachable "withExistsElimAlongPathImp: `P` is equality but neither of sides is `a`"
  | _ => assertUnreachable s!"withExistsElimAlongPathImp: unexpected P = {← ppExpr P}"

/--
Definition of `withExistsElimAlongPath` / `withExistsElimAlongPath` 的定义

English:
definition withExistsElimAlongPath
  signature: {u : Level} {α : Q(Sort u)}
  body: withExistsElimAlongPathImp h exs path [] act

中文:
定义 withExistsElimAlongPath
  签名: {u : Level} {α : Q(类型层 u)}
  定义体: withExistsElimAlongPathImp h exs path [] act

Depends on / 依赖: withExistsElimAlongPathImp
-/
def withExistsElimAlongPath {u : Level} {α : Q(Sort u)}
    {P goal : Q(Prop)} (h : Q($P)) {a a' : Q($α)} (exs : List VarQ) (path : Path)
    (act : Q($a = $a') -> List HypQ -> MetaM Q($goal)) :
    MetaM Q($goal) :=
  withExistsElimAlongPathImp h exs path [] act

/--
Definition of `withNestedExistsIntro` / `withNestedExistsIntro` 的定义

English:
definition withNestedExistsIntro
  signature: {P body : Q(Prop)} (exs : List VarQ)
  body: do
  match exs with
  | [] =>
let _ : P =Q body := ⟨⟩
    act
  | ⟨u, β, b⟩ :: tl =>
    let ~q(@Exists.{u} $γ $p) := P
      | assertUnreachable "withNestedExistsIntro: `exs` is not empty but `P` is not `Exists`"
let _ : β =Q γ := ⟨⟩
    let pf ← withNestedExistsIntro tl act
    return q(Exists.intro $b $pf)

中文:
定义 withNestedExists整数ro
  签名: {P body : Q(命题)} (exs : 列表 VarQ)
  定义体: do
  match exs with
  | [] =>
let _ : P =Q body := ⟨⟩
    act
  | ⟨u, β, b⟩ :: tl =>
    let ~q(@Exists.{u} $γ $p) := P
      | assertUnreachable "withNestedExistsIntro: `exs` is not empty but `P` is not `Exists`"
let _ : β =Q γ := ⟨⟩
    let pf ← withNestedExistsIntro tl act
    return q(Exists.intro $b $pf)
-/
def withNestedExistsIntro {P body : Q(Prop)} (exs : List VarQ)
    (act : MetaM Q($body)) : MetaM Q($P) := do
  match exs with
  | [] =>
let _ : P =Q body := ⟨⟩
    act
  | ⟨u, β, b⟩ :: tl =>
    let ~q(@Exists.{u} $γ $p) := P
      | assertUnreachable "withNestedExistsIntro: `exs` is not empty but `P` is not `Exists`"
let _ : β =Q γ := ⟨⟩
    let pf ← withNestedExistsIntro tl act
    return q(Exists.intro $b $pf)

/--
Definition of `mkBeforeToAfter` / `mkBeforeToAfter` 的定义

English:
definition mkBeforeToAfter
  signature: {u : Level} {α : Q(Sort u)} {p : Q($α -> Prop)}
  body: do
  withLocalDeclQ .anonymous .default q(exists a, $p a) fun h => do
  withLocalDeclQ .anonymous .default q($α) fun a => do
  withLocalDeclQ .anonymous .default q($p $a) fun ha => do
    let pf1 ← withExistsElimAlongPath ha fvars path fun (h_eq : Q($a = $a')) hs => do
      let pf1 : Q($P') ← withNestedExistsIntro fvars (body := newBody) do
        let pf ← go ha fvars hs path h_eq
        pure pf
      pure pf1
    let pf2 : Q(forall a : $α, $p a -> $P') ← mkLambdaFVars #[a, ha] pf1
    let pf3 : Q($P') := q(Exists.elim $h $pf2)
    mkLambdaFVars #[h] pf3

中文:
定义 mkBeforeToAfter
  签名: {u : Level} {α : Q(类型层 u)} {p : Q($α -> 命题)}
  定义体: do
  withLocalDeclQ .anonymous .default q(exists a, $p a) fun h => do
  withLocalDeclQ .anonymous .default q($α) fun a => do
  withLocalDeclQ .anonymous .default q($p $a) fun ha => do
    let pf1 ← withExistsElimAlongPath ha fvars path fun (h_eq : Q($a = $a')) hs => do
      let pf1 : Q($P') ← withNestedExistsIntro fvars (body := newBody) do
        let pf ← go ha fvars hs path h_eq
        pure pf
      pure pf1
    let pf2 : Q(forall a : $α, $p a -> $P') ← mkLambdaFVars #[a, ha] pf1
    let pf3 : Q($P') := q(Exists.elim $h $pf2)
    mkLambdaFVars #[h] pf3
-/
partial def mkBeforeToAfter {u : Level} {α : Q(Sort u)} {p : Q($α -> Prop)}
    {P' : Q(Prop)} (a' : Q($α)) (newBody : Q(Prop)) (fvars : List VarQ) (path : Path) :
MetaM Q((exists a, $p a) -> $P') := do
  withLocalDeclQ .anonymous .default q(exists a, $p a) fun h => do
  withLocalDeclQ .anonymous .default q($α) fun a => do
  withLocalDeclQ .anonymous .default q($p $a) fun ha => do
    let pf1 ← withExistsElimAlongPath ha fvars path fun (h_eq : Q($a = $a')) hs => do
      let pf1 : Q($P') ← withNestedExistsIntro fvars (body := newBody) do
        let pf ← go ha fvars hs path h_eq
        pure pf
      pure pf1
    let pf2 : Q(forall a : $α, $p a -> $P') ← mkLambdaFVars #[a, ha] pf1
    let pf3 : Q($P') := q(Exists.elim $h $pf2)
    mkLambdaFVars #[h] pf3
where
  /-- Traverses `P` and `goal` simultaneously, proving `goal`. -/
  go {goal P : Q(Prop)} (h : Q($P)) (exs : List VarQ) (hs : List HypQ) (path : Path)
    {u : Level} {α : Q(Sort u)} {a a' : Q($α)} (h_eq : Q($a = $a')) :
    MetaM Q($goal) := do
  match P with
  | ~q(@Exists $β $pb) =>
    match exs with
    | [] => assertUnreachable "mkBeforeToAfter: `P` is `Exists` but `exs` is empty"
    | ⟨v, γ, b⟩ :: exsTail =>
    let _ : u_1 =QL v := ⟨⟩
let _ : γ =Q β := ⟨⟩
    match hs with
    | [] => assertUnreachable "mkBeforeToAfter: `P` is `Exists` but `hs` is empty"
    | ⟨H, hb⟩ :: hsTail =>
let _ : H =Q pb b := ⟨⟩
    let pf : Q($goal) ← go hb exsTail hsTail path h_eq
    return pf
  | ~q(And $L $R) =>
    let ~q($L' ∧ $R') := goal
      | assertUnreachable "mkBeforeToAfter: `P` is `And` but `goal` is not `And`"
    match path with
    | [] => assertUnreachable "mkBeforeToAfter: `P` is `And` but `path` is empty"
    | .left :: tl =>
      let pa : Q($α -> Prop) ← mkLambdaFVars #[a] R
let _ : R =Q pa a := ⟨⟩
let _ : R' =Q pa a' := ⟨⟩
      let pfRight : Q($R) := q(And.right $h)
      let pfRight' : Q($R') := q(Eq.mp (congrArg $pa $h_eq) $pfRight)
      let pfLeft' : Q($L') ← go q(And.left $h) exs hs tl h_eq
      return q(And.intro $pfLeft' $pfRight')
    | .right :: tl =>
      let pa : Q($α -> Prop) ← mkLambdaFVars #[a] L
let _ : L =Q pa a := ⟨⟩
let _ : L' =Q pa a' := ⟨⟩
      let pfLeft : Q($L) := q(And.left $h)
      let pfLeft' : Q($L') := q(Eq.mp (congrArg $pa $h_eq) $pfLeft)
      let pfRight' : Q($R') ← go q(And.right $h) exs hs tl h_eq
      return q(And.intro $pfLeft' $pfRight')
  | _ =>
    let ~q($x = $y) := goal
      | assertUnreachable s!"mkBeforeToAfter: unexpected goal = {← ppExpr goal}"
    if !path.isEmpty then
      assertUnreachable "mkBeforeToAfter: goal is equality but path is not empty"
let _ : x =Q y := ⟨⟩
    return q(rfl)

/-- Triggers at goals of the form `∃ a, body` and checks if `body` allows a single value `a'`
for `a`. If so, replaces `a` with `a'` and removes quantifier.

It looks through nested quantifiers and conjunctions searching for a `a = a'`
or `a' = a` subexpression. -/
simproc ↓ existsAndEq (Exists _) := fun e => do
  let_expr f@Exists α p := e | return .continue
  lambdaBoundedTelescope p 1 fun xs (body : Q(Prop)) => withNewMCtxDepth do
    let some u := f.constLevels![0]? | unreachable!
    have α : Q(Sort $u) := α; have p : Q($α -> Prop) := p
    let some (a : Q($α)) := xs[0]? | return .continue
    let some path ← findEqPath a body | return .continue
    let (fvars, lctx, newBody, a') ← findEq a body path
    withLCtx' lctx do
      let newBody := newBody.replaceFVar a a'
      let P' : Q(Prop) ← mkNestedExists fvars newBody
      let pfBeforeAfter : Q((exists a, $p a) -> $P') ← mkBeforeToAfter a' newBody fvars path
      let pfAfterBefore : Q($P' -> (exists a, $p a)) ← mkAfterToBefore a' newBody fvars path
      let pf := q(propext (Iff.intro $pfBeforeAfter $pfAfterBefore))
return .visit Simp.ResultQ.mk _ some q($pf)

end ExistsAndEq

export ExistsAndEq (existsAndEq)
