/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init
public meta import Lean.CoreM
public meta import Lean.Util.FoldConsts

/-!
A rudimentary export format, adapted from
<https://github.com/leanprover-community/lean/blob/master/doc/export_format.md>
with support for Lean 4 kernel primitives.
-/

public meta section

open Lean
open Std (HashMap HashSet)

namespace Lean

namespace Export

/-! References -/

private opaque MethodsRefPointed : NonemptyType.{0}

/--
Definition of `MethodsRef` / `MethodsRef` 的定义

English:
definition MethodsRef
  signature: : Type
  body: MethodsRefPointed.type

中文:
定义 MethodsRef
  签名: : Type
  定义体: MethodsRefPointed.type
-/
private def MethodsRef : Type := MethodsRefPointed.type

/--
Inductive type `Entry` / 归纳类型 `Entry`

English:
inductive Entry
  constructors (4):
    - name: (n : Name)
    - level: (n : Level)
    - expr: (n : Expr)
    - defn: (n : Name)

中文:
归纳类型 Entry
  构造子 (4 个):
    - name: (n : Name)
    - level: (n : Level)
    - expr: (n : Expr)
    - defn: (n : Name)
-/
inductive Entry
  | name (n : Name)
  | level (n : Level)
  | expr (n : Expr)
  | defn (n : Name)
deriving Inhabited

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Name Entry
  body: ⟨Entry.name⟩

中文:
实例 :
  签名: Coe Name Entry
  定义体: ⟨Entry.name⟩

Depends on / 依赖: Entry.name
-/
instance : Coe Name Entry := ⟨Entry.name⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Level Entry
  body: ⟨Entry.level⟩

中文:
实例 :
  签名: Coe Level Entry
  定义体: ⟨Entry.level⟩

Depends on / 依赖: Entry.level
-/
instance : Coe Level Entry := ⟨Entry.level⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Expr Entry
  body: ⟨Entry.expr⟩

中文:
实例 :
  签名: Coe Expr Entry
  定义体: ⟨Entry.expr⟩

Depends on / 依赖: Entry.expr
-/
instance : Coe Expr Entry := ⟨Entry.expr⟩

/--
Definition of `Alloc` / `Alloc` 的定义

English:
structure Alloc
  parameters: (α) [BEq α] [Hashable α]
  axioms and operations (2):
    - map : Std.HashMap α Nat
    - next : Nat

中文:
结构 Alloc
  参数: (α) [BEq α] [Hashable α]
  公理与运算 (2 个):
    - map : Std.HashMap α 自然数
    - next : 自然数
-/
structure Alloc (α) [BEq α] [Hashable α] where
  map : Std.HashMap α Nat
  next : Nat
deriving Inhabited

/--
Definition of `State` / `State` 的定义

English:
structure State
  parameters: where
  axioms and operations (5):
    - names : Alloc Name  [default: ⟨(∅ : Std.HashMap Name Nat).insert Name.anonymous 0, 1⟩]
    - levels : Alloc Level  [default: ⟨(∅ : Std.HashMap Level Nat).insert .zero 0, 1⟩]
    - exprs : Alloc Expr
    - defs : Std.HashSet Name
    - stk : Array (Bool × Entry)

中文:
结构 State
  参数: where
  公理与运算 (5 个):
    - names : Alloc Name  [默认: ⟨(∅ : Std.HashMap Name Nat).insert Name.anonymous 0, 1⟩]
    - levels : Alloc Level  [默认: ⟨(∅ : Std.HashMap Level Nat).insert .zero 0, 1⟩]
    - exprs : Alloc Expr
    - defs : Std.HashSet Name
    - stk : Array (布尔 × Entry)

Depends on / 依赖: HashMap, Name.anonymous, Std.HashMap, anonymous, insert
-/
structure State where
  names : Alloc Name := ⟨(∅ : Std.HashMap Name Nat).insert Name.anonymous 0, 1⟩
  levels : Alloc Level := ⟨(∅ : Std.HashMap Level Nat).insert .zero 0, 1⟩
  exprs : Alloc Expr
  defs : Std.HashSet Name
  stk : Array (Bool × Entry)
deriving Inhabited

/--
Definition of `OfState` / `OfState` 的定义

English:
class OfState
  parameters: (α : Type) [BEq α] [Hashable α]
  axioms and operations (2):
    - get : State -> Alloc α
    - modify : (Alloc α -> Alloc α) -> State -> State

中文:
类 OfState
  参数: (α : Type) [BEq α] [Hashable α]
  公理与运算 (2 个):
    - get : State -> Alloc α
    - modify : (Alloc α -> Alloc α) -> State -> State
-/
class OfState (α : Type) [BEq α] [Hashable α] where
  get : State -> Alloc α
  modify : (Alloc α -> Alloc α) -> State -> State

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OfState Name
  body: s.names
  modify f s := { s with names := f s.names }

中文:
实例 :
  签名: OfState Name
  定义体: s.names
  modify f s := { s with names := f s.names }

Depends on / 依赖: s.names
-/
instance : OfState Name where
  get s := s.names
  modify f s := { s with names := f s.names }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OfState Level
  body: s.levels
  modify f s := { s with levels := f s.levels }

中文:
实例 :
  签名: OfState Level
  定义体: s.levels
  modify f s := { s with levels := f s.levels }

Depends on / 依赖: levels, s.levels
-/
instance : OfState Level where
  get s := s.levels
  modify f s := { s with levels := f s.levels }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OfState Expr
  body: s.exprs
  modify f s := { s with exprs := f s.exprs }

中文:
实例 :
  签名: OfState Expr
  定义体: s.exprs
  modify f s := { s with exprs := f s.exprs }

Depends on / 依赖: s.exprs
-/
instance : OfState Expr where
  get s := s.exprs
  modify f s := { s with exprs := f s.exprs }

end Export

/--
Definition of `ExportM` / `ExportM` 的定义

English:
abbreviation ExportM
  body: StateT Export.State CoreM

中文:
缩写 ExportM
  定义体: StateT Export.State CoreM

Depends on / 依赖: Export, Export.State, StateT
-/
abbrev ExportM := StateT Export.State CoreM

namespace Export

/--
Definition of `alloc` / `alloc` 的定义

English:
definition alloc
  signature: {α} [BEq α] [Hashable α] [OfState α] (a : α)
  body: do
  let n := (OfState.get (α := α) (← get)).next
modify OfState.modify (α := α) fun s => {map := s.map.insert a n, next := n + 1}
  pure n

中文:
定义 alloc
  签名: {α} [BEq α] [Hashable α] [OfState α] (a : α)
  定义体: do
  let n := (OfState.get (α := α) (← get)).next
modify OfState.modify (α := α) fun s => {map := s.map.insert a n, next := n + 1}
  pure n
-/
def alloc {α} [BEq α] [Hashable α] [OfState α] (a : α) : ExportM Nat := do
  let n := (OfState.get (α := α) (← get)).next
modify OfState.modify (α := α) fun s => {map := s.map.insert a n, next := n + 1}
  pure n

/--
Definition of `exportName` / `exportName` 的定义

English:
definition exportName
  signature: (n : Name)
  body: do
  match (← get).names.map[n]? with
  | some i => pure i
  | none => match n with
    | .anonymous => pure 0
    | .num p a => let i ← alloc n; IO.println s!"{i} #NI {← exportName p} {a}"; pure i
    | .str p s => let i ← alloc n; IO.println s!"{i} #NS {← exportName p} {s}"; pure i

中文:
定义 exportName
  签名: (n : Name)
  定义体: do
  match (← get).names.map[n]? with
  | some i => pure i
  | none => match n with
    | .anonymous => pure 0
    | .num p a => let i ← alloc n; IO.println s!"{i} #NI {← exportName p} {a}"; pure i
    | .str p s => let i ← alloc n; IO.println s!"{i} #NS {← exportName p} {s}"; pure i
-/
def exportName (n : Name) : ExportM Nat := do
  match (← get).names.map[n]? with
  | some i => pure i
  | none => match n with
    | .anonymous => pure 0
    | .num p a => let i ← alloc n; IO.println s!"{i} #NI {← exportName p} {a}"; pure i
    | .str p s => let i ← alloc n; IO.println s!"{i} #NS {← exportName p} {s}"; pure i

/--
Definition of `exportLevel` / `exportLevel` 的定义

English:
definition exportLevel
  signature: (L : Level)
  body: do
  match (← get).levels.map[L]? with
  | some i => pure i
  | none => match L with
    | .zero => pure 0
    | .succ l =>
      let i ← alloc L; IO.println s!"{i} #US {← exportLevel l}"; pure i
    | .max l₁ l₂ =>
      let i ← alloc L; IO.println s!"{i} #UM {← exportLevel l₁} {← exportLevel l₂}";

中文:
定义 exportLevel
  签名: (L : Level)
  定义体: do
  match (← get).levels.map[L]? with
  | some i => pure i
  | none => match L with
    | .zero => pure 0
    | .succ l =>
      let i ← alloc L; IO.println s!"{i} #US {← exportLevel l}"; pure i
    | .max l₁ l₂ =>
      let i ← alloc L; IO.println s!"{i} #UM {← exportLevel l₁} {← exportLevel l₂}";
-/
def exportLevel (L : Level) : ExportM Nat := do
  match (← get).levels.map[L]? with
  | some i => pure i
  | none => match L with
    | .zero => pure 0
    | .succ l =>
      let i ← alloc L; IO.println s!"{i} #US {← exportLevel l}"; pure i
    | .max l₁ l₂ =>
      let i ← alloc L; IO.println s!"{i} #UM {← exportLevel l₁} {← exportLevel l₂}"; pure i
    | .imax l₁ l₂ =>
      let i ← alloc L; IO.println s!"{i} #UIM {← exportLevel l₁} {← exportLevel l₂}"; pure i
    | .param n =>
      let i ← alloc L; IO.println s!"{i} #UP {← exportName n}"; pure i
    | .mvar _ => unreachable!

/--
Definition of `biStr` / `biStr` 的定义

English:
definition biStr
  signature: : BinderInfo -> String

中文:
定义 biStr
  签名: : BinderInfo -> String
-/
def biStr : BinderInfo -> String
  | BinderInfo.default => "#BD"
  | BinderInfo.implicit => "#BI"
  | BinderInfo.strictImplicit => "#BS"
  | BinderInfo.instImplicit => "#BC"

open ConstantInfo in
mutual

/--
Definition of `exportExpr` / `exportExpr` 的定义

English:
definition exportExpr
  signature: (E : Expr)
  body: do
  match (← get).exprs.map[E]? with
  | some i => pure i
  | none => match E with
    | .bvar n => let i ← alloc E; IO.println s!"{i} #EV {n}"; pure i
    | .fvar _ => unreachable!
    | .mvar _ => unreachable!
    | .sort l => let i ← alloc E; IO.println s!"{i} #ES {← exportLevel l}"; pure i
    

中文:
定义 exportExpr
  签名: (E : Expr)
  定义体: do
  match (← get).exprs.map[E]? with
  | some i => pure i
  | none => match E with
    | .bvar n => let i ← alloc E; IO.println s!"{i} #EV {n}"; pure i
    | .fvar _ => unreachable!
    | .mvar _ => unreachable!
    | .sort l => let i ← alloc E; IO.println s!"{i} #ES {← exportLevel l}"; pure i
    
-/
partial def exportExpr (E : Expr) : ExportM Nat := do
  match (← get).exprs.map[E]? with
  | some i => pure i
  | none => match E with
    | .bvar n => let i ← alloc E; IO.println s!"{i} #EV {n}"; pure i
    | .fvar _ => unreachable!
    | .mvar _ => unreachable!
    | .sort l => let i ← alloc E; IO.println s!"{i} #ES {← exportLevel l}"; pure i
    | .const n ls =>
      exportDef n
      let i ← alloc E
      let mut s := s!"{i} #EC {← exportName n}"
      for l in ls do s := s ++ s!" {← exportLevel l}"
      IO.println s; pure i
    | .app e₁ e₂ =>
      let i ← alloc E; IO.println s!"{i} #EA {← exportExpr e₁} {← exportExpr e₂}"; pure i
    | .lam _ e₁ e₂ d =>
      let i ← alloc E
      IO.println s!"{i} #EL {biStr d} {← exportExpr e₁} {← exportExpr e₂}"; pure i
    | .forallE _ e₁ e₂ d =>
      let i ← alloc E
      IO.println s!"{i} #EP {biStr d} {← exportExpr e₁} {← exportExpr e₂}"; pure i
    | .letE _ e₁ e₂ e₃ _ =>
      let i ← alloc E
      IO.println s!"{i} #EP {← exportExpr e₁} {← exportExpr e₂} {← exportExpr e₃}"; pure i
    | .lit (.natVal n) => let i ← alloc E; IO.println s!"{i} #EN {n}"; pure i
    | .lit (.strVal s) => let i ← alloc E; IO.println s!"{i} #ET {s}"; pure i
    | .mdata _ _ => unreachable!
    | .proj n k e =>
      let i ← alloc E; IO.println s!"{i} #EJ {← exportName n} {k} {← exportExpr e}"; pure i

/--
Definition of `exportDef` / `exportDef` 的定义

English:
definition exportDef
  signature: (n : Name)
  body: do
  if (← get).defs.contains n then return
  let ci ← getConstInfo n
  for c in ci.value!.getUsedConstants do
    unless (← get).defs.contains c do
      exportDef c
  match ci with
  | axiomInfo val => axdef "#AX" val.name val.type val.levelParams
  | defnInfo val => defn "#DEF" val.name val.type 

中文:
定义 exportDef
  签名: (n : Name)
  定义体: do
  if (← get).defs.contains n then return
  let ci ← getConstInfo n
  for c in ci.value!.getUsedConstants do
    unless (← get).defs.contains c do
      exportDef c
  match ci with
  | axiomInfo val => axdef "#AX" val.name val.type val.levelParams
  | defnInfo val => defn "#DEF" val.name val.type 
-/
partial def exportDef (n : Name) : ExportM Unit := do
  if (← get).defs.contains n then return
  let ci ← getConstInfo n
  for c in ci.value!.getUsedConstants do
    unless (← get).defs.contains c do
      exportDef c
  match ci with
  | axiomInfo val => axdef "#AX" val.name val.type val.levelParams
  | defnInfo val => defn "#DEF" val.name val.type val.value val.levelParams
  | thmInfo val => defn "#THM" val.name val.type val.value val.levelParams
  | opaqueInfo val => defn "#CN" val.name val.type val.value val.levelParams
  | quotInfo _ =>
    IO.println "#QUOT"
    for n in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
      insert n
  | inductInfo val => ind val.all
  | ctorInfo val => ind (← getConstInfoInduct val.induct).all
  | recInfo val => ind val.all
where
  insert (n : Name) : ExportM Unit :=
    modify fun s => { s with defs := s.defs.insert n }
  defn (ty : String) (n : Name) (t e : Expr) (ls : List Name) : ExportM Unit := do
    let mut s := s!"{ty} {← exportName n} {← exportExpr t} {← exportExpr e}"
    for l in ls do s := s ++ s!" {← exportName l}"
    IO.println s
    insert n
  axdef (ty : String) (n : Name) (t : Expr) (ls : List Name) : ExportM Unit := do
    let mut s := s!"{ty} {← exportName n} {← exportExpr t}"
    for l in ls do s := s ++ s!" {← exportName l}"
    IO.println s
    insert n
  ind : List Name -> ExportM Unit
  | [] => unreachable!
  | is@(i::_) => do
    let val ← getConstInfoInduct i
    let mut s := match is.length with
    | 1 => s!"#IND {val.numParams}"
    | n => s!"#MUT {val.numParams} {n}"
    for j in is do insert j; insert (mkRecName j)
    for j in is do
      let val ← getConstInfoInduct j
      s := s ++ s!" {← exportName val.name} {← exportExpr val.type} {val.ctors.length}"
      for c in val.ctors do
        insert c
        s := s ++ s!" {← exportName c} {← exportExpr (← getConstInfoCtor c).type}"
    for j in is do s ← indbody j s
    for l in val.levelParams do s := s ++ s!" {← exportName l}"
    IO.println s
  indbody (ind : Name) (s : String) : ExportM String := do
    let val ← getConstInfoInduct ind
    let mut s := s ++ s!" {← exportName ind} {← exportExpr val.type} {val.ctors.length}"
    for c in val.ctors do
      s := s ++ s!" {← exportName c} {← exportExpr (← getConstInfoCtor c).type}"
    pure s

end

/--
Definition of `runExportM` / `runExportM` 的定义

English:
definition runExportM
  signature: {α : Type} (m : ExportM α)
  body: m.run' default

中文:
定义 runExportM
  签名: {α : Type} (m : ExportM α)
  定义体: m.run' default

Depends on / 依赖: m.run
-/
def runExportM {α : Type} (m : ExportM α) : CoreM α := m.run' default

-- #eval runExportM (exportDef `Lean.Expr)
end Export

end Lean
