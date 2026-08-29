/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init

/-!
# Basic Definitions for `RefinedDiscrTree`

We define
* `Key`, the discrimination tree key
* `LazyEntry`, the partial, lazy computation of a sequence of `Key`s
* `Trie`, a node of the discrimination tree, which is indexed with `Key`s
  and stores an array of pending `LazyEntry`s
* `RefinedDiscrTree`, the discrimination tree itself.
-/

@[expose] public section

namespace Lean.Meta.RefinedDiscrTree


/--
Inductive type `Key` / 归纳类型 `Key`

English:
inductive Key
  parameters: where
  constructors (11):
    - star: 
    - labelledStar: (id : Nat)
    - opaque: 
    - const: (declName : Name) (nargs : Nat)
    - fvar: (fvarId : FVarId) (nargs : Nat)
    - bvar: (deBruijnIndex nargs : Nat)
    - lit: (v : Literal)
    - sort: 
    - lam: 
    - forall: 
    - proj: (typeName : Name) (idx nargs : Nat)

中文:
归纳类型 Key
  参数: where
  构造子 (11 个):
    - star: 
    - labelledStar: (id : 自然数)
    - opaque: 
    - const: (declName : Name) (nargs : 自然数)
    - fvar: (fvarId : FVarId) (nargs : 自然数)
    - bvar: (deBruijnIndex nargs : 自然数)
    - lit: (v : Literal)
    - sort: 
    - lam: 
    - forall: 
    - proj: (typeName : Name) (idx nargs : 自然数)
-/
inductive Key where
  /-- A metavariable. This key matches with anything. -/
  | star
  /-- A metavariable. This key matches with anything. It stores an identifier. -/
  | labelledStar (id : Nat)
  /-- An opaque variable. This key only matches with `Key.star`. -/
  | opaque
  /-- A constant. It stores the name and the arity. -/
  | const (declName : Name) (nargs : Nat)
  /-- A free variable. It stores the `FVarId` and the arity. -/
  | fvar (fvarId : FVarId) (nargs : Nat)
  /-- A bound variable, from a lambda or forall binder.
  It stores the De Bruijn index and the arity. -/
  | bvar (deBruijnIndex nargs : Nat)
  /-- A literal. -/
  | lit (v : Literal)
  /-- A sort. Universe levels are ignored. -/
  | sort
  /-- A lambda function. -/
  | lam
  /-- A dependent arrow. -/
  | forall
  /-- A projection. It stores the structure name, the projection index and the arity. -/
  | proj (typeName : Name) (idx nargs : Nat)
  deriving Inhabited, BEq

/--
Definition of `Key.hash` / `Key.hash` 的定义

English:
definition Key.hash
  signature: : Key -> UInt64

中文:
定义 Key.hash
  签名: : Key -> U整数64
-/
protected def Key.hash : Key -> UInt64
  | .star => 0
| .labelledStar id => mixHash 5 hash id
  | .opaque => 1
  | .const name _ => hash name
| .fvar fvarId nargs => mixHash 6 mixHash (hash fvarId) (hash nargs)
| .bvar idx nargs => mixHash 7 mixHash (hash idx) (hash nargs)
| .lit v => mixHash 8 hash v
  | .sort => 2
  | .lam => 3
  | .«forall» => 4
| .proj name idx nargs => mixHash (hash nargs) mixHash (hash name) (hash idx)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Hashable Key
  body: ⟨Key.hash⟩

中文:
实例 :
  签名: Hashable Key
  定义体: ⟨Key.hash⟩

Depends on / 依赖: Key.hash
-/
instance : Hashable Key := ⟨Key.hash⟩

/--
Definition of `Key.format` / `Key.format` 的定义

English:
definition Key.format
  signature: : Key -> Format

中文:
定义 Key.format
  签名: : Key -> Format
-/
def Key.format : Key -> Format
  | .star => f!"*"
  | .labelledStar id => f!"*{id}"
  | .opaque => "◾"
  | .const name nargs => f!"⟨{name}, {nargs}⟩"
  | .fvar fvarId nargs => f!"⟨{fvarId.name}, {nargs}⟩"
  | .lit (Literal.natVal n) => f!"{n}"
  | .lit (Literal.strVal s) => f!"{s.quote}"
  | .sort => "Sort"
  | .bvar i nargs => f!"⟨#{i}, {nargs}⟩"
  | .lam => "fun"
  | .forall => "forall"
  | .proj name idx nargs => f!"⟨{name}.{idx}, {nargs}⟩"

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToFormat Key
  body: ⟨Key.format⟩

中文:
实例 :
  签名: ToFormat Key
  定义体: ⟨Key.format⟩

Depends on / 依赖: Key.format, format
-/
instance : ToFormat Key := ⟨Key.format⟩

/--
Definition of `keysAsPattern` / `keysAsPattern` 的定义

English:
definition keysAsPattern
  signature: (keys : Array Key)
  body: do
.run keys.toList let (msg, keys) ← go (paren := false)
  if !keys.isEmpty then
    throwError "illegal discrimination tree entry: {keys.map Key.format}"
  return msg

中文:
定义 keysAsPattern
  签名: (keys : Array Key)
  定义体: do
.run keys.toList let (msg, keys) ← go (paren := false)
  if !keys.isEmpty then
    throwError "illegal discrimination tree entry: {keys.map Key.format}"
  return msg
-/
partial def keysAsPattern (keys : Array Key) : CoreM MessageData := do
.run keys.toList let (msg, keys) ← go (paren := false)
  if !keys.isEmpty then
    throwError "illegal discrimination tree entry: {keys.map Key.format}"
  return msg
where
  /-- Get the next key. -/
  next : StateRefT (List Key) CoreM Key := do
    let key :: keys ← get | throwError "illegal discrimination tree entry: {keys.map Key.format}"
    set keys
    return key
  /-- Format the application `f args`. -/
  mkApp (f : MessageData) (nargs : Nat) (paren : Bool) : StateRefT (List Key) CoreM MessageData :=
    if nargs == 0 then
      return f
    else do
      let mut r := m!""
      for _ in [:nargs] do
        r := r ++ Format.line ++ (← go)
      r := f ++ .nest 2 r
      if paren then
        return .paren r
      else
        return .group r

  /-- Format the next expression. -/
  go (paren := true) : StateRefT (List Key) CoreM MessageData := do
    let key ← next
    match key with
    | .const declName nargs =>
      mkApp m!"{← mkConstWithLevelParams declName}" nargs paren
    | .fvar fvarId nargs =>
      mkApp m!"{mkFVar fvarId}" nargs paren
    | .proj _ i nargs =>
      mkApp m!"{← go}.{i+1}" nargs paren
    | .bvar i nargs =>
      mkApp m!"#{i}" nargs paren
    | .lam =>
      return parenthesize m!"fun, {← go (paren := false)}" paren
    | .forall =>
      return parenthesize m!"{← go} -> {← go (paren := false)}" paren
    | _ => return key.format
  /-- Add parentheses if `paren == true`. -/
  parenthesize (msg : MessageData) (paren : Bool) : MessageData :=
    if paren then msg.paren else msg.group

/--
Definition of `Key.arity` / `Key.arity` 的定义

English:
definition Key.arity
  signature: : Key -> Nat

中文:
定义 Key.arity
  签名: : Key -> 自然数
-/
def Key.arity : Key -> Nat
  | .const _ nargs => nargs
  | .fvar _ nargs => nargs
  | .bvar _ nargs => nargs
  | .lam => 1
  | .forall => 2
  | .proj _ _ nargs => nargs + 1
  | _ => 0

/--
Definition of `ExprInfo` / `ExprInfo` 的定义

English:
structure ExprInfo
  parameters: where
  axioms and operations (5):
    - expr : Expr
    - bvars : List FVarId  [default: []]
    - lctx : LocalContext
    - localInsts : LocalInstances
    - cfg : Config

中文:
结构 ExprInfo
  参数: where
  公理与运算 (5 个):
    - expr : Expr
    - bvars : List FVarId  [默认: []]
    - lctx : LocalContext
    - localInsts : LocalInstances
    - cfg : Config
-/
structure ExprInfo where
  /-- The expression -/
  expr : Expr
  /-- Variables that come from a lambda or forall binder.
  The list index gives the De Bruijn index. -/
  bvars : List FVarId := []
  /-- The local context, which contains the introduced bound variables. -/
  lctx : LocalContext
  /-- The local instances, which may contain the introduced bound variables. -/
  localInsts : LocalInstances
  /-- The `Meta.Config` used by this entry. -/
  cfg : Config

/--
Definition of `mkExprInfo` / `mkExprInfo` 的定义

English:
definition mkExprInfo
  signature: (expr : Expr) (bvars : List FVarId)
  body: return {
    expr, bvars,
    lctx := ← getLCtx
    localInsts := ← getLocalInstances
    cfg := ← getConfig
  }

中文:
定义 mkExprInfo
  签名: (expr : Expr) (bvars : List FVarId)
  定义体: return {
    expr, bvars,
    lctx := ← getLCtx
    localInsts := ← getLocalInstances
    cfg := ← getConfig
  }

Depends on / 依赖: getConfig, getLCtx, getLocalInstances, localInsts, return
-/
def mkExprInfo (expr : Expr) (bvars : List FVarId) : MetaM ExprInfo :=
  return {
    expr, bvars,
    lctx := ← getLCtx
    localInsts := ← getLocalInstances
    cfg := ← getConfig
  }

/--
Inductive type `StackEntry` / 归纳类型 `StackEntry`

English:
inductive StackEntry
  parameters: where
  constructors (2):
    - star: 
    - expr: (info : ExprInfo)

中文:
归纳类型 StackEntry
  参数: where
  构造子 (2 个):
    - star: 
    - expr: (info : ExprInfo)
-/
inductive StackEntry where
  /-- `.star` is an expression that will not be explicitly indexed. -/
  | star
  /-- `.expr` is an expression that will be indexed. -/
  | expr (info : ExprInfo)

/--
Definition of `StackEntry.format` / `StackEntry.format` 的定义

English:
definition StackEntry.format
  signature: : StackEntry -> Format

中文:
定义 StackEntry.format
  签名: : StackEntry -> Format
-/
def StackEntry.format : StackEntry -> Format
  | .star => f!".star"
  | .expr info => f!".expr {info.expr}"

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToFormat StackEntry
  body: ⟨StackEntry.format⟩

中文:
实例 :
  签名: ToFormat StackEntry
  定义体: ⟨StackEntry.format⟩

Depends on / 依赖: StackEntry, StackEntry.format, format
-/
instance : ToFormat StackEntry := ⟨StackEntry.format⟩

/--
Definition of `LazyEntry` / `LazyEntry` 的定义

English:
structure LazyEntry
  parameters: where
  axioms and operations (5):
    - previous : Option ExprInfo  [default: none]
    - stack : List StackEntry  [default: []]
    - mctx : MetavarContext
    - labelledStars? : Option (Array MVarId)
    - computedKeys : List Key  [default: []]

中文:
结构 LazyEntry
  参数: where
  公理与运算 (5 个):
    - previous : Option ExprInfo  [默认: none]
    - stack : List StackEntry  [默认: []]
    - mctx : MetavarContext
    - labelledStars? : Option (Array MVarId)
    - computedKeys : List Key  [默认: []]
-/
structure LazyEntry where
  /--
  If an expression creates more entries in the stack, for example because it is an application,
  then instead of pushing to the stack greedily, we only extend the stack once we need to.
  So, the field `previous` is used to extend the `stack` before looking in the `stack`.

  For example in `10.add (20.add 30)`, after computing the key `⟨Nat.add, 2⟩`, the stack is still
  empty, and `previous` will be `10.add (20.add 30)`.
  -/
  previous : Option ExprInfo := none
  /--
  The stack, used to emulate recursion. It contains the list of all expressions for which the
  keys still need to be computed, in that order.

  For example in `10.add (20.add 30)`, after computing the keys `⟨Nat.add, 2⟩` and `10`, the stack
  will be a list of length 1 containing the expression `20.add 30`.
  -/
  stack : List StackEntry := []
  /-- The metavariable context, which may contain variables appearing in this entry. -/
  mctx : MetavarContext
  /--
  `MVarId`s corresponding to the `.labelledStar` labels. The index in the array is the label.
  It is `none` if we use `.star` instead of `labelledStar`,
  for example when encoding the lookup expression.
  -/
  labelledStars? : Option (Array MVarId)
  /--
  The `Key`s that have already been computed.

  Sometimes, more than one `Key` ends up being computed in one go. This happens when
  there are lambda binders (because it depends on the body whether the lambda key
  should be indexed or not). In that case the remaining `Key`s are stored in `results`.
  -/
  computedKeys : List Key := []
deriving Inhabited

/--
Definition of `mkInitLazyEntry` / `mkInitLazyEntry` 的定义

English:
definition mkInitLazyEntry
  signature: (labelledStars : Bool)
  body: return {
    mctx := ← getMCtx
    labelledStars? := if labelledStars then some #[] else none
  }

中文:
定义 mkInitLazyEntry
  签名: (labelledStars : 布尔)
  定义体: return {
    mctx := ← getMCtx
    labelledStars? := if labelledStars then some #[] else none
  }

Depends on / 依赖: getMCtx, labelledStars, return
-/
def mkInitLazyEntry (labelledStars : Bool) : MetaM LazyEntry :=
  return {
    mctx := ← getMCtx
    labelledStars? := if labelledStars then some #[] else none
  }

/--
Definition of `LazyEntry.format` / `LazyEntry.format` 的定义

English:
definition LazyEntry.format
  signature: (entry : LazyEntry)
  body: Id.run do
  let mut parts := #[f!"stack: {entry.stack}"]
  unless entry.computedKeys == [] do
    parts := parts.push f!"results: {entry.computedKeys}"
  if let some info := entry.previous then
    parts := parts.push f!"todo: {info.expr}"
  return Format.joinSep parts.toList ", "

中文:
定义 LazyEntry.format
  签名: (entry : LazyEntry)
  定义体: Id.run do
  let mut parts := #[f!"stack: {entry.stack}"]
  unless entry.computedKeys == [] do
    parts := parts.push f!"results: {entry.computedKeys}"
  if let some info := entry.previous then
    parts := parts.push f!"todo: {info.expr}"
  return Format.joinSep parts.toList ", "

Depends on / 依赖: Id.run
-/
def LazyEntry.format (entry : LazyEntry) : Format := Id.run do
  let mut parts := #[f!"stack: {entry.stack}"]
  unless entry.computedKeys == [] do
    parts := parts.push f!"results: {entry.computedKeys}"
  if let some info := entry.previous then
    parts := parts.push f!"todo: {info.expr}"
  return Format.joinSep parts.toList ", "

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToFormat LazyEntry
  body: ⟨LazyEntry.format⟩

中文:
实例 :
  签名: ToFormat LazyEntry
  定义体: ⟨LazyEntry.format⟩

Depends on / 依赖: LazyEntry, LazyEntry.format, format
-/
instance : ToFormat LazyEntry := ⟨LazyEntry.format⟩

/--
Definition of `TrieIndex` / `TrieIndex` 的定义

English:
abbreviation TrieIndex
  body: Nat

中文:
缩写 TrieIndex
  定义体: Nat
-/
abbrev TrieIndex := Nat

/--
Definition of `Trie` / `Trie` 的定义

English:
structure Trie
  parameters: (α : Type)
  axioms and operations (1):
    - node : : values : Array α star : Option TrieIndex labelledStars : Std.HashMap Nat TrieIndex children : Std.HashMap Key TrieIndex pending : Array (LazyEntry × α)

中文:
结构 Trie
  参数: (α : Type)
  公理与运算 (1 个):
    - node : : values : Array α star : Option TrieIndex labelledStars : Std.HashMap 自然数 TrieIndex children : Std.HashMap Key TrieIndex pending : Array (LazyEntry × α)
-/
structure Trie (α : Type) where
  node ::
    /-- Return values, at a leaf -/
    values : Array α
    /-- Following `Trie`s based on a `Key.star`. -/
    star : Option TrieIndex
    /-- Following `Trie`s based on a `Key.labelledStar`. -/
    labelledStars : Std.HashMap Nat TrieIndex
    /-- Following `Trie`s based on the `Key`. -/
    children : Std.HashMap Key TrieIndex
    /-- Lazy entries that still have to be evaluated. -/
    pending : Array (LazyEntry × α)

instance {α : Type} : Inhabited (Trie α) := ⟨.node #[] none {} {} #[]⟩

end RefinedDiscrTree

open RefinedDiscrTree in

/--
Definition of `RefinedDiscrTree` / `RefinedDiscrTree` 的定义

English:
structure RefinedDiscrTree
  parameters: (α : Type)
  axioms and operations (2):
    - root : Std.HashMap Key TrieIndex  [default: {}]
    - tries : Array (Trie α)  [default: #[]]

中文:
结构 RefinedDiscrTree
  参数: (α : Type)
  公理与运算 (2 个):
    - root : Std.HashMap Key TrieIndex  [默认: {}]
    - tries : Array (Trie α)  [默认: #[]]
-/
structure RefinedDiscrTree (α : Type) where
  /-- `Trie`s at the root based of the `Key`. -/
  root : Std.HashMap Key TrieIndex := {}
  /-- Array of trie entries. Should be owned by this trie. -/
  tries : Array (Trie α) := #[]
deriving Inhabited

namespace RefinedDiscrTree

variable {α : Type}

/--
Definition of `format` / `format` 的定义

English:
definition format
  signature: [ToFormat α] (tree : RefinedDiscrTree α)
  body: let lines := tree.root.fold (init := #[]) fun lines key trie =>
    lines.push (Format.nest 2 f!"{key} =>{Format.line}{go trie}")
  if lines.size = 0 then
    f!"<empty discrimination tree>"
  else
    "Discrimination tree flowchart:\n" ++ Format.joinSep lines.toList "\n"

中文:
定义 format
  签名: [ToFormat α] (tree : RefinedDiscrTree α)
  定义体: let lines := tree.root.fold (init := #[]) fun lines key trie =>
    lines.push (Format.nest 2 f!"{key} =>{Format.line}{go trie}")
  if lines.size = 0 then
    f!"<empty discrimination tree>"
  else
    "Discrimination tree flowchart:\n" ++ Format.joinSep lines.toList "\n"
-/
partial def format [ToFormat α] (tree : RefinedDiscrTree α) : Format :=
  let lines := tree.root.fold (init := #[]) fun lines key trie =>
    lines.push (Format.nest 2 f!"{key} =>{Format.line}{go trie}")
  if lines.size = 0 then
    f!"<empty discrimination tree>"
  else
    "Discrimination tree flowchart:\n" ++ Format.joinSep lines.toList "\n"
where
  /-- Auxiliary function for `RefinedDiscrTree.format`. -/
  go (trie : TrieIndex) : Format := Id.run do
    let { values, star, labelledStars, children, pending } := tree.tries[trie]!
    let mut lines := #[]
    unless pending.isEmpty do
      lines := lines.push f!"pending entries: {pending.map (·.2)}"
    unless values.isEmpty do
      lines := lines.push f!"entries: {values}"
    if let some trie := star then
      lines := lines.push (Format.nest 2 f!"* =>{Format.line}{go trie}")
    lines := labelledStars.fold (init := lines) fun lines key trie =>
      lines.push (Format.nest 2 f!"*{key} =>{Format.line}{go trie}")
    lines := children.fold (init := lines) fun lines key trie =>
      lines.push (Format.nest 2 f!"{key} =>{Format.line}{go trie}")
    if lines.isEmpty then
      f!"<empty node>"
    else
      Format.joinSep lines.toList "\n"

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ToFormat
  signature: α] : ToFormat (RefinedDiscrTree α)
  body: ⟨format⟩

中文:
实例 [ToFormat
  签名: α] : ToFormat (RefinedDiscrTree α)
  定义体: ⟨format⟩

Depends on / 依赖: format
-/
instance [ToFormat α] : ToFormat (RefinedDiscrTree α) := ⟨format⟩

end Lean.Meta.RefinedDiscrTree
