/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Lean.Meta.RefinedDiscrTree.Basic
public import Lean.Meta.CompletionName

/-!
# Constructing a RefinedDiscrTree

`RefinedDiscrTree` is lazy, so to add an entry, we need to compute
the first `Key` and a `LazyEntry`. These are computed by `initializeLazyEntry`.

We provide `RefinedDiscrTree.insert` for directly performing this insert.

For initializing a `RefinedDiscrTree` using all imported constants,
we provide `createImportedDiscrTree`, which loops through all imported constants,
and does this with a parallel computation.

There is also `createModuleDiscrTree` which does the same but with the constants
from the current file.

-/

public section

namespace Lean.Meta.RefinedDiscrTree

variable {α : Type}

/--
Definition of `insert` / `insert` 的定义

English:
definition insert
  signature: (d : RefinedDiscrTree α) (key : Key) (entry : LazyEntry × α)
  body: if let some trie := d.root[key]? then
    { d with
      tries := d.tries.modify trie fun node => { node with pending := node.pending.push entry } }
  else
    { d with
      root := d.root.insert key d.tries.size
tries := d.tries.push .node #[] none {} {} #[entry] }

中文:
定义 insert
  签名: (d : RefinedDiscrTree α) (key : Key) (entry : LazyEntry × α)
  定义体: if let some trie := d.root[key]? then
    { d with
      tries := d.tries.modify trie fun node => { node with pending := node.pending.push entry } }
  else
    { d with
      root := d.root.insert key d.tries.size
tries := d.tries.push .node #[] none {} {} #[entry] }

Depends on / 依赖: d.root, d.root.insert, d.tries.modify, d.tries.push, d.tries.size, insert, modify, node.pending.push, pending
-/
def insert (d : RefinedDiscrTree α) (key : Key) (entry : LazyEntry × α) : RefinedDiscrTree α :=
  if let some trie := d.root[key]? then
    { d with
      tries := d.tries.modify trie fun node => { node with pending := node.pending.push entry } }
  else
    { d with
      root := d.root.insert key d.tries.size
tries := d.tries.push .node #[] none {} {} #[entry] }

/--
Definition of `PreDiscrTree` / `PreDiscrTree` 的定义

English:
structure PreDiscrTree
  parameters: (α : Type)
  axioms and operations (2):
    - root : Std.HashMap Key Nat  [default: {}]
    - tries : Array (Array (LazyEntry × α))  [default: #[]]

中文:
结构 PreDiscrTree
  参数: (α : 类型)
  公理与运算 (2 个):
    - root : Std.HashMap Key 自然数  [默认: {}]
    - tries : 数组 (数组 (LazyEntry × α))  [默认: #[]]
-/
structure PreDiscrTree (α : Type) where
  /-- Maps keys to index in tries array. -/
  root : Std.HashMap Key Nat := {}
  /-- Lazy entries for root of trie. -/
  tries : Array (Array (LazyEntry × α)) := #[]
  deriving Inhabited

namespace PreDiscrTree

@[specialize]
/--
Definition of `modifyAt` / `modifyAt` 的定义

English:
definition modifyAt
  signature: (d : PreDiscrTree α) (k : Key)
  body: let { root, tries } := d
  match root[k]? with
  | none =>
    { root := root.insert k tries.size, tries := tries.push (f #[]) }
  | some i =>
    { root, tries := tries.modify i f }

中文:
定义 modifyAt
  签名: (d : PreDiscrTree α) (k : Key)
  定义体: let { root, tries } := d
  match root[k]? with
  | none =>
    { root := root.insert k tries.size, tries := tries.push (f #[]) }
  | some i =>
    { root, tries := tries.modify i f }
-/
private def modifyAt (d : PreDiscrTree α) (k : Key)
    (f : Array (LazyEntry × α) -> Array (LazyEntry × α)) : PreDiscrTree α :=
  let { root, tries } := d
  match root[k]? with
  | none =>
    { root := root.insert k tries.size, tries := tries.push (f #[]) }
  | some i =>
    { root, tries := tries.modify i f }

/--
Definition of `push` / `push` 的定义

English:
definition push
  signature: (d : PreDiscrTree α) (k : Key) (e : LazyEntry × α)
  body: d.modifyAt k (·.push e)

中文:
定义 push
  签名: (d : PreDiscrTree α) (k : Key) (e : LazyEntry × α)
  定义体: d.modifyAt k (·.push e)

Depends on / 依赖: d.modifyAt, modifyAt
-/
def push (d : PreDiscrTree α) (k : Key) (e : LazyEntry × α) : PreDiscrTree α :=
  d.modifyAt k (·.push e)

/--
Definition of `toRefinedDiscrTree` / `toRefinedDiscrTree` 的定义

English:
definition toRefinedDiscrTree
  signature: (d : PreDiscrTree α)
  body: let { root, tries } := d
  { root, tries := tries.map fun pending => .node #[] none {} {} pending }

中文:
定义 toRefinedDiscrTree
  签名: (d : PreDiscrTree α)
  定义体: let { root, tries } := d
  { root, tries := tries.map fun pending => .node #[] none {} {} pending }

Depends on / 依赖: pending, tries.map
-/
def toRefinedDiscrTree (d : PreDiscrTree α) : RefinedDiscrTree α :=
  let { root, tries } := d
  { root, tries := tries.map fun pending => .node #[] none {} {} pending }

/--
Definition of `append` / `append` 的定义

English:
definition append
  signature: (x y : PreDiscrTree α)
  body: let (x, y, f) :=
    if x.root.size >= y.root.size then
      (x, y, fun y x => x ++ y)
    else
      (y, x, fun x y => x ++ y)
  let { root := yk, tries := ya } := y
  yk.fold (init := x) fun d k yi => d.modifyAt k (f ya[yi]!)

中文:
定义 append
  签名: (x y : PreDiscrTree α)
  定义体: let (x, y, f) :=
    if x.root.size >= y.root.size then
      (x, y, fun y x => x ++ y)
    else
      (y, x, fun x y => x ++ y)
  let { root := yk, tries := ya } := y
  yk.fold (init := x) fun d k yi => d.modifyAt k (f ya[yi]!)

Depends on / 依赖: d.modifyAt, modifyAt, x.root.size, y.root.size, yk.fold
-/
def append (x y : PreDiscrTree α) : PreDiscrTree α :=
  let (x, y, f) :=
    if x.root.size >= y.root.size then
      (x, y, fun y x => x ++ y)
    else
      (y, x, fun x y => x ++ y)
  let { root := yk, tries := ya } := y
  yk.fold (init := x) fun d k yi => d.modifyAt k (f ya[yi]!)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Append (PreDiscrTree α)
  body: PreDiscrTree.append

中文:
实例 :
  签名: Append (PreDiscrTree α)
  定义体: PreDiscrTree.append

Depends on / 依赖: PreDiscrTree, PreDiscrTree.append, append
-/
instance : Append (PreDiscrTree α) where
  append := PreDiscrTree.append

end PreDiscrTree


/--
Definition of `ImportFailure` / `ImportFailure` 的定义

English:
structure ImportFailure
  parameters: where
  axioms and operations (3):
    - module : Name
    - const : Name
    - exception : Exception

中文:
结构 ImportFailure
  参数: where
  公理与运算 (3 个):
    - module : Name
    - const : Name
    - exception : Exception
-/
private structure ImportFailure where
  /-- Module containing the constant whose import failed. -/
  module : Name
  /-- Constant whose import failed. -/
  const : Name
  /-- Exception that triggered the error. -/
  exception : Exception

/--
Definition of `ImportErrorData` / `ImportErrorData` 的定义

English:
structure ImportErrorData
  parameters: where
  axioms and operations (1):
    - errors : IO.Ref (Array ImportFailure)

中文:
结构 ImportErrorData
  参数: where
  公理与运算 (1 个):
    - errors : IO.Ref (数组 ImportFailure)
-/
private structure ImportErrorData where
  errors : IO.Ref (Array ImportFailure)

/--
Definition of `ImportErrorData.new` / `ImportErrorData.new` 的定义

English:
definition ImportErrorData.new
  signature: : BaseIO ImportErrorData
  body: do
  return { errors := ← IO.mkRef #[] }

中文:
定义 ImportErrorData.new
  签名: : BaseIO ImportErrorData
  定义体: do
  return { errors := ← IO.mkRef #[] }
-/
private def ImportErrorData.new : BaseIO ImportErrorData := do
  return { errors := ← IO.mkRef #[] }

/--
Definition of `blacklistInsertion` / `blacklistInsertion` 的定义

English:
definition blacklistInsertion
  signature: (env : Environment) (declName : Name)
  body: declName.isInternalDetail ||
  declName.isMetaprogramming ||
  !allowCompletion env declName ||
  Linter.isDeprecated env declName ||
  declName == ``sorryAx ||
  (declName matches .str _ "inj" | .str _ "injEq" | .str _ "sizeOf_spec")

中文:
定义 blacklistInsertion
  签名: (env : Environment) (declName : Name)
  定义体: declName.isInternalDetail ||
  declName.isMetaprogramming ||
  !allowCompletion env declName ||
  Linter.isDeprecated env declName ||
  declName == ``sorryAx ||
  (declName matches .str _ "inj" | .str _ "injEq" | .str _ "sizeOf_spec")

Depends on / 依赖: Linter, Linter.isDeprecated, allowCompletion, declName, declName.isInternalDetail, declName.isMetaprogramming, isDeprecated, isInternalDetail, isMetaprogramming, matches, sizeOf_spec, sorryAx
-/
def blacklistInsertion (env : Environment) (declName : Name) : Bool :=
  declName.isInternalDetail ||
  declName.isMetaprogramming ||
  !allowCompletion env declName ||
  Linter.isDeprecated env declName ||
  declName == ``sorryAx ||
  (declName matches .str _ "inj" | .str _ "injEq" | .str _ "sizeOf_spec")

/--
Definition of `addConstToPreDiscrTree` / `addConstToPreDiscrTree` 的定义

English:
definition addConstToPreDiscrTree
  body: do
  -- here we use an if-then-else clause instead of the more stylish if-then-return,
  -- because it compiles to more performant code
  if constInfo.isUnsafe then pure tree else
  if blacklistInsertion env name then pure tree else
  /- For efficiency, we leave it up to the implementation of `act` to reset the states if needed -/
  -- mstate.modify fun s => { cache := s.cache }
  -- cstate.modify fun s => { env := s.env, cache := s.cache, ngen := s.ngen }
  let mctx := { keyedConfig := Config.toConfigWithKey { transparency := .reducible } }
  match ← (((act name constInfo) mctx mstate) cctx cstate).toBaseIO with
  | .ok a =>
    return a.foldl (fun t (val, entries) =>
      entries.foldl (fun t (key, entry) => t.push key (entry, val)) t) tree
  | .error e =>
    let i : ImportFailure := {
      module := modName,
      const := name,
      exception := e }
    data.errors.modify (·.push i)
    return tree

中文:
定义 addConstToPreDiscrTree
  定义体: do
  -- here we use an if-then-else clause instead of the more stylish if-then-return,
  -- because it compiles to more performant code
  if constInfo.isUnsafe then pure tree else
  if blacklistInsertion env name then pure tree else
  /- For efficiency, we leave it up to the implementation of `act` to reset the states if needed -/
  -- mstate.modify fun s => { cache := s.cache }
  -- cstate.modify fun s => { env := s.env, cache := s.cache, ngen := s.ngen }
  let mctx := { keyedConfig := Config.toConfigWithKey { transparency := .reducible } }
  match ← (((act name constInfo) mctx mstate) cctx cstate).toBaseIO with
  | .ok a =>
    return a.foldl (fun t (val, entries) =>
      entries.foldl (fun t (key, entry) => t.push key (entry, val)) t) tree
  | .error e =>
    let i : ImportFailure := {
      module := modName,
      const := name,
      exception := e }
    data.errors.modify (·.push i)
    return tree
-/
@[inline] private def addConstToPreDiscrTree
    (cctx : Core.Context)
    (env : Environment)
    (modName : Name)
    (data : ImportErrorData)
    (mstate : IO.Ref Meta.State)
    (cstate : IO.Ref Core.State)
    (act : Name -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry))))
    (tree : PreDiscrTree α) (name : Name) (constInfo : ConstantInfo) :
    BaseIO (PreDiscrTree α) := do
  -- here we use an if-then-else clause instead of the more stylish if-then-return,
  -- because it compiles to more performant code
  if constInfo.isUnsafe then pure tree else
  if blacklistInsertion env name then pure tree else
  /- For efficiency, we leave it up to the implementation of `act` to reset the states if needed -/
  -- mstate.modify fun s => { cache := s.cache }
  -- cstate.modify fun s => { env := s.env, cache := s.cache, ngen := s.ngen }
  let mctx := { keyedConfig := Config.toConfigWithKey { transparency := .reducible } }
  match ← (((act name constInfo) mctx mstate) cctx cstate).toBaseIO with
  | .ok a =>
    return a.foldl (fun t (val, entries) =>
      entries.foldl (fun t (key, entry) => t.push key (entry, val)) t) tree
  | .error e =>
    let i : ImportFailure := {
      module := modName,
      const := name,
      exception := e }
    data.errors.modify (·.push i)
    return tree


/--
Definition of `InitResults` / `InitResults` 的定义

English:
structure InitResults
  parameters: (α : Type)
  axioms and operations (2):
    - tree : PreDiscrTree α  [default: {}]
    - errors : Array ImportFailure  [default: #[]]

中文:
结构 InitResults
  参数: (α : 类型)
  公理与运算 (2 个):
    - tree : PreDiscrTree α  [默认: {}]
    - errors : 数组 ImportFailure  [默认: #[]]
-/
private structure InitResults (α : Type) where
  tree : PreDiscrTree α := {}
  errors : Array ImportFailure := #[]

namespace InitResults

/--
Definition of `protected` / `protected` 的定义

English:
definition protected
  signature: def append (x y : InitResults α)
  body: let { tree := xv, errors := xe } := x
  let { tree := yv, errors := ye } := y
  { tree := xv ++ yv, errors := xe ++ ye }

中文:
定义 protected
  签名: def append (x y : InitResults α)
  定义体: let { tree := xv, errors := xe } := x
  let { tree := yv, errors := ye } := y
  { tree := xv ++ yv, errors := xe ++ ye }
-/
private protected def append (x y : InitResults α) : InitResults α :=
  let { tree := xv, errors := xe } := x
  let { tree := yv, errors := ye } := y
  { tree := xv ++ yv, errors := xe ++ ye }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Append (InitResults α)
  body: InitResults.append

中文:
实例 :
  签名: Append (InitResults α)
  定义体: InitResults.append
-/
private instance : Append (InitResults α) where
  append := InitResults.append

end InitResults

/--
Definition of `toInitResults` / `toInitResults` 的定义

English:
definition toInitResults
  signature: (data : ImportErrorData) (tree : PreDiscrTree α)
  body: do
  let de ← data.errors.swap #[]
  pure ⟨tree, de⟩

中文:
定义 toInitResults
  签名: (data : ImportErrorData) (tree : PreDiscrTree α)
  定义体: do
  let de ← data.errors.swap #[]
  pure ⟨tree, de⟩
-/
private def toInitResults (data : ImportErrorData) (tree : PreDiscrTree α) :
    BaseIO (InitResults α) := do
  let de ← data.errors.swap #[]
  pure ⟨tree, de⟩

/--
Definition of `loadImportedModule` / `loadImportedModule` 的定义

English:
definition loadImportedModule
  body: do
  if h : i < mdata.constNames.size then
    let name := mdata.constNames[i]
    let constInfo := mdata.constants[i]!
    let state ← addConstToPreDiscrTree cctx env mname data mstate cstate act tree name constInfo
    loadImportedModule cctx env data mstate cstate act mname mdata state (i+1)
  else
    return tree

中文:
定义 loadImportedModule
  定义体: do
  if h : i < mdata.constNames.size then
    let name := mdata.constNames[i]
    let constInfo := mdata.constants[i]!
    let state ← addConstToPreDiscrTree cctx env mname data mstate cstate act tree name constInfo
    loadImportedModule cctx env data mstate cstate act mname mdata state (i+1)
  else
    return tree
-/
private partial def loadImportedModule
    (cctx : Core.Context)
    (env : Environment)
    (data : ImportErrorData)
    (mstate : IO.Ref Meta.State)
    (cstate : IO.Ref Core.State)
    (act : Name -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry))))
    (mname : Name)
    (mdata : ModuleData)
    (tree : PreDiscrTree α)
    (i : Nat := 0) : BaseIO (PreDiscrTree α) := do
  if h : i < mdata.constNames.size then
    let name := mdata.constNames[i]
    let constInfo := mdata.constants[i]!
    let state ← addConstToPreDiscrTree cctx env mname data mstate cstate act tree name constInfo
    loadImportedModule cctx env data mstate cstate act mname mdata state (i+1)
  else
    return tree

/--
Definition of `createImportInitResults` / `createImportInitResults` 的定义

English:
definition createImportInitResults
  signature: (cctx : Core.Context) (ngen : NameGenerator)
  body: do
  let tree := { root := .emptyWithCapacity capacity }
  go start stop tree (← ImportErrorData.new) (← IO.mkRef {}) (← IO.mkRef { env, ngen })

中文:
定义 createImportInitResults
  签名: (cctx : 核.余ntext) (ngen : NameGenerator)
  定义体: do
  let tree := { root := .emptyWithCapacity capacity }
  go start stop tree (← ImportErrorData.new) (← IO.mkRef {}) (← IO.mkRef { env, ngen })
-/
private def createImportInitResults (cctx : Core.Context) (ngen : NameGenerator)
    (env : Environment) (act : Name -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry))))
    (capacity start stop : Nat) : BaseIO (InitResults α) := do
  let tree := { root := .emptyWithCapacity capacity }
  go start stop tree (← ImportErrorData.new) (← IO.mkRef {}) (← IO.mkRef { env, ngen })
where
  go (start stop : Nat) (tree : PreDiscrTree α)
      (data : ImportErrorData)
      (mstate : IO.Ref Meta.State)
      (cstate : IO.Ref Core.State) :
      BaseIO (InitResults α) := do
    if start < stop then
      let mname := env.header.moduleNames[start]!
      let mdata := env.header.moduleData[start]!
      let tree ← loadImportedModule cctx env data mstate cstate act mname mdata tree
      go (start+1) stop tree data mstate cstate
    else
      toInitResults data tree
  termination_by stop - start

/--
Definition of `getChildNgen` / `getChildNgen` 的定义

English:
definition getChildNgen
  signature: : CoreM NameGenerator
  body: do
  let ngen ← getNGen
  let (cngen, ngen) := ngen.mkChild
  setNGen ngen
  pure cngen

中文:
定义 getChildNgen
  签名: : CoreM NameGenerator
  定义体: do
  let ngen ← getNGen
  let (cngen, ngen) := ngen.mkChild
  setNGen ngen
  pure cngen
-/
private def getChildNgen : CoreM NameGenerator := do
  let ngen ← getNGen
  let (cngen, ngen) := ngen.mkChild
  setNGen ngen
  pure cngen

/--
Definition of `logImportFailure` / `logImportFailure` 的定义

English:
definition logImportFailure
  signature: (f : ImportFailure)
  body: logError m!"Processing failure with {f.const} in {f.module}:\n {f.exception.toMessageData}"

中文:
定义 logImportFailure
  签名: (f : ImportFailure)
  定义体: logError m!"Processing failure with {f.const} in {f.module}:\n {f.exception.toMessageData}"
-/
private def logImportFailure (f : ImportFailure) : CoreM Unit :=
  logError m!"Processing failure with {f.const} in {f.module}:\n {f.exception.toMessageData}"

/--
Definition of `createImportedDiscrTree` / `createImportedDiscrTree` 的定义

English:
definition createImportedDiscrTree
  signature: (ngen : NameGenerator) (env : Environment)
  body: do
  let numModules := env.header.moduleData.size
  let cctx ← read
  let rec
    /-- Allocate constants to tasks according to `constantsPerTask`. -/
    go (ngen : NameGenerator) (tasks : Array (Task (InitResults α))) (start cnt idx : Nat) := do
      if h : idx < numModules then
        let mdata := env.header.moduleData[idx]
        let cnt := cnt + mdata.constants.size
        if cnt > constantsPerTask then
          let (childNGen, ngen) := ngen.mkChild
          let t ← (createImportInitResults
            cctx childNGen env act capacityPerTask start (idx+1)).asTask
          go ngen (tasks.push t) (idx+1) 0 (idx+1)
        else
          go ngen tasks start cnt (idx+1)
      else
        if start < numModules then
          let (childNGen, _) := ngen.mkChild
          let t ← (createImportInitResults
            cctx childNGen env act capacityPerTask start numModules).asTask
          pure (tasks.push t)
        else
          pure tasks
    termination_by env.header.moduleData.size - idx
  let tasks ← go ngen #[] 0 0 0
  let r : InitResults α := tasks.foldl (init := {}) (· ++ ·.get)
  r.errors.forM logImportFailure
  return r.tree.toRefinedDiscrTree

中文:
定义 createImportedDiscrTree
  签名: (ngen : NameGenerator) (env : Environment)
  定义体: do
  let numModules := env.header.moduleData.size
  let cctx ← read
  let rec
    /-- Allocate constants to tasks according to `constantsPerTask`. -/
    go (ngen : NameGenerator) (tasks : Array (Task (InitResults α))) (start cnt idx : Nat) := do
      if h : idx < numModules then
        let mdata := env.header.moduleData[idx]
        let cnt := cnt + mdata.constants.size
        if cnt > constantsPerTask then
          let (childNGen, ngen) := ngen.mkChild
          let t ← (createImportInitResults
            cctx childNGen env act capacityPerTask start (idx+1)).asTask
          go ngen (tasks.push t) (idx+1) 0 (idx+1)
        else
          go ngen tasks start cnt (idx+1)
      else
        if start < numModules then
          let (childNGen, _) := ngen.mkChild
          let t ← (createImportInitResults
            cctx childNGen env act capacityPerTask start numModules).asTask
          pure (tasks.push t)
        else
          pure tasks
    termination_by env.header.moduleData.size - idx
  let tasks ← go ngen #[] 0 0 0
  let r : InitResults α := tasks.foldl (init := {}) (· ++ ·.get)
  r.errors.forM logImportFailure
  return r.tree.toRefinedDiscrTree
-/
def createImportedDiscrTree (ngen : NameGenerator) (env : Environment)
    (act : Name -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry))))
    (constantsPerTask capacityPerTask : Nat) :
    CoreM (RefinedDiscrTree α) := do
  let numModules := env.header.moduleData.size
  let cctx ← read
  let rec
    /-- Allocate constants to tasks according to `constantsPerTask`. -/
    go (ngen : NameGenerator) (tasks : Array (Task (InitResults α))) (start cnt idx : Nat) := do
      if h : idx < numModules then
        let mdata := env.header.moduleData[idx]
        let cnt := cnt + mdata.constants.size
        if cnt > constantsPerTask then
          let (childNGen, ngen) := ngen.mkChild
          let t ← (createImportInitResults
            cctx childNGen env act capacityPerTask start (idx+1)).asTask
          go ngen (tasks.push t) (idx+1) 0 (idx+1)
        else
          go ngen tasks start cnt (idx+1)
      else
        if start < numModules then
          let (childNGen, _) := ngen.mkChild
          let t ← (createImportInitResults
            cctx childNGen env act capacityPerTask start numModules).asTask
          pure (tasks.push t)
        else
          pure tasks
    termination_by env.header.moduleData.size - idx
  let tasks ← go ngen #[] 0 0 0
  let r : InitResults α := tasks.foldl (init := {}) (· ++ ·.get)
  r.errors.forM logImportFailure
  return r.tree.toRefinedDiscrTree

/--
Definition of `ModuleDiscrTreeRef` / `ModuleDiscrTreeRef` 的定义

English:
structure ModuleDiscrTreeRef
  parameters: (α : Type _)
  axioms and operations (1):
    - ref : IO.Ref (RefinedDiscrTree α)

中文:
结构 ModuleDiscrTreeRef
  参数: (α : 类型 _)
  公理与运算 (1 个):
    - ref : IO.Ref (RefinedDiscrTree α)
-/
structure ModuleDiscrTreeRef (α : Type _) where
  /-- The reference to the `RefinedDiscrTree`. -/
  ref : IO.Ref (RefinedDiscrTree α)

/--
Definition of `createModulePreDiscrTree` / `createModulePreDiscrTree` 的定义

English:
definition createModulePreDiscrTree
  body: do
  let modName := env.header.mainModule
  let data ← ImportErrorData.new
  let r ← env.constants.map₂.foldlM (init := {}) (addConstToPreDiscrTree
    cctx env modName data (← IO.mkRef {}) (← IO.mkRef { env, ngen }) act)
  toInitResults data r

中文:
定义 createModulePreDiscrTree
  定义体: do
  let modName := env.header.mainModule
  let data ← ImportErrorData.new
  let r ← env.constants.map₂.foldlM (init := {}) (addConstToPreDiscrTree
    cctx env modName data (← IO.mkRef {}) (← IO.mkRef { env, ngen }) act)
  toInitResults data r
-/
private def createModulePreDiscrTree
    (cctx : Core.Context)
    (ngen : NameGenerator)
    (env : Environment)
    (act : Name -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry)))) :
    BaseIO (InitResults α) := do
  let modName := env.header.mainModule
  let data ← ImportErrorData.new
  let r ← env.constants.map₂.foldlM (init := {}) (addConstToPreDiscrTree
    cctx env modName data (← IO.mkRef {}) (← IO.mkRef { env, ngen }) act)
  toInitResults data r

/--
Definition of `createModuleDiscrTree` / `createModuleDiscrTree` 的定义

English:
definition createModuleDiscrTree
  signature: (act : Name -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry))))
  body: do
  let env ← getEnv
  let ngen ← getChildNgen
  let ctx ← readThe Core.Context
  let { tree, errors } ← createModulePreDiscrTree ctx ngen env act
  errors.forM logImportFailure
  return tree.toRefinedDiscrTree

中文:
定义 createModuleDiscrTree
  签名: (act : Name -> ConstantInfo -> MetaM (列表 (α × 列表 (Key × LazyEntry))))
  定义体: do
  let env ← getEnv
  let ngen ← getChildNgen
  let ctx ← readThe Core.Context
  let { tree, errors } ← createModulePreDiscrTree ctx ngen env act
  errors.forM logImportFailure
  return tree.toRefinedDiscrTree
-/
def createModuleDiscrTree (act : Name -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry)))) :
    CoreM (RefinedDiscrTree α) := do
  let env ← getEnv
  let ngen ← getChildNgen
  let ctx ← readThe Core.Context
  let { tree, errors } ← createModulePreDiscrTree ctx ngen env act
  errors.forM logImportFailure
  return tree.toRefinedDiscrTree

/--
Definition of `createModuleTreeRef` / `createModuleTreeRef` 的定义

English:
definition createModuleTreeRef
  signature: (act : Name -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry))))
  body: do
  profileitM Exception "build module discriminator tree" (← getOptions) do
    let t ← createModuleDiscrTree act
    pure { ref := ← IO.mkRef t }

中文:
定义 createModuleTreeRef
  签名: (act : Name -> ConstantInfo -> MetaM (列表 (α × 列表 (Key × LazyEntry))))
  定义体: do
  profileitM Exception "build module discriminator tree" (← getOptions) do
    let t ← createModuleDiscrTree act
    pure { ref := ← IO.mkRef t }
-/
def createModuleTreeRef (act : Name -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry)))) :
    MetaM (ModuleDiscrTreeRef α) := do
  profileitM Exception "build module discriminator tree" (← getOptions) do
    let t ← createModuleDiscrTree act
    pure { ref := ← IO.mkRef t }

end Lean.Meta.RefinedDiscrTree
