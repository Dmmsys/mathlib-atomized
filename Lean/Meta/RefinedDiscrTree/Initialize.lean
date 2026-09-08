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

/-- Directly insert a `Key`, `LazyEntry` pair into a `RefinedDiscrTree`. -/
/-
**Lean.Meta.RefinedDiscrTree.insert** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Meta.Refined
DiscrTree`。
形式化陈述：insert (d : RefinedDiscrTree α) (key : Key) (entry : LazyEntry × α) : Refi
nedDiscrTree α
参数：d : RefinedDiscrTree α；key : Key；entry : LazyEntry × α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Directly insert a `Key`, `LazyEntry` pair into a `RefinedDiscrTree`.
-/
def insert (d : RefinedDiscrTree α) (key : Key) (entry : LazyEntry × α) : RefinedDiscrTree α :=
  if let some trie := d.root[key]? then
    { d with
      tries := d.tries.modify trie fun node => { node with pending := node.pending.push entry } }
  else
    { d with
      root := d.root.insert key d.tries.size
      tries := d.tries.push <| .node #[] none {} {} #[entry] }

/--
Structure for quickly initializing a lazy discrimination tree with a large number
of elements using concurrent functions for generating entries.

This preliminary structure is converted to a `RefinedDiscrTree` via `toRefinedDiscrTree`.
-/
/-
**Lean.Meta.RefinedDiscrTree.PreDiscrTree** 是 Mathlib 中的一个结构，位于命名空间 `Lean.Meta.R
efinedDiscrTree`。
形式化陈述：PreDiscrTree (α : Type) where /-- Maps keys to index in tries array. -/ ro
ot : Std.HashMap Key Nat
参数：α : Type。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure for quickly initializing a lazy discrimination tree with a large numbe
r
of elements using concurrent functions for generating entries.

This preliminary structure is converted to a `RefinedDiscrTree` via `toRefinedDi
scrTree`.
-/
structure PreDiscrTree (α : Type) where
  /-- Maps keys to index in tries array. -/
  root : Std.HashMap Key Nat := {}
  /-- Lazy entries for root of trie. -/
  tries : Array (Array (LazyEntry × α)) := #[]
  deriving Inhabited

namespace PreDiscrTree

@[specialize]
/-
**Lean.Meta.RefinedDiscrTree.PreDiscrTree.modifyAt** 是 Mathlib 中的一个定义，位于命名空间 `Le
an.Meta.RefinedDiscrTree.PreDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def modifyAt (d : PreDiscrTree α) (k : Key)
    (f : Array (LazyEntry × α) → Array (LazyEntry × α)) : PreDiscrTree α :=
  let { root, tries } := d
  match root[k]? with
  | none =>
    { root := root.insert k tries.size, tries := tries.push (f #[]) }
  | some i =>
    { root, tries := tries.modify i f }

/-- Add an entry to the `PreDiscrTree`. -/
/-
**Lean.Meta.RefinedDiscrTree.PreDiscrTree.push** 是 Mathlib 中的一个定义，位于命名空间 `Lean.M
eta.RefinedDiscrTree.PreDiscrTree`。
形式化陈述：push (d : PreDiscrTree α) (k : Key) (e : LazyEntry × α) : PreDiscrTree α
参数：d : PreDiscrTree α；k : Key；e : LazyEntry × α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add an entry to the `PreDiscrTree`.
-/
def push (d : PreDiscrTree α) (k : Key) (e : LazyEntry × α) : PreDiscrTree α :=
  d.modifyAt k (·.push e)

/-- Convert a `PreDiscrTree` to a `RefinedDiscrTree`. -/
/-
**Lean.Meta.RefinedDiscrTree.PreDiscrTree.toRefinedDiscrTree** 是 Mathlib 中的一个定义，
位于命名空间 `Lean.Meta.RefinedDiscrTree.PreDiscrTree`。
形式化陈述：toRefinedDiscrTree (d : PreDiscrTree α) : RefinedDiscrTree α
参数：d : PreDiscrTree α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a `PreDiscrTree` to a `RefinedDiscrTree`.
-/
def toRefinedDiscrTree (d : PreDiscrTree α) : RefinedDiscrTree α :=
  let { root, tries } := d
  { root, tries := tries.map fun pending => .node #[] none {} {} pending }

/-- Merge two `PreDiscrTree`s. -/
/-
**Lean.Meta.RefinedDiscrTree.PreDiscrTree.append** 是 Mathlib 中的一个定义，位于命名空间 `Lean
.Meta.RefinedDiscrTree.PreDiscrTree`。
形式化陈述：append (x y : PreDiscrTree α) : PreDiscrTree α
参数：x y : PreDiscrTree α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Merge two `PreDiscrTree`s.
-/
def append (x y : PreDiscrTree α) : PreDiscrTree α :=
  let (x, y, f) :=
    if x.root.size ≥ y.root.size then
      (x, y, fun y x => x ++ y)
    else
      (y, x, fun x y => x ++ y)
  let { root := yk, tries := ya } := y
  yk.fold (init := x) fun d k yi => d.modifyAt k (f ya[yi]!)
/-
**Lean.Meta.RefinedDiscrTree.PreDiscrTree.** 是 Mathlib 中的一个实例，位于命名空间 `Lean.Meta.
RefinedDiscrTree.PreDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Append (PreDiscrTree α) where
  append := PreDiscrTree.append

end PreDiscrTree


/-- Information about a failed import. -/
/-
**Lean.Meta.RefinedDiscrTree.ImportFailure** 是 Mathlib 中的一个结构，位于命名空间 `Lean.Meta.
RefinedDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Information about a failed import.
-/
private structure ImportFailure where
  /-- Module containing the constant whose import failed. -/
  module : Name
  /-- Constant whose import failed. -/
  const : Name
  /-- Exception that triggered the error. -/
  exception : Exception

/-- Information generated from imported modules. -/
/-
**Lean.Meta.RefinedDiscrTree.ImportErrorData** 是 Mathlib 中的一个结构，位于命名空间 `Lean.Met
a.RefinedDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Information generated from imported modules.
-/
private structure ImportErrorData where
  errors : IO.Ref (Array ImportFailure)
/-
**Lean.Meta.RefinedDiscrTree.ImportErrorData.new** 是 Mathlib 中的一个定义，位于命名空间 `Lean
.Meta.RefinedDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def ImportErrorData.new : BaseIO ImportErrorData := do
  return { errors := ← IO.mkRef #[] }

/-- Return true if `declName` is automatically generated,
or otherwise unsuitable as a lemma suggestion. -/
/-
**Lean.Meta.RefinedDiscrTree.blacklistInsertion** 是 Mathlib 中的一个定义，位于命名空间 `Lean.
Meta.RefinedDiscrTree`。
形式化陈述：blacklistInsertion (env : Environment) (declName : Name) : Bool
参数：env : Environment；declName : Name。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return true if `declName` is automatically generated,
or otherwise unsuitable as a lemma suggestion.
-/
def blacklistInsertion (env : Environment) (declName : Name) : Bool :=
  declName.isInternalDetail ||
  declName.isMetaprogramming ||
  !allowCompletion env declName ||
  Linter.isDeprecated env declName ||
  declName == ``sorryAx ||
  (declName matches .str _ "inj" | .str _ "injEq" | .str _ "sizeOf_spec")

/--
Add the entries generated by `act name constInfo` to the `PreDiscrTree`.

Note: It is expensive to create two new `IO.Ref`s for every `MetaM` operation,
  so instead we reuse the same refs `mstate` and `cstate`. These are also used to
  remember the cache, and the name generator across the operations.
-/
/-
**Lean.Meta.RefinedDiscrTree.addConstToPreDiscrTree** 是 Mathlib 中的一个定义，位于命名空间 `L
ean.Meta.RefinedDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add the entries generated by `act name constInfo` to the `PreDiscrTree`.

Note: It is expensive to create two new `IO.Ref`s for every `MetaM` operation,
  so instead we reuse the same refs `mstate` and `cstate`. These are also used t
o
  remember the cache, and the name generator across the operations.
-/
@[inline] private def addConstToPreDiscrTree
    (cctx : Core.Context)
    (env : Environment)
    (modName : Name)
    (data : ImportErrorData)
    (mstate : IO.Ref Meta.State)
    (cstate : IO.Ref Core.State)
    (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry))))
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
Contains a `PreDiscrTree` and any errors occurring during initialization of
the library search tree.
-/
/-
**Lean.Meta.RefinedDiscrTree.InitResults** 是 Mathlib 中的一个结构，位于命名空间 `Lean.Meta.Re
finedDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Contains a `PreDiscrTree` and any errors occurring during initialization of
the library search tree.
-/
private structure InitResults (α : Type) where
  tree : PreDiscrTree α := {}
  errors : Array ImportFailure := #[]

namespace InitResults

/-- Combine two initial results. -/
/-
**Lean.Meta.RefinedDiscrTree.InitResults.append** 是 Mathlib 中的一个定义，位于命名空间 `Lean.
Meta.RefinedDiscrTree.InitResults`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine two initial results.
-/
private protected def append (x y : InitResults α) : InitResults α :=
  let { tree := xv, errors := xe } := x
  let { tree := yv, errors := ye } := y
  { tree := xv ++ yv, errors := xe ++ ye }
/-
**Lean.Meta.RefinedDiscrTree.InitResults.** 是 Mathlib 中的一个实例，位于命名空间 `Lean.Meta.R
efinedDiscrTree.InitResults`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance : Append (InitResults α) where
  append := InitResults.append

end InitResults

/-
**Lean.Meta.RefinedDiscrTree.toInitResults** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Meta.
RefinedDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def toInitResults (data : ImportErrorData) (tree : PreDiscrTree α) :
    BaseIO (InitResults α) := do
  let de ← data.errors.swap #[]
  pure ⟨tree, de⟩

/--
Loop through all constants that appear in the module `mdata`,
and add the entries generated by `act` to the `PreDiscrTree`.
-/
/-
**Lean.Meta.RefinedDiscrTree.loadImportedModule** 是 Mathlib 中的一个定义，位于命名空间 `Lean.
Meta.RefinedDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Loop through all constants that appear in the module `mdata`,
and add the entries generated by `act` to the `PreDiscrTree`.
-/
private partial def loadImportedModule
    (cctx : Core.Context)
    (env : Environment)
    (data : ImportErrorData)
    (mstate : IO.Ref Meta.State)
    (cstate : IO.Ref Core.State)
    (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry))))
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
Loop through all constants that appear in the modules with module index from `start` to `stop - 1`,
and add the entries generated by `act` to the `PreDiscrTree`.
-/
/-
**Lean.Meta.RefinedDiscrTree.createImportInitResults** 是 Mathlib 中的一个定义，位于命名空间 `
Lean.Meta.RefinedDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Loop through all constants that appear in the modules with module index from `st
art` to `stop - 1`,
and add the entries generated by `act` to the `PreDiscrTree`.
-/
private def createImportInitResults (cctx : Core.Context) (ngen : NameGenerator)
    (env : Environment) (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry))))
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
/-
**Lean.Meta.RefinedDiscrTree.getChildNgen** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Meta.R
efinedDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def getChildNgen : CoreM NameGenerator := do
  let ngen ← getNGen
  let (cngen, ngen) := ngen.mkChild
  setNGen ngen
  pure cngen
/-
**Lean.Meta.RefinedDiscrTree.logImportFailure** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Me
ta.RefinedDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def logImportFailure (f : ImportFailure) : CoreM Unit :=
  logError m!"Processing failure with {f.const} in {f.module}:\n  {f.exception.toMessageData}"

/--
Create a `RefinedDiscrTree` consisting of all entries generated by `act`
from imported constants; `addConstToPreDiscrTree` calls this helper.
This uses parallel computation.
-/
/-
**Lean.Meta.RefinedDiscrTree.createImportedDiscrTree** 是 Mathlib 中的一个定义，位于命名空间 `
Lean.Meta.RefinedDiscrTree`。
形式化陈述：createImportedDiscrTree (ngen : NameGenerator) (env : Environment) (act : 
Name -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry)))) (constantsPer
Task capacityPerTask : Nat) : CoreM (RefinedDiscrTree α)
参数：ngen : NameGenerator；env : Environment；act : Name -> ConstantInfo -> MetaM (L
ist (α × List (Key × LazyEntry)))；constantsPerTask capacityPerTask : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a `RefinedDiscrTree` consisting of all entries generated by `act`
from imported constants; `addConstToPreDiscrTree` calls this helper.
This uses parallel computation.
-/
def createImportedDiscrTree (ngen : NameGenerator) (env : Environment)
    (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry))))
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
A discriminator tree for the current module's declarations only.

Note: We use different discrimination trees for imported and current module
declarations since imported declarations are typically much more numerous but
not changed while the current module is edited.
-/
/-
**Lean.Meta.RefinedDiscrTree.ModuleDiscrTreeRef** 是 Mathlib 中的一个结构，位于命名空间 `Lean.
Meta.RefinedDiscrTree`。
形式化陈述：ModuleDiscrTreeRef (α : Type _) where /-- The reference to the `RefinedDis
crTree`. -/ ref : IO.Ref (RefinedDiscrTree α)  private def createModulePreDiscrT
ree (cctx : Core.Context) (ngen : NameGenerator) (env : Environment) (act : Name
 -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry)))) : BaseIO (InitRes
ults α)
参数：α : Type _。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A discriminator tree for the current module's declarations only.

Note: We use different discrimination trees for imported and current module
declarations since imported declarations are typically much more numerous but
not changed while the current module is edited.
-/
structure ModuleDiscrTreeRef (α : Type _) where
  /-- The reference to the `RefinedDiscrTree`. -/
  ref : IO.Ref (RefinedDiscrTree α)
/-
**Lean.Meta.RefinedDiscrTree.createModulePreDiscrTree** 是 Mathlib 中的一个定义，位于命名空间 
`Lean.Meta.RefinedDiscrTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def createModulePreDiscrTree
    (cctx : Core.Context)
    (ngen : NameGenerator)
    (env : Environment)
    (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry)))) :
    BaseIO (InitResults α) := do
  let modName := env.header.mainModule
  let data ← ImportErrorData.new
  let r ← env.constants.map₂.foldlM (init := {}) (addConstToPreDiscrTree
    cctx env modName data (← IO.mkRef {}) (← IO.mkRef { env, ngen }) act)
  toInitResults data r

/--
Create a `RefinedDiscrTree` for current module declarations, consisting of all
entries generated by `act` from constants in the current file.
This is called by `addConstToPreDiscrTree`.
-/
/-
**Lean.Meta.RefinedDiscrTree.createModuleDiscrTree** 是 Mathlib 中的一个定义，位于命名空间 `Le
an.Meta.RefinedDiscrTree`。
形式化陈述：createModuleDiscrTree (act : Name -> ConstantInfo -> MetaM (List (α × List
 (Key × LazyEntry)))) : CoreM (RefinedDiscrTree α)
参数：act : Name -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry)))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a `RefinedDiscrTree` for current module declarations, consisting of all
entries generated by `act` from constants in the current file.
This is called by `addConstToPreDiscrTree`.
-/
def createModuleDiscrTree (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry)))) :
    CoreM (RefinedDiscrTree α) := do
  let env ← getEnv
  let ngen ← getChildNgen
  let ctx ← readThe Core.Context
  let { tree, errors } ← createModulePreDiscrTree ctx ngen env act
  errors.forM logImportFailure
  return tree.toRefinedDiscrTree

/--
Create a reference for a `RefinedDiscrTree` for current module declarations.
-/
/-
**Lean.Meta.RefinedDiscrTree.createModuleTreeRef** 是 Mathlib 中的一个定义，位于命名空间 `Lean
.Meta.RefinedDiscrTree`。
形式化陈述：createModuleTreeRef (act : Name -> ConstantInfo -> MetaM (List (α × List (
Key × LazyEntry)))) : MetaM (ModuleDiscrTreeRef α)
参数：act : Name -> ConstantInfo -> MetaM (List (α × List (Key × LazyEntry)))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a reference for a `RefinedDiscrTree` for current module declarations.
-/
def createModuleTreeRef (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry)))) :
    MetaM (ModuleDiscrTreeRef α) := do
  profileitM Exception "build module discriminator tree" (← getOptions) do
    let t ← createModuleDiscrTree act
    pure { ref := ← IO.mkRef t }

end Lean.Meta.RefinedDiscrTree

