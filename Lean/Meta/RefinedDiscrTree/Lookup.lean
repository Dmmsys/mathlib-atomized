/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Lean.Meta.RefinedDiscrTree.Encode

/-!
# Matching with a RefinedDiscrTree

This file defines the matching procedure for the `RefinedDiscrTree`.

The main definitions are
* The structure `MatchResult`, which contains the match results, ordered by matching score.
* The (private) function `evalNode` which evaluates a node of the `RefinedDiscrTree`
* The (private) function `getMatchLoop`, which is the main function that computes the matches.
  It implements the non-deterministic computation by keeping a stack of `PartialMatch`es,
  and repeatedly processing the most recent one.
* The matching function `getMatch` that also returns an updated `RefinedDiscrTree`

To find the matches, we first encode the expression as a `List Key`. Then using this,
we find all matches with the tree. When `unify == true`, we also allow metavariables in the target
expression to be assigned.

We use a simple unification algorithm. For all star/metavariable patterns in the
`RefinedDiscrTree` (and in the target if `unify == true`), we store the assignment,
and when it is attempted to be assigned again, we check that it is the same assignment.

-/

public section

namespace Lean.Meta.RefinedDiscrTree

variable {α β : Type}

/--
Definition of `TreeM` / `TreeM` 的定义

English:
abbreviation TreeM
  signature: α
  body: StateRefT (Array (Trie α)) MetaM

中文:
缩写 TreeM
  签名: α
  定义体: StateRefT (Array (Trie α)) MetaM
-/
private abbrev TreeM α := StateRefT (Array (Trie α)) MetaM

/--
Definition of `runTreeM` / `runTreeM` 的定义

English:
definition runTreeM
  signature: (d : RefinedDiscrTree α) (m : TreeM α β)
  body: do
  let { tries, root } := d
  let (result, tries) ← m.run tries
  pure (result, { tries, root })

中文:
定义 runTreeM
  签名: (d : RefinedDiscrTree α) (m : TreeM α β)
  定义体: do
  let { tries, root } := d
  let (result, tries) ← m.run tries
  pure (result, { tries, root })
-/
@[inline] private def runTreeM (d : RefinedDiscrTree α) (m : TreeM α β) :
    MetaM (β × RefinedDiscrTree α) := do
  let { tries, root } := d
  let (result, tries) ← m.run tries
  pure (result, { tries, root })

/--
Definition of `setTrie` / `setTrie` 的定义

English:
definition setTrie
  signature: (i : TrieIndex) (v : Trie α)
  body: modify (·.set! i v)

中文:
定义 setTrie
  签名: (i : TrieIndex) (v : Trie α)
  定义体: modify (·.set! i v)
-/
private def setTrie (i : TrieIndex) (v : Trie α) : TreeM α Unit :=
  modify (·.set! i v)

/--
Definition of `newTrie` / `newTrie` 的定义

English:
definition newTrie
  signature: (e : LazyEntry × α)
  body: do
  modifyGet fun a => (a.size, a.push (.node #[] none {} {} #[e]))

中文:
定义 newTrie
  签名: (e : LazyEntry × α)
  定义体: do
  modifyGet fun a => (a.size, a.push (.node #[] none {} {} #[e]))
-/
private def newTrie (e : LazyEntry × α) : TreeM α TrieIndex := do
  modifyGet fun a => (a.size, a.push (.node #[] none {} {} #[e]))

/--
Definition of `addLazyEntryToTrie` / `addLazyEntryToTrie` 的定义

English:
definition addLazyEntryToTrie
  signature: (i : TrieIndex) (e : LazyEntry × α)
  body: modify (·.modify i fun node => { node with pending := node.pending.push e })

中文:
定义 addLazyEntryToTrie
  签名: (i : TrieIndex) (e : LazyEntry × α)
  定义体: modify (·.modify i fun node => { node with pending := node.pending.push e })
-/
private def addLazyEntryToTrie (i : TrieIndex) (e : LazyEntry × α) : TreeM α Unit :=
  modify (·.modify i fun node => { node with pending := node.pending.push e })

/--
Definition of `processPending` / `processPending` 的定义

English:
definition processPending
  signature: (pending : Array (LazyEntry × α)) (start stop : Nat)
  body: do
  Core.checkInterrupted
  let mut values := #[]
  let mut newEntries := #[]
  for (entry, value) in pending[start...stop] do
    match ← evalLazyEntry entry true with
    | some entries =>
      for (key, entry) in entries do
        newEntries := newEntries.push (key, entry, value)
    | none =>

中文:
定义 processPending
  签名: (pending : 数组 (LazyEntry × α)) (start stop : 自然数)
  定义体: do
  Core.checkInterrupted
  let mut values := #[]
  let mut newEntries := #[]
  for (entry, value) in pending[start...stop] do
    match ← evalLazyEntry entry true with
    | some entries =>
      for (key, entry) in entries do
        newEntries := newEntries.push (key, entry, value)
    | none =>
-/
private def processPending (pending : Array (LazyEntry × α)) (start stop : Nat) :
    MetaM (Array α × Array (Key × LazyEntry × α)) := do
  Core.checkInterrupted
  let mut values := #[]
  let mut newEntries := #[]
  for (entry, value) in pending[start...stop] do
    match ← evalLazyEntry entry true with
    | some entries =>
      for (key, entry) in entries do
        newEntries := newEntries.push (key, entry, value)
    | none =>
      values := values.push value
  return (values, newEntries)

/--
Definition of `evalNode` / `evalNode` 的定义

English:
definition evalNode
  signature: (trie : TrieIndex)
  body: do
  let node := (← get)[trie]!
  if node.pending.isEmpty then
    return node
  let numTasks := node.pending.size / 5000 + 1
  Core.checkInterrupted
  let tasks ← numTasks.foldM (init := #[]) fun i _ tasks => do
return tasks.push ← EIO.asTask
      Core.withCurrHeartbeats (processPending node.pendi

中文:
定义 evalNode
  签名: (trie : TrieIndex)
  定义体: do
  let node := (← get)[trie]!
  if node.pending.isEmpty then
    return node
  let numTasks := node.pending.size / 5000 + 1
  Core.checkInterrupted
  let tasks ← numTasks.foldM (init := #[]) fun i _ tasks => do
return tasks.push ← EIO.asTask
      Core.withCurrHeartbeats (processPending node.pendi
-/
private def evalNode (trie : TrieIndex) : TreeM α (Trie α) := do
  let node := (← get)[trie]!
  if node.pending.isEmpty then
    return node
  let numTasks := node.pending.size / 5000 + 1
  Core.checkInterrupted
  let tasks ← numTasks.foldM (init := #[]) fun i _ tasks => do
return tasks.push ← EIO.asTask
      Core.withCurrHeartbeats (processPending node.pending (i * 5000) ((i + 1) * 5000))
.run' (← readThe _) (← getThe _)
.run' (← readThe _) (← getThe _)
  setTrie trie default -- reduce the reference count to `node` to be 1
  let mut { values, star, labelledStars, children, .. } := node
  for task in tasks do
    let (values', newEntries) ← MonadExcept.ofExcept task.get
    values := values ++ values'
    for (key, entry) in newEntries do
      match key with
      | .labelledStar label =>
        if let some trie := labelledStars[label]? then
          addLazyEntryToTrie trie entry
        else
          labelledStars := labelledStars.insert label (← newTrie entry)
      | .star =>
        if let some trie := star then
          addLazyEntryToTrie trie entry
        else
          star := some (← newTrie entry)
      | _ =>
        if let some trie := children[key]? then
          addLazyEntryToTrie trie entry
        else
          children := children.insert key (← newTrie entry)
  let node := { values, star, labelledStars, children, pending := #[] }
  setTrie trie node
  return node


/--
Definition of `MatchResult` / `MatchResult` 的定义

English:
structure MatchResult
  parameters: (α : Type)
  axioms and operations (1):
    - elts : Std.TreeMap Nat (Array (Array α))  [default: {}]

中文:
结构 MatchResult
  参数: (α : 类型)
  公理与运算 (1 个):
    - elts : Std.TreeMap 自然数 (数组 (数组 α))  [默认: {}]
-/
structure MatchResult (α : Type) where
  /--
  The elements in the match result.

  The `Nat` in the tree map represents the `score` of the results.
  The elements are arrays of arrays, where each sub-array corresponds to one discr tree pattern.
  -/
  elts : Std.TreeMap Nat (Array (Array α)) := {}
  deriving Inhabited

/--
Definition of `MatchResult.push` / `MatchResult.push` 的定义

English:
definition MatchResult.push
  signature: (mr : MatchResult α) (score : Nat) (e : Array α)
  body: { elts := mr.elts.alter score fun | some arr => arr.push e | none => #[e] }

中文:
定义 MatchResult.push
  签名: (mr : MatchResult α) (score : 自然数) (e : 数组 α)
  定义体: { elts := mr.elts.alter score fun | some arr => arr.push e | none => #[e] }
-/
private def MatchResult.push (mr : MatchResult α) (score : Nat) (e : Array α) : MatchResult α :=
  { elts := mr.elts.alter score fun | some arr => arr.push e | none => #[e] }

/--
Definition of `MatchResult.toArray` / `MatchResult.toArray` 的定义

English:
definition MatchResult.toArray
  signature: (mr : MatchResult α)
  body: mr.elts.foldr (init := #[]) fun _ a r => a.foldl (init := r) (· ++ ·)

中文:
定义 MatchResult.toArray
  签名: (mr : MatchResult α)
  定义体: mr.elts.foldr (init := #[]) fun _ a r => a.foldl (init := r) (· ++ ·)

Depends on / 依赖: a.foldl, mr.elts.foldr
-/
def MatchResult.toArray (mr : MatchResult α) : Array α :=
  mr.elts.foldr (init := #[]) fun _ a r => a.foldl (init := r) (· ++ ·)

/--
Definition of `MatchResult.flatten` / `MatchResult.flatten` 的定义

English:
definition MatchResult.flatten
  signature: (mr : MatchResult α)
  body: mr.elts.foldr (init := #[]) (fun _ arr cand => cand ++ arr)

中文:
定义 MatchResult.flatten
  签名: (mr : MatchResult α)
  定义体: mr.elts.foldr (init := #[]) (fun _ arr cand => cand ++ arr)

Depends on / 依赖: mr.elts.foldr
-/
def MatchResult.flatten (mr : MatchResult α) : Array (Array α) :=
  mr.elts.foldr (init := #[]) (fun _ arr cand => cand ++ arr)

/--
Definition of `PartialMatch` / `PartialMatch` 的定义

English:
structure PartialMatch
  parameters: where
  axioms and operations (4):
    - keys : List Key
    - score : Nat
    - trie : TrieIndex
    - treeStars : Std.HashMap Nat (List Key)  [default: {}]

中文:
结构 PartialMatch
  参数: where
  公理与运算 (4 个):
    - keys : 列表 Key
    - score : 自然数
    - trie : TrieIndex
    - treeStars : Std.HashMap 自然数 (列表 Key)  [默认: {}]
-/
private structure PartialMatch where
  /-- Remaining terms to match -/
  keys : List Key
  /-- Number of non-star matches so far -/
  score : Nat
  /-- Trie to match next -/
  trie : TrieIndex
  /-- Metavariable assignments for `.labelledStar` patterns in the discrimination tree.
  We use a `List Key`, in the reverse order. -/
  treeStars : Std.HashMap Nat (List Key) := {}
  deriving Inhabited


/--
Definition of `matchQueryStar` / `matchQueryStar` 的定义

English:
definition matchQueryStar
  signature: (trie : TrieIndex) (pMatch : PartialMatch)
  body: do
  match skip with
  | skip+1 =>
    let { star, labelledStars, children, .. } ← evalNode trie
    let mut todo := todo
    if let some trie := star then
      todo ← matchQueryStar trie pMatch todo skip
    todo ← labelledStars.foldM (init := todo) fun todo _ trie =>
      matchQueryStar trie pMa

中文:
定义 matchQueryStar
  签名: (trie : TrieIndex) (pMatch : PartialMatch)
  定义体: do
  match skip with
  | skip+1 =>
    let { star, labelledStars, children, .. } ← evalNode trie
    let mut todo := todo
    if let some trie := star then
      todo ← matchQueryStar trie pMatch todo skip
    todo ← labelledStars.foldM (init := todo) fun todo _ trie =>
      matchQueryStar trie pMa
-/
private partial def matchQueryStar (trie : TrieIndex) (pMatch : PartialMatch)
    (todo : Array PartialMatch) (skip : Nat := 1) : TreeM α (Array PartialMatch) := do
  match skip with
  | skip+1 =>
    let { star, labelledStars, children, .. } ← evalNode trie
    let mut todo := todo
    if let some trie := star then
      todo ← matchQueryStar trie pMatch todo skip
    todo ← labelledStars.foldM (init := todo) fun todo _ trie =>
      matchQueryStar trie pMatch todo skip
    todo ← children.foldM (init := todo) fun todo key trie =>
      matchQueryStar trie pMatch todo (skip + key.arity)
    return todo
  | 0 =>
    return todo.push { pMatch with trie }

/--
Definition of `matchEverything` / `matchEverything` 的定义

English:
definition matchEverything
  signature: (root : Std.HashMap Key TrieIndex)
  body: do
  let pMatches ← root.foldM (init := #[]) fun todo key trie =>
    matchQueryStar trie { keys := [], score := 0, trie := 0 } todo key.arity
  pMatches.foldlM (init := {}) fun result pMatch => do
    let { values, .. } ← evalNode pMatch.trie
    return result.push (score := 0) values

中文:
定义 matchEverything
  签名: (root : Std.HashMap Key TrieIndex)
  定义体: do
  let pMatches ← root.foldM (init := #[]) fun todo key trie =>
    matchQueryStar trie { keys := [], score := 0, trie := 0 } todo key.arity
  pMatches.foldlM (init := {}) fun result pMatch => do
    let { values, .. } ← evalNode pMatch.trie
    return result.push (score := 0) values
-/
private def matchEverything (root : Std.HashMap Key TrieIndex) : TreeM α (MatchResult α) := do
  let pMatches ← root.foldM (init := #[]) fun todo key trie =>
    matchQueryStar trie { keys := [], score := 0, trie := 0 } todo key.arity
  pMatches.foldlM (init := {}) fun result pMatch => do
    let { values, .. } ← evalNode pMatch.trie
    return result.push (score := 0) values

/--
Definition of `Key.score` / `Key.score` 的定义

English:
definition Key.score
  signature: (key : Key)
  body: do
  match key with
  | .const n _ =>
    if (← getConstInfo n).type.getForallBody.isSort then
      return 1
    else
      return 10
  | .fvar fvarId _ =>
    if (← fvarId.getType).getForallBody.isSort then
      return 1
    else
      return 10
  | _ => return 10

中文:
定义 Key.score
  签名: (key : Key)
  定义体: do
  match key with
  | .const n _ =>
    if (← getConstInfo n).type.getForallBody.isSort then
      return 1
    else
      return 10
  | .fvar fvarId _ =>
    if (← fvarId.getType).getForallBody.isSort then
      return 1
    else
      return 10
  | _ => return 10
-/
private def Key.score (key : Key) : MetaM Nat := do
  match key with
  | .const n _ =>
    if (← getConstInfo n).type.getForallBody.isSort then
      return 1
    else
      return 10
  | .fvar fvarId _ =>
    if (← fvarId.getType).getForallBody.isSort then
      return 1
    else
      return 10
  | _ => return 10

/--
Definition of `matchTreeStars` / `matchTreeStars` 的定义

English:
definition matchTreeStars
  signature: (key : Key) (node : Trie α) (pMatch : PartialMatch)
  body: do
  let { star, labelledStars, .. } := node
  if labelledStars.isEmpty && star.isNone then
    return todo
  else
    let (dropped, keys) := drop [key] pMatch.keys key.arity
    let mut todo := todo
    if let some trie := star then
      todo := todo.push { pMatch with keys, trie }
    todo ← node

中文:
定义 matchTreeStars
  签名: (key : Key) (node : Trie α) (pMatch : PartialMatch)
  定义体: do
  let { star, labelledStars, .. } := node
  if labelledStars.isEmpty && star.isNone then
    return todo
  else
    let (dropped, keys) := drop [key] pMatch.keys key.arity
    let mut todo := todo
    if let some trie := star then
      todo := todo.push { pMatch with keys, trie }
    todo ← node
-/
private partial def matchTreeStars (key : Key) (node : Trie α) (pMatch : PartialMatch)
    (todo : Array PartialMatch) (unify : Bool) : MetaM (Array PartialMatch) := do
  let { star, labelledStars, .. } := node
  if labelledStars.isEmpty && star.isNone then
    return todo
  else
    let (dropped, keys) := drop [key] pMatch.keys key.arity
    let mut todo := todo
    if let some trie := star then
      todo := todo.push { pMatch with keys, trie }
    todo ← node.labelledStars.foldM (init := todo) fun todo id trie => do
      if let some assignment := pMatch.treeStars[id]? then
        let eq lhs rhs := if unify then (isEq lhs.reverse rhs.reverse).isSome else lhs == rhs
        if eq dropped assignment then
          return todo.push { pMatch with
            keys, trie
            score := (← dropped.mapM (·.score)).foldl (· + ·) pMatch.score }
        else
          return todo
      else
        let treeStars := pMatch.treeStars.insert id dropped
        return todo.push { pMatch with keys, trie, treeStars }
    return todo
where
  /-- Drop the keys corresponding to the next `n` expressions. -/
  drop (dropped rest : List Key) (n : Nat) : (List Key × List Key) := Id.run do
    match n with
    | 0 => (dropped, rest)
    | n + 1 =>
      let key :: rest := rest | panic! "too few keys"
      drop (key :: dropped) rest (n + key.arity)

  isEq (lhs rhs : List Key) : Option (List Key × List Key) := do
    match lhs with
    | [] => panic! "too few keys"
    | .star :: lhs =>
      let (_, rhs) := drop [] rhs 1
      return (lhs, rhs)
    | lHead :: lhs =>
    match rhs with
    | [] => panic! "too few keys"
    | .star :: rhs =>
      let (_, lhs) := drop [] lhs 1
      return (lhs, rhs)
    | rHead :: rhs =>
      guard (lHead == rHead)
      lHead.arity.foldM (init := (lhs, rhs)) fun _ _ (lhs, rhs) => isEq lhs rhs

/--
Definition of `matchKey` / `matchKey` 的定义

English:
definition matchKey
  signature: (key : Key) (children : Std.HashMap Key TrieIndex) (pMatch : PartialMatch)
  body: if key == .opaque then todo else
  match children[key]? with
  | none => todo
  | some trie => todo.push { pMatch with trie, score := pMatch.score + 1 }

中文:
定义 matchKey
  签名: (key : Key) (children : Std.HashMap Key TrieIndex) (pMatch : PartialMatch)
  定义体: if key == .opaque then todo else
  match children[key]? with
  | none => todo
  | some trie => todo.push { pMatch with trie, score := pMatch.score + 1 }
-/
private def matchKey (key : Key) (children : Std.HashMap Key TrieIndex) (pMatch : PartialMatch)
    (todo : Array PartialMatch) : Array PartialMatch :=
  if key == .opaque then todo else
  match children[key]? with
  | none => todo
  | some trie => todo.push { pMatch with trie, score := pMatch.score + 1 }

/--
Definition of `getMatchLoop` / `getMatchLoop` 的定义

English:
definition getMatchLoop
  signature: (todo : Array PartialMatch) (result : MatchResult α)
  body: do
  if h : todo.size = 0 then
    return result
  else
    let pMatch := todo.back
    let todo := todo.pop
    let node ← evalNode pMatch.trie
    match pMatch.keys with
    | [] =>
      getMatchLoop todo (result.push (score := pMatch.score) node.values) unify
    | key :: keys =>
      let pMatc

中文:
定义 getMatchLoop
  签名: (todo : 数组 PartialMatch) (result : MatchResult α)
  定义体: do
  if h : todo.size = 0 then
    return result
  else
    let pMatch := todo.back
    let todo := todo.pop
    let node ← evalNode pMatch.trie
    match pMatch.keys with
    | [] =>
      getMatchLoop todo (result.push (score := pMatch.score) node.values) unify
    | key :: keys =>
      let pMatc
-/
private partial def getMatchLoop (todo : Array PartialMatch) (result : MatchResult α)
    (unify : Bool) : TreeM α (MatchResult α) := do
  if h : todo.size = 0 then
    return result
  else
    let pMatch := todo.back
    let todo := todo.pop
    let node ← evalNode pMatch.trie
    match pMatch.keys with
    | [] =>
      getMatchLoop todo (result.push (score := pMatch.score) node.values) unify
    | key :: keys =>
      let pMatch := { pMatch with keys }
      match key with
      -- `key` is not a `.labelledStar`
      | .star =>
        if unify then
          let todo ← matchQueryStar pMatch.trie pMatch todo
          getMatchLoop todo result unify
        else
          let todo ← matchTreeStars key node pMatch todo unify
          getMatchLoop todo result unify
      | _ =>
        let todo ← matchTreeStars key node pMatch todo unify
        let todo := matchKey key node.children pMatch todo
        getMatchLoop todo result unify

/--
Definition of `matchTreeRootStar` / `matchTreeRootStar` 的定义

English:
definition matchTreeRootStar
  signature: (root : Std.HashMap Key TrieIndex)
  body: do
  let mut result := {}
  if let some trie := root[Key.labelledStar 0]? then
    let { values, .. } ← evalNode trie
    result := result.push (score := 0) values
  if let some trie := root[Key.star]? then
    let { values, .. } ← evalNode trie
    result := result.push (score := 0) values
  return

中文:
定义 matchTreeRootStar
  签名: (root : Std.HashMap Key TrieIndex)
  定义体: do
  let mut result := {}
  if let some trie := root[Key.labelledStar 0]? then
    let { values, .. } ← evalNode trie
    result := result.push (score := 0) values
  if let some trie := root[Key.star]? then
    let { values, .. } ← evalNode trie
    result := result.push (score := 0) values
  return
-/
private def matchTreeRootStar (root : Std.HashMap Key TrieIndex) : TreeM α (MatchResult α) := do
  let mut result := {}
  if let some trie := root[Key.labelledStar 0]? then
    let { values, .. } ← evalNode trie
    result := result.push (score := 0) values
  if let some trie := root[Key.star]? then
    let { values, .. } ← evalNode trie
    result := result.push (score := 0) values
  return result

/--
Definition of `getMatch` / `getMatch` 的定义

English:
definition getMatch
  signature: (d : RefinedDiscrTree α) (e : Expr) (unify matchRootStar : Bool)
  body: do
  withReducible do runTreeM d do
    let (key, keys) ← encodeExpr e (labelledStars := false)
    let pMatch : PartialMatch := { keys, score := 0, trie := default }
    if key == .star then
      if matchRootStar then
        if unify then
          matchEverything d.root
        else
          ma

中文:
定义 getMatch
  签名: (d : RefinedDiscrTree α) (e : Expr) (unify matchRootStar : 布尔值)
  定义体: do
  withReducible do runTreeM d do
    let (key, keys) ← encodeExpr e (labelledStars := false)
    let pMatch : PartialMatch := { keys, score := 0, trie := default }
    if key == .star then
      if matchRootStar then
        if unify then
          matchEverything d.root
        else
          ma
-/
def getMatch (d : RefinedDiscrTree α) (e : Expr) (unify matchRootStar : Bool) :
    MetaM (MatchResult α × RefinedDiscrTree α) := do
  withReducible do runTreeM d do
    let (key, keys) ← encodeExpr e (labelledStars := false)
    let pMatch : PartialMatch := { keys, score := 0, trie := default }
    if key == .star then
      if matchRootStar then
        if unify then
          matchEverything d.root
        else
          matchTreeRootStar d.root
      else
        return {}
    else
      let todo := matchKey key d.root pMatch #[]
      if matchRootStar then
        getMatchLoop todo (← matchTreeRootStar d.root) unify
      else
        getMatchLoop todo {} unify

end Lean.Meta.RefinedDiscrTree
