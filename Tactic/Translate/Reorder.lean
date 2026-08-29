/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init

/-!
# Reordering arguments in a translation

This module defines reorders, which can be specified with `to_dual (reorder := ...)` or
`to_additive (reorder := ...)`, to deal with definitions and theorems that need to have their
arguments and/or universe parameters reordered.

A reordering is specified using disjoint cycle notation. For example, `1 2 3, 4 5` will
move the 1st argument to the 2nd, move the 2nd to the 3rd, and the 3rd to the 1st, and it will
swap the 4th and 5th arguments.

Instead of using numbers to refer to argument, you can also refer to them by name. For example
`a b` will swap the arguments named `a` and `b`. This is implemented in `elabArgStx`.

To specify reordering arguments of arguments, the syntax is recursive. For example,
`4 (1 2)` will reorder the first two arguments of the fourth argument.

If the declaration is translated to itself or to an existing declaration,
the heuristic in `guessReorder` tries to predict the argument reorder.
This is done with a syntactic comparison of which variable is moved where.

The universe reordering is always inferred automatically, using `guessUnivReorder`.

## Examples

- `to_dual` needs to swap the arguments of some definitions to translate them,
  such as `a ≤ b` ↦ `b ≤ a` and `a ⇨ b` ↦ `b \ a`.
  In these cases, we reorder the 3rd and 4th arguments, which can be specified using
  `@[to_dual (reorder := 3 4)]`.

- `to_additive` needs to swap the arguments when translating `a ^ n` ↦ `n • a`.

- Some theorems are dual to themselves only after reordering some arguments.
  For example, `le_total : ∀ a b : α, a ≤ b ∨ b ≤ a` is dual to itself after swapping `a` and `b`.
  Thanks to the heuristic in `guessReorder`, it suffices to write `@[to_dual self]`.

## Implementation details

Permutation are stored as their disjoint cycle representation (`Permutation`).
This allows efficiently permuting an array/list of arguments/universes
(`Permutation.permute!`/`Permutation.permuteList!`).

-/

public meta section

namespace Mathlib.Tactic.Translate
open Lean Meta Elab

/--
Definition of `Permutation` / `Permutation` 的定义

English:
abbreviation Permutation
  body: List {l : List Nat // 2 <= l.length}

中文:
缩写 置换
  定义体: List {l : List Nat // 2 <= l.length}

Depends on / 依赖: l.length, length
-/
abbrev Permutation := List {l : List Nat // 2 <= l.length}

namespace Permutation

/--
Definition of `permute!` / `permute!` 的定义

English:
definition permute!
  signature: {α} [Inhabited α] (c : Permutation)
  body: c.foldl (cyclicPermute! · ·.1)

中文:
定义 permute!
  签名: {α} [可居 α] (c : 置换)
  定义体: c.foldl (cyclicPermute! · ·.1)

Depends on / 依赖: c.foldl, cyclicPermute
-/
def permute! {α} [Inhabited α] (c : Permutation) : Array α -> Array α :=
  c.foldl (cyclicPermute! · ·.1)
where
  /-- Permute the array using a sequence of indices defining a cyclic permutation.
  If the list of indices `l = [i₁, i₂, ..., iₙ]` are all distinct then
  `(cyclicPermute! a l)[iₖ₊₁] = a[iₖ]` and `(cyclicPermute! a l)[i₀] = a[iₙ]` -/
  cyclicPermute! : Array α -> List Nat -> Array α
    | a, [] => a
    | a, i :: is => cyclicPermuteAux a is a[i]! i
  cyclicPermuteAux : Array α -> List Nat -> α -> Nat -> Array α
    | a, [], x, i0 => a.set! i0 x
    | a, i :: is, x, i0 =>
      let (y, a) := a.swapAt! i x
      cyclicPermuteAux a is y i0

/--
Definition of `permuteList!` / `permuteList!` 的定义

English:
definition permuteList!
  signature: {α} [Inhabited α] (p : Permutation) (us : List α)
  body: if p.isEmpty then us else (p.permute! us.toArray).toList

中文:
定义 permuteList!
  签名: {α} [可居 α] (p : 置换) (us : 列表 α)
  定义体: if p.isEmpty then us else (p.permute! us.toArray).toList

Depends on / 依赖: isEmpty, p.isEmpty, p.permute, permute, toArray, toList, us.toArray
-/
def permuteList! {α} [Inhabited α] (p : Permutation) (us : List α) : List α :=
  if p.isEmpty then us else (p.permute! us.toArray).toList

/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: (c : Permutation)
  body: c.map (⟨·.1.reverse, by grind⟩)

中文:
定义 reverse
  签名: (c : 置换)
  定义体: c.map (⟨·.1.reverse, by grind⟩)

Depends on / 依赖: c.map, reverse
-/
def reverse (c : Permutation) : Permutation :=
  c.map (⟨·.1.reverse, by grind⟩)

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (p : Permutation)
  body: .fold max 0 .map (· + 1) p.iter.flatMap (·.1.iter)

中文:
定义 range
  签名: (p : 置换)
  定义体: .fold max 0 .map (· + 1) p.iter.flatMap (·.1.iter)

Depends on / 依赖: flatMap, p.iter.flatMap
-/
def range (p : Permutation) : Nat :=
.fold max 0 .map (· + 1) p.iter.flatMap (·.1.iter)

/--
Definition of `beq` / `beq` 的定义

English:
definition beq
  signature: (p₁ p₂ : Permutation)
  body: p₁.range == p₂.range &&
    let rangeArr := (0...p₁.range).toArray;
    p₁.permute! rangeArr == p₂.permute! rangeArr

中文:
定义 beq
  签名: (p₁ p₂ : 置换)
  定义体: p₁.range == p₂.range &&
    let rangeArr := (0...p₁.range).toArray;
    p₁.permute! rangeArr == p₂.permute! rangeArr

Depends on / 依赖: permute, rangeArr, toArray
-/
def beq (p₁ p₂ : Permutation) : Bool :=
  p₁.range == p₂.range &&
    let rangeArr := (0...p₁.range).toArray;
    p₁.permute! rangeArr == p₂.permute! rangeArr

end Permutation

/--
Definition of `ArgReorder` / `ArgReorder` 的定义

English:
structure ArgReorder
  parameters: where
  axioms and operations (2):
    - perm : Permutation  [default: []]
    - argReorders : Array (Nat × ArgReorder)  [default: #[]]

中文:
结构 ArgReorder
  参数: where
  公理与运算 (2 个):
    - perm : 置换  [默认: []]
    - argReorders : 数组 (自然数 × ArgReorder)  [默认: #[]]
-/
structure ArgReorder where
  /-- The list of disjoint cycles that represents the permutation. -/
  perm : Permutation := []
  /-- The recursive reorders for reordering arguments of arguments.
  For the purpose of checking equality between reorders, this should be sorted. -/
  argReorders : Array (Nat × ArgReorder) := #[]
  deriving Inhabited

namespace ArgReorder

/--
Definition of `isEmpty` / `isEmpty` 的定义

English:
definition isEmpty
  signature: (r : ArgReorder)
  body: r matches ⟨[], #[]⟩

中文:
定义 isEmpty
  签名: (r : ArgReorder)
  定义体: r matches ⟨[], #[]⟩

Depends on / 依赖: matches
-/
def isEmpty (r : ArgReorder) : Bool := r matches ⟨[], #[]⟩

/--
Definition of `permute!` / `permute!` 的定义

English:
definition permute!
  signature: {α} [Inhabited α] (r : ArgReorder)
  body: r.perm.permute!

中文:
定义 permute!
  签名: {α} [可居 α] (r : ArgReorder)
  定义体: r.perm.permute!

Depends on / 依赖: permute, r.perm.permute
-/
def permute! {α} [Inhabited α] (r : ArgReorder) : Array α -> Array α :=
  r.perm.permute!

/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: (r : ArgReorder)
  body: {
  perm := r.perm.reverse
  argReorders := r.argReorders.map fun x => (permuteSingle r x.1, x.2.reverse)
}
decreasing_by
  cases r; grind [-> Array.sizeOf_lt_of_mem]

中文:
定义 reverse
  签名: (r : ArgReorder)
  定义体: {
  perm := r.perm.reverse
  argReorders := r.argReorders.map fun x => (permuteSingle r x.1, x.2.reverse)
}
decreasing_by
  cases r; grind [-> Array.sizeOf_lt_of_mem]
-/
def reverse (r : ArgReorder) : ArgReorder := {
  perm := r.perm.reverse
  argReorders := r.argReorders.map fun x => (permuteSingle r x.1, x.2.reverse)
}
decreasing_by
  cases r; grind [-> Array.sizeOf_lt_of_mem]
where
  /-- Compute where `ArgReorder.permute!` sends the `n`-th element in an array. -/
  permuteSingle (r : ArgReorder) (n : Nat) : Nat :=
.getD n r.perm.findSome? (fun cycle => getCycleSuccessor n (cycle.1.head (by grind)) cycle.1)
  /-- Return the successor of `n` in a cycle, where `head` is the head of the cycle list. -/
  getCycleSuccessor (n head : Nat) : List Nat -> Option Nat
    | [] => none
    | b :: bs => if b = n then bs.head?.getD head else getCycleSuccessor n head bs

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (r : ArgReorder)
  body: r.argReorders.foldl (max · <| ·.1 + 1)
.fold max 0 .map (· + 1) r.perm.iter.flatMap (·.1.iter)

中文:
定义 range
  签名: (r : ArgReorder)
  定义体: r.argReorders.foldl (max · <| ·.1 + 1)
.fold max 0 .map (· + 1) r.perm.iter.flatMap (·.1.iter)

Depends on / 依赖: argReorders, flatMap, r.argReorders.foldl, r.perm.iter.flatMap
-/
def range (r : ArgReorder) : Nat :=
r.argReorders.foldl (max · <| ·.1 + 1)
.fold max 0 .map (· + 1) r.perm.iter.flatMap (·.1.iter)

/--
Definition of `beq` / `beq` 的定义

English:
definition beq
  signature: (r₁ r₂ : ArgReorder)
  body: r₁.perm.beq r₂.perm &&
    have : BEq ArgReorder := ⟨beq⟩
    r₁.argReorders == r₂.argReorders

中文:
定义 beq
  签名: (r₁ r₂ : ArgReorder)
  定义体: r₁.perm.beq r₂.perm &&
    have : BEq ArgReorder := ⟨beq⟩
    r₁.argReorders == r₂.argReorders
-/
partial def beq (r₁ r₂ : ArgReorder) : Bool :=
  r₁.perm.beq r₂.perm &&
    have : BEq ArgReorder := ⟨beq⟩
    r₁.argReorders == r₂.argReorders

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BEq ArgReorder
  body: ⟨beq⟩

中文:
实例 :
  签名: BEq ArgReorder
  定义体: ⟨beq⟩
-/
instance : BEq ArgReorder := ⟨beq⟩

/--
Definition of `toString` / `toString` 的定义

English:
definition toString
  signature: (r : ArgReorder)
  body: let perm := r.perm.map (" ".intercalate <| ·.1.map (s!"{· + 1}"))
  let argReorders := r.argReorders.map (fun x => s!"{x.1 + 1} ({x.2.toString})")
  s!"{", ".intercalate (perm ++ argReorders.toList)}"
decreasing_by
  cases r; grind [-> Array.sizeOf_lt_of_mem]

中文:
定义 toString
  签名: (r : ArgReorder)
  定义体: let perm := r.perm.map (" ".intercalate <| ·.1.map (s!"{· + 1}"))
  let argReorders := r.argReorders.map (fun x => s!"{x.1 + 1} ({x.2.toString})")
  s!"{", ".intercalate (perm ++ argReorders.toList)}"
decreasing_by
  cases r; grind [-> Array.sizeOf_lt_of_mem]

Depends on / 依赖: Array.sizeOf_lt_of_mem, argReorders, argReorders.toList, decreasing_by, intercalate, r.argReorders.map, r.perm.map, sizeOf_lt_of_mem, toList, toString
-/
def toString (r : ArgReorder) : String :=
  let perm := r.perm.map (" ".intercalate <| ·.1.map (s!"{· + 1}"))
  let argReorders := r.argReorders.map (fun x => s!"{x.1 + 1} ({x.2.toString})")
  s!"{", ".intercalate (perm ++ argReorders.toList)}"
decreasing_by
  cases r; grind [-> Array.sizeOf_lt_of_mem]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString ArgReorder
  body: ⟨fun x => x.toString⟩

中文:
实例 :
  签名: ToString ArgReorder
  定义体: ⟨fun x => x.toString⟩

Depends on / 依赖: toString, x.toString
-/
instance : ToString ArgReorder := ⟨fun x => x.toString⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToMessageData ArgReorder
  body: ⟨fun x => x.toString⟩

中文:
实例 :
  签名: ToMessageData ArgReorder
  定义体: ⟨fun x => x.toString⟩

Depends on / 依赖: toString, x.toString
-/
instance : ToMessageData ArgReorder := ⟨fun x => x.toString⟩

end ArgReorder

/--
Definition of `Reorder` / `Reorder` 的定义

English:
structure Reorder
  parameters: where
  axioms and operations (2):
    - univReorder : Permutation  [default: []]
    - reorder : ArgReorder  [default: {}]

中文:
结构 Reorder
  参数: where
  公理与运算 (2 个):
    - univReorder : 置换  [默认: []]
    - reorder : ArgReorder  [默认: {}]
-/
structure Reorder where
  /-- The reordering of universe levels. -/
  univReorder : Permutation := []
  /-- The reordering of arguments. -/
  reorder : ArgReorder := {}

/--
Definition of `Reorder.reverse` / `Reorder.reverse` 的定义

English:
definition Reorder.reverse
  signature: (r : Reorder)
  body: r.univReorder.reverse
  reorder := r.reorder.reverse

中文:
定义 Reorder.reverse
  签名: (r : Reorder)
  定义体: r.univReorder.reverse
  reorder := r.reorder.reverse

Depends on / 依赖: r.univReorder.reverse, reverse, univReorder
-/
def Reorder.reverse (r : Reorder) : Reorder where
  univReorder := r.univReorder.reverse
  reorder := r.reorder.reverse

/-! ### Reordering an expression -/

/--
Definition of `fixBinderInfos` / `fixBinderInfos` 的定义

English:
definition fixBinderInfos
  signature: (bis : List BinderInfo) (e : Expr)
  body: match bis, e with
  | bi :: bis, .forallE n d b _ => .forallE n d (fixBinderInfos bis b) bi
  | bi :: bis, .lam n d b _ => .lam n d (fixBinderInfos bis b) bi
  | _, _ => e

中文:
定义 fixBinderInfos
  签名: (bis : 列表 BinderInfo) (e : Expr)
  定义体: match bis, e with
  | bi :: bis, .forallE n d b _ => .forallE n d (fixBinderInfos bis b) bi
  | bi :: bis, .lam n d b _ => .lam n d (fixBinderInfos bis b) bi
  | _, _ => e
-/
private def fixBinderInfos (bis : List BinderInfo) (e : Expr) : Expr :=
  match bis, e with
  | bi :: bis, .forallE n d b _ => .forallE n d (fixBinderInfos bis b) bi
  | bi :: bis, .lam n d b _ => .lam n d (fixBinderInfos bis b) bi
  | _, _ => e

/-
In the implementation of `reorderForall` and `reorderLambda` we use metavariables.
To reorder the arguments in one, we assign it to a reordered new metavariable.
This trick lets us avoid traversing the expression manually when handling recursive reorderings.
Instead, we implicitly rely on `instantiateMVars`.
-/
mutual

/--
Definition of `reorderMVars` / `reorderMVars` 的定义

English:
definition reorderMVars
  signature: (mvars : Array Expr) (reorder : ArgReorder)
  body: do
  let mut mvars := mvars
  for (arg, argReorder) in reorder.argReorders do
    let mvarId := mvars[arg]!.mvarId!
    let decl ← mvarId.getDecl
    let mvarId' ← mkFreshExprMVar (← reorderForall argReorder decl.type) (userName := decl.userName)
    -- Note: we assign `mvarId` in terms of `mvarId'`

中文:
定义 reorderMVars
  签名: (mvars : 数组 Expr) (reorder : ArgReorder)
  定义体: do
  let mut mvars := mvars
  for (arg, argReorder) in reorder.argReorders do
    let mvarId := mvars[arg]!.mvarId!
    let decl ← mvarId.getDecl
    let mvarId' ← mkFreshExprMVar (← reorderForall argReorder decl.type) (userName := decl.userName)
    -- Note: we assign `mvarId` in terms of `mvarId'`
-/
private partial def reorderMVars (mvars : Array Expr) (reorder : ArgReorder) :
    MetaM (Array Expr) := do
  let mut mvars := mvars
  for (arg, argReorder) in reorder.argReorders do
    let mvarId := mvars[arg]!.mvarId!
    let decl ← mvarId.getDecl
    let mvarId' ← mkFreshExprMVar (← reorderForall argReorder decl.type) (userName := decl.userName)
    -- Note: we assign `mvarId` in terms of `mvarId'`, and to do this we need to reorder `mvarId'`
    -- with the reverse reorder of `argReorder`.
    mvarId.assign (← reorderLambda argReorder.reverse mvarId')
    mvars := mvars.set! arg mvarId'
  return reorder.permute! mvars

/--
Definition of `reorderForall` / `reorderForall` 的定义

English:
definition reorderForall
  signature: (reorder : ArgReorder) (e : Expr)
  body: do
  let (mvars, bis, e) ← forallMetaBoundedTelescope e reorder.range
  unless mvars.size = reorder.range do
    throwError "the permutation (reorder := {reorder}) is out of bounds, \
      the type{indentExpr e}\nhas only {mvars.size} arguments"
.toList let bis := reorder.permute! bis
  -- Note tha

中文:
定义 reorderForall
  签名: (reorder : ArgReorder) (e : Expr)
  定义体: do
  let (mvars, bis, e) ← forallMetaBoundedTelescope e reorder.range
  unless mvars.size = reorder.range do
    throwError "the permutation (reorder := {reorder}) is out of bounds, \
      the type{indentExpr e}\nhas only {mvars.size} arguments"
.toList let bis := reorder.permute! bis
  -- Note tha
-/
partial def reorderForall (reorder : ArgReorder) (e : Expr) : MetaM Expr := do
  let (mvars, bis, e) ← forallMetaBoundedTelescope e reorder.range
  unless mvars.size = reorder.range do
    throwError "the permutation (reorder := {reorder}) is out of bounds, \
      the type{indentExpr e}\nhas only {mvars.size} arguments"
.toList let bis := reorder.permute! bis
  -- Note that `mkForallFVars` also works with mvars.
fixBinderInfos bis < > mkForallFVars (← reorderMVars mvars reorder) e

/--
Definition of `reorderLambda` / `reorderLambda` 的定义

English:
definition reorderLambda
  signature: (reorder : ArgReorder) (e : Expr)
  body: do
  let (mvars, bis, _) ← forallMetaBoundedTelescope (← inferType e) reorder.range
  unless mvars.size = reorder.range do
    throwError "the permutation (reorder := {reorder}) is out of bounds, \
      the function{indentExpr e}\nhas only {mvars.size} arguments"
.toList let bis := reorder.permute!

中文:
定义 reorderLambda
  签名: (reorder : ArgReorder) (e : Expr)
  定义体: do
  let (mvars, bis, _) ← forallMetaBoundedTelescope (← inferType e) reorder.range
  unless mvars.size = reorder.range do
    throwError "the permutation (reorder := {reorder}) is out of bounds, \
      the function{indentExpr e}\nhas only {mvars.size} arguments"
.toList let bis := reorder.permute!
-/
partial def reorderLambda (reorder : ArgReorder) (e : Expr) : MetaM Expr := do
  let (mvars, bis, _) ← forallMetaBoundedTelescope (← inferType e) reorder.range
  unless mvars.size = reorder.range do
    throwError "the permutation (reorder := {reorder}) is out of bounds, \
      the function{indentExpr e}\nhas only {mvars.size} arguments"
.toList let bis := reorder.permute! bis
  -- Note that `mkLambdaFVars` also works with mvars.
fixBinderInfos bis < > mkLambdaFVars (← reorderMVars mvars reorder) (e.beta mvars)

end

/-! ### Guessing the reorder given the reordered expression -/

/--
Definition of `decomposePerm` / `decomposePerm` 的定义

English:
definition decomposePerm
  signature: {n} (map : Vector (Option (Fin n)) n)
  body: Id.run do
  let mut map := map
  let mut perm := []
  for h : i in *...n do
    let mut some j := map[i] | continue
    if i = j then continue
    let mut cycle := ⟨[i, j], by grind⟩
    repeat do
      let some j' := map[j] | return [] -- If the permutation is malformed, return `[]`.
      -- To av

中文:
定义 decomposePerm
  签名: {n} (map : Vector (选项类型 (有限集 n)) n)
  定义体: Id.run do
  let mut map := map
  let mut perm := []
  for h : i in *...n do
    let mut some j := map[i] | continue
    if i = j then continue
    let mut cycle := ⟨[i, j], by grind⟩
    repeat do
      let some j' := map[j] | return [] -- If the permutation is malformed, return `[]`.
      -- To av
-/
private def decomposePerm {n} (map : Vector (Option (Fin n)) n) : Permutation := Id.run do
  let mut map := map
  let mut perm := []
  for h : i in *...n do
    let mut some j := map[i] | continue
    if i = j then continue
    let mut cycle := ⟨[i, j], by grind⟩
    repeat do
      let some j' := map[j] | return [] -- If the permutation is malformed, return `[]`.
      -- To avoid computing the same cycle multiple times, and to avoid infinite loops,
      -- we erase visited elements from `map`.
      map := map.set! j none
      if j' = i then break
      j := j'
      cycle := ⟨cycle.1 ++ [j.val], by grind⟩
    perm := cycle :: perm
  return perm

/--
Definition of `getPermutation` / `getPermutation` 的定义

English:
definition getPermutation
  signature: {α : Type*} [BEq α] (src : Array α) (tgt : Array α)
  body: do
  let n := src.size
  if h : n = tgt.size then
    have src : Vector α n := src.toVector
    have tgt : Vector α n := h ▸ tgt.toVector
    return decomposePerm (← src.mapM (some <$> tgt.finIdxOf? ·))
  else
    none

中文:
定义 getPermutation
  签名: {α : 类型} [BEq α] (src : 数组 α) (tgt : 数组 α)
  定义体: do
  let n := src.size
  if h : n = tgt.size then
    have src : Vector α n := src.toVector
    have tgt : Vector α n := h ▸ tgt.toVector
    return decomposePerm (← src.mapM (some <$> tgt.finIdxOf? ·))
  else
    none
-/
def getPermutation {α : Type*} [BEq α] (src : Array α) (tgt : Array α) : Option Permutation := do
  let n := src.size
  if h : n = tgt.size then
    have src : Vector α n := src.toVector
    have tgt : Vector α n := h ▸ tgt.toVector
    return decomposePerm (← src.mapM (some <$> tgt.finIdxOf? ·))
  else
    none

/--
Definition of `depForallDepth` / `depForallDepth` 的定义

English:
definition depForallDepth
  signature: : Expr -> Nat
  body: depForallDepth b
    if d == 0 && !b.hasLooseBVar 0 then 0 else d + 1
  | _ => 0

中文:
定义 depForallDepth
  签名: : Expr -> 自然数
  定义体: depForallDepth b
    if d == 0 && !b.hasLooseBVar 0 then 0 else d + 1
  | _ => 0
-/
private def depForallDepth : Expr -> Nat
  | .forallE _ _ b _ =>
    let d := depForallDepth b
    if d == 0 && !b.hasLooseBVar 0 then 0 else d + 1
  | _ => 0

/--
Definition of `guessReorder` / `guessReorder` 的定义

English:
definition guessReorder
  signature: (src tgt : Expr)
  body: withReducible do
  let src ← whnf src; let tgt ← whnf tgt
  let depth := depForallDepth src
  unless depth == depForallDepth tgt do return {}
  forallBoundedTelescope src depth fun srcVars src => do
  forallBoundedTelescope tgt depth fun tgtVars tgt => do
let srcMap : Std.HashMap FVarId Nat := .ofAr

中文:
定义 guessReorder
  签名: (src tgt : Expr)
  定义体: withReducible do
  let src ← whnf src; let tgt ← whnf tgt
  let depth := depForallDepth src
  unless depth == depForallDepth tgt do return {}
  forallBoundedTelescope src depth fun srcVars src => do
  forallBoundedTelescope tgt depth fun tgtVars tgt => do
let srcMap : Std.HashMap FVarId Nat := .ofAr
-/
partial def guessReorder (src tgt : Expr) : MetaM ArgReorder := withReducible do
  let src ← whnf src; let tgt ← whnf tgt
  let depth := depForallDepth src
  unless depth == depForallDepth tgt do return {}
  forallBoundedTelescope src depth fun srcVars src => do
  forallBoundedTelescope tgt depth fun tgtVars tgt => do
let srcMap : Std.HashMap FVarId Nat := .ofArray srcVars.mapIdx fun i x => (x.fvarId!, i)
let tgtMap : Std.HashMap FVarId Nat := .ofArray tgtVars.mapIdx fun i x => (x.fvarId!, i)
  let perm := (← visit src tgt (.replicate depth none) |>.run (srcMap, tgtMap) |>.run' {} |>.run)
.elim [] decomposePerm
  -- Recursively guess the reorder in the hypotheses
  let mut argReorders := #[]
  for i in *...depth do
    let r ← guessReorder (← inferType srcVars[i]!) (← inferType tgtVars[i]!)
    unless r.isEmpty do
      argReorders := argReorders.push (i, r)
  let mut src := src; let mut tgt := tgt
  let mut n := depth
  while src.isForall && tgt.isForall do
    let r ← guessReorder src.bindingDomain! tgt.bindingDomain!
    unless r.isEmpty do
      argReorders := argReorders.push (n, r)
    -- This won't create loose bound variables, because we already introduced all dependent foralls.
    src := src.bindingBody!
    tgt := tgt.bindingBody!
    n := n + 1
  return { perm, argReorders }
where
  /-- Determine for each `i : Fin n` to what `j : Fin n` it should get translated. -/
  visit (src tgt : Expr) {n : Nat} (map : Vector (Option (Fin n)) n) :
      ReaderT (Std.HashMap FVarId Nat × Std.HashMap FVarId Nat)
      StateRefT (Std.HashSet (Expr × Expr)) (OptionT BaseIO) (Vector (Option (Fin n)) n) := do
    if (← get).contains (src, tgt) then return map
    let map ← match src, tgt with
      | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => visit d₁ d₂ map >>= visit b₁ b₂
      | .lam _ d₁ b₁ _ , .lam _ d₂ b₂ _ => visit d₁ d₂ map >>= visit b₁ b₂
      | .mdata _ e₁ , .mdata _ e₂ => visit e₁ e₂ map
      | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => visit t₁ t₂ map >>= visit v₁ v₂ >>= visit b₁ b₂
      | .app f₁ a₁ , .app f₂ a₂ => visit f₁ f₂ map >>= visit a₁ a₂
      | .proj _ _ e₁ , .proj _ _ e₂ => visit e₁ e₂ map
      | .fvar fvarId₁ , .fvar fvarId₂ =>
        let some i₁ := (← read).1[fvarId₁]? | pure map
        let some i₂ := (← read).2[fvarId₂]? | pure map
        if h : i₂ < n then
          if let some i₂' := map[i₁]! then
            guard (i₂ == i₂') -- If `i₂ ≠ i₂'`, it's not clear what `i₁` should be translated to.
            pure map
          else
pure map.set! i₁ (some ⟨i₂, h⟩)
        else
          panic! s!"index {i₂} is out of bounds ({n})"
      /- To avoid false positives, we do a sanity check to make sure that the two expressions are
      indeed of the same shape. Note that we cannot check for `e₁ == e₁`, because the universes
      in `e₁` and `e₂` might be different (because we decide only later whether to swap them). -/
      | .lit _, .lit _ | .bvar _, .bvar _ | .sort _, .sort _ | .const .., .const .. => pure map
      | _, _ => failure
    modify (·.insert (src, tgt))
    return map

/-! ### Syntax for specifying a reorder -/

-- Note: We have to use `declare_syntax_cat` because the reorder syntax is recursive.
/-- The syntax category for the reorder syntax. -/
declare_syntax_cat translateReorder

syntax reorderPart := (ident <|> num)+ (" (" translateReorder ")")?
attribute [nolint docBlame] reorderPart

/--
`(reorder := ...)` reorders the arguments/hypotheses in the generated declaration.
This is used in `to_dual` to swap the arguments in `≤`, `<` and `⟶`,
and it is used in `to_additive` to translate from `a ^ n` to `n • a`.
It uses disjoint cycle notation for the permutation. For reordering arguments of an argument `a`,
it uses the notation `a (...)` where `...` can be any reorder.

For example:
- `(reorder := α β, 5 6)` swaps the arguments `α` and `β` with each other and the fifth and
  the sixth argument.
- `(reorder := 3 4 5)` will move the fifth argument before the third argument.
- `(reorder := H (x y))` will swap the arguments `x` and `y` that appear in the hypothesis `H`.

If the translated declaration already exists (i.e. when using `existing` or `self`), the reorder
argument is automatically inferred using the function `guessReorder`. -/
syntax (name := reorder) reorderPart,* : translateReorder

/--
Definition of `elabArgStx` / `elabArgStx` 的定义

English:
definition elabArgStx
  signature: (stx : TSyntax [`ident, `num]) (argNames : Array Name) (fvars : Array Expr)
  body: do
  let n ← match stx with
    | `($name:ident) => match argNames.idxOf? name.getId with
      | some n => pure n
      | none => throwErrorAt stx
        "invalid argument `{stx}`, it is not an argument of `{head}`."
    | `($n:num) =>
      if n.getNat = 0 then
        throwErrorAt stx "invalid i

中文:
定义 elabArgStx
  签名: (stx : TSyntax [`ident, `num]) (argNames : 数组 Name) (fvars : 数组 Expr)
  定义体: do
  let n ← match stx with
    | `($name:ident) => match argNames.idxOf? name.getId with
      | some n => pure n
      | none => throwErrorAt stx
        "invalid argument `{stx}`, it is not an argument of `{head}`."
    | `($n:num) =>
      if n.getNat = 0 then
        throwErrorAt stx "invalid i
-/
def elabArgStx (stx : TSyntax [`ident, `num]) (argNames : Array Name) (fvars : Array Expr)
    (head : MessageData) : MetaM Nat := do
  let n ← match stx with
    | `($name:ident) => match argNames.idxOf? name.getId with
      | some n => pure n
      | none => throwErrorAt stx
        "invalid argument `{stx}`, it is not an argument of `{head}`."
    | `($n:num) =>
      if n.getNat = 0 then
        throwErrorAt stx "invalid index `{stx}`, arguments are counted starting from 1."
      if n.getNat > fvars.size then
        throwErrorAt stx "index `{stx}` is out of bounds, there are only `{fvars.size}` arguments"
      pure (n.getNat - 1)
    | _ => throwUnsupportedSyntax
.run' Elab.Term.addTermInfo' stx fvars[n]!
  return n

/--
Definition of `elabReorder` / `elabReorder` 的定义

English:
definition elabReorder
  signature: (stx : TSyntax `translateReorder) (argNames : Array Name)
  body: match stx with
  | `(reorder| $[$parts],*) => withRef stx do
    let mut perm := []
    let mut argReorders := #[]
    for part in parts do
      let `(reorderPart| $[$cycleStx]* $[($argReorder?)]?) := part | throwUnsupportedSyntax
      let cycle ← cycleStx.toList.mapM (elabArgStx · argNames args h

中文:
定义 elabReorder
  签名: (stx : TSyntax `translateReorder) (argNames : 数组 Name)
  定义体: match stx with
  | `(reorder| $[$parts],*) => withRef stx do
    let mut perm := []
    let mut argReorders := #[]
    for part in parts do
      let `(reorderPart| $[$cycleStx]* $[($argReorder?)]?) := part | throwUnsupportedSyntax
      let cycle ← cycleStx.toList.mapM (elabArgStx · argNames args h
-/
partial def elabReorder (stx : TSyntax `translateReorder) (argNames : Array Name)
    (args : Array Expr) (head : MessageData) : MetaM ArgReorder :=
  match stx with
  | `(reorder| $[$parts],*) => withRef stx do
    let mut perm := []
    let mut argReorders := #[]
    for part in parts do
      let `(reorderPart| $[$cycleStx]* $[($argReorder?)]?) := part | throwUnsupportedSyntax
      let cycle ← cycleStx.toList.mapM (elabArgStx · argNames args head)
      if h : 2 <= cycle.length then
        perm := ⟨cycle, h⟩ :: perm
      else if argReorder?.isNone then
        throwErrorAt part "\
          Invalid cycle `{part}`, a cycle must have at least 2 elements.\n\
            See the docstring of `reorder` for how to specify reorders."
      if let some argReorder := argReorder? then
        for arg in cycle do
        let reorder ←
          -- Use a reducing telescope to see through `autoParam`.
withReducible forallTelescopeReducing (← inferType args[arg]!) fun xs _ => do
            let argNames ← xs.mapM (·.fvarId!.getUserName)
            -- Recursively elaborate the nested reorder syntax.
            elabReorder argReorder argNames xs m!"{args[arg]!}"
        argReorders := argReorders.push (arg, reorder)
    -- Check that the cycles are disjoint
.foldM (init := ({} : Std.HashSet Nat)) fun s n => do _ ← perm.iter.flatMap (·.1.iter)
      let (contains, s) := s.containsThenInsert n
      if contains then throwError
        "Please remove the duplicate entries from the disjoint cycle representation.\n\
        See the docstring of `reorder` for how to specify reorders."
      return s
    argReorders := argReorders.qsort (·.1 < ·.1)
    -- check that the `argReorders` aren't duplicated.
    for h : i in *...(argReorders.size - 1) do
      let arg₀ := argReorders[i]; let arg₁ := argReorders[i + 1]
      if arg₀.1 == arg₁.1 then
        throwError "The reorder within argument {arg₀.1 + 1} has been set to both \
          `{arg₀.2.toString}` and `{arg₁.2.toString}`. Please specify it only once."
    return { perm, argReorders }
  | _ => throwUnsupportedSyntax

end Mathlib.Tactic.Translate
