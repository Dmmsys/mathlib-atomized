/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Edward Ayers
-/
module

public import Mathlib.Init

/-!
# Fixpoint function with memoisation

-/

variable {α β : Type}

@[noinline, deprecated "deprecated without replacement" (since := "2026-01-24")]
/--
Definition of `injectIntoBaseIO` / `injectIntoBaseIO` 的定义

English:
definition injectIntoBaseIO
  signature: {α : Type} (a : α)
  body: pure a

@[deprecated "deprecated without replacement" (since := "2026-01-24")]
unsafe def memoFixImpl [Nonempty β] (f : (α -> β) -> (α -> β)) : α -> β := unsafeBaseIO do
  let cache : IO.Ref (Lean.PtrMap α β) ← ST.mkRef Lean.mkPtrMap
  let rec fix (a) : β := unsafeBaseIO do
    if let some b := (← c

中文:
定义 inject整数oBaseIO
  签名: {α : 类型} (a : α)
  定义体: pure a

@[deprecated "deprecated without replacement" (since := "2026-01-24")]
unsafe def memoFixImpl [Nonempty β] (f : (α -> β) -> (α -> β)) : α -> β := unsafeBaseIO do
  let cache : IO.Ref (Lean.PtrMap α β) ← ST.mkRef Lean.mkPtrMap
  let rec fix (a) : β := unsafeBaseIO do
    if let some b := (← c
-/
def injectIntoBaseIO {α : Type} (a : α) : BaseIO α := pure a

@[deprecated "deprecated without replacement" (since := "2026-01-24")]
unsafe def memoFixImpl [Nonempty β] (f : (α -> β) -> (α -> β)) : α -> β := unsafeBaseIO do
  let cache : IO.Ref (Lean.PtrMap α β) ← ST.mkRef Lean.mkPtrMap
  let rec fix (a) : β := unsafeBaseIO do
    if let some b := (← cache.get).find? a then
      return b
    let b ← injectIntoBaseIO (f fix a)
    cache.modify (·.insert a b)
    return b
  return fix

/-- Takes the fixpoint of `f` with caching of values that have been seen before.
Hashing makes use of a pointer hash.

This is useful for implementing tree traversal functions where
subtrees may be referenced in multiple places.
-/
@[implemented_by memoFixImpl,
deprecated "use `MonadCacheT` and `checkCache`" (since := "2026-01-24")]
public opaque memoFix [Nonempty β] (f : (α -> β) -> (α -> β)) : α -> β
