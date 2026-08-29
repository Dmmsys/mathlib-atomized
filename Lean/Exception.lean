/-
Copyright (c) 2022 Edward Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward Ayers
-/
module

public import Mathlib.Init
public import Lean.Exception

/-!
# Additional methods for working with `Exception`s

This file contains two additional methods for working with `Exception`s
* `successIfFail`, a generalisation of `fail_if_success` to arbitrary `MonadError`s
* `isFailedToSynthesize`: check if an exception is of the "failed to synthesize" form

-/

@[expose] public section

open Lean

/--
Definition of `successIfFail` / `successIfFail` 的定义

English:
definition successIfFail
  signature: {α : Type} {M : Type -> Type} [MonadError M] [Monad M] (m : M α)
  body: do
  match ← tryCatch (m *> pure none) (pure ∘ some) with
  | none => throwError "Expected an exception."
  | some ex => return ex

中文:
定义 successIfFail
  签名: {α : Type} {M : Type -> Type} [MonadError M] [Monad M] (m : M α)
  定义体: do
  match ← tryCatch (m *> pure none) (pure ∘ some) with
  | none => throwError "Expected an exception."
  | some ex => return ex
-/
def successIfFail {α : Type} {M : Type -> Type} [MonadError M] [Monad M] (m : M α) :
    M Exception := do
  match ← tryCatch (m *> pure none) (pure ∘ some) with
  | none => throwError "Expected an exception."
  | some ex => return ex

namespace Lean

namespace Exception

/--
Definition of `isFailedToSynthesize` / `isFailedToSynthesize` 的定义

English:
definition isFailedToSynthesize
  signature: (e : Exception)
  body: do
pure (← e.toMessageData.toString).startsWith "failed to synthesize"

中文:
定义 isFailedToSynthesize
  签名: (e : Exception)
  定义体: do
pure (← e.toMessageData.toString).startsWith "failed to synthesize"
-/
def isFailedToSynthesize (e : Exception) : IO Bool := do
pure (← e.toMessageData.toString).startsWith "failed to synthesize"

end Exception

end Lean
