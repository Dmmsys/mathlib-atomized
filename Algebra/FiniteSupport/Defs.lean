/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.Set.Finite.Basic

/-!
# Make `fun_prop` work for finite (multiplicative) support

We define a new predicate `HasFiniteMulSupport` (and its additivized version) on functions
and provide the infrastructure so that `fun_prop` can prove it for functions that are
built from other functions with finite multiplicative support. The relevant API lemmas
are provided in [Mathlib.Algebra.FiniteSupport.Basic](Mathlib/Algebra/FiniteSupport/Basic.lean).
-/

@[expose] public section

namespace Function

variable {α M : Type*} [One M]

/-- The function `f` has finite multiplicative support. -/
@[to_additive (attr := fun_prop) /-- The function `f` has finite support. -/]
/--
Definition of `HasFiniteMulSupport` / `HasFiniteMulSupport` 的定义

English:
definition HasFiniteMulSupport
  signature: (f : α -> M)
  body: f.mulSupport.Finite

@[to_additive (attr := fun_prop)]

中文:
定义 HasFiniteMulSupport
  签名: (f : α -> M)
  定义体: f.mulSupport.Finite

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Finite, f.mulSupport.Finite, mulSupport
-/
def HasFiniteMulSupport (f : α -> M) : Prop := f.mulSupport.Finite

@[to_additive (attr := fun_prop)]
/--
lemma `hasFiniteMulSupport_one` / 引理 `hasFiniteMulSupport_one`

English:
lemma hasFiniteMulSupport_one
  statement: HasFiniteMulSupport fun _ : α => (1 : M)
  proof: by
  simp [HasFiniteMulSupport]

中文:
引理 hasFiniteMulSupport_one
  结论: HasFiniteMulSupport fun _ : α => (1 : M)
  证明: by
  simp [HasFiniteMulSupport]

Depends on / 依赖: HasFiniteMulSupport
-/
lemma hasFiniteMulSupport_one : HasFiniteMulSupport fun _ : α => (1 : M) := by
  simp [HasFiniteMulSupport]

end Function

end
