/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Group.AddChar

/-!
# Direct sum of additive characters

This file defines the direct sum of additive characters.
-/

@[expose] public section

open Function
open scoped DirectSum

variable {ι R : Type*} {G : ι -> Type*} [DecidableEq ι] [forall i, AddCommGroup (G i)] [CommMonoid R]

namespace AddChar
section DirectSum

/-- Direct sum of additive characters. -/
@[simps!]
/--
Definition of `directSum` / `directSum` 的定义

English:
definition directSum
  signature: (ψ : forall i, AddChar (G i) R)
  body: toAddMonoidHomEquiv.symm DirectSum.toAddMonoid fun i => toAddMonoidHomEquiv (ψ i)

中文:
定义 directSum
  签名: (ψ : 对任意 i, AddChar (G i) R)
  定义体: toAddMonoidHomEquiv.symm DirectSum.toAddMonoid fun i => toAddMonoidHomEquiv (ψ i)

Depends on / 依赖: DirectSum, DirectSum.toAddMonoid, toAddMonoid, toAddMonoidHomEquiv, toAddMonoidHomEquiv.symm
-/
def directSum (ψ : forall i, AddChar (G i) R) : AddChar (⨁ i, G i) R :=
toAddMonoidHomEquiv.symm DirectSum.toAddMonoid fun i => toAddMonoidHomEquiv (ψ i)

/--
lemma `directSum_injective` / 引理 `directSum_injective`

English:
lemma directSum_injective
  proof: by
refine toAddMonoidHomEquiv.symm.injective.comp DirectSum.toAddMonoid_injective.comp ?_
  rintro ψ χ h
  simpa [funext_iff] using h

中文:
引理 directSum_injective
  证明: by
refine toAddMonoidHomEquiv.symm.injective.comp DirectSum.toAddMonoid_injective.comp ?_
  rintro ψ χ h
  simpa [funext_iff] using h

Depends on / 依赖: DirectSum, DirectSum.toAddMonoid_injective.comp, funext_iff, injective, toAddMonoidHomEquiv, toAddMonoidHomEquiv.symm.injective.comp, toAddMonoid_injective
-/
lemma directSum_injective :
    Injective (directSum : (forall i, AddChar (G i) R) -> AddChar (⨁ i, G i) R) := by
refine toAddMonoidHomEquiv.symm.injective.comp DirectSum.toAddMonoid_injective.comp ?_
  rintro ψ χ h
  simpa [funext_iff] using h

end DirectSum
end AddChar
