/-
Copyright (c) 2026 Arnoud van der Leer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arnoud van der Leer
-/
module

public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The Nerve of a Codiscrete Category

In the codiscrete category on a type `X`, every hom-type is given by `Unit`.
When we take the nerve of such a category, the `n`-simplices become equivalent to
`X`-vectors of length `n + 1`.
Therefore, if `X` has decidable equality, so does the type of `n`-simplices in this nerve.
-/

@[expose] public section

universe u

namespace CategoryTheory.Codiscrete

open Simplicial

variable {X : Type u} {n : Nat}

/-- Since the morphisms in a codiscrete category do not carry information, an n-simplex of
coherentIso is equivalent to an X-vector of length (n + 1). -/
@[simps! +dsimpLhs]
/--
Definition of `equivFun` / `equivFun` 的定义

English:
definition equivFun
  signature: : nerve (Codiscrete X) _⦋n⦌ ≃ (Fin (n + 1) -> X) where
  body: (f.obj k).as
  invFun f := .mk (fun k => .mk (f k)) (fun _ => iso _ _|>.hom) (fun _ => rfl) (fun _ _ => rfl)

中文:
定义 equivFun
  签名: : nerve (余discrete X) _⦋n⦌ ≃ (有限集 (n + 1) -> X) where
  定义体: (f.obj k).as
  invFun f := .mk (fun k => .mk (f k)) (fun _ => iso _ _|>.hom) (fun _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: f.obj
-/
def equivFun : nerve (Codiscrete X) _⦋n⦌ ≃ (Fin (n + 1) -> X) where
  toFun f k := (f.obj k).as
  invFun f := .mk (fun k => .mk (f k)) (fun _ => iso _ _|>.hom) (fun _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: X] : DecidableEq (nerve (Codiscrete X) _⦋n⦌)
  body: fun _ _ => decidable_of_iff _ (Equiv.apply_eq_iff_eq equivFun)

中文:
实例 [DecidableEq
  签名: X] : DecidableEq (nerve (余discrete X) _⦋n⦌)
  定义体: fun _ _ => decidable_of_iff _ (Equiv.apply_eq_iff_eq equivFun)

Depends on / 依赖: Equiv.apply_eq_iff_eq, apply_eq_iff_eq, decidable_of_iff, equivFun
-/
instance [DecidableEq X] : DecidableEq (nerve (Codiscrete X) _⦋n⦌) :=
  fun _ _ => decidable_of_iff _ (Equiv.apply_eq_iff_eq equivFun)

end CategoryTheory.Codiscrete
