/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over

/-!
# CoversTop in over-categories

This file contains a transitivity lemma for `GrothendieckTopology.CoversTop`: if a family
`X : I → C` covers the top for `J`, and for each `i` a family `Y i` covers the top for the
induced topology on `Over (X i)`, then the combined family covers the top for `J`.

-/

@[expose] public section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}

/--
lemma `CoversTop.over` / 引理 `CoversTop.over`

English:
lemma CoversTop.over
  statement: {I : Type*} {X : I -> C} (hX : J.CoversTop X) {I' : I -> Type u}
  proof: fun j => J.transitive (hX j) _ fun Z f ⟨i, ⟨g⟩⟩ => J.superset_covering
    ((Sieve.functorPushforward_ofObjects_le _ _ _).trans (Sieve.ofObjects_mono fun i' => by aesop))
    (hY _ (.mk g))

中文:
引理 CoversTop.over
  结论: {I : 类型} {X : I -> C} (hX : J.CoversTop X) {I' : I -> 类型u}
  证明: fun j => J.transitive (hX j) _ fun Z f ⟨i, ⟨g⟩⟩ => J.superset_covering
    ((Sieve.functorPushforward_ofObjects_le _ _ _).trans (Sieve.ofObjects_mono fun i' => by aesop))
    (hY _ (.mk g))

Depends on / 依赖: J.superset_covering, J.transitive, Sieve.functorPushforward_ofObjects_le, Sieve.ofObjects_mono, functorPushforward_ofObjects_le, ofObjects_mono, superset_covering, transitive
-/
lemma CoversTop.over {I : Type*} {X : I -> C} (hX : J.CoversTop X) {I' : I -> Type u}
    {Y : (i : I) -> I' i -> Over (X i)} (hY : forall i, (J.over (X i)).CoversTop (Y i)) :
    J.CoversTop (fun (j : (i : I) × I' i) => (Y j.1 j.2).left) :=
  fun j => J.transitive (hX j) _ fun Z f ⟨i, ⟨g⟩⟩ => J.superset_covering
    ((Sieve.functorPushforward_ofObjects_le _ _ _).trans (Sieve.ofObjects_mono fun i' => by aesop))
    (hY _ (.mk g))

end CategoryTheory.GrothendieckTopology
