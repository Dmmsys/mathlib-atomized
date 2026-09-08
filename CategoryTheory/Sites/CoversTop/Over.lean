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

/-
**CategoryTheory.GrothendieckTopology.CoversTop.over** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.GrothendieckTopology.CoversTop`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {J : Catego
ryTheory.GrothendieckTopology C}   {I : Type u_2} {X : I → C},   J.CoversTop X →
     ∀ {I' : I → Type u} {Y : (i : I) → I' i → CategoryTheory.Over (X i)},      
 (∀ (i : I), (J.over (X i)).CoversTop (Y i)) → J.CoversTop fun j => (Y j.fst j.s
nd).left
参数：i : I；X i；∀ (i : I), (J.over (X i)).CoversTop (Y i)；Y j.fst j.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.Sieve.functorPushforward_ofObjects_le`：functorPushforward
_ofObjects_le {I : Type*} (X : I -> C) (Y : C) : (ofObjects X Y).functorPushforw
ard F <= ofObjects (F.obj ∘ X) (F.obj Y)
· 使用引理 `CategoryTheory.Sieve.ofObjects_mono`：ofObjects_mono {I : Type*} {X : I -
> C} {I' : Type*} {X' : I' -> C} {Y : C} (h : Set.range X subseteq Set.range X')
 : Sieve.ofObjects X Y <=…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma CoversTop.over {I : Type*} {X : I → C} (hX : J.CoversTop X) {I' : I → Type u}
    {Y : (i : I) → I' i → Over (X i)} (hY : ∀ i, (J.over (X i)).CoversTop (Y i)) :
    J.CoversTop (fun (j : (i : I) × I' i) ↦ (Y j.1 j.2).left) :=
  fun j ↦ J.transitive (hX j) _ fun Z f ⟨i, ⟨g⟩⟩ ↦ J.superset_covering
    ((Sieve.functorPushforward_ofObjects_le _ _ _).trans (Sieve.ofObjects_mono fun i' ↦ by aesop))
    (hY _ (.mk g))

end CategoryTheory.GrothendieckTopology

