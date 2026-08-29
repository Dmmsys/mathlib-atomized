/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Johannes Hölzl, Reid Barton
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Order.GaloisConnection.Defs

/-!

# Galois connections between preorders are adjunctions.

* `GaloisConnection.adjunction` is the adjunction associated to a Galois connection.

-/

@[expose] public section


universe u v

section

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/--
Definition of `GaloisConnection.adjunction` / `GaloisConnection.adjunction` 的定义

English:
definition GaloisConnection.adjunction
  signature: {l : X -> Y} {u : Y -> X} (gc : GaloisConnection l u)
  body: CategoryTheory.Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => CategoryTheory.homOfLE (gc.le_u f.le)
          invFun := fun f => CategoryTheory.homOfLE (gc.l_le f.le)
          left_inv := by cat_disch
          right_inv := by cat_disch } }

中文:
定义 GaloisConnection.adjunction
  签名: {l : X -> Y} {u : Y -> X} (gc : GaloisConnection l u)
  定义体: CategoryTheory.Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => CategoryTheory.homOfLE (gc.le_u f.le)
          invFun := fun f => CategoryTheory.homOfLE (gc.l_le f.le)
          left_inv := by cat_disch
          right_inv := by cat_disch } }

Depends on / 依赖: Adjunction, CategoryTheory, CategoryTheory.Adjunction.mkOfHomEquiv, CategoryTheory.homOfLE, cat_disch, f.le, gc.l_le, gc.le_u, homEquiv, homOfLE, invFun, l_le, le_u, left_inv, mkOfHomEquiv, right_inv
-/
def GaloisConnection.adjunction {l : X -> Y} {u : Y -> X} (gc : GaloisConnection l u) :
    gc.monotone_l.functor ⊣ gc.monotone_u.functor :=
  CategoryTheory.Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => CategoryTheory.homOfLE (gc.le_u f.le)
          invFun := fun f => CategoryTheory.homOfLE (gc.l_le f.le)
          left_inv := by cat_disch
          right_inv := by cat_disch } }

end

namespace CategoryTheory

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/--
theorem `Adjunction.gc` / 定理 `Adjunction.gc`

English:
theorem Adjunction.gc
  given: {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R)
  statement: GaloisConnection L.obj R.obj
  proof: fun x y =>
  ⟨fun h => ((adj.homEquiv x y).toFun h.hom).le, fun h => ((adj.homEquiv x y).invFun h.hom).le⟩

中文:
定理 Adjunction.gc
  条件: {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R)
  结论: GaloisConnection L.obj R.obj
  证明: fun x y =>
  ⟨fun h => ((adj.homEquiv x y).toFun h.hom).le, fun h => ((adj.homEquiv x y).invFun h.hom).le⟩

Depends on / 依赖: Category, Category.assoc, HasLimit, HasLimit.isoOfNatIso_hom_, Iso.trans_hom, adj.homEquiv, colimitHomIsoLimitYoneda, colimitYonedaHomIsoLimit, h.hom, homEquiv, invFun, trans_hom, uliftFunctor, yonedaLemma
-/
theorem Adjunction.gc {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R) : GaloisConnection L.obj R.obj :=
  fun x y =>
  ⟨fun h => ((adj.homEquiv x y).toFun h.hom).le, fun h => ((adj.homEquiv x y).invFun h.hom).le⟩

end CategoryTheory
