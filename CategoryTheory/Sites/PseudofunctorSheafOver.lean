/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Sheaves on Over categories, as a pseudofunctor

Given a Grothendieck topology `J` on a category `C` and
a category `A`, we define the pseudofunctor
`J.pseudofunctorOver A : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat`
which sends `X : C` to the category of sheaves on `Over X`
with values in `A`.

-/

@[expose] public section

universe v' v u' u

namespace CategoryTheory

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a Grothendieck topology `J` on a category `C` and a category `A`,
this is the pseudofunctor which sends `X : C` to the categories of
sheaves on `Over X` with values in `A`. -/
@[simps!]
/--
Definition of `pseudofunctorOver` / `pseudofunctorOver` 的定义

English:
definition pseudofunctorOver
  signature: : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat
  body: LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of (Sheaf (J.over X.unop) A))
    (fun f => (J.overMapPullback A f.unop).toCatHom)
    (fun X => Cat.Hom.isoMk <| (J.overMapPullbackId A X.unop))
    (fun f g => Cat.Hom.isoMk <| (J.overMapPullbackComp A g.unop f.unop).symm)
    (fun f g h => by ext1

中文:
定义 pseudofunctorOver
  签名: : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat
  定义体: LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of (Sheaf (J.over X.unop) A))
    (fun f => (J.overMapPullback A f.unop).toCatHom)
    (fun X => Cat.Hom.isoMk <| (J.overMapPullbackId A X.unop))
    (fun f g => Cat.Hom.isoMk <| (J.overMapPullbackComp A g.unop f.unop).symm)
    (fun f g h => by ext1

Depends on / 依赖: Cat.Hom.isoMk, Cat.of, J.over, J.overMapPullback, J.overMapPullbackComp, J.overMapPullbackId, J.overMapPullback_assoc, J.overMapPullback_comp_id, LocallyDiscrete, LocallyDiscrete.mkPseudofunctor, X.unop, f.unop, g.unop, h.unop, mkPseudofunctor, overMapPullback, overMapPullbackComp, overMapPullbackCongr_eq_eqToIso, overMapPullbackId, overMapPullback_assoc
-/
def pseudofunctorOver : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of (Sheaf (J.over X.unop) A))
    (fun f => (J.overMapPullback A f.unop).toCatHom)
    (fun X => Cat.Hom.isoMk <| (J.overMapPullbackId A X.unop))
    (fun f g => Cat.Hom.isoMk <| (J.overMapPullbackComp A g.unop f.unop).symm)
    (fun f g h => by ext1; simpa [overMapPullbackCongr_eq_eqToIso] using!
      J.overMapPullback_assoc A h.unop g.unop f.unop)
    (fun f => by ext1; simpa [overMapPullbackCongr_eq_eqToIso] using!
      J.overMapPullback_comp_id A f.unop)
    (fun f => by ext1; simpa [overMapPullbackCongr_eq_eqToIso] using!
      J.overMapPullback_id_comp A f.unop)

end GrothendieckTopology

end CategoryTheory
