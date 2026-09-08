/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesColimit

/-!
# Nonsingular simplicial sets, as colimits of standard simplices

In the file `Mathlib/AlgebraicTopology/SimplicialSet/NonDegenerateSimplicesColimit.lean`,
it was shown that any simplicial set `X` is the colimit (indexed by the type `X.N`
of nondegenerate simplices) of its monogenous subcomplexes.

In this file, we assume that `X` is nonsingular, in which case its monogenous subcomplexes
identify to standard simplices. This allows to show that `X` is the colimit
of `Δ[x.dim]` for `x : X.N`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Limits

namespace SSet

variable (X : SSet.{u}) [X.Nonsingular]

namespace N

set_option backward.isDefEq.respectTransparency false in
/-- If `X` is a nonsingular simplicial set, this is the functor
`X.N ⥤ SemiSimplexCategory` which sends a nondegenerate
simplex `s : X.N` to `⦋s.dim⦌ₛ`. -/
@[simps obj map]
/-
**SSet.N.toSemiSimplexCategory** 是 Mathlib 中的一个定义，位于命名空间 `SSet.N`。
形式化陈述：toSemiSimplexCategory : X.N ⥤ SemiSimplexCategory where obj s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a nonsingular simplicial set, this is the functor
`X.N ⥤ SemiSimplexCategory` which sends a nondegenerate
simplex `s : X.N` to `⦋s.dim⦌ₛ`.
-/
noncomputable def toSemiSimplexCategory : X.N ⥤ SemiSimplexCategory where
  obj s := ⦋s.dim⦌ₛ
  map f := SemiSimplexCategory.homOfMono (N.monoOfLE (leOfHom f))
  map_id _ := SemiSimplexCategory.toSimplexCategory.map_injective (by simp)
  map_comp _ _ := SemiSimplexCategory.toSimplexCategory.map_injective (by simp)

end N

/-- The functor `X.N ⥤ SSet` which sends `x : X.N` to `Δ[x.dim]`. -/
/-
**SSet.functorN'** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：functorN' : X.N ⥤ SSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `X.N ⥤ SSet` which sends `x : X.N` to `Δ[x.dim]`.
-/
noncomputable abbrev functorN' : X.N ⥤ SSet.{u} :=
    N.toSemiSimplexCategory X ⋙ SemiSimplexCategory.toSimplexCategory ⋙ SSet.stdSimplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism `X.functorN' ≅ X.functorN` for a nonsingular simplicial set `X`. -/
/-
**SSet.functorN'Iso** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：(X : _root_.SSet) → [inst : X.Nonsingular] → X.functorN' ≅ X.functorN
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.N.nonDegenerate`：∀ {X : _root_.SSet} (self : X.N), self.simplex ∈ X
.nonDegenerate self.dim

--- 原说明 ---
The isomorphism `X.functorN' ≅ X.functorN` for a nonsingular simplicial set `X`.
-/
noncomputable def functorN'Iso : X.functorN' ≅ X.functorN :=
  NatIso.ofComponents (fun x ↦ Nonsingular.iso _ x.nonDegenerate) (fun _ ↦ by
    simp [← cancel_mono (Subcomplex.ι _)])

/-- If `X` is a nonsingular simplicial set, this is the cocone consisting
of the (mono)morphisms `Δ[x.dim] ⟶ X` for all nondegenerate simplices `x : X.N`. -/
@[simps]
/-
**SSet.coconeN'** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：coconeN' : Cocone X.functorN' where pt
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `X` is a nonsingular simplicial set, this is the cocone consisting
of the (mono)morphisms `Δ[x.dim] ⟶ X` for all nondegenerate simplices `x : X.N`.
-/
noncomputable def coconeN' : Cocone X.functorN' where
  pt := X
  ι.app s := yonedaEquiv.symm s.simplex
  ι.naturality _ _ f := N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex (leOfHom f)

/-- If `X` is a nonsingular simplicial set, `X` is the colimit of `Δ[x.dim]`
for all nondegenerate simplices `x : X.N`. -/
/-
**SSet.isColimitCoconeN'** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：isColimitCoconeN' : IsColimit X.coconeN'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a nonsingular simplicial set, `X` is the colimit of `Δ[x.dim]`
for all nondegenerate simplices `x : X.N`.
-/
noncomputable def isColimitCoconeN' : IsColimit X.coconeN' :=
  (IsColimit.equivOfNatIsoOfIso
    X.functorN'Iso.symm _ _ (Cocone.ext (Iso.refl _))).1 X.isColimitCoconeN

end SSet

