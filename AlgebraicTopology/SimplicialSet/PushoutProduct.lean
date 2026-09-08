/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Pushout-products of simplicial sets

Results about pushout-products and pullback-homs in the category of simplicial sets.

-/

@[expose] public section

universe v u

namespace SSet

open CategoryTheory MonoidalCategory

variable {X Y : SSet.{u}} (S : X.Subcomplex) (T : Y.Subcomplex)

namespace Subcomplex

namespace unionProd

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inclusion `(S.unionProd T).toSSet ⟶ X ⊗ Y` is isomorphic to the pushout-product
`S.ι □ T.ι`. -/
@[simps! -isSimp]
noncomputable
/-
**SSet.Subcomplex.unionProd.** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.unionPro
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ιIso : Arrow.mk (S.unionProd T).ι ≅ S.ι □ T.ι :=
  Arrow.isoMk' _ _ (isPushout S T).isoPushout (Iso.refl _)
    (by
      apply (unionProd.isPushout S T).hom_ext <;>
      simp [Limits.pushout.inl_desc, Limits.pushout.inr_desc])

/-- Given subcomplexes `S` and `T` of simplicial sets, this if a `Functor.PushoutObjObj`
/-
**SSet.Subcomplex.unionProd.for** 是 Mathlib 中的一个结构，位于命名空间 `SSet.Subcomplex.union
Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure for the chosen binary products on `SSet`, with point `S.unionProd T`. -/
@[simps]
/-
**SSet.Subcomplex.unionProd.pushoutObjObj** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcom
plex.unionProd`。
形式化陈述：pushoutObjObj : (curriedTensor _).PushoutObjObj S.ι T.ι where pt
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.unionProd.isPushout`：isPushout : IsPushout (S.ι ▷ (T : S
Set)) ((S : SSet) ◁ T.ι) (unionProd.ι₁ S T) (unionProd.ι₂ S T)

--- 原说明 ---
Given subcomplexes `S` and `T` of simplicial sets, this if a `Functor.PushoutObj
Obj`
structure for the chosen binary products on `SSet`, with point `S.unionProd T`.
-/
noncomputable def pushoutObjObj : (curriedTensor _).PushoutObjObj S.ι T.ι where
  pt := S.unionProd T
  inl := unionProd.ι₁ S T
  inr := unionProd.ι₂ S T
  isPushout := unionProd.isPushout S T
  ι := (S.unionProd T).ι

end unionProd

end Subcomplex

end SSet

