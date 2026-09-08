/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.Topology.Category.CompHausLike.Limits

/-!
# Cartesian monoidal structure on `CompHausLike`

If the predicate `P` is preserved under taking type-theoretic products and `PUnit` satisfies it,
then `CompHausLike P` is a cartesian monoidal category.

If the predicate `P` is preserved under taking type-theoretic sums, we provide an explicit coproduct
cocone in `CompHausLike P`. When we have the dual of `CartesianMonoidalCategory`, this can be used
to provide an instance of that on `CompHausLike P`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CompHausLike

variable {P : TopCat.{u} → Prop} (X Y : CompHausLike.{u} P)

section Product

variable [HasProp P (X × Y)]

/--
Explicit binary fan in `CompHausLike P`, given that the predicate `P` is preserved under taking
type-theoretic products.
-/
/-
**CompHausLike.productCone** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：productCone : BinaryFan X Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.instHasPropCarrierToTop`：∀ (P : TopCat → Prop) (X : CompHau
sLike P), CompHausLike.HasProp P ↑X.toTop

--- 原说明 ---
Explicit binary fan in `CompHausLike P`, given that the predicate `P` is preserv
ed under taking
type-theoretic products.
-/
def productCone : BinaryFan X Y :=
  BinaryFan.mk (P := CompHausLike.of P (X × Y))
    (ofHom _ { toFun := Prod.fst }) (ofHom _ { toFun := Prod.snd })

/--
When the predicate `P` is preserved under taking type-theoretic products, that product is a
category-theoretic product in `CompHausLike P`.
-/
/-
**CompHausLike.productIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：productIsLimit : IsLimit (productCone X Y)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.instHasPropCarrierToTop`：∀ (P : TopCat → Prop) (X : CompHau
sLike P), CompHausLike.HasProp P ↑X.toTop

--- 原说明 ---
When the predicate `P` is preserved under taking type-theoretic products, that p
roduct is a
category-theoretic product in `CompHausLike P`.
-/
def productIsLimit : IsLimit (productCone X Y) := by
  refine BinaryFan.isLimitMk (fun s ↦ ofHom _ { toFun x := (s.fst x, s.snd x) })
    (by rfl_cat) (by rfl_cat) fun _ _ h₁ h₂ ↦ ?_
  ext x
  exacts [ConcreteCategory.congr_hom h₁ _, ConcreteCategory.congr_hom h₂ _]

/--
When the predicate `P` is preserved under taking type-theoretic products and `PUnit` satisfies it,
then `CompHausLike P` is a cartesian monoidal category.

This could be an instance but that causes some slowness issues with typeclass search, therefore we
keep it as a def and turn it on as an instance for the explicit examples of `CompHausLike` as
needed.
-/
@[instance_reducible]
/-
**CompHausLike.cartesianMonoidalCategory** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike
`。
形式化陈述：cartesianMonoidalCategory [forall (X Y : CompHausLike.{u} P), HasProp P (X
 × Y)] [HasProp P PUnit.{u + 1}] : CartesianMonoidalCategory (CompHausLike.{u} P
)
参数：X Y : CompHausLike.{u} P；X × Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `instDiscreteTopologyPUnit`：DiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
When the predicate `P` is preserved under taking type-theoretic products and `PU
nit` satisfies it,
then `CompHausLike P` is a cartesian monoidal category.

This could be an instance but that causes some slowness issues with typeclass se
arch, therefore we
keep it as a def and turn it on as an instance for the explicit examples of `Com
pHausLike` as
needed.
-/
def cartesianMonoidalCategory [∀ (X Y : CompHausLike.{u} P), HasProp P (X × Y)]
    [HasProp P PUnit.{u + 1}] : CartesianMonoidalCategory (CompHausLike.{u} P) :=
  .ofChosenFiniteProducts
    ⟨_, CompHausLike.isTerminalPUnit⟩
    (fun X Y ↦ ⟨productCone X Y, productIsLimit X Y⟩)

end Product

section Coproduct

variable [HasProp P (X ⊕ Y)]

/--
Explicit binary cofan in `CompHausLike P`, given that the predicate `P` is preserved under taking
type-theoretic sums.
-/
/-
**CompHausLike.coproductCocone** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：coproductCocone : BinaryCofan X Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.instHasPropCarrierToTop`：∀ (P : TopCat → Prop) (X : CompHau
sLike P), CompHausLike.HasProp P ↑X.toTop

--- 原说明 ---
Explicit binary cofan in `CompHausLike P`, given that the predicate `P` is prese
rved under taking
type-theoretic sums.
-/
def coproductCocone : BinaryCofan X Y := BinaryCofan.mk (P := CompHausLike.of P (X ⊕ Y))
  (ofHom _ { toFun := Sum.inl }) (ofHom _ { toFun := Sum.inr })

set_option backward.isDefEq.respectTransparency.types false in
/--
When the predicate `P` is preserved under taking type-theoretic sums, that sum is a
category-theoretic coproduct in `CompHausLike P`.
-/
/-
**CompHausLike.coproductIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：coproductIsColimit : IsColimit (coproductCocone X Y)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.instHasPropCarrierToTop`：∀ (P : TopCat → Prop) (X : CompHau
sLike P), CompHausLike.HasProp P ↑X.toTop

--- 原说明 ---
When the predicate `P` is preserved under taking type-theoretic sums, that sum i
s a
category-theoretic coproduct in `CompHausLike P`.
-/
def coproductIsColimit : IsColimit (coproductCocone X Y) := by
  refine BinaryCofan.isColimitMk (fun s ↦ ofHom _ { toFun := Sum.elim s.inl s.inr })
    (by rfl_cat) (by rfl_cat) fun _ _ h₁ h₂ ↦ ?_
  ext ⟨⟩
  exacts [ConcreteCategory.congr_hom h₁ _, ConcreteCategory.congr_hom h₂ _]

end Coproduct

end CompHausLike

