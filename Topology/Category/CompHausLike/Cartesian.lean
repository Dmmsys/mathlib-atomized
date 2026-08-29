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

variable {P : TopCat.{u} -> Prop} (X Y : CompHausLike.{u} P)

section Product

variable [HasProp P (X × Y)]

/--
Definition of `productCone` / `productCone` 的定义

English:
definition productCone
  signature: : BinaryFan X Y
  body: BinaryFan.mk (P := CompHausLike.of P (X × Y))
    (ofHom _ { toFun := Prod.fst }) (ofHom _ { toFun := Prod.snd })

中文:
定义 productCone
  签名: : BinaryFan X Y
  定义体: BinaryFan.mk (P := CompHausLike.of P (X × Y))
    (ofHom _ { toFun := Prod.fst }) (ofHom _ { toFun := Prod.snd })

Depends on / 依赖: BinaryFan, BinaryFan.mk, CompHausLike, CompHausLike.of, Prod.fst, Prod.snd
-/
def productCone : BinaryFan X Y :=
  BinaryFan.mk (P := CompHausLike.of P (X × Y))
    (ofHom _ { toFun := Prod.fst }) (ofHom _ { toFun := Prod.snd })

/--
Definition of `productIsLimit` / `productIsLimit` 的定义

English:
definition productIsLimit
  signature: : IsLimit (productCone X Y)
  body: by
  refine BinaryFan.isLimitMk (fun s => ofHom _ { toFun x := (s.fst x, s.snd x) })
    (by rfl_cat) (by rfl_cat) fun _ _ h₁ h₂ => ?_
  ext x
  exacts [ConcreteCategory.congr_hom h₁ _, ConcreteCategory.congr_hom h₂ _]

中文:
定义 productIsLimit
  签名: : 是极限 (productCone X Y)
  定义体: by
  refine BinaryFan.isLimitMk (fun s => ofHom _ { toFun x := (s.fst x, s.snd x) })
    (by rfl_cat) (by rfl_cat) fun _ _ h₁ h₂ => ?_
  ext x
  exacts [ConcreteCategory.congr_hom h₁ _, ConcreteCategory.congr_hom h₂ _]

Depends on / 依赖: BinaryFan, BinaryFan.isLimitMk, ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, exacts, isLimitMk, rfl_cat, s.fst, s.snd
-/
def productIsLimit : IsLimit (productCone X Y) := by
  refine BinaryFan.isLimitMk (fun s => ofHom _ { toFun x := (s.fst x, s.snd x) })
    (by rfl_cat) (by rfl_cat) fun _ _ h₁ h₂ => ?_
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
/--
Definition of `cartesianMonoidalCategory` / `cartesianMonoidalCategory` 的定义

English:
definition cartesianMonoidalCategory
  signature: [forall (X Y : CompHausLike.{u} P), HasProp P (X × Y)]
  body: .ofChosenFiniteProducts
    ⟨_, CompHausLike.isTerminalPUnit⟩
    (fun X Y => ⟨productCone X Y, productIsLimit X Y⟩)

中文:
定义 cartesianMonoidalCategory
  签名: [对任意 (X Y : 余mpHausLike.{u} P), 有命题 P (X × Y)]
  定义体: .ofChosenFiniteProducts
    ⟨_, CompHausLike.isTerminalPUnit⟩
    (fun X Y => ⟨productCone X Y, productIsLimit X Y⟩)

Depends on / 依赖: CompHausLike, CompHausLike.isTerminalPUnit, isTerminalPUnit, ofChosenFiniteProducts, productCone, productIsLimit
-/
def cartesianMonoidalCategory [forall (X Y : CompHausLike.{u} P), HasProp P (X × Y)]
    [HasProp P PUnit.{u + 1}] : CartesianMonoidalCategory (CompHausLike.{u} P) :=
  .ofChosenFiniteProducts
    ⟨_, CompHausLike.isTerminalPUnit⟩
    (fun X Y => ⟨productCone X Y, productIsLimit X Y⟩)

end Product

section Coproduct

variable [HasProp P (X oplus Y)]

/--
Definition of `coproductCocone` / `coproductCocone` 的定义

English:
definition coproductCocone
  signature: : BinaryCofan X Y
  body: BinaryCofan.mk (P := CompHausLike.of P (X oplus Y))
  (ofHom _ { toFun := Sum.inl }) (ofHom _ { toFun := Sum.inr })

中文:
定义 coproductCocone
  签名: : BinaryCofan X Y
  定义体: BinaryCofan.mk (P := CompHausLike.of P (X oplus Y))
  (ofHom _ { toFun := Sum.inl }) (ofHom _ { toFun := Sum.inr })

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, CompHausLike, CompHausLike.of
-/
def coproductCocone : BinaryCofan X Y := BinaryCofan.mk (P := CompHausLike.of P (X oplus Y))
  (ofHom _ { toFun := Sum.inl }) (ofHom _ { toFun := Sum.inr })

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `coproductIsColimit` / `coproductIsColimit` 的定义

English:
definition coproductIsColimit
  signature: : IsColimit (coproductCocone X Y)
  body: by
  refine BinaryCofan.isColimitMk (fun s => ofHom _ { toFun := Sum.elim s.inl s.inr })
    (by rfl_cat) (by rfl_cat) fun _ _ h₁ h₂ => ?_
  ext ⟨⟩
  exacts [ConcreteCategory.congr_hom h₁ _, ConcreteCategory.congr_hom h₂ _]

中文:
定义 coproductIsColimit
  签名: : 是余极限 (coproductCocone X Y)
  定义体: by
  refine BinaryCofan.isColimitMk (fun s => ofHom _ { toFun := Sum.elim s.inl s.inr })
    (by rfl_cat) (by rfl_cat) fun _ _ h₁ h₂ => ?_
  ext ⟨⟩
  exacts [ConcreteCategory.congr_hom h₁ _, ConcreteCategory.congr_hom h₂ _]

Depends on / 依赖: BinaryCofan, BinaryCofan.isColimitMk, ConcreteCategory, ConcreteCategory.congr_hom, Sum.elim, congr_hom, exacts, isColimitMk, rfl_cat, s.inl, s.inr
-/
def coproductIsColimit : IsColimit (coproductCocone X Y) := by
  refine BinaryCofan.isColimitMk (fun s => ofHom _ { toFun := Sum.elim s.inl s.inr })
    (by rfl_cat) (by rfl_cat) fun _ _ h₁ h₂ => ?_
  ext ⟨⟩
  exacts [ConcreteCategory.congr_hom h₁ _, ConcreteCategory.congr_hom h₂ _]

end Coproduct

end CompHausLike
