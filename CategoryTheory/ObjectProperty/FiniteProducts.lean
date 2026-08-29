/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.Data.Fintype.Shrink

/-!
# Properties of objects that are stable under finite products

We introduce typeclasses `IsClosedUnderBinaryProducts` and
`IsClosedUnderFiniteProducts` expressing that `P : ObjectProperty C`
is closed under binary products or finite products.
We introduce a constructor for `P.IsClosedUnderFiniteProducts`
assuming `P.IsClosedUnderBinaryProducts`,
`P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)` and that `C`
has finite products.

-/

universe w

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] (P : ObjectProperty C)

/--
Definition of `IsClosedUnderBinaryProducts` / `IsClosedUnderBinaryProducts` 的定义

English:
abbreviation IsClosedUnderBinaryProducts
  body: P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)

中文:
缩写 IsClosedUnderBinaryProducts
  定义体: P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)

Depends on / 依赖: Discrete, IsClosedUnderLimitsOfShape, P.IsClosedUnderLimitsOfShape, WalkingPair
-/
abbrev IsClosedUnderBinaryProducts :=
  P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)

/--
lemma `prop_of_isLimit_binaryFan` / 引理 `prop_of_isLimit_binaryFan`

English:
lemma prop_of_isLimit_binaryFan
  statement: [P.IsClosedUnderBinaryProducts] {X Y : C} {B : BinaryFan X Y}
  proof: P.prop_of_isLimit hB (by rintro ⟨_ | _⟩ <;> assumption)

中文:
引理 prop_of_isLimit_binaryFan
  结论: [P.IsClosedUnderBinaryProducts] {X Y : C} {B : BinaryFan X Y}
  证明: P.prop_of_isLimit hB (by rintro ⟨_ | _⟩ <;> assumption)

Depends on / 依赖: P.prop_of_isLimit, prop_of_isLimit
-/
lemma prop_of_isLimit_binaryFan [P.IsClosedUnderBinaryProducts] {X Y : C} {B : BinaryFan X Y}
    (hB : IsLimit B) (hX : P X) (hY : P Y) :
    P B.pt :=
  P.prop_of_isLimit hB (by rintro ⟨_ | _⟩ <;> assumption)

/--
lemma `prop_prod` / 引理 `prop_prod`

English:
lemma prop_prod
  statement: [P.IsClosedUnderBinaryProducts] (X Y : C) [HasBinaryProduct X Y]
  proof: P.prop_of_isLimit_binaryFan (limit.isLimit _) hX hY

中文:
引理 prop_prod
  结论: [P.IsClosedUnderBinaryProducts] (X Y : C) [HasBinaryProduct X Y]
  证明: P.prop_of_isLimit_binaryFan (limit.isLimit _) hX hY

Depends on / 依赖: P.prop_of_isLimit_binaryFan, isLimit, limit.isLimit, prop_of_isLimit_binaryFan
-/
lemma prop_prod [P.IsClosedUnderBinaryProducts] (X Y : C) [HasBinaryProduct X Y]
    (hX : P X) (hY : P Y) :
    P (X ⨯ Y) :=
  P.prop_of_isLimit_binaryFan (limit.isLimit _) hX hY

/--
lemma `prop_of_isTerminal` / 引理 `prop_of_isTerminal`

English:
lemma prop_of_isTerminal
  statement: [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)]
  proof: P.prop_of_isLimit hX (by rintro ⟨⟨⟩⟩)

中文:
引理 prop_of_isTerminal
  结论: [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)]
  证明: P.prop_of_isLimit hX (by rintro ⟨⟨⟩⟩)

Depends on / 依赖: P.prop_of_isLimit, prop_of_isLimit
-/
lemma prop_of_isTerminal [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)]
    (X : C) (hX : IsTerminal X) :
    P X :=
  P.prop_of_isLimit hX (by rintro ⟨⟨⟩⟩)

/--
lemma `prop_terminal` / 引理 `prop_terminal`

English:
lemma prop_terminal
  given: [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [HasTerminal C]
  proof: P.prop_of_isTerminal _ terminalIsTerminal

中文:
引理 prop_terminal
  条件: [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [HasTerminal C]
  证明: P.prop_of_isTerminal _ terminalIsTerminal

Depends on / 依赖: P.prop_of_isTerminal, prop_of_isTerminal, terminalIsTerminal
-/
lemma prop_terminal [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [HasTerminal C] :
    P (⊤_ C) :=
  P.prop_of_isTerminal _ terminalIsTerminal

-- see Note [lower instance priority]
instance (priority := 100) [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [HasTerminal C] :
    P.Nonempty :=
  nonempty_of_prop P.prop_terminal

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `IsClosedUnderBinaryProducts.closedUnderIsomorphisms` / 引理 `IsClosedUnderBinaryProducts.closedUnderIsomorphisms`

English:
lemma IsClosedUnderBinaryProducts.closedUnderIsomorphisms
  statement: [HasTerminal C]
  proof: by
    let h : IsLimit (BinaryFan.mk (terminal.from Y) e.inv) :=
      BinaryFan.IsLimit.mk _ (fun _ f => f ≫ e.hom) (by cat_disch) (by simp) (by cat_disch)
    exact P.prop_of_isLimit_binaryFan h P.prop_terminal hX

中文:
引理 IsClosedUnderBinaryProducts.closedUnderIsomorphisms
  结论: [HasTerminal C]
  证明: by
    let h : IsLimit (BinaryFan.mk (terminal.from Y) e.inv) :=
      BinaryFan.IsLimit.mk _ (fun _ f => f ≫ e.hom) (by cat_disch) (by simp) (by cat_disch)
    exact P.prop_of_isLimit_binaryFan h P.prop_terminal hX

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.mk, BinaryFan.mk, IsLimit, P.prop_of_isLimit_binaryFan, P.prop_terminal, cat_disch, e.hom, e.inv, prop_of_isLimit_binaryFan, prop_terminal, terminal, terminal.from
-/
lemma IsClosedUnderBinaryProducts.closedUnderIsomorphisms [HasTerminal C]
    [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let h : IsLimit (BinaryFan.mk (terminal.from Y) e.inv) :=
      BinaryFan.IsLimit.mk _ (fun _ f => f ≫ e.hom) (by cat_disch) (by simp) (by cat_disch)
    exact P.prop_of_isLimit_binaryFan h P.prop_terminal hX

/--
Definition of `binaryProductsClosure` / `binaryProductsClosure` 的定义

English:
abbreviation binaryProductsClosure
  signature: (P : ObjectProperty C)
  body: P.limitClosure (Discrete WalkingPair)

中文:
缩写 binaryProductsClosure
  签名: (P : Object命题erty C)
  定义体: P.limitClosure (Discrete WalkingPair)

Depends on / 依赖: Discrete, NatTrans, NatTrans.isIso_iff_isIso_app, P.limitClosure, WalkingPair, isIso_iff_isIso_app, limitClosure, natTransTruncLTOfLE, someOctahedron, t.isIso, t.natTransTruncLTOfLE, t.triangleLTGE_distinguished, t.triangleLTLTGELT_distinguished, t.truncGELT, t.truncLT, triangleLTGE_distinguished, triangleLTLTGELT_distinguished, truncGELT, truncLT
-/
abbrev binaryProductsClosure (P : ObjectProperty C) : ObjectProperty C :=
  P.limitClosure (Discrete WalkingPair)

/--
lemma `binaryProductsClosure_le_iff` / 引理 `binaryProductsClosure_le_iff`

English:
lemma binaryProductsClosure_le_iff
  statement: [HasTerminal C] {P Q : ObjectProperty C}
  proof: by
  refine ⟨fun h => (P.le_limitsClosure _).trans h, fun h => ?_⟩
  let : Q.IsClosedUnderIsomorphisms := IsClosedUnderBinaryProducts.closedUnderIsomorphisms Q
  exact limitsClosure_le h

中文:
引理 binaryProductsClosure_le_iff
  结论: [HasTerminal C] {P Q : Object命题erty C}
  证明: by
  refine ⟨fun h => (P.le_limitsClosure _).trans h, fun h => ?_⟩
  let : Q.IsClosedUnderIsomorphisms := IsClosedUnderBinaryProducts.closedUnderIsomorphisms Q
  exact limitsClosure_le h

Depends on / 依赖: IsClosedUnderBinaryProducts, IsClosedUnderBinaryProducts.closedUnderIsomorphisms, IsClosedUnderIsomorphisms, P.le_limitsClosure, Q.IsClosedUnderIsomorphisms, closedUnderIsomorphisms, infer_instance, le_limitsClosure, limitsClosure_le, t.truncLT_map_truncGE_map_truncLT
-/
lemma binaryProductsClosure_le_iff [HasTerminal C] {P Q : ObjectProperty C}
    [Q.IsClosedUnderBinaryProducts] [Q.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] :
    P.binaryProductsClosure <= Q ↔ P <= Q := by
  refine ⟨fun h => (P.le_limitsClosure _).trans h, fun h => ?_⟩
  let : Q.IsClosedUnderIsomorphisms := IsClosedUnderBinaryProducts.closedUnderIsomorphisms Q
  exact limitsClosure_le h

/--
Definition of `IsClosedUnderFiniteProducts` / `IsClosedUnderFiniteProducts` 的定义

English:
class IsClosedUnderFiniteProducts
  parameters: : Prop where
  axioms and operations (1):
    - isClosedUnderLimitsOfShape((J : Type) [Finite J]) : P.IsClosedUnderLimitsOfShape (Discrete J)  [default: by infer_instance]

中文:
类 IsClosedUnderFiniteProducts
  参数: : 命题 where
  公理与运算 (1 个):
    - isClosedUnderLimitsOfShape((J : Type) [Finite J]) : P.IsClosedUnderLimitsOfShape (Discrete J)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsClosedUnderFiniteProducts : Prop where
  isClosedUnderLimitsOfShape (J : Type) [Finite J] :
    P.IsClosedUnderLimitsOfShape (Discrete J) := by infer_instance

variable {P} in
/--
lemma `IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape` / 引理 `IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape`

English:
lemma IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape
  proof: by
    rw [P.isClosedUnderLimitsOfShape_iff_of_equivalence (Discrete.equivalence (equivShrink.{w} _))]
    exact H _

中文:
引理 IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape
  证明: by
    rw [P.isClosedUnderLimitsOfShape_iff_of_equivalence (Discrete.equivalence (equivShrink.{w} _))]
    exact H _

Depends on / 依赖: Discrete, Discrete.equivalence, P.isClosedUnderLimitsOfShape_iff_of_equivalence, equivShrink, equivalence, isClosedUnderLimitsOfShape_iff_of_equivalence
-/
lemma IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape
    (H : forall (J : Type w) [Finite J], P.IsClosedUnderLimitsOfShape (Discrete J)) :
    P.IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    rw [P.isClosedUnderLimitsOfShape_iff_of_equivalence (Discrete.equivalence (equivShrink.{w} _))]
    exact H _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderFiniteProducts]
  signature: (J : Type*) [Finite J]
  body: by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have : P.IsClosedUnderLimitsOfShape (Discrete (Fin n)) :=
    IsClosedUnderFiniteProducts.isClosedUnderLimitsOfShape _
  exact IsClosedUnderLimitsOfShape.of_equivalence (Discrete.equivalence e.symm)

中文:
实例 [P.IsClosedUnderFiniteProducts]
  签名: (J : 类型) [Finite J]
  定义体: by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have : P.IsClosedUnderLimitsOfShape (Discrete (Fin n)) :=
    IsClosedUnderFiniteProducts.isClosedUnderLimitsOfShape _
  exact IsClosedUnderLimitsOfShape.of_equivalence (Discrete.equivalence e.symm)

Depends on / 依赖: Discrete, Discrete.equivalence, Finite, Finite.exists_equiv_fin, IsClosedUnderFiniteProducts, IsClosedUnderFiniteProducts.isClosedUnderLimitsOfShape, IsClosedUnderLimitsOfShape, IsClosedUnderLimitsOfShape.of_equivalence, P.IsClosedUnderLimitsOfShape, e.symm, equivalence, exists_equiv_fin, isClosedUnderLimitsOfShape, of_equivalence
-/
instance [P.IsClosedUnderFiniteProducts] (J : Type*) [Finite J] :
    P.IsClosedUnderLimitsOfShape (Discrete J) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have : P.IsClosedUnderLimitsOfShape (Discrete (Fin n)) :=
    IsClosedUnderFiniteProducts.isClosedUnderLimitsOfShape _
  exact IsClosedUnderLimitsOfShape.of_equivalence (Discrete.equivalence e.symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteProducts
  signature: C] [P.IsClosedUnderFiniteProducts] :
  body: inferInstance

中文:
实例 [HasFiniteProducts
  签名: C] [P.IsClosedUnderFiniteProducts] :
  定义体: inferInstance
-/
instance [HasFiniteProducts C] [P.IsClosedUnderFiniteProducts] :
    HasFiniteProducts P.FullSubcategory where
  out _ := inferInstance

/--
lemma `prop_of_isLimit_fan` / 引理 `prop_of_isLimit_fan`

English:
lemma prop_of_isLimit_fan
  statement: [P.IsClosedUnderFiniteProducts] {J : Type*} [Finite J] {f : J -> C}
  proof: P.prop_of_isLimit hF (by intro ⟨j⟩; exact h j)

中文:
引理 prop_of_isLimit_fan
  结论: [P.IsClosedUnderFiniteProducts] {J : 类型} [Finite J] {f : J -> C}
  证明: P.prop_of_isLimit hF (by intro ⟨j⟩; exact h j)

Depends on / 依赖: P.prop_of_isLimit, prop_of_isLimit
-/
lemma prop_of_isLimit_fan [P.IsClosedUnderFiniteProducts] {J : Type*} [Finite J] {f : J -> C}
    {F : Fan f} (hF : IsLimit F) (h : forall j, P (f j)) :
    P F.pt :=
  P.prop_of_isLimit hF (by intro ⟨j⟩; exact h j)

/--
lemma `prop_product` / 引理 `prop_product`

English:
lemma prop_product
  statement: [P.IsClosedUnderFiniteProducts] {J : Type*} [Finite J] {f : J -> C}
  proof: P.prop_of_isLimit_fan (limit.isLimit (Discrete.functor f)) h

中文:
引理 prop_product
  结论: [P.IsClosedUnderFiniteProducts] {J : 类型} [Finite J] {f : J -> C}
  证明: P.prop_of_isLimit_fan (limit.isLimit (Discrete.functor f)) h

Depends on / 依赖: Discrete, Discrete.functor, P.prop_of_isLimit_fan, functor, isLimit, limit.isLimit, prop_of_isLimit_fan
-/
lemma prop_product [P.IsClosedUnderFiniteProducts] {J : Type*} [Finite J] {f : J -> C}
    [HasProduct f] (h : forall j, P (f j)) :
    P (∏ᶜ f) :=
  P.prop_of_isLimit_fan (limit.isLimit (Discrete.functor f)) h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsZero]
  signature: [P.IsClosedUnderIsomorphisms]
  body: by
    rintro X ⟨p⟩
    obtain ⟨Z, hZ, hZ₂⟩ := P.exists_prop_of_containsZero
    have hX : IsTerminal X :=
      (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
    exact P.prop_of_isZero (IsZero.of_iso hZ
      (IsLimit.c

中文:
实例 [P.ContainsZero]
  签名: [P.IsClosedUnderIsomorphisms]
  定义体: by
    rintro X ⟨p⟩
    obtain ⟨Z, hZ, hZ₂⟩ := P.exists_prop_of_containsZero
    have hX : IsTerminal X :=
      (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
    exact P.prop_of_isZero (IsZero.of_iso hZ
      (IsLimit.c

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.conePointUniqueUpToIso, IsLimit.equivOfNatIsoOfIso, IsTerminal, IsZero, IsZero.isTerminal, IsZero.of_iso, Iso.refl, P.exists_prop_of_containsZero, P.prop_of_isZero, conePointUniqueUpToIso, equivOfNatIsoOfIso, exists_prop_of_containsZero, isLimit, isTerminal, of_iso, p.diag.uniqueFromEmpty, p.isLimit, prop_of_isZero
-/
instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    obtain ⟨Z, hZ, hZ₂⟩ := P.exists_prop_of_containsZero
    have hX : IsTerminal X :=
      (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
    exact P.prop_of_isZero (IsZero.of_iso hZ
      (IsLimit.conePointUniqueUpToIso hX (IsZero.isTerminal hZ)))

variable {P} in
/--
lemma `IsClosedUnderFiniteProducts.mk'` / 引理 `IsClosedUnderFiniteProducts.mk'`

English:
lemma IsClosedUnderFiniteProducts.mk'
  statement: [HasFiniteProducts C]
  proof: by
  have := IsClosedUnderBinaryProducts.closedUnderIsomorphisms P
  have := hasFiniteProducts_of_has_binary_and_terminal (C := P.FullSubcategory)
  have := PreservesFiniteProducts.of_preserves_binary_and_terminal P.ι
  exact ⟨fun J _ => P.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι _⟩

中文:
引理 IsClosedUnderFiniteProducts.mk'
  结论: [HasFiniteProducts C]
  证明: by
  have := IsClosedUnderBinaryProducts.closedUnderIsomorphisms P
  have := hasFiniteProducts_of_has_binary_and_terminal (C := P.FullSubcategory)
  have := PreservesFiniteProducts.of_preserves_binary_and_terminal P.ι
  exact ⟨fun J _ => P.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι _⟩

Depends on / 依赖: FullSubcategory, IsClosedUnderBinaryProducts, IsClosedUnderBinaryProducts.closedUnderIsomorphisms, P.FullSubcategory, P.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_, PreservesFiniteProducts, PreservesFiniteProducts.of_preserves_binary_and_terminal, closedUnderIsomorphisms, hasFiniteProducts_of_has_binary_and_terminal, of_preserves_binary_and_terminal
-/
lemma IsClosedUnderFiniteProducts.mk' [HasFiniteProducts C]
    [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)]
    [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderFiniteProducts := by
  have := IsClosedUnderBinaryProducts.closedUnderIsomorphisms P
  have := hasFiniteProducts_of_has_binary_and_terminal (C := P.FullSubcategory)
  have := PreservesFiniteProducts.of_preserves_binary_and_terminal P.ι
  exact ⟨fun J _ => P.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι _⟩

/--
Definition of `IsClosedUnderBinaryCoproducts` / `IsClosedUnderBinaryCoproducts` 的定义

English:
abbreviation IsClosedUnderBinaryCoproducts
  body: P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)

中文:
缩写 IsClosedUnderBinaryCoproducts
  定义体: P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)

Depends on / 依赖: Discrete, IsClosedUnderColimitsOfShape, P.IsClosedUnderColimitsOfShape, WalkingPair
-/
abbrev IsClosedUnderBinaryCoproducts :=
  P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)

/--
lemma `prop_of_isColimit_binaryCofan` / 引理 `prop_of_isColimit_binaryCofan`

English:
lemma prop_of_isColimit_binaryCofan
  statement: [P.IsClosedUnderBinaryCoproducts] {X Y : C}
  proof: P.prop_of_isColimit hB (by rintro ⟨_ | _⟩ <;> assumption)

中文:
引理 prop_of_isColimit_binaryCofan
  结论: [P.IsClosedUnderBinaryCoproducts] {X Y : C}
  证明: P.prop_of_isColimit hB (by rintro ⟨_ | _⟩ <;> assumption)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, P.prop_of_isColimit, prop_of_isColimit
-/
lemma prop_of_isColimit_binaryCofan [P.IsClosedUnderBinaryCoproducts] {X Y : C}
    {B : BinaryCofan X Y} (hB : IsColimit B) (hX : P X) (hY : P Y) :
    P B.pt :=
  P.prop_of_isColimit hB (by rintro ⟨_ | _⟩ <;> assumption)

/--
lemma `prop_coprod` / 引理 `prop_coprod`

English:
lemma prop_coprod
  statement: [P.IsClosedUnderBinaryCoproducts] (X Y : C) [HasBinaryCoproduct X Y]
  proof: P.prop_of_isColimit_binaryCofan (colimit.isColimit (Limits.pair X Y)) hX hY

中文:
引理 prop_coprod
  结论: [P.IsClosedUnderBinaryCoproducts] (X Y : C) [HasBinaryCoproduct X Y]
  证明: P.prop_of_isColimit_binaryCofan (colimit.isColimit (Limits.pair X Y)) hX hY

Depends on / 依赖: Limits, Limits.pair, P.prop_of_isColimit_binaryCofan, colimit, colimit.isColimit, isColimit, prop_of_isColimit_binaryCofan
-/
lemma prop_coprod [P.IsClosedUnderBinaryCoproducts] (X Y : C) [HasBinaryCoproduct X Y]
    (hX : P X) (hY : P Y) :
    P (X ⨿ Y) :=
  P.prop_of_isColimit_binaryCofan (colimit.isColimit (Limits.pair X Y)) hX hY

/--
lemma `prop_of_isInitial` / 引理 `prop_of_isInitial`

English:
lemma prop_of_isInitial
  statement: [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)]
  proof: P.prop_of_isColimit hX (by rintro ⟨⟨⟩⟩)

中文:
引理 prop_of_isInitial
  结论: [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)]
  证明: P.prop_of_isColimit hX (by rintro ⟨⟨⟩⟩)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, P.prop_of_isColimit, prop_of_isColimit
-/
lemma prop_of_isInitial [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)]
    (X : C) (hX : IsInitial X) :
    P X :=
  P.prop_of_isColimit hX (by rintro ⟨⟨⟩⟩)

/--
lemma `prop_initial` / 引理 `prop_initial`

English:
lemma prop_initial
  given: [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] [HasInitial C]
  proof: P.prop_of_isInitial _ initialIsInitial

中文:
引理 prop_initial
  条件: [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] [HasInitial C]
  证明: P.prop_of_isInitial _ initialIsInitial

Depends on / 依赖: P.prop_of_isInitial, initialIsInitial, prop_of_isInitial
-/
lemma prop_initial [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] [HasInitial C] :
    P (⊥_ C) :=
  P.prop_of_isInitial _ initialIsInitial

-- see Note [lower instance priority]
instance (priority := 100) [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] [HasInitial C] :
    P.Nonempty :=
  nonempty_of_prop P.prop_initial

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms` / 引理 `IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms`

English:
lemma IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms
  statement: [HasInitial C]
  proof: by
    let h : IsColimit (BinaryCofan.mk (initial.to Y) e.hom) :=
      BinaryCofan.IsColimit.mk _ (fun _ f => e.inv ≫ f) (by cat_disch) (by simp) (by cat_disch)
    exact P.prop_of_isColimit_binaryCofan h P.prop_initial hX

中文:
引理 IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms
  结论: [HasInitial C]
  证明: by
    let h : IsColimit (BinaryCofan.mk (initial.to Y) e.hom) :=
      BinaryCofan.IsColimit.mk _ (fun _ f => e.inv ≫ f) (by cat_disch) (by simp) (by cat_disch)
    exact P.prop_of_isColimit_binaryCofan h P.prop_initial hX

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.mk, BinaryCofan.mk, IsColimit, P.prop_initial, P.prop_of_isColimit_binaryCofan, cat_disch, e.hom, e.inv, initial, initial.to, prop_initial, prop_of_isColimit_binaryCofan
-/
lemma IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms [HasInitial C]
    [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] [P.IsClosedUnderBinaryCoproducts] :
    P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let h : IsColimit (BinaryCofan.mk (initial.to Y) e.hom) :=
      BinaryCofan.IsColimit.mk _ (fun _ f => e.inv ≫ f) (by cat_disch) (by simp) (by cat_disch)
    exact P.prop_of_isColimit_binaryCofan h P.prop_initial hX

/--
Definition of `binaryCoproductsClosure` / `binaryCoproductsClosure` 的定义

English:
abbreviation binaryCoproductsClosure
  signature: (P : ObjectProperty C)
  body: P.colimitClosure (Discrete WalkingPair)

中文:
缩写 binaryCoproductsClosure
  签名: (P : Object命题erty C)
  定义体: P.colimitClosure (Discrete WalkingPair)

Depends on / 依赖: Discrete, P.colimitClosure, WalkingPair, colimitClosure
-/
abbrev binaryCoproductsClosure (P : ObjectProperty C) : ObjectProperty C :=
  P.colimitClosure (Discrete WalkingPair)

/--
lemma `binaryCoproductsClosure_le_iff` / 引理 `binaryCoproductsClosure_le_iff`

English:
lemma binaryCoproductsClosure_le_iff
  statement: [HasInitial C] {P Q : ObjectProperty C}
  proof: by
  refine ⟨fun h => (P.le_colimitsClosure _).trans h, fun h => ?_⟩
  let : Q.IsClosedUnderIsomorphisms := IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms Q
  exact colimitsClosure_le h

中文:
引理 binaryCoproductsClosure_le_iff
  结论: [HasInitial C] {P Q : Object命题erty C}
  证明: by
  refine ⟨fun h => (P.le_colimitsClosure _).trans h, fun h => ?_⟩
  let : Q.IsClosedUnderIsomorphisms := IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms Q
  exact colimitsClosure_le h

Depends on / 依赖: IsClosedUnderBinaryCoproducts, IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms, IsClosedUnderIsomorphisms, P.le_colimitsClosure, Q.IsClosedUnderIsomorphisms, closedUnderIsomorphisms, colimitsClosure_le, le_colimitsClosure
-/
lemma binaryCoproductsClosure_le_iff [HasInitial C] {P Q : ObjectProperty C}
    [Q.IsClosedUnderBinaryCoproducts] [Q.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] :
    P.binaryCoproductsClosure <= Q ↔ P <= Q := by
  refine ⟨fun h => (P.le_colimitsClosure _).trans h, fun h => ?_⟩
  let : Q.IsClosedUnderIsomorphisms := IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms Q
  exact colimitsClosure_le h

/--
Definition of `IsClosedUnderFiniteCoproducts` / `IsClosedUnderFiniteCoproducts` 的定义

English:
class IsClosedUnderFiniteCoproducts
  parameters: : Prop where
  axioms and operations (1):
    - isClosedUnderColimitsOfShape((J : Type) [Finite J]) : P.IsClosedUnderColimitsOfShape (Discrete J)  [default: by infer_instance]

中文:
类 IsClosedUnderFiniteCoproducts
  参数: : 命题 where
  公理与运算 (1 个):
    - isClosedUnderColimitsOfShape((J : Type) [Finite J]) : P.IsClosedUnderColimitsOfShape (Discrete J)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsClosedUnderFiniteCoproducts : Prop where
  isClosedUnderColimitsOfShape (J : Type) [Finite J] :
    P.IsClosedUnderColimitsOfShape (Discrete J) := by infer_instance

variable {P} in
/--
lemma `IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape` / 引理 `IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape`

English:
lemma IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape
  proof: by
    rw [P.isClosedUnderColimitsOfShape_iff_of_equivalence
      (Discrete.equivalence (equivShrink.{w} _))]
    exact H _

中文:
引理 IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape
  证明: by
    rw [P.isClosedUnderColimitsOfShape_iff_of_equivalence
      (Discrete.equivalence (equivShrink.{w} _))]
    exact H _

Depends on / 依赖: Discrete, Discrete.equivalence, P.isClosedUnderColimitsOfShape_iff_of_equivalence, equivShrink, equivalence, isClosedUnderColimitsOfShape_iff_of_equivalence
-/
lemma IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape
    (H : forall (J : Type w) [Finite J], P.IsClosedUnderColimitsOfShape (Discrete J)) :
    P.IsClosedUnderFiniteCoproducts where
  isClosedUnderColimitsOfShape J _ := by
    rw [P.isClosedUnderColimitsOfShape_iff_of_equivalence
      (Discrete.equivalence (equivShrink.{w} _))]
    exact H _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderFiniteCoproducts]
  signature: (J : Type*) [Finite J]
  body: by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have : P.IsClosedUnderColimitsOfShape (Discrete (Fin n)) :=
    IsClosedUnderFiniteCoproducts.isClosedUnderColimitsOfShape _
  exact IsClosedUnderColimitsOfShape.of_equivalence (Discrete.equivalence e.symm)

中文:
实例 [P.IsClosedUnderFiniteCoproducts]
  签名: (J : 类型) [Finite J]
  定义体: by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have : P.IsClosedUnderColimitsOfShape (Discrete (Fin n)) :=
    IsClosedUnderFiniteCoproducts.isClosedUnderColimitsOfShape _
  exact IsClosedUnderColimitsOfShape.of_equivalence (Discrete.equivalence e.symm)

Depends on / 依赖: Discrete, Discrete.equivalence, Finite, Finite.exists_equiv_fin, IsClosedUnderColimitsOfShape, IsClosedUnderColimitsOfShape.of_equivalence, IsClosedUnderFiniteCoproducts, IsClosedUnderFiniteCoproducts.isClosedUnderColimitsOfShape, P.IsClosedUnderColimitsOfShape, e.symm, equivalence, exists_equiv_fin, isClosedUnderColimitsOfShape, of_equivalence
-/
instance [P.IsClosedUnderFiniteCoproducts] (J : Type*) [Finite J] :
    P.IsClosedUnderColimitsOfShape (Discrete J) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have : P.IsClosedUnderColimitsOfShape (Discrete (Fin n)) :=
    IsClosedUnderFiniteCoproducts.isClosedUnderColimitsOfShape _
  exact IsClosedUnderColimitsOfShape.of_equivalence (Discrete.equivalence e.symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteCoproducts
  signature: C] [P.IsClosedUnderFiniteCoproducts] :
  body: inferInstance

中文:
实例 [HasFiniteCoproducts
  签名: C] [P.IsClosedUnderFiniteCoproducts] :
  定义体: inferInstance
-/
instance [HasFiniteCoproducts C] [P.IsClosedUnderFiniteCoproducts] :
    HasFiniteCoproducts P.FullSubcategory where
  out _ := inferInstance

/--
lemma `prop_of_isColimit_cofan` / 引理 `prop_of_isColimit_cofan`

English:
lemma prop_of_isColimit_cofan
  statement: [P.IsClosedUnderFiniteCoproducts] {J : Type*} [Finite J] {f : J -> C}
  proof: P.prop_of_isColimit hF (by intro ⟨j⟩; exact h j)

中文:
引理 prop_of_isColimit_cofan
  结论: [P.IsClosedUnderFiniteCoproducts] {J : 类型} [Finite J] {f : J -> C}
  证明: P.prop_of_isColimit hF (by intro ⟨j⟩; exact h j)

Depends on / 依赖: P.prop_of_isColimit, prop_of_isColimit
-/
lemma prop_of_isColimit_cofan [P.IsClosedUnderFiniteCoproducts] {J : Type*} [Finite J] {f : J -> C}
    {F : Cofan f} (hF : IsColimit F) (h : forall j, P (f j)) :
    P F.pt :=
  P.prop_of_isColimit hF (by intro ⟨j⟩; exact h j)

/--
lemma `prop_coproduct` / 引理 `prop_coproduct`

English:
lemma prop_coproduct
  statement: [P.IsClosedUnderFiniteCoproducts] {J : Type*} [Finite J] {f : J -> C}
  proof: P.prop_of_isColimit_cofan (colimit.isColimit (Discrete.functor f)) h

中文:
引理 prop_coproduct
  结论: [P.IsClosedUnderFiniteCoproducts] {J : 类型} [Finite J] {f : J -> C}
  证明: P.prop_of_isColimit_cofan (colimit.isColimit (Discrete.functor f)) h

Depends on / 依赖: Discrete, Discrete.functor, P.prop_of_isColimit_cofan, colimit, colimit.isColimit, functor, isColimit, prop_of_isColimit_cofan
-/
lemma prop_coproduct [P.IsClosedUnderFiniteCoproducts] {J : Type*} [Finite J] {f : J -> C}
    [HasCoproduct f] (h : forall j, P (f j)) :
    P (∐ f) :=
  P.prop_of_isColimit_cofan (colimit.isColimit (Discrete.functor f)) h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsZero]
  signature: [P.IsClosedUnderIsomorphisms]
  body: by
    rintro X ⟨p⟩
    obtain ⟨Z, hZ, hZ₂⟩ := P.exists_prop_of_containsZero
    have hX : IsInitial X :=
      (IsColimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cocone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isColimit
    exact P.prop_of_isZero (IsZero.of_iso hZ
      (IsCo

中文:
实例 [P.ContainsZero]
  签名: [P.IsClosedUnderIsomorphisms]
  定义体: by
    rintro X ⟨p⟩
    obtain ⟨Z, hZ, hZ₂⟩ := P.exists_prop_of_containsZero
    have hX : IsInitial X :=
      (IsColimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cocone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isColimit
    exact P.prop_of_isZero (IsZero.of_iso hZ
      (IsCo

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.coconePointUniqueUpToIso, IsColimit.equivOfNatIsoOfIso, IsInitial, IsZero, IsZero.isInitial, IsZero.of_iso, Iso.refl, P.exists_prop_of_containsZero, P.prop_of_isZero, coconePointUniqueUpToIso, equivOfNatIsoOfIso, exists_prop_of_containsZero, isColimit, isInitial, of_iso, p.diag.uniqueFromEmpty, p.isColimit
-/
instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty) where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    obtain ⟨Z, hZ, hZ₂⟩ := P.exists_prop_of_containsZero
    have hX : IsInitial X :=
      (IsColimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cocone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isColimit
    exact P.prop_of_isZero (IsZero.of_iso hZ
      (IsColimit.coconePointUniqueUpToIso hX (IsZero.isInitial hZ)))

variable {P} in
/--
lemma `IsClosedUnderFiniteCoproducts.mk'` / 引理 `IsClosedUnderFiniteCoproducts.mk'`

English:
lemma IsClosedUnderFiniteCoproducts.mk'
  statement: [HasFiniteCoproducts C]
  proof: by
  have := IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms P
  have := hasFiniteCoproducts_of_has_binary_and_initial (C := P.FullSubcategory)
  have := PreservesFiniteCoproducts.of_preserves_binary_and_initial P.ι
  exact ⟨fun J _ => P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape

中文:
引理 IsClosedUnderFiniteCoproducts.mk'
  结论: [HasFiniteCoproducts C]
  证明: by
  have := IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms P
  have := hasFiniteCoproducts_of_has_binary_and_initial (C := P.FullSubcategory)
  have := PreservesFiniteCoproducts.of_preserves_binary_and_initial P.ι
  exact ⟨fun J _ => P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape

Depends on / 依赖: FullSubcategory, IsClosedUnderBinaryCoproducts, IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms, P.FullSubcategory, P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_, PreservesFiniteCoproducts, PreservesFiniteCoproducts.of_preserves_binary_and_initial, closedUnderIsomorphisms, hasFiniteCoproducts_of_has_binary_and_initial, of_preserves_binary_and_initial
-/
lemma IsClosedUnderFiniteCoproducts.mk' [HasFiniteCoproducts C]
    [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)]
    [P.IsClosedUnderBinaryCoproducts] :
    P.IsClosedUnderFiniteCoproducts := by
  have := IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms P
  have := hasFiniteCoproducts_of_has_binary_and_initial (C := P.FullSubcategory)
  have := PreservesFiniteCoproducts.of_preserves_binary_and_initial P.ι
  exact ⟨fun J _ => P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _⟩

end CategoryTheory.ObjectProperty
