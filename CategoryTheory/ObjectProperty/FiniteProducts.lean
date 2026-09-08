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

/-- The typeclass saying that `P : ObjectProperty C` is stable under binary products. -/
/-
**CategoryTheory.ObjectProperty.IsClosedUnderBinaryProducts** 是 Mathlib 中的一个缩写定义
，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：IsClosedUnderBinaryProducts
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The typeclass saying that `P : ObjectProperty C` is stable under binary products
.
-/
abbrev IsClosedUnderBinaryProducts :=
  P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)
/-
**CategoryTheory.ObjectProperty.prop_of_isLimit_binaryFan** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：prop_of_isLimit_binaryFan [P.IsClosedUnderBinaryProducts] {X Y : C} {B : B
inaryFan X Y} (hB : IsLimit B) (hX : P X) (hY : P Y) : P B.pt
参数：hB : IsLimit B；hX : P X；hY : P Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isLimit`：prop_of_isLimit {F : J ⥤ 
C} {c : Cone F} (hc : IsLimit c) (hF : forall (j : J), P (F.obj j)) : P c.pt
-/
lemma prop_of_isLimit_binaryFan [P.IsClosedUnderBinaryProducts] {X Y : C} {B : BinaryFan X Y}
    (hB : IsLimit B) (hX : P X) (hY : P Y) :
    P B.pt :=
  P.prop_of_isLimit hB (by rintro ⟨_ | _⟩ <;> assumption)
/-
**CategoryTheory.ObjectProperty.prop_prod** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ObjectProperty`。
形式化陈述：prop_prod [P.IsClosedUnderBinaryProducts] (X Y : C) [HasBinaryProduct X Y]
 (hX : P X) (hY : P Y) : P (X ⨯ Y)
参数：X Y : C；hX : P X；hY : P Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isLimit_binaryFan`：prop_of_isLimit
_binaryFan [P.IsClosedUnderBinaryProducts] {X Y : C} {B : BinaryFan X Y} (hB : I
sLimit B) (hX : P X) (hY : P Y) : P B.pt
-/
lemma prop_prod [P.IsClosedUnderBinaryProducts] (X Y : C) [HasBinaryProduct X Y]
    (hX : P X) (hY : P Y) :
    P (X ⨯ Y) :=
  P.prop_of_isLimit_binaryFan (limit.isLimit _) hX hY
/-
**CategoryTheory.ObjectProperty.prop_of_isTerminal** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：prop_of_isTerminal [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] (X
 : C) (hX : IsTerminal X) : P X
参数：Discrete.{0} PEmpty；X : C；hX : IsTerminal X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isLimit`：prop_of_isLimit {F : J ⥤ 
C} {c : Cone F} (hc : IsLimit c) (hF : forall (j : J), P (F.obj j)) : P c.pt
-/
lemma prop_of_isTerminal [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)]
    (X : C) (hX : IsTerminal X) :
    P X :=
  P.prop_of_isLimit hX (by rintro ⟨⟨⟩⟩)
/-
**CategoryTheory.ObjectProperty.prop_terminal** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：prop_terminal [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [HasTer
minal C] : P (⊤_ C)
参数：Discrete.{0} PEmpty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isTerminal`：prop_of_isTerminal [P.
IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] (X : C) (hX : IsTerminal X) : 
P X
-/
lemma prop_terminal [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [HasTerminal C] :
    P (⊤_ C) :=
  P.prop_of_isTerminal _ terminalIsTerminal

-- see Note [lower instance priority]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [HasTerminal C] :
    P.Nonempty :=
  nonempty_of_prop P.prop_terminal

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ObjectProperty.IsClosedUnderBinaryProducts.closedUnderIsomorphi
sms** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnderBinary
Products`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : Catego
ryTheory.ObjectProperty C)   [CategoryTheory.Limits.HasTerminal C] [P.IsClosedUn
derLimitsOfShape (CategoryTheory.Discrete PEmpty.{1})]   [P.IsClosedUnderBinaryP
roducts], P.IsClosedUnderIsomorphisms
参数：P : CategoryTheory.ObjectProperty C；CategoryTheory.Discrete PEmpty.{1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isLimit_binaryFan`：prop_of_isLimit
_binaryFan [P.IsClosedUnderBinaryProducts] {X Y : C} {B : BinaryFan X Y} (hB : I
sLimit B) (hX : P X) (hY : P Y) : P B.pt
· 使用引理 `CategoryTheory.ObjectProperty.prop_terminal`：prop_terminal [P.IsClosedUn
derLimitsOfShape (Discrete.{0} PEmpty)] [HasTerminal C] : P (⊤_ C)
-/
lemma IsClosedUnderBinaryProducts.closedUnderIsomorphisms [HasTerminal C]
    [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let h : IsLimit (BinaryFan.mk (terminal.from Y) e.inv) :=
      BinaryFan.IsLimit.mk _ (fun _ f ↦ f ≫ e.hom) (by cat_disch) (by simp) (by cat_disch)
    exact P.prop_of_isLimit_binaryFan h P.prop_terminal hX

/-- All objects that are binary products of objects in `P`. -/
/-
**CategoryTheory.ObjectProperty.binaryProductsClosure** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：binaryProductsClosure (P : ObjectProperty C) : ObjectProperty C
参数：P : ObjectProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All objects that are binary products of objects in `P`.
-/
abbrev binaryProductsClosure (P : ObjectProperty C) : ObjectProperty C :=
  P.limitClosure (Discrete WalkingPair)
/-
**CategoryTheory.ObjectProperty.binaryProductsClosure_le_iff** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：binaryProductsClosure_le_iff [HasTerminal C] {P Q : ObjectProperty C} [Q.I
sClosedUnderBinaryProducts] [Q.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)]
 : P.binaryProductsClosure <= Q ↔ P <= Q
参数：Discrete.{0} PEmpty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.ObjectProperty.le_limitsClosure`：le_limitsClosure : P <= 
P.limitsClosure J
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderBinaryProducts.closedUnderIso
morphisms`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : C
ategoryTheory.ObjectProperty C)   [CategoryTheory.Limits.HasTerminal C]…
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_le`：limitsClosure_le {Q : Ob
jectProperty C} [Q.IsClosedUnderIsomorphisms] [forall (a : α), Q.IsClosedUnderLi
mitsOfShape (J a)] (h : P <= Q) : P.…
-/
lemma binaryProductsClosure_le_iff [HasTerminal C] {P Q : ObjectProperty C}
    [Q.IsClosedUnderBinaryProducts] [Q.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] :
    P.binaryProductsClosure ≤ Q ↔ P ≤ Q := by
  refine ⟨fun h ↦ (P.le_limitsClosure _).trans h, fun h ↦ ?_⟩
  let : Q.IsClosedUnderIsomorphisms := IsClosedUnderBinaryProducts.closedUnderIsomorphisms Q
  exact limitsClosure_le h

/-- The typeclass saying that `P : ObjectProperty C` is stable under finite products. -/
/-
**CategoryTheory.ObjectProperty.IsClosedUnderFiniteProducts** 是 Mathlib 中的一个类，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：IsClosedUnderFiniteProducts : Prop where isClosedUnderLimitsOfShape (J : T
ype) [Finite J] : P.IsClosedUnderLimitsOfShape (Discrete J)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The typeclass saying that `P : ObjectProperty C` is stable under finite products
.
-/
class IsClosedUnderFiniteProducts : Prop where
  isClosedUnderLimitsOfShape (J : Type) [Finite J] :
    P.IsClosedUnderLimitsOfShape (Discrete J) := by infer_instance

variable {P} in
/-- `IsClosedUnderFiniteProducts` may be checked at any universe. -/
/-
**CategoryTheory.ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderLimi
tsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnder
FiniteProducts`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C},   (∀ (J : Type w) [Finite J], P.IsClosedUnderLimitsO
fShape (CategoryTheory.Discrete J)) → P.IsClosedUnderFiniteProducts
参数：∀ (J : Type w) [Finite J], P.IsClosedUnderLimitsOfShape (CategoryTheory.Discr
ete J)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff_of_equivale
nce`：isClosedUnderLimitsOfShape_iff_of_equivalence (e : J ≌ J') : P.IsClosedUnde
rLimitsOfShape J ↔ P.IsClosedUnderLimitsOfShape J'

--- 原说明 ---
`IsClosedUnderFiniteProducts` may be checked at any universe.
-/
lemma IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape
    (H : ∀ (J : Type w) [Finite J], P.IsClosedUnderLimitsOfShape (Discrete J)) :
    P.IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    rw [P.isClosedUnderLimitsOfShape_iff_of_equivalence (Discrete.equivalence (equivShrink.{w} _))]
    exact H _
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderFiniteProducts] (J : Type*) [Finite J] :
    P.IsClosedUnderLimitsOfShape (Discrete J) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have : P.IsClosedUnderLimitsOfShape (Discrete (Fin n)) :=
    IsClosedUnderFiniteProducts.isClosedUnderLimitsOfShape _
  exact IsClosedUnderLimitsOfShape.of_equivalence (Discrete.equivalence e.symm)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteProducts C] [P.IsClosedUnderFiniteProducts] :
    HasFiniteProducts P.FullSubcategory where
  out _ := inferInstance
/-
**CategoryTheory.ObjectProperty.prop_of_isLimit_fan** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：prop_of_isLimit_fan [P.IsClosedUnderFiniteProducts] {J : Type*} [Finite J]
 {f : J -> C} {F : Fan f} (hF : IsLimit F) (h : forall j, P (f j)) : P F.pt
参数：hF : IsLimit F；h : forall j, P (f j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isLimit`：prop_of_isLimit {F : J ⥤ 
C} {c : Cone F} (hc : IsLimit c) (hF : forall (j : J), P (F.obj j)) : P c.pt
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderLimitsOfShapeDiscreteOfIs
ClosedUnderFiniteProductsOfFinite`：∀ {C : Type u_1} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C] (P : CategoryTheory.ObjectProperty C)   [P.IsClosedUnderFinite
Products] (J : …
-/
lemma prop_of_isLimit_fan [P.IsClosedUnderFiniteProducts] {J : Type*} [Finite J] {f : J → C}
    {F : Fan f} (hF : IsLimit F) (h : ∀ j, P (f j)) :
    P F.pt :=
  P.prop_of_isLimit hF (by intro ⟨j⟩; exact h j)
/-
**CategoryTheory.ObjectProperty.prop_product** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：prop_product [P.IsClosedUnderFiniteProducts] {J : Type*} [Finite J] {f : J
 -> C} [HasProduct f] (h : forall j, P (f j)) : P (∏ᶜ f)
参数：h : forall j, P (f j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isLimit_fan`：prop_of_isLimit_fan [
P.IsClosedUnderFiniteProducts] {J : Type*} [Finite J] {f : J -> C} {F : Fan f} (
hF : IsLimit F) (h : forall j, P (f j))…
-/
lemma prop_product [P.IsClosedUnderFiniteProducts] {J : Type*} [Finite J] {f : J → C}
    [HasProduct f] (h : ∀ j, P (f j)) :
    P (∏ᶜ f) :=
  P.prop_of_isLimit_fan (limit.isLimit (Discrete.functor f)) h
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.ObjectProperty.IsClosedUnderFiniteProducts.mk'** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnderFiniteProducts`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C}   [CategoryTheory.Limits.HasFiniteProducts C] [P.IsCl
osedUnderLimitsOfShape (CategoryTheory.Discrete PEmpty.{1})]   [P.IsClosedUnderB
inaryProducts], P.IsClosedUnderFiniteProducts
参数：CategoryTheory.Discrete PEmpty.{1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderBinaryProducts.closedUnderIso
morphisms`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : C
ategoryTheory.ObjectProperty C)   [CategoryTheory.Limits.HasTerminal C]…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal`：hasFinitePr
oducts_of_has_binary_and_terminal : HasFiniteProducts C
· 使用定理 `CategoryTheory.Limits.PreservesFiniteProducts.of_preserves_binary_and_te
rminal`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [
inst_1 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.F…
· 使用定理 `CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimi
tsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type
 u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_of_preservesLim
itsOfShape_ι`：isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι [HasLimitsO
fShape J P.FullSubcategory] [P.IsClosedUnderIsomorphisms] [PreservesLimits…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma IsClosedUnderFiniteProducts.mk' [HasFiniteProducts C]
    [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)]
    [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderFiniteProducts := by
  have := IsClosedUnderBinaryProducts.closedUnderIsomorphisms P
  have := hasFiniteProducts_of_has_binary_and_terminal (C := P.FullSubcategory)
  have := PreservesFiniteProducts.of_preserves_binary_and_terminal P.ι
  exact ⟨fun J _ ↦ P.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι _⟩

/-- The typeclass saying that `P : ObjectProperty C` is stable under binary coproducts. -/
/-
**CategoryTheory.ObjectProperty.IsClosedUnderBinaryCoproducts** 是 Mathlib 中的一个缩写
定义，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：IsClosedUnderBinaryCoproducts
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The typeclass saying that `P : ObjectProperty C` is stable under binary coproduc
ts.
-/
abbrev IsClosedUnderBinaryCoproducts :=
  P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)
/-
**CategoryTheory.ObjectProperty.prop_of_isColimit_binaryCofan** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：prop_of_isColimit_binaryCofan [P.IsClosedUnderBinaryCoproducts] {X Y : C} 
{B : BinaryCofan X Y} (hB : IsColimit B) (hX : P X) (hY : P Y) : P B.pt
参数：hB : IsColimit B；hX : P X；hY : P Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isColimit`：prop_of_isColimit {F : 
J ⥤ C} {c : Cocone F} (hc : IsColimit c) (hF : forall (j : J), P (F.obj j)) : P 
c.pt
-/
lemma prop_of_isColimit_binaryCofan [P.IsClosedUnderBinaryCoproducts] {X Y : C}
    {B : BinaryCofan X Y} (hB : IsColimit B) (hX : P X) (hY : P Y) :
    P B.pt :=
  P.prop_of_isColimit hB (by rintro ⟨_ | _⟩ <;> assumption)
/-
**CategoryTheory.ObjectProperty.prop_coprod** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：prop_coprod [P.IsClosedUnderBinaryCoproducts] (X Y : C) [HasBinaryCoproduc
t X Y] (hX : P X) (hY : P Y) : P (X ⨿ Y)
参数：X Y : C；hX : P X；hY : P Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isColimit_binaryCofan`：prop_of_isC
olimit_binaryCofan [P.IsClosedUnderBinaryCoproducts] {X Y : C} {B : BinaryCofan 
X Y} (hB : IsColimit B) (hX : P X) (hY : P Y) : P…
-/
lemma prop_coprod [P.IsClosedUnderBinaryCoproducts] (X Y : C) [HasBinaryCoproduct X Y]
    (hX : P X) (hY : P Y) :
    P (X ⨿ Y) :=
  P.prop_of_isColimit_binaryCofan (colimit.isColimit (Limits.pair X Y)) hX hY
/-
**CategoryTheory.ObjectProperty.prop_of_isInitial** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：prop_of_isInitial [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] (
X : C) (hX : IsInitial X) : P X
参数：Discrete.{0} PEmpty；X : C；hX : IsInitial X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isColimit`：prop_of_isColimit {F : 
J ⥤ C} {c : Cocone F} (hc : IsColimit c) (hF : forall (j : J), P (F.obj j)) : P 
c.pt
-/
lemma prop_of_isInitial [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)]
    (X : C) (hX : IsInitial X) :
    P X :=
  P.prop_of_isColimit hX (by rintro ⟨⟨⟩⟩)
/-
**CategoryTheory.ObjectProperty.prop_initial** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：prop_initial [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] [HasIn
itial C] : P (⊥_ C)
参数：Discrete.{0} PEmpty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isInitial`：prop_of_isInitial [P.Is
ClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] (X : C) (hX : IsInitial X) : P
 X
-/
lemma prop_initial [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] [HasInitial C] :
    P (⊥_ C) :=
  P.prop_of_isInitial _ initialIsInitial

-- see Note [lower instance priority]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] [HasInitial C] :
    P.Nonempty :=
  nonempty_of_prop P.prop_initial

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ObjectProperty.IsClosedUnderBinaryCoproducts.closedUnderIsomorp
hisms** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnderBina
ryCoproducts`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : Catego
ryTheory.ObjectProperty C)   [CategoryTheory.Limits.HasInitial C] [P.IsClosedUnd
erColimitsOfShape (CategoryTheory.Discrete PEmpty.{1})]   [P.IsClosedUnderBinary
Coproducts], P.IsClosedUnderIsomorphisms
参数：P : CategoryTheory.ObjectProperty C；CategoryTheory.Discrete PEmpty.{1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.initial.to_comp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasInitial C] {P Q : 
C}   (f : P ⟶ Q),   Categor…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isColimit_binaryCofan`：prop_of_isC
olimit_binaryCofan [P.IsClosedUnderBinaryCoproducts] {X Y : C} {B : BinaryCofan 
X Y} (hB : IsColimit B) (hX : P X) (hY : P Y) : P…
· 使用引理 `CategoryTheory.ObjectProperty.prop_initial`：prop_initial [P.IsClosedUnde
rColimitsOfShape (Discrete.{0} PEmpty)] [HasInitial C] : P (⊥_ C)
-/
lemma IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms [HasInitial C]
    [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] [P.IsClosedUnderBinaryCoproducts] :
    P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let h : IsColimit (BinaryCofan.mk (initial.to Y) e.hom) :=
      BinaryCofan.IsColimit.mk _ (fun _ f ↦ e.inv ≫ f) (by cat_disch) (by simp) (by cat_disch)
    exact P.prop_of_isColimit_binaryCofan h P.prop_initial hX

/-- All objects that are binary coproducts of objects in `P`. -/
/-
**CategoryTheory.ObjectProperty.binaryCoproductsClosure** 是 Mathlib 中的一个缩写定义，位于命
名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：binaryCoproductsClosure (P : ObjectProperty C) : ObjectProperty C
参数：P : ObjectProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All objects that are binary coproducts of objects in `P`.
-/
abbrev binaryCoproductsClosure (P : ObjectProperty C) : ObjectProperty C :=
  P.colimitClosure (Discrete WalkingPair)
/-
**CategoryTheory.ObjectProperty.binaryCoproductsClosure_le_iff** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：binaryCoproductsClosure_le_iff [HasInitial C] {P Q : ObjectProperty C} [Q.
IsClosedUnderBinaryCoproducts] [Q.IsClosedUnderColimitsOfShape (Discrete.{0} PEm
pty)] : P.binaryCoproductsClosure <= Q ↔ P <= Q
参数：Discrete.{0} PEmpty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.ObjectProperty.le_colimitsClosure`：le_colimitsClosure : P
 <= P.colimitsClosure J
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderBinaryCoproducts.closedUnderI
somorphisms`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P :
 CategoryTheory.ObjectProperty C)   [CategoryTheory.Limits.HasInitial C] …
· 使用引理 `CategoryTheory.ObjectProperty.colimitsClosure_le`：colimitsClosure_le {Q 
: ObjectProperty C} [Q.IsClosedUnderIsomorphisms] [forall (a : α), Q.IsClosedUnd
erColimitsOfShape (J a)] (h : P <= Q) …
-/
lemma binaryCoproductsClosure_le_iff [HasInitial C] {P Q : ObjectProperty C}
    [Q.IsClosedUnderBinaryCoproducts] [Q.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] :
    P.binaryCoproductsClosure ≤ Q ↔ P ≤ Q := by
  refine ⟨fun h ↦ (P.le_colimitsClosure _).trans h, fun h ↦ ?_⟩
  let : Q.IsClosedUnderIsomorphisms := IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms Q
  exact colimitsClosure_le h

/-- The typeclass saying that `P : ObjectProperty C` is stable under finite coproducts. -/
/-
**CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts** 是 Mathlib 中的一个类，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：IsClosedUnderFiniteCoproducts : Prop where isClosedUnderColimitsOfShape (J
 : Type) [Finite J] : P.IsClosedUnderColimitsOfShape (Discrete J)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The typeclass saying that `P : ObjectProperty C` is stable under finite coproduc
ts.
-/
class IsClosedUnderFiniteCoproducts : Prop where
  isClosedUnderColimitsOfShape (J : Type) [Finite J] :
    P.IsClosedUnderColimitsOfShape (Discrete J) := by infer_instance

variable {P} in
/-- `IsClosedUnderFiniteProducts` may be checked at any universe. -/
/-
**CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts.of_isClosedUnderCo
limitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedU
nderFiniteCoproducts`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C},   (∀ (J : Type w) [Finite J], P.IsClosedUnderColimit
sOfShape (CategoryTheory.Discrete J)) →     P.IsClosedUnderFiniteCoproducts
参数：∀ (J : Type w) [Finite J], P.IsClosedUnderColimitsOfShape (CategoryTheory.Dis
crete J)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff_of_equiva
lence`：isClosedUnderColimitsOfShape_iff_of_equivalence (e : J ≌ J') : P.IsClosed
UnderColimitsOfShape J ↔ P.IsClosedUnderColimitsOfShape J'

--- 原说明 ---
`IsClosedUnderFiniteProducts` may be checked at any universe.
-/
lemma IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape
    (H : ∀ (J : Type w) [Finite J], P.IsClosedUnderColimitsOfShape (Discrete J)) :
    P.IsClosedUnderFiniteCoproducts where
  isClosedUnderColimitsOfShape J _ := by
    rw [P.isClosedUnderColimitsOfShape_iff_of_equivalence
      (Discrete.equivalence (equivShrink.{w} _))]
    exact H _
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderFiniteCoproducts] (J : Type*) [Finite J] :
    P.IsClosedUnderColimitsOfShape (Discrete J) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have : P.IsClosedUnderColimitsOfShape (Discrete (Fin n)) :=
    IsClosedUnderFiniteCoproducts.isClosedUnderColimitsOfShape _
  exact IsClosedUnderColimitsOfShape.of_equivalence (Discrete.equivalence e.symm)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteCoproducts C] [P.IsClosedUnderFiniteCoproducts] :
    HasFiniteCoproducts P.FullSubcategory where
  out _ := inferInstance
/-
**CategoryTheory.ObjectProperty.prop_of_isColimit_cofan** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：prop_of_isColimit_cofan [P.IsClosedUnderFiniteCoproducts] {J : Type*} [Fin
ite J] {f : J -> C} {F : Cofan f} (hF : IsColimit F) (h : forall j, P (f j)) : P
 F.pt
参数：hF : IsColimit F；h : forall j, P (f j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isColimit`：prop_of_isColimit {F : 
J ⥤ C} {c : Cocone F} (hc : IsColimit c) (hF : forall (j : J), P (F.obj j)) : P 
c.pt
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderColimitsOfShapeDiscreteOf
IsClosedUnderFiniteCoproductsOfFinite`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] (P : CategoryTheory.ObjectProperty C)   [P.IsClosedUnderFi
niteCoproducts] (J …
-/
lemma prop_of_isColimit_cofan [P.IsClosedUnderFiniteCoproducts] {J : Type*} [Finite J] {f : J → C}
    {F : Cofan f} (hF : IsColimit F) (h : ∀ j, P (f j)) :
    P F.pt :=
  P.prop_of_isColimit hF (by intro ⟨j⟩; exact h j)
/-
**CategoryTheory.ObjectProperty.prop_coproduct** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：prop_coproduct [P.IsClosedUnderFiniteCoproducts] {J : Type*} [Finite J] {f
 : J -> C} [HasCoproduct f] (h : forall j, P (f j)) : P (∐ f)
参数：h : forall j, P (f j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isColimit_cofan`：prop_of_isColimit
_cofan [P.IsClosedUnderFiniteCoproducts] {J : Type*} [Finite J] {f : J -> C} {F 
: Cofan f} (hF : IsColimit F) (h : forall j…
-/
lemma prop_coproduct [P.IsClosedUnderFiniteCoproducts] {J : Type*} [Finite J] {f : J → C}
    [HasCoproduct f] (h : ∀ j, P (f j)) :
    P (∐ f) :=
  P.prop_of_isColimit_cofan (colimit.isColimit (Discrete.functor f)) h
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts.mk'** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C}   [CategoryTheory.Limits.HasFiniteCoproducts C] [P.Is
ClosedUnderColimitsOfShape (CategoryTheory.Discrete PEmpty.{1})]   [P.IsClosedUn
derBinaryCoproducts], P.IsClosedUnderFiniteCoproducts
参数：CategoryTheory.Discrete PEmpty.{1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderBinaryCoproducts.closedUnderI
somorphisms`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P :
 CategoryTheory.ObjectProperty C)   [CategoryTheory.Limits.HasInitial C] …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.hasFiniteCoproducts_of_has_binary_and_initial`：hasFiniteC
oproducts_of_has_binary_and_initial : HasFiniteCoproducts C
· 使用定理 `CategoryTheory.PreservesFiniteCoproducts.of_preserves_binary_and_initial
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1
 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.F…
· 使用定理 `CategoryTheory.preservesColimitOfShape_of_createsColimitsOfShape_and_has
ColimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_of_preservesC
olimitsOfShape_ι`：isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι [Ha
sColimitsOfShape J P.FullSubcategory] [P.IsClosedUnderIsomorphisms] [Preserves…
-/
lemma IsClosedUnderFiniteCoproducts.mk' [HasFiniteCoproducts C]
    [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)]
    [P.IsClosedUnderBinaryCoproducts] :
    P.IsClosedUnderFiniteCoproducts := by
  have := IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms P
  have := hasFiniteCoproducts_of_has_binary_and_initial (C := P.FullSubcategory)
  have := PreservesFiniteCoproducts.of_preserves_binary_and_initial P.ι
  exact ⟨fun J _ ↦ P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _⟩

end CategoryTheory.ObjectProperty

