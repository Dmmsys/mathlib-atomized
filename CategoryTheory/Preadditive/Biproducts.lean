/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Ext
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Tactic.Abel

/-!
# Basic facts about biproducts in preadditive categories.

In (or between) preadditive categories,

* Any biproduct satisfies the equality
  `total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`,
  or, in the binary case, `total : fst ≫ inl + snd ≫ inr = 𝟙 X`.

* Any (binary) `product` or (binary) `coproduct` is a (binary) `biproduct`.

* In any category (with zero morphisms), if `biprod.map f g` is an isomorphism,
  then both `f` and `g` are isomorphisms.

* If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
  so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
  via Gaussian elimination.

* As a corollary of the previous two facts,
  if we have an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  we can construct an isomorphism `X₂ ≅ Y₂`.

* If `f : W ⊞ X ⟶ Y ⊞ Z` is an isomorphism, either `𝟙 W = 0`,
  or at least one of the component maps `W ⟶ Y` and `W ⟶ Z` is nonzero.

* If `f : ⨁ S ⟶ ⨁ T` is an isomorphism,
  then every column (corresponding to a nonzero summand in the domain)
  has some nonzero matrix entry.

* A functor preserves a biproduct if and only if it preserves
  the corresponding product if and only if it preserves the corresponding coproduct.

There are connections between this material and the special case of the category whose morphisms are
matrices over a ring, in particular the Schur complement (see
`Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`). In particular, the declarations
`CategoryTheory.Biprod.isoElim`, `CategoryTheory.Biprod.gaussian`
and `Matrix.invertibleOfFromBlocks₁₁Invertible` are all closely related.

-/

@[expose] public section


open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

open CategoryTheory.Functor

open CategoryTheory.Preadditive

universe v v' u u'

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace Limits

section Fintype

variable {J : Type*} [Fintype J]

set_option backward.isDefEq.respectTransparency false in
/-- In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
/-
**CategoryTheory.Limits.isBilimitOfTotal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：isBilimitOfTotal {f : J -> C} (b : Bicone f) (total : ∑ j : J, b.π j ≫ b.ι
 j = 𝟙 b.pt) : b.IsBilimit where isLimit
参数：b : Bicone f；total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
def isBilimitOfTotal {f : J → C} (b : Bicone f) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt) :
    b.IsBilimit where
  isLimit :=
    { lift := fun s => ∑ j : J, s.π.app ⟨j⟩ ≫ b.ι j
      uniq := fun s m h => by
        rw [← Category.comp_id m]
        dsimp
        rw [← total, comp_sum]
        apply Finset.sum_congr rfl
        intro j _
        have reassoced : m ≫ Bicone.π b j ≫ Bicone.ι b j = s.π.app ⟨j⟩ ≫ Bicone.ι b j := by
          simpa using eq_whisker (h ⟨j⟩) _
        rw [reassoced]
      fac := fun s j => by
        classical
        cases j
        simp only [sum_comp, Category.assoc, Bicone.toCone_π_app, b.ι_π, comp_dite]
        simp }
  isColimit :=
    { desc := fun s => ∑ j : J, b.π j ≫ s.ι.app ⟨j⟩
      uniq := fun s m h => by
        rw [← Category.id_comp m]
        dsimp
        rw [← total, sum_comp]
        apply Finset.sum_congr rfl
        intro j _
        simpa using b.π j ≫= h ⟨j⟩
      fac := fun s j => by
        classical
        cases j
        simp only [comp_sum, ← Category.assoc, Bicone.toCocone_ι_app, b.ι_π, dite_comp]
        simp }
/-
**CategoryTheory.Limits.IsBilimit.total** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.IsBilimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {J : Type u_1}   [inst_2 : Fintype J] {f : J → C} {b : Ca
tegoryTheory.Limits.Bicone f} (i : b.IsBilimit),   ∑ j, CategoryTheory.CategoryS
truct.comp (b.π j) (b.ι j) = CategoryTheory.CategoryStruct.id b.pt
参数：i : b.IsBilimit；b.π j；b.ι j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Bicone.ι_π`：∀ {J : Type w} {C : Type uC} [inst : C
ategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C] {F : J → C} …
· 使用定理 `CategoryTheory.comp_dite`：comp_dite {P : Prop} [Decidable P] {X Y Z : C}
 (f : X ⟶ Y) (g : P -> (Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (f ≫ if h : P then g h el
se g' h) = if …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsBilimit.total {f : J → C} {b : Bicone f} (i : b.IsBilimit) :
    ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt :=
  i.isLimit.hom_ext fun j => by
    classical
    cases j
    simp [sum_comp, b.ι_π, comp_dite]

/-- In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
/-
**CategoryTheory.Limits.hasBiproduct_of_total** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：hasBiproduct_of_total {f : J -> C} (b : Bicone f) (total : ∑ j : J, b.π j 
≫ b.ι j = 𝟙 b.pt) : HasBiproduct f
参数：b : Bicone f；total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBiproduct.mk`：∀ {J : Type w} {C : Type uC} [ins
t : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C] {F : J → C} …

--- 原说明 ---
In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
theorem hasBiproduct_of_total {f : J → C} (b : Bicone f)
    (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt) : HasBiproduct f :=
  HasBiproduct.mk
    { bicone := b
      isBilimit := isBilimitOfTotal b total }

/-- In a preadditive category, any finite bicone which is a limit cone is in fact a bilimit
bicone. -/
/-
**CategoryTheory.Limits.isBilimitOfIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：isBilimitOfIsLimit {f : J -> C} (t : Bicone f) (ht : IsLimit t.toCone) : t
.IsBilimit
参数：t : Bicone f；ht : IsLimit t.toCone。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a preadditive category, any finite bicone which is a limit cone is in fact a 
bilimit
bicone.
-/
def isBilimitOfIsLimit {f : J → C} (t : Bicone f) (ht : IsLimit t.toCone) : t.IsBilimit :=
  isBilimitOfTotal _ <|
    ht.hom_ext fun j => by
      classical
      cases j
      simp [sum_comp, t.ι_π, comp_dite]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- We can turn any limit cone over a pair into a bilimit bicone. -/
/-
**CategoryTheory.Limits.biconeIsBilimitOfLimitConeOfIsLimit** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：biconeIsBilimitOfLimitConeOfIsLimit {f : J -> C} {t : Cone (Discrete.funct
or f)} (ht : IsLimit t) : (Bicone.ofLimitCone ht).IsBilimit
参数：Discrete.functor f；ht : IsLimit t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can turn any limit cone over a pair into a bilimit bicone.
-/
def biconeIsBilimitOfLimitConeOfIsLimit {f : J → C} {t : Cone (Discrete.functor f)}
    (ht : IsLimit t) : (Bicone.ofLimitCone ht).IsBilimit :=
  isBilimitOfIsLimit _ <| IsLimit.ofIsoLimit ht <| Cone.ext (Iso.refl _) (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In a preadditive category, any finite bicone which is a colimit cocone is in fact a bilimit
bicone. -/
/-
**CategoryTheory.Limits.isBilimitOfIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：isBilimitOfIsColimit {f : J -> C} (t : Bicone f) (ht : IsColimit t.toCocon
e) : t.IsBilimit
参数：t : Bicone f；ht : IsColimit t.toCocone。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a preadditive category, any finite bicone which is a colimit cocone is in fac
t a bilimit
bicone.
-/
def isBilimitOfIsColimit {f : J → C} (t : Bicone f) (ht : IsColimit t.toCocone) : t.IsBilimit :=
  isBilimitOfTotal _ <|
    ht.hom_ext fun j => by
      classical
      cases j
      simp_rw [Bicone.toCocone_ι_app, comp_sum, ← Category.assoc, t.ι_π, dite_comp]
      simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- We can turn any limit cone over a pair into a bilimit bicone. -/
/-
**CategoryTheory.Limits.biconeIsBilimitOfColimitCoconeOfIsColimit** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：biconeIsBilimitOfColimitCoconeOfIsColimit {f : J -> C} {t : Cocone (Discre
te.functor f)} (ht : IsColimit t) : (Bicone.ofColimitCocone ht).IsBilimit
参数：Discrete.functor f；ht : IsColimit t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can turn any limit cone over a pair into a bilimit bicone.
-/
def biconeIsBilimitOfColimitCoconeOfIsColimit {f : J → C} {t : Cocone (Discrete.functor f)}
    (ht : IsColimit t) : (Bicone.ofColimitCocone ht).IsBilimit :=
  isBilimitOfIsColimit _ <| IsColimit.ofIsoColimit ht <| Cocone.ext (Iso.refl _) <| by
    simp

end Fintype

section Finite

variable {J : Type*} [Finite J]

/-- In a preadditive category, if the product over `f : J → C` exists,
then the biproduct over `f` exists. -/
/-
**CategoryTheory.Limits.HasBiproduct.of_hasProduct** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.HasBiproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {J : Type u_1}   [Finite J] (f : J → C) [CategoryTheory.L
imits.HasProduct f], CategoryTheory.Limits.HasBiproduct f
参数：f : J → C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `CategoryTheory.Limits.HasBiproduct.mk`：∀ {J : Type w} {C : Type uC} [ins
t : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C] {F : J → C} …

--- 原说明 ---
In a preadditive category, if the product over `f : J → C` exists,
then the biproduct over `f` exists.
-/
theorem HasBiproduct.of_hasProduct (f : J → C) [HasProduct f] : HasBiproduct f := by
  cases nonempty_fintype J
  exact HasBiproduct.mk
    { bicone := _
      isBilimit := biconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }

/-- In a preadditive category, if the coproduct over `f : J → C` exists,
then the biproduct over `f` exists. -/
/-
**CategoryTheory.Limits.HasBiproduct.of_hasCoproduct** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.HasBiproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {J : Type u_1}   [Finite J] (f : J → C) [CategoryTheory.L
imits.HasCoproduct f], CategoryTheory.Limits.HasBiproduct f
参数：f : J → C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `CategoryTheory.Limits.HasBiproduct.mk`：∀ {J : Type w} {C : Type uC} [ins
t : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C] {F : J → C} …

--- 原说明 ---
In a preadditive category, if the coproduct over `f : J → C` exists,
then the biproduct over `f` exists.
-/
theorem HasBiproduct.of_hasCoproduct (f : J → C) [HasCoproduct f] : HasBiproduct f := by
  cases nonempty_fintype J
  exact HasBiproduct.mk
    { bicone := _
      isBilimit := biconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }

end Finite

/-- A preadditive category with finite products has finite biproducts. -/
/-
**CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits.HasFiniteBiproducts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [CategoryTheory.Limits.HasFiniteProducts C], CategoryTh
eory.Limits.HasFiniteBiproducts C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBiproduct.of_hasProduct`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {J : 
Type u_1}   [Finite J] (f : J → C) [Ca…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
A preadditive category with finite products has finite biproducts.
-/
theorem HasFiniteBiproducts.of_hasFiniteProducts [HasFiniteProducts C] : HasFiniteBiproducts C :=
  ⟨fun _ => { has_biproduct := fun _ => HasBiproduct.of_hasProduct _ }⟩

/-- A preadditive category with finite coproducts has finite biproducts. -/
/-
**CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteCoproducts** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Limits.HasFiniteBiproducts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [CategoryTheory.Limits.HasFiniteCoproducts C], Category
Theory.Limits.HasFiniteBiproducts C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBiproduct.of_hasCoproduct`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {J 
: Type u_1}   [Finite J] (f : J → C) [Ca…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
A preadditive category with finite coproducts has finite biproducts.
-/
theorem HasFiniteBiproducts.of_hasFiniteCoproducts [HasFiniteCoproducts C] :
    HasFiniteBiproducts C :=
  ⟨fun _ => { has_biproduct := fun _ => HasBiproduct.of_hasCoproduct _ }⟩

section HasBiproduct

variable {J : Type} [Fintype J] {f : J → C} [HasBiproduct f]

/-- In any preadditive category, any biproduct satisfies
`∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
-/
@[simp]
/-
**CategoryTheory.Limits.biproduct.total** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.biproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {J : Type}   [inst_2 : Fintype J] {f : J → C} [inst_3 : C
ategoryTheory.Limits.HasBiproduct f],   ∑ j,       CategoryTheory.CategoryStruct
.comp (CategoryTheory.Limits.biproduct.π f j)         (CategoryTheory.Limits.bip
roduct.ι f j) =     CategoryTheory.CategoryStruct.id (⨁ f)
参数：CategoryTheory.Limits.biproduct.π f j；CategoryTheory.Limits.biproduct.ι f j；⨁
 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsBilimit.total`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {J : Type u_1}  
 [inst_2 : Fintype J] {f : …

--- 原说明 ---
In any preadditive category, any biproduct satisfies
`∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
-/
theorem biproduct.total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) :=
  IsBilimit.total (biproduct.isBilimit _)
/-
**CategoryTheory.Limits.biproduct.lift_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.biproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {J : Type}   [inst_2 : Fintype J] {f : J → C} [inst_3 : C
ategoryTheory.Limits.HasBiproduct f] {T : C} {g : (j : J) → T ⟶ f j},   Category
Theory.Limits.biproduct.lift g =     ∑ j, CategoryTheory.CategoryStruct.comp (g 
j) (CategoryTheory.Limits.biproduct.ι f j)
参数：j : J；g j；CategoryTheory.Limits.biproduct.ι f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π`：∀ {J : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.comp_dite`：comp_dite {P : Prop} [Decidable P] {X Y Z : C}
 (f : X ⟶ Y) (g : P -> (Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (f ≫ if h : P then g h el
se g' h) = if …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.lift_eq {T : C} {g : ∀ j, T ⟶ f j} :
    biproduct.lift g = ∑ j, g j ≫ biproduct.ι f j := by
  classical
  ext j
  simp only [sum_comp, biproduct.ι_π, comp_dite, biproduct.lift_π, Category.assoc, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, if_true]
/-
**CategoryTheory.Limits.biproduct.desc_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.biproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {J : Type}   [inst_2 : Fintype J] {f : J → C} [inst_3 : C
ategoryTheory.Limits.HasBiproduct f] {T : C} {g : (j : J) → f j ⟶ T},   Category
Theory.Limits.biproduct.desc g =     ∑ j, CategoryTheory.CategoryStruct.comp (Ca
tegoryTheory.Limits.biproduct.π f j) (g j)
参数：j : J；CategoryTheory.Limits.biproduct.π f j；g j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π_assoc`：∀ {J : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.dite_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {P : Prop} [inst_1 : Decidable P] {X Y Z : C} (g : P → (Z ⟶ Y))   (g'
 : ¬P → (Z ⟶ Y…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Finset.sum_dite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → a = x → M)
, (∑ x ∈…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.desc_eq {T : C} {g : ∀ j, f j ⟶ T} :
    biproduct.desc g = ∑ j, biproduct.π f j ≫ g j := by
  classical
  ext j
  simp [comp_sum, biproduct.ι_π_assoc, dite_comp]

@[reassoc]
/-
**CategoryTheory.Limits.biproduct.lift_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.biproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {J : Type}   [inst_2 : Fintype J] {f : J → C} [inst_3 : C
ategoryTheory.Limits.HasBiproduct f] {T U : C} {g : (j : J) → T ⟶ f j}   {h : (j
 : J) → f j ⟶ U},   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.bi
product.lift g) (CategoryTheory.Limits.biproduct.desc h) =     ∑ j, CategoryTheo
ry.CategoryStruct.comp (g j) (h j)
参数：j : J；j : J；CategoryTheory.Limits.biproduct.lift g；CategoryTheory.Limits.bipr
oduct.desc h；g j；h j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biproduct.lift_eq`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {J : Type}   [
inst_2 : Fintype J] {f : J → …
· 使用定理 `CategoryTheory.Limits.biproduct.desc_eq`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {J : Type}   [
inst_2 : Fintype J] {f : J → …
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π_assoc`：∀ {J : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.dite_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {P : Prop} [inst_1 : Decidable P] {X Y Z : C} (g : P → (Z ⟶ Y))   (g'
 : ¬P → (Z ⟶ Y…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.comp_dite`：comp_dite {P : Prop} [Decidable P] {X Y Z : C}
 (f : X ⟶ Y) (g : P -> (Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (f ≫ if h : P then g h el
se g' h) = if …
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.lift_desc {T U : C} {g : ∀ j, T ⟶ f j} {h : ∀ j, f j ⟶ U} :
    biproduct.lift g ≫ biproduct.desc h = ∑ j : J, g j ≫ h j := by
  classical
  simp [biproduct.lift_eq, biproduct.desc_eq, comp_sum, sum_comp, biproduct.ι_π_assoc, comp_dite,
    dite_comp]
/-
**CategoryTheory.Limits.biproduct.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.biproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {J : Type}   [inst_2 : Fintype J] [inst_3 : CategoryTheor
y.Limits.HasFiniteBiproducts C] {f g : J → C} {h : (j : J) → f j ⟶ g j},   Categ
oryTheory.Limits.biproduct.map h =     ∑ j,       CategoryTheory.CategoryStruct.
comp (CategoryTheory.Limits.biproduct.π f j)         (CategoryTheory.CategoryStr
uct.comp (h j) (CategoryTheory.Limits.biproduct.ι g j))
参数：j : J；CategoryTheory.Limits.biproduct.π f j；CategoryTheory.CategoryStruct.com
p (h j) (CategoryTheory.Limits.biproduct.ι g j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.map_π`：∀ {J : Type w} {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π_assoc`：∀ {J : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.dite_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {P : Prop} [inst_1 : Decidable P] {X Y Z : C} (g : P → (Z ⟶ Y))   (g'
 : ¬P → (Z ⟶ Y…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π`：∀ {J : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.comp_dite`：comp_dite {P : Prop} [Decidable P] {X Y Z : C}
 (f : X ⟶ Y) (g : P -> (Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (f ≫ if h : P then g h el
se g' h) = if …
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.map_eq [HasFiniteBiproducts C] {f g : J → C} {h : ∀ j, f j ⟶ g j} :
    biproduct.map h = ∑ j : J, biproduct.π f j ≫ h j ≫ biproduct.ι g j := by
  classical
  ext
  simp [biproduct.ι_π, biproduct.ι_π_assoc, sum_comp, comp_dite, dite_comp]

@[reassoc]
/-
**CategoryTheory.Limits.biproduct.lift_matrix** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.biproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {J : Type}   [inst_2 : Fintype J] {K : Type} [inst_3 : Fi
nite K] [inst_4 : CategoryTheory.Limits.HasFiniteBiproducts C] {f : J → C}   {g 
: K → C} {P : C} (x : (j : J) → P ⟶ f j) (m : (j : J) → (k : K) → f j ⟶ g k),   
CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.biproduct.lift x)     
  (CategoryTheory.Limits.biproduct.matrix m) =     CategoryTheory.Limits.biprodu
ct.lift fun k => ∑ j, CategoryTheory.CategoryStruct.comp (x j) (m j k)
参数：x : (j : J) → P ⟶ f j；m : (j : J) → (k : K) → f j ⟶ g k；CategoryTheory.Limits
.biproduct.lift x；CategoryTheory.Limits.biproduct.matrix m；x j；m j k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.matrix_π`：∀ {J : Type} [inst : Finite J]
 {K : Type} [inst_1 : Finite K] {C : Type u} [inst_2 : CategoryTheory.Category.{
v, u} C]   [inst_3 : CategoryT…
· 使用定理 `CategoryTheory.Limits.biproduct.lift_desc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {J : Type}  
 [inst_2 : Fintype J] {f : J → …
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.lift_matrix {K : Type} [Finite K] [HasFiniteBiproducts C] {f : J → C} {g : K → C}
    {P} (x : ∀ j, P ⟶ f j) (m : ∀ j k, f j ⟶ g k) :
    biproduct.lift x ≫ biproduct.matrix m = biproduct.lift fun k => ∑ j, x j ≫ m j k := by
  ext
  simp [biproduct.lift_desc]

end HasBiproduct

section HasFiniteBiproducts

variable {J K : Type} [Finite J] {f : J → C} [HasFiniteBiproducts C]

@[reassoc]
/-
**CategoryTheory.Limits.biproduct.matrix_desc** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.biproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {J K : Type}   [inst_2 : Finite J] [inst_3 : CategoryTheo
ry.Limits.HasFiniteBiproducts C] [inst_4 : Fintype K] {f : J → C}   {g : K → C} 
(m : (j : J) → (k : K) → f j ⟶ g k) {P : C} (x : (k : K) → g k ⟶ P),   CategoryT
heory.CategoryStruct.comp (CategoryTheory.Limits.biproduct.matrix m)       (Cate
goryTheory.Limits.biproduct.desc x) =     CategoryTheory.Limits.biproduct.desc f
un j => ∑ k, CategoryTheory.CategoryStruct.comp (m j k) (x k)
参数：m : (j : J) → (k : K) → f j ⟶ g k；x : (k : K) → g k ⟶ P；CategoryTheory.Limits
.biproduct.matrix m；CategoryTheory.Limits.biproduct.desc x；m j k；x k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.ι_matrix_assoc`：∀ {J : Type} [inst : Fin
ite J] {K : Type} [inst_1 : Finite K] {C : Type u} [inst_2 : CategoryTheory.Cate
gory.{v, u} C]   [inst_3 : CategoryT…
· 使用定理 `CategoryTheory.Limits.biproduct.lift_desc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {J : Type}  
 [inst_2 : Fintype J] {f : J → …
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.matrix_desc [Fintype K] {f : J → C} {g : K → C}
    (m : ∀ j k, f j ⟶ g k) {P} (x : ∀ k, g k ⟶ P) :
    biproduct.matrix m ≫ biproduct.desc x = biproduct.desc fun j => ∑ k, m j k ≫ x k := by
  ext
  simp [lift_desc]

variable [Finite K]

@[reassoc]
/-
**CategoryTheory.Limits.biproduct.matrix_map** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.biproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {J K : Type}   [inst_2 : Finite J] [inst_3 : CategoryTheo
ry.Limits.HasFiniteBiproducts C] [inst_4 : Finite K] {f : J → C}   {g h : K → C}
 (m : (j : J) → (k : K) → f j ⟶ g k) (n : (k : K) → g k ⟶ h k),   CategoryTheory
.CategoryStruct.comp (CategoryTheory.Limits.biproduct.matrix m)       (CategoryT
heory.Limits.biproduct.map n) =     CategoryTheory.Limits.biproduct.matrix fun j
 k => CategoryTheory.CategoryStruct.comp (m j k) (n k)
参数：m : (j : J) → (k : K) → f j ⟶ g k；n : (k : K) → g k ⟶ h k；CategoryTheory.Limi
ts.biproduct.matrix m；CategoryTheory.Limits.biproduct.map n；m j k；n k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.map_π`：∀ {J : Type w} {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Limits.biproduct.matrix_π_assoc`：∀ {J : Type} [inst : Fin
ite J] {K : Type} [inst_1 : Finite K] {C : Type u} [inst_2 : CategoryTheory.Cate
gory.{v, u} C]   [inst_3 : CategoryT…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc_assoc`：∀ {J : Type w} {C : Type u
} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.matrix_π`：∀ {J : Type} [inst : Finite J]
 {K : Type} [inst_1 : Finite K] {C : Type u} [inst_2 : CategoryTheory.Category.{
v, u} C]   [inst_3 : CategoryT…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.matrix_map {f : J → C} {g : K → C} {h : K → C} (m : ∀ j k, f j ⟶ g k)
    (n : ∀ k, g k ⟶ h k) :
    biproduct.matrix m ≫ biproduct.map n = biproduct.matrix fun j k => m j k ≫ n k := by
  ext
  simp

@[reassoc]
/-
**CategoryTheory.Limits.biproduct.map_matrix** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.biproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {J K : Type}   [inst_2 : Finite J] [inst_3 : CategoryTheo
ry.Limits.HasFiniteBiproducts C] [inst_4 : Finite K] {f g : J → C}   {h : K → C}
 (m : (k : J) → f k ⟶ g k) (n : (j : J) → (k : K) → g j ⟶ h k),   CategoryTheory
.CategoryStruct.comp (CategoryTheory.Limits.biproduct.map m)       (CategoryTheo
ry.Limits.biproduct.matrix n) =     CategoryTheory.Limits.biproduct.matrix fun j
 k => CategoryTheory.CategoryStruct.comp (m j) (n j k)
参数：m : (k : J) → f k ⟶ g k；n : (j : J) → (k : K) → g j ⟶ h k；CategoryTheory.Limi
ts.biproduct.map m；CategoryTheory.Limits.biproduct.matrix n；m j；n j k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.matrix_π`：∀ {J : Type} [inst : Finite J]
 {K : Type} [inst_1 : Finite K] {C : Type u} [inst_2 : CategoryTheory.Category.{
v, u} C]   [inst_3 : CategoryT…
· 使用定理 `CategoryTheory.Limits.biproduct.map_desc`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.map_matrix {f : J → C} {g : J → C} {h : K → C} (m : ∀ k, f k ⟶ g k)
    (n : ∀ j k, g j ⟶ h k) :
    biproduct.map m ≫ biproduct.matrix n = biproduct.matrix fun j k => m j ≫ n j k := by
  ext
  simp

end HasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
/-- Reindex a categorical biproduct via an equivalence of the index types. -/
@[simps]
/-
**CategoryTheory.Limits.biproduct.reindex** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.biproduct`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       {β γ : Type} →         [Finite β] →      
     (ε : β ≃ γ) →             (f : γ → C) →               [inst_3 : CategoryThe
ory.Limits.HasBiproduct f] →                 [inst_4 : CategoryTheory.Limits.Has
Biproduct (f ∘ ⇑ε)] → ⨁ f ∘ ⇑ε ≅ ⨁ f
参数：ε : β ≃ γ；f : γ → C；f ∘ ⇑ε。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reindex a categorical biproduct via an equivalence of the index types.
-/
def biproduct.reindex {β γ : Type} [Finite β] (ε : β ≃ γ)
    (f : γ → C) [HasBiproduct f] [HasBiproduct (f ∘ ε)] : ⨁ f ∘ ε ≅ ⨁ f where
  hom := biproduct.desc fun b => biproduct.ι f (ε b)
  inv := biproduct.lift fun b => biproduct.π f (ε b)
  hom_inv_id := by
    ext b b'
    by_cases h : b' = b
    · subst h; simp
    · have : ε b' ≠ ε b := by simp [h]
      simp [biproduct.ι_π_ne _ h, biproduct.ι_π_ne _ this]
  inv_hom_id := by
    classical
    cases nonempty_fintype β
    ext g g'
    by_cases h : g' = g <;>
      simp [Preadditive.sum_comp, biproduct.lift_desc, biproduct.ι_π, comp_dite,
        ← Equiv.eq_symm_apply, h]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- In a preadditive category, we can construct a binary biproduct for `X Y : C` from
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
/-
**CategoryTheory.Limits.isBinaryBilimitOfTotal** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：isBinaryBilimitOfTotal {X Y : C} (b : BinaryBicone X Y) (total : b.fst ≫ b
.inl + b.snd ≫ b.inr = 𝟙 b.pt) : b.IsBilimit where isLimit
参数：b : BinaryBicone X Y；total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a preadditive category, we can construct a binary biproduct for `X Y : C` fro
m
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`
.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
def isBinaryBilimitOfTotal {X Y : C} (b : BinaryBicone X Y)
    (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) : b.IsBilimit where
  isLimit :=
    { lift := fun s =>
      (BinaryFan.fst s ≫ b.inl : s.pt ⟶ b.pt) + (BinaryFan.snd s ≫ b.inr : s.pt ⟶ b.pt)
      uniq := fun s m h => by
        have hₗ := h ⟨.left⟩
        have hᵣ := h ⟨.right⟩
        dsimp at hₗ hᵣ
        simpa [← hₗ, ← hᵣ] using m ≫= total.symm
      fac := fun s j => by rcases j with ⟨⟨⟩⟩ <;> simp }
  isColimit :=
    { desc := fun s =>
        (b.fst ≫ BinaryCofan.inl s : b.pt ⟶ s.pt) + (b.snd ≫ BinaryCofan.inr s : b.pt ⟶ s.pt)
      uniq := fun s m h => by
        have hₗ := h ⟨.left⟩
        have hᵣ := h ⟨.right⟩
        dsimp at hₗ hᵣ
        simpa [← hₗ, ← hᵣ] using total.symm =≫ m
      fac := fun s j => by rcases j with ⟨⟨⟩⟩ <;> simp }
/-
**CategoryTheory.Limits.IsBilimit.binary_total** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.IsBilimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {X Y : C}   {b : CategoryTheory.Limits.BinaryBicone X Y} 
(i : b.IsBilimit),   CategoryTheory.CategoryStruct.comp b.fst b.inl + CategoryTh
eory.CategoryStruct.comp b.snd b.inr =     CategoryTheory.CategoryStruct.id b.pt
参数：i : b.IsBilimit。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem IsBilimit.binary_total {X Y : C} {b : BinaryBicone X Y} (i : b.IsBilimit) :
    b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt :=
  i.isLimit.hom_ext fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

/-- In a preadditive category, we can construct a binary biproduct for `X Y : C` from
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
/-
**CategoryTheory.Limits.hasBinaryBiproduct_of_total** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasBinaryBiproduct_of_total {X Y : C} (b : BinaryBicone X Y) (total : b.fs
t ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) : HasBinaryBiproduct X Y
参数：b : BinaryBicone X Y；total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.mk`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {P Q : C} (d : CategoryTh…

--- 原说明 ---
In a preadditive category, we can construct a binary biproduct for `X Y : C` fro
m
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`
.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
theorem hasBinaryBiproduct_of_total {X Y : C} (b : BinaryBicone X Y)
    (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) : HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := b
      isBilimit := isBinaryBilimitOfTotal b total }

set_option backward.isDefEq.respectTransparency false in
/-- We can turn any limit cone over a pair into a bicone. -/
@[simps]
/-
**CategoryTheory.Limits.BinaryBicone.ofLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       {X Y : C} →         {t : CategoryTheory.L
imits.Cone (CategoryTheory.Limits.pair X Y)} →           CategoryTheory.Limits.I
sLimit t → CategoryTheory.Limits.BinaryBicone X Y
参数：CategoryTheory.Limits.pair X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can turn any limit cone over a pair into a bicone.
-/
def BinaryBicone.ofLimitCone {X Y : C} {t : Cone (pair X Y)} (ht : IsLimit t) :
    BinaryBicone X Y where
  pt := t.pt
  fst := t.π.app ⟨WalkingPair.left⟩
  snd := t.π.app ⟨WalkingPair.right⟩
  inl := BinaryFan.IsLimit.lift ht (𝟙 X) 0
  inr := BinaryFan.IsLimit.lift ht 0 (𝟙 Y)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.inl_of_isLimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：inl_of_isLimit {X Y : C} {t : BinaryBicone X Y} (ht : IsLimit t.toCone) : 
t.inl = BinaryFan.IsLimit.lift ht (𝟙 X) 0
参数：ht : IsLimit t.toCone。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem inl_of_isLimit {X Y : C} {t : BinaryBicone X Y} (ht : IsLimit t.toCone) :
    t.inl = BinaryFan.IsLimit.lift ht (𝟙 X) 0 := by
  apply ht.uniq (BinaryFan.mk (𝟙 X) 0); rintro ⟨⟨⟩⟩ <;> simp

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.inr_of_isLimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：inr_of_isLimit {X Y : C} {t : BinaryBicone X Y} (ht : IsLimit t.toCone) : 
t.inr = BinaryFan.IsLimit.lift ht 0 (𝟙 Y)
参数：ht : IsLimit t.toCone。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem inr_of_isLimit {X Y : C} {t : BinaryBicone X Y} (ht : IsLimit t.toCone) :
    t.inr = BinaryFan.IsLimit.lift ht 0 (𝟙 Y) := by
  apply ht.uniq (BinaryFan.mk 0 (𝟙 Y)); rintro ⟨⟨⟩⟩ <;> simp

/-- In a preadditive category, any binary bicone which is a limit cone is in fact a bilimit
bicone. -/
/-
**CategoryTheory.Limits.isBinaryBilimitOfIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：isBinaryBilimitOfIsLimit {X Y : C} (t : BinaryBicone X Y) (ht : IsLimit t.
toCone) : t.IsBilimit
参数：t : BinaryBicone X Y；ht : IsLimit t.toCone。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a preadditive category, any binary bicone which is a limit cone is in fact a 
bilimit
bicone.
-/
def isBinaryBilimitOfIsLimit {X Y : C} (t : BinaryBicone X Y) (ht : IsLimit t.toCone) :
    t.IsBilimit :=
  isBinaryBilimitOfTotal _ (by refine BinaryFan.IsLimit.hom_ext ht ?_ ?_ <;> simp)

set_option backward.isDefEq.respectTransparency false in
/-- We can turn any limit cone over a pair into a bilimit bicone. -/
/-
**CategoryTheory.Limits.binaryBiconeIsBilimitOfLimitConeOfIsLimit** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：binaryBiconeIsBilimitOfLimitConeOfIsLimit {X Y : C} {t : Cone (pair X Y)} 
(ht : IsLimit t) : (BinaryBicone.ofLimitCone ht).IsBilimit
参数：pair X Y；ht : IsLimit t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can turn any limit cone over a pair into a bilimit bicone.
-/
def binaryBiconeIsBilimitOfLimitConeOfIsLimit {X Y : C} {t : Cone (pair X Y)} (ht : IsLimit t) :
    (BinaryBicone.ofLimitCone ht).IsBilimit :=
  isBinaryBilimitOfTotal _ <| BinaryFan.IsLimit.hom_ext ht (by simp) (by simp)

/-- In a preadditive category, if the product of `X` and `Y` exists, then the
binary biproduct of `X` and `Y` exists. -/
/-
**CategoryTheory.Limits.HasBinaryBiproduct.of_hasBinaryProduct** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits.HasBinaryBiproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] (X Y : C)   [CategoryTheory.Limits.HasBinaryProduct X Y],
 CategoryTheory.Limits.HasBinaryBiproduct X Y
参数：X Y : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.mk`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {P Q : C} (d : CategoryTh…

--- 原说明 ---
In a preadditive category, if the product of `X` and `Y` exists, then the
binary biproduct of `X` and `Y` exists.
-/
theorem HasBinaryBiproduct.of_hasBinaryProduct (X Y : C) [HasBinaryProduct X Y] :
    HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := _
      isBilimit := binaryBiconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }

/-- In a preadditive category, if all binary products exist, then all binary biproducts exist. -/
/-
**CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits.HasBinaryBiproducts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [CategoryTheory.Limits.HasBinaryProducts C], CategoryTh
eory.Limits.HasBinaryBiproducts C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.of_hasBinaryProduct`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preaddit
ive C] (X Y : C)   [CategoryTheory.Limits.HasBinar…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
In a preadditive category, if all binary products exist, then all binary biprodu
cts exist.
-/
theorem HasBinaryBiproducts.of_hasBinaryProducts [HasBinaryProducts C] : HasBinaryBiproducts C :=
  { has_binary_biproduct := fun X Y => HasBinaryBiproduct.of_hasBinaryProduct X Y }

set_option backward.isDefEq.respectTransparency false in
/-- We can turn any colimit cocone over a pair into a bicone. -/
@[simps]
/-
**CategoryTheory.Limits.BinaryBicone.ofColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       {X Y : C} →         {t : CategoryTheory.L
imits.Cocone (CategoryTheory.Limits.pair X Y)} →           CategoryTheory.Limits
.IsColimit t → CategoryTheory.Limits.BinaryBicone X Y
参数：CategoryTheory.Limits.pair X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can turn any colimit cocone over a pair into a bicone.
-/
def BinaryBicone.ofColimitCocone {X Y : C} {t : Cocone (pair X Y)} (ht : IsColimit t) :
    BinaryBicone X Y where
  pt := t.pt
  fst := BinaryCofan.IsColimit.desc ht (𝟙 X) 0
  snd := BinaryCofan.IsColimit.desc ht 0 (𝟙 Y)
  inl := t.ι.app ⟨WalkingPair.left⟩
  inr := t.ι.app ⟨WalkingPair.right⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.fst_of_isColimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：fst_of_isColimit {X Y : C} {t : BinaryBicone X Y} (ht : IsColimit t.toCoco
ne) : t.fst = BinaryCofan.IsColimit.desc ht (𝟙 X) 0
参数：ht : IsColimit t.toCocone。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.uniq`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem fst_of_isColimit {X Y : C} {t : BinaryBicone X Y} (ht : IsColimit t.toCocone) :
    t.fst = BinaryCofan.IsColimit.desc ht (𝟙 X) 0 := by
  apply ht.uniq (BinaryCofan.mk (𝟙 X) 0)
  rintro ⟨⟨⟩⟩ <;> simp

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.snd_of_isColimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：snd_of_isColimit {X Y : C} {t : BinaryBicone X Y} (ht : IsColimit t.toCoco
ne) : t.snd = BinaryCofan.IsColimit.desc ht 0 (𝟙 Y)
参数：ht : IsColimit t.toCocone。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.uniq`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem snd_of_isColimit {X Y : C} {t : BinaryBicone X Y} (ht : IsColimit t.toCocone) :
    t.snd = BinaryCofan.IsColimit.desc ht 0 (𝟙 Y) := by
  apply ht.uniq (BinaryCofan.mk 0 (𝟙 Y))
  rintro ⟨⟨⟩⟩ <;> simp

set_option backward.defeqAttrib.useBackward true in
/-- In a preadditive category, any binary bicone which is a colimit cocone is in fact a
bilimit bicone. -/
/-
**CategoryTheory.Limits.isBinaryBilimitOfIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：isBinaryBilimitOfIsColimit {X Y : C} (t : BinaryBicone X Y) (ht : IsColimi
t t.toCocone) : t.IsBilimit
参数：t : BinaryBicone X Y；ht : IsColimit t.toCocone。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a preadditive category, any binary bicone which is a colimit cocone is in fac
t a
bilimit bicone.
-/
def isBinaryBilimitOfIsColimit {X Y : C} (t : BinaryBicone X Y) (ht : IsColimit t.toCocone) :
    t.IsBilimit :=
  isBinaryBilimitOfTotal _ <| by
    refine BinaryCofan.IsColimit.hom_ext ht ?_ ?_ <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- We can turn any colimit cocone over a pair into a bilimit bicone. -/
/-
**CategoryTheory.Limits.binaryBiconeIsBilimitOfColimitCoconeOfIsColimit** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：binaryBiconeIsBilimitOfColimitCoconeOfIsColimit {X Y : C} {t : Cocone (pai
r X Y)} (ht : IsColimit t) : (BinaryBicone.ofColimitCocone ht).IsBilimit
参数：pair X Y；ht : IsColimit t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can turn any colimit cocone over a pair into a bilimit bicone.
-/
def binaryBiconeIsBilimitOfColimitCoconeOfIsColimit {X Y : C} {t : Cocone (pair X Y)}
    (ht : IsColimit t) : (BinaryBicone.ofColimitCocone ht).IsBilimit :=
  isBinaryBilimitOfIsColimit (BinaryBicone.ofColimitCocone ht) <|
    IsColimit.ofIsoColimit ht <|
      Cocone.ext (Iso.refl _) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp

/-- In a preadditive category, if the coproduct of `X` and `Y` exists, then the
binary biproduct of `X` and `Y` exists. -/
/-
**CategoryTheory.Limits.HasBinaryBiproduct.of_hasBinaryCoproduct** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits.HasBinaryBiproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] (X Y : C)   [CategoryTheory.Limits.HasBinaryCoproduct X Y
], CategoryTheory.Limits.HasBinaryBiproduct X Y
参数：X Y : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.mk`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {P Q : C} (d : CategoryTh…

--- 原说明 ---
In a preadditive category, if the coproduct of `X` and `Y` exists, then the
binary biproduct of `X` and `Y` exists.
-/
theorem HasBinaryBiproduct.of_hasBinaryCoproduct (X Y : C) [HasBinaryCoproduct X Y] :
    HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := _
      isBilimit := binaryBiconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }

/-- In a preadditive category, if all binary coproducts exist, then all binary biproducts exist. -/
/-
**CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryCoproducts** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Limits.HasBinaryBiproducts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [CategoryTheory.Limits.HasBinaryCoproducts C], Category
Theory.Limits.HasBinaryBiproducts C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.of_hasBinaryCoproduct`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadd
itive C] (X Y : C)   [CategoryTheory.Limits.HasBinar…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
In a preadditive category, if all binary coproducts exist, then all binary bipro
ducts exist.
-/
theorem HasBinaryBiproducts.of_hasBinaryCoproducts [HasBinaryCoproducts C] :
    HasBinaryBiproducts C :=
  { has_binary_biproduct := fun X Y => HasBinaryBiproduct.of_hasBinaryCoproduct X Y }

section

variable {X Y : C} [HasBinaryBiproduct X Y]

/-- In any preadditive category, any binary biproduct satisfies
`biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y)`.
-/
@[simp]
/-
**CategoryTheory.Limits.biprod.total** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {X Y : C}   [inst_2 : CategoryTheory.Limits.HasBinaryBipr
oduct X Y],   CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.fs
t CategoryTheory.Limits.biprod.inl +       CategoryTheory.CategoryStruct.comp Ca
tegoryTheory.Limits.biprod.snd CategoryTheory.Limits.biprod.inr =     CategoryTh
eory.CategoryStruct.id (X ⊞ Y)
参数：X ⊞ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…

--- 原说明 ---
In any preadditive category, any binary biproduct satisfies
`biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y)`.
-/
theorem biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) := by
  ext <;> simp
/-
**CategoryTheory.Limits.biprod.lift_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {X Y : C}   [inst_2 : CategoryTheory.Limits.HasBinaryBipr
oduct X Y] {T : C} {f : T ⟶ X} {g : T ⟶ Y},   CategoryTheory.Limits.biprod.lift 
f g =     CategoryTheory.CategoryStruct.comp f CategoryTheory.Limits.biprod.inl 
+       CategoryTheory.CategoryStruct.comp g CategoryTheory.Limits.biprod.inr
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem biprod.lift_eq {T : C} {f : T ⟶ X} {g : T ⟶ Y} :
    biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr := by ext <;> simp [add_comp]
/-
**CategoryTheory.Limits.biprod.desc_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {X Y : C}   [inst_2 : CategoryTheory.Limits.HasBinaryBipr
oduct X Y] {T : C} {f : X ⟶ T} {g : Y ⟶ T},   CategoryTheory.Limits.biprod.desc 
f g =     CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.fst f 
+       CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.snd g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem biprod.desc_eq {T : C} {f : X ⟶ T} {g : Y ⟶ T} :
    biprod.desc f g = biprod.fst ≫ f + biprod.snd ≫ g := by ext <;> simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biprod.lift_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {X Y : C}   [inst_2 : CategoryTheory.Limits.HasBinaryBipr
oduct X Y] {T U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U},   Category
Theory.CategoryStruct.comp (CategoryTheory.Limits.biprod.lift f g) (CategoryTheo
ry.Limits.biprod.desc h i) =     CategoryTheory.CategoryStruct.comp f h + Catego
ryTheory.CategoryStruct.comp g i
参数：CategoryTheory.Limits.biprod.lift f g；CategoryTheory.Limits.biprod.desc h i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biprod.lift_eq`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [inst
_2 : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.biprod.desc_eq`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [inst
_2 : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biprod.lift_desc {T U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U} :
    biprod.lift f g ≫ biprod.desc h i = f ≫ h + g ≫ i := by simp [biprod.lift_eq, biprod.desc_eq]
/-
**CategoryTheory.Limits.biprod.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasBinaryBiproducts C] 
{W X Y Z : C} {f : W ⟶ Y} {g : X ⟶ Z},   CategoryTheory.Limits.biprod.map f g = 
    CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.fst         
(CategoryTheory.CategoryStruct.comp f CategoryTheory.Limits.biprod.inl) +       
CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.snd         (Cat
egoryTheory.CategoryStruct.comp g CategoryTheory.Limits.biprod.inr)
参数：CategoryTheory.CategoryStruct.comp f CategoryTheory.Limits.biprod.inl；Categor
yTheory.CategoryStruct.comp g CategoryTheory.Limits.biprod.inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.inl_map`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.biprod.inr_map`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {W X Y Z : C} [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
-/
theorem biprod.map_eq [HasBinaryBiproducts C] {W X Y Z : C} {f : W ⟶ Y} {g : X ⟶ Z} :
    biprod.map f g = biprod.fst ≫ f ≫ biprod.inl + biprod.snd ≫ g ≫ biprod.inr := by
  ext <;> simp

section

variable {Z : C}

/-
**CategoryTheory.Limits.biprod.decomp_hom_to** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {X Y : C}   [inst_2 : CategoryTheory.Limits.HasBinaryBipr
oduct X Y] {Z : C} (f : Z ⟶ X ⊞ Y),   ∃ f₁ f₂,     f =       CategoryTheory.Cate
goryStruct.comp f₁ CategoryTheory.Limits.biprod.inl +         CategoryTheory.Cat
egoryStruct.comp f₂ CategoryTheory.Limits.biprod.inr
参数：f : Z ⟶ X ⊞ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma biprod.decomp_hom_to (f : Z ⟶ X ⊞ Y) :
    ∃ f₁ f₂, f = f₁ ≫ biprod.inl + f₂ ≫ biprod.inr :=
  ⟨f ≫ biprod.fst, f ≫ biprod.snd, by aesop⟩
/-
**CategoryTheory.Limits.biprod.ext_to_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {X Y : C}   [inst_2 : CategoryTheory.Limits.HasBinaryBipr
oduct X Y] {Z : C} {f g : Z ⟶ X ⊞ Y},   f = g ↔     CategoryTheory.CategoryStruc
t.comp f CategoryTheory.Limits.biprod.fst =         CategoryTheory.CategoryStruc
t.comp g CategoryTheory.Limits.biprod.fst ∧       CategoryTheory.CategoryStruct.
comp f CategoryTheory.Limits.biprod.snd =         CategoryTheory.CategoryStruct.
comp g CategoryTheory.Limits.biprod.snd
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma biprod.ext_to_iff {f g : Z ⟶ X ⊞ Y} :
    f = g ↔ f ≫ biprod.fst = g ≫ biprod.fst ∧ f ≫ biprod.snd = g ≫ biprod.snd := by
  aesop
/-
**CategoryTheory.Limits.biprod.decomp_hom_from** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {X Y : C}   [inst_2 : CategoryTheory.Limits.HasBinaryBipr
oduct X Y] {Z : C} (f : X ⊞ Y ⟶ Z),   ∃ f₁ f₂,     f =       CategoryTheory.Cate
goryStruct.comp CategoryTheory.Limits.biprod.fst f₁ +         CategoryTheory.Cat
egoryStruct.comp CategoryTheory.Limits.biprod.snd f₂
参数：f : X ⊞ Y ⟶ Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma biprod.decomp_hom_from (f : X ⊞ Y ⟶ Z) :
    ∃ f₁ f₂, f = biprod.fst ≫ f₁ + biprod.snd ≫ f₂ :=
  ⟨biprod.inl ≫ f, biprod.inr ≫ f, by aesop⟩
/-
**CategoryTheory.Limits.biprod.ext_from_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {X Y : C}   [inst_2 : CategoryTheory.Limits.HasBinaryBipr
oduct X Y] {Z : C} {f g : X ⊞ Y ⟶ Z},   f = g ↔     CategoryTheory.CategoryStruc
t.comp CategoryTheory.Limits.biprod.inl f =         CategoryTheory.CategoryStruc
t.comp CategoryTheory.Limits.biprod.inl g ∧       CategoryTheory.CategoryStruct.
comp CategoryTheory.Limits.biprod.inr f =         CategoryTheory.CategoryStruct.
comp CategoryTheory.Limits.biprod.inr g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma biprod.ext_from_iff {f g : X ⊞ Y ⟶ Z} :
    f = g ↔ biprod.inl ≫ f = biprod.inl ≫ g ∧ biprod.inr ≫ f = biprod.inr ≫ g := by
  aesop

end

set_option backward.isDefEq.respectTransparency false in
/-- Every split mono `f` with a cokernel induces a binary bicone with `f` as its `inl` and
the cokernel map as its `snd`.
We will show in `isBilimitBinaryBiconeOfIsSplitMonoOfCokernel` that this binary bicone is in
fact already a biproduct. -/
@[simps]
/-
**CategoryTheory.Limits.binaryBiconeOfIsSplitMonoOfCokernel** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：binaryBiconeOfIsSplitMonoOfCokernel {X Y : C} {f : X ⟶ Y} [IsSplitMono f] 
{c : CokernelCofork f} (i : IsColimit c) : BinaryBicone X c.pt where pt
参数：i : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every split mono `f` with a cokernel induces a binary bicone with `f` as its `in
l` and
the cokernel map as its `snd`.
We will show in `isBilimitBinaryBiconeOfIsSplitMonoOfCokernel` that this binary 
bicone is in
fact already a biproduct.
-/
def binaryBiconeOfIsSplitMonoOfCokernel {X Y : C} {f : X ⟶ Y} [IsSplitMono f] {c : CokernelCofork f}
    (i : IsColimit c) : BinaryBicone X c.pt where
  pt := Y
  fst := retraction f
  snd := c.π
  inl := f
  inr :=
    let c' : CokernelCofork (𝟙 Y - (𝟙 Y - retraction f ≫ f)) :=
      CokernelCofork.ofπ (Cofork.π c) (by simp)
    let i' : IsColimit c' := isCokernelEpiComp i (retraction f) (by simp)
    let i'' := isColimitCoforkOfCokernelCofork i'
    (splitEpiOfIdempotentOfIsColimitCofork C (by simp) i'').section_
  inl_fst := by simp
  inl_snd := by simp
  inr_fst := by
    dsimp only
    rw [splitEpiOfIdempotentOfIsColimitCofork_section_,
      isColimitCoforkOfCokernelCofork_desc, isCokernelEpiComp_desc]
    dsimp only [cokernelCoforkOfCofork_ofπ]
    let := epi_of_isColimit_cofork i
    apply zero_of_epi_comp c.π
    simp only [sub_comp, comp_sub, Category.comp_id, Category.assoc, IsSplitMono.id, sub_self,
      Cofork.IsColimit.π_desc_assoc, CokernelCofork.π_ofπ, IsSplitMono.id_assoc]
    apply sub_eq_zero_of_eq
    apply Category.id_comp
  inr_snd := by apply SplitEpi.id

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bicone constructed in `binaryBiconeOfSplitMonoOfCokernel` is a bilimit.
This is a version of the splitting lemma that holds in all preadditive categories. -/
/-
**CategoryTheory.Limits.isBilimitBinaryBiconeOfIsSplitMonoOfCokernel** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isBilimitBinaryBiconeOfIsSplitMonoOfCokernel {X Y : C} {f : X ⟶ Y} [IsSpli
tMono f] {c : CokernelCofork f} (i : IsColimit c) : (binaryBiconeOfIsSplitMonoOf
Cokernel i).IsBilimit
参数：i : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bicone constructed in `binaryBiconeOfSplitMonoOfCokernel` is a bilimit.
This is a version of the splitting lemma that holds in all preadditive categorie
s.
-/
def isBilimitBinaryBiconeOfIsSplitMonoOfCokernel {X Y : C} {f : X ⟶ Y} [IsSplitMono f]
    {c : CokernelCofork f} (i : IsColimit c) : (binaryBiconeOfIsSplitMonoOfCokernel i).IsBilimit :=
  isBinaryBilimitOfTotal _
    (by
      simp only [binaryBiconeOfIsSplitMonoOfCokernel_fst,
        binaryBiconeOfIsSplitMonoOfCokernel_inr,
        binaryBiconeOfIsSplitMonoOfCokernel_snd,
        splitEpiOfIdempotentOfIsColimitCofork_section_]
      dsimp only [binaryBiconeOfIsSplitMonoOfCokernel_pt]
      rw [isColimitCoforkOfCokernelCofork_desc, isCokernelEpiComp_desc]
      simp only [binaryBiconeOfIsSplitMonoOfCokernel_inl, Cofork.IsColimit.π_desc,
        cokernelCoforkOfCofork_π, Cofork.π_ofπ, add_sub_cancel])

set_option backward.isDefEq.respectTransparency false in
/-- If `b` is a binary bicone such that `b.inl` is a kernel of `b.snd`, then `b` is a bilimit
bicone. -/
/-
**CategoryTheory.Limits.BinaryBicone.isBilimitOfKernelInl** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       {X Y : C} →         (b : CategoryTheory.L
imits.BinaryBicone X Y) → CategoryTheory.Limits.IsLimit b.sndKernelFork → b.IsBi
limit
参数：b : CategoryTheory.Limits.BinaryBicone X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `b` is a binary bicone such that `b.inl` is a kernel of `b.snd`, then `b` is 
a bilimit
bicone.
-/
def BinaryBicone.isBilimitOfKernelInl {X Y : C} (b : BinaryBicone X Y)
    (hb : IsLimit b.sndKernelFork) : b.IsBilimit :=
  isBinaryBilimitOfIsLimit _ <|
    BinaryFan.IsLimit.mk _ (fun f g => f ≫ b.inl + g ≫ b.inr) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : ((m : T ⟶ b.pt) - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by
        simpa using sub_eq_zero.2 h₁
      have h₂' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.snd = 0 := by simpa using sub_eq_zero.2 h₂
      obtain ⟨q : T ⟶ X, hq : q ≫ b.inl = m - (f ≫ b.inl + g ≫ b.inr)⟩ :=
        KernelFork.IsLimit.lift' hb _ h₂'
      rw [← sub_eq_zero, ← hq, ← Category.comp_id q, ← b.inl_fst, ← Category.assoc, hq, h₁',
        zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- If `b` is a binary bicone such that `b.inr` is a kernel of `b.fst`, then `b` is a bilimit
bicone. -/
/-
**CategoryTheory.Limits.BinaryBicone.isBilimitOfKernelInr** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       {X Y : C} →         (b : CategoryTheory.L
imits.BinaryBicone X Y) → CategoryTheory.Limits.IsLimit b.fstKernelFork → b.IsBi
limit
参数：b : CategoryTheory.Limits.BinaryBicone X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `b` is a binary bicone such that `b.inr` is a kernel of `b.fst`, then `b` is 
a bilimit
bicone.
-/
def BinaryBicone.isBilimitOfKernelInr {X Y : C} (b : BinaryBicone X Y)
    (hb : IsLimit b.fstKernelFork) : b.IsBilimit :=
  isBinaryBilimitOfIsLimit _ <|
    BinaryFan.IsLimit.mk _ (fun f g => f ≫ b.inl + g ≫ b.inr) (fun f g => by simp)
    (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.snd = 0 := by simpa using sub_eq_zero.2 h₂
      obtain ⟨q : T ⟶ Y, hq : q ≫ b.inr = m - (f ≫ b.inl + g ≫ b.inr)⟩ :=
        KernelFork.IsLimit.lift' hb _ h₁'
      rw [← sub_eq_zero, ← hq, ← Category.comp_id q, ← b.inr_snd, ← Category.assoc, hq, h₂',
        zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- If `b` is a binary bicone such that `b.fst` is a cokernel of `b.inr`, then `b` is a bilimit
bicone. -/
/-
**CategoryTheory.Limits.BinaryBicone.isBilimitOfCokernelFst** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       {X Y : C} →         (b : CategoryTheory.L
imits.BinaryBicone X Y) → CategoryTheory.Limits.IsColimit b.inrCokernelCofork → 
b.IsBilimit
参数：b : CategoryTheory.Limits.BinaryBicone X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `b` is a binary bicone such that `b.fst` is a cokernel of `b.inr`, then `b` i
s a bilimit
bicone.
-/
def BinaryBicone.isBilimitOfCokernelFst {X Y : C} (b : BinaryBicone X Y)
    (hb : IsColimit b.inrCokernelCofork) : b.IsBilimit :=
  isBinaryBilimitOfIsColimit _ <|
    BinaryCofan.IsColimit.mk _ (fun f g => b.fst ≫ f + b.snd ≫ g) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : b.inr ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₂
      obtain ⟨q : X ⟶ T, hq : b.fst ≫ q = m - (b.fst ≫ f + b.snd ≫ g)⟩ :=
        CokernelCofork.IsColimit.desc' hb _ h₂'
      rw [← sub_eq_zero, ← hq, ← Category.id_comp q, ← b.inl_fst, Category.assoc, hq, h₁',
        comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- If `b` is a binary bicone such that `b.snd` is a cokernel of `b.inl`, then `b` is a bilimit
bicone. -/
/-
**CategoryTheory.Limits.BinaryBicone.isBilimitOfCokernelSnd** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.BinaryBicone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       {X Y : C} →         (b : CategoryTheory.L
imits.BinaryBicone X Y) → CategoryTheory.Limits.IsColimit b.inlCokernelCofork → 
b.IsBilimit
参数：b : CategoryTheory.Limits.BinaryBicone X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `b` is a binary bicone such that `b.snd` is a cokernel of `b.inl`, then `b` i
s a bilimit
bicone.
-/
def BinaryBicone.isBilimitOfCokernelSnd {X Y : C} (b : BinaryBicone X Y)
    (hb : IsColimit b.inlCokernelCofork) : b.IsBilimit :=
  isBinaryBilimitOfIsColimit _ <|
    BinaryCofan.IsColimit.mk _ (fun f g => b.fst ≫ f + b.snd ≫ g) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : b.inr ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₂
      obtain ⟨q : Y ⟶ T, hq : b.snd ≫ q = m - (b.fst ≫ f + b.snd ≫ g)⟩ :=
        CokernelCofork.IsColimit.desc' hb _ h₁'
      rw [← sub_eq_zero, ← hq, ← Category.id_comp q, ← b.inr_snd, Category.assoc, hq, h₂',
        comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Every split epi `f` with a kernel induces a binary bicone with `f` as its `snd` and
the kernel map as its `inl`.
We will show in `isBilimitBinaryBiconeOfIsSplitEpiOfKernel` that this binary bicone is in fact
already a biproduct. -/
@[simps]
/-
**CategoryTheory.Limits.binaryBiconeOfIsSplitEpiOfKernel** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：binaryBiconeOfIsSplitEpiOfKernel {X Y : C} {f : X ⟶ Y} [IsSplitEpi f] {c :
 KernelFork f} (i : IsLimit c) : BinaryBicone c.pt Y
参数：i : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every split epi `f` with a kernel induces a binary bicone with `f` as its `snd` 
and
the kernel map as its `inl`.
We will show in `isBilimitBinaryBiconeOfIsSplitEpiOfKernel` that this binary bic
one is in fact
already a biproduct.
-/
def binaryBiconeOfIsSplitEpiOfKernel {X Y : C} {f : X ⟶ Y} [IsSplitEpi f] {c : KernelFork f}
    (i : IsLimit c) : BinaryBicone c.pt Y :=
  { pt := X
    fst :=
      let c' : KernelFork (𝟙 X - (𝟙 X - f ≫ section_ f)) := KernelFork.ofι (Fork.ι c) (by simp)
      let i' : IsLimit c' := isKernelCompMono i (section_ f) (by simp)
      let i'' := isLimitForkOfKernelFork i'
      (splitMonoOfIdempotentOfIsLimitFork C (by simp) i'').retraction
    snd := f
    inl := c.ι
    inr := section_ f
    inl_fst := by apply SplitMono.id
    inl_snd := by simp
    inr_fst := by
      dsimp only
      rw [splitMonoOfIdempotentOfIsLimitFork_retraction, isLimitForkOfKernelFork_lift,
        isKernelCompMono_lift]
      dsimp only [kernelForkOfFork_ι]
      let := mono_of_isLimit_fork i
      apply zero_of_comp_mono c.ι
      simp only [comp_sub, Category.comp_id, Category.assoc, sub_self, Fork.IsLimit.lift_ι,
        Fork.ι_ofι, IsSplitEpi.id_assoc]
    inr_snd := by simp }

set_option backward.isDefEq.respectTransparency false in
/-- The bicone constructed in `binaryBiconeOfIsSplitEpiOfKernel` is a bilimit.
This is a version of the splitting lemma that holds in all preadditive categories. -/
/-
**CategoryTheory.Limits.isBilimitBinaryBiconeOfIsSplitEpiOfKernel** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isBilimitBinaryBiconeOfIsSplitEpiOfKernel {X Y : C} {f : X ⟶ Y} [IsSplitEp
i f] {c : KernelFork f} (i : IsLimit c) : (binaryBiconeOfIsSplitEpiOfKernel i).I
sBilimit
参数：i : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bicone constructed in `binaryBiconeOfIsSplitEpiOfKernel` is a bilimit.
This is a version of the splitting lemma that holds in all preadditive categorie
s.
-/
def isBilimitBinaryBiconeOfIsSplitEpiOfKernel {X Y : C} {f : X ⟶ Y} [IsSplitEpi f]
    {c : KernelFork f} (i : IsLimit c) : (binaryBiconeOfIsSplitEpiOfKernel i).IsBilimit :=
  BinaryBicone.isBilimitOfKernelInl _ <| i.ofIsoLimit <| Fork.ext (Iso.refl _) (by simp)

end

section

variable {X Y : C} (f g : X ⟶ Y)

/-- The existence of binary biproducts implies that there is at most one preadditive structure. -/
/-
**CategoryTheory.Limits.biprod.add_eq_lift_id_desc** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {X Y : C} (f g : X ⟶ Y)   [inst_2 : CategoryTheory.Limits
.HasBinaryBiproduct X X],   f + g =     CategoryTheory.CategoryStruct.comp      
 (CategoryTheory.Limits.biprod.lift (CategoryTheory.CategoryStruct.id X) (Catego
ryTheory.CategoryStruct.id X))       (CategoryTheory.Limits.biprod.desc f g)
参数：f g : X ⟶ Y；CategoryTheory.Limits.biprod.lift (CategoryTheory.CategoryStruct.
id X) (CategoryTheory.CategoryStruct.id X)；CategoryTheory.Limits.biprod.desc f g
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.lift_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [in
st_2 : CategoryTheory.Limits…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The existence of binary biproducts implies that there is at most one preadditive
 structure.
-/
theorem biprod.add_eq_lift_id_desc [HasBinaryBiproduct X X] :
    f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g := by simp

/-- The existence of binary biproducts implies that there is at most one preadditive structure. -/
/-
**CategoryTheory.Limits.biprod.add_eq_lift_desc_id** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {X Y : C} (f g : X ⟶ Y)   [inst_2 : CategoryTheory.Limits
.HasBinaryBiproduct Y Y],   f + g =     CategoryTheory.CategoryStruct.comp (Cate
goryTheory.Limits.biprod.lift f g)       (CategoryTheory.Limits.biprod.desc (Cat
egoryTheory.CategoryStruct.id Y) (CategoryTheory.CategoryStruct.id Y))
参数：f g : X ⟶ Y；CategoryTheory.Limits.biprod.lift f g；CategoryTheory.Limits.bipro
d.desc (CategoryTheory.CategoryStruct.id Y) (CategoryTheory.CategoryStruct.id Y)
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.lift_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [in
st_2 : CategoryTheory.Limits…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The existence of binary biproducts implies that there is at most one preadditive
 structure.
-/
theorem biprod.add_eq_lift_desc_id [HasBinaryBiproduct Y Y] :
    f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y) := by simp

end

end Limits

open CategoryTheory.Limits

section

attribute [local ext] Preadditive

/-- The existence of binary biproducts implies that there is at most one preadditive structure. -/
/-
**CategoryTheory.subsingleton_preadditive_of_hasBinaryBiproducts** 是 Mathlib 中的一
个实例，位于命名空间 `CategoryTheory`。
形式化陈述：subsingleton_preadditive_of_hasBinaryBiproducts {C : Type u} [Category.{v}
 C] [HasZeroMorphisms C] [HasBinaryBiproducts C] : Subsingleton (Preadditive C) 
where allEq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.ext`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {x y : CategoryTheory.Preadditive C},   CategoryTheory.Preaddit
ive.homGroup = Categ…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddCommGroup.ext`：∀ {G : Type u_1} ⦃g₁ g₂ : AddCommGroup G⦄, HAdd.hAdd =
 HAdd.hAdd → g₁ = g₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.instSubsingleton`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C], Subsingleton (CategoryTheory.Limits.H
asZeroMorphisms C)
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.biprod.add_eq_lift_id_desc`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y 
: C} (f g : X ⟶ Y)   [inst_2 : Categor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
The existence of binary biproducts implies that there is at most one preadditive
 structure.
-/
instance subsingleton_preadditive_of_hasBinaryBiproducts {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasBinaryBiproducts C] : Subsingleton (Preadditive C) where
  allEq := fun a b => by
    apply Preadditive.ext; funext X Y; apply AddCommGroup.ext; funext f g
    have h₁ := @biprod.add_eq_lift_id_desc _ _ a _ _ f g
      (by convert! (inferInstance : HasBinaryBiproduct X X); subsingleton)
    have h₂ := @biprod.add_eq_lift_id_desc _ _ b _ _ f g
      (by convert! (inferInstance : HasBinaryBiproduct X X); subsingleton)
    refine h₁.trans (Eq.trans ?_ h₂.symm)
    congr! 2 <;> subsingleton

end

section

variable [HasBinaryBiproducts.{v} C]
variable {X₁ X₂ Y₁ Y₂ : C}
variable (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)

/-- The "matrix" morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` with specified components.
-/
/-
**CategoryTheory.Biprod.ofComponents** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.B
iprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.HasBinary
Biproducts C] →         {X₁ X₂ Y₁ Y₂ : C} → (X₁ ⟶ Y₁) → (X₁ ⟶ Y₂) → (X₂ ⟶ Y₁) → 
(X₂ ⟶ Y₂) → (X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂)
参数：X₁ ⟶ Y₁；X₁ ⟶ Y₂；X₂ ⟶ Y₁；X₂ ⟶ Y₂；X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "matrix" morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` with specified components.
-/
def Biprod.ofComponents : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂ :=
  biprod.fst ≫ f₁₁ ≫ biprod.inl + biprod.fst ≫ f₁₂ ≫ biprod.inr + biprod.snd ≫ f₂₁ ≫ biprod.inl +
    biprod.snd ≫ f₂₂ ≫ biprod.inr

@[simp]
/-
**CategoryTheory.Biprod.inl_ofComponents** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasBinaryBiproducts C] 
{X₁ X₂ Y₁ Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂)   (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ 
Y₂),   CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.inl      
 (CategoryTheory.Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂) =     CategoryTheory.Categ
oryStruct.comp f₁₁ CategoryTheory.Limits.biprod.inl +       CategoryTheory.Categ
oryStruct.comp f₁₂ CategoryTheory.Limits.biprod.inr
参数：f₁₁ : X₁ ⟶ Y₁；f₁₂ : X₁ ⟶ Y₂；f₂₁ : X₂ ⟶ Y₁；f₂₂ : X₂ ⟶ Y₂；CategoryTheory.Biprod
.ofComponents f₁₁ f₁₂ f₂₁ f₂₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Biprod.inl_ofComponents :
    biprod.inl ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ = f₁₁ ≫ biprod.inl + f₁₂ ≫ biprod.inr := by
  simp [Biprod.ofComponents]

@[simp]
/-
**CategoryTheory.Biprod.inr_ofComponents** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasBinaryBiproducts C] 
{X₁ X₂ Y₁ Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂)   (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ 
Y₂),   CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.inr      
 (CategoryTheory.Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂) =     CategoryTheory.Categ
oryStruct.comp f₂₁ CategoryTheory.Limits.biprod.inl +       CategoryTheory.Categ
oryStruct.comp f₂₂ CategoryTheory.Limits.biprod.inr
参数：f₁₁ : X₁ ⟶ Y₁；f₁₂ : X₁ ⟶ Y₂；f₂₁ : X₂ ⟶ Y₁；f₂₂ : X₂ ⟶ Y₂；CategoryTheory.Biprod
.ofComponents f₁₁ f₁₂ f₂₁ f₂₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Biprod.inr_ofComponents :
    biprod.inr ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ = f₂₁ ≫ biprod.inl + f₂₂ ≫ biprod.inr := by
  simp [Biprod.ofComponents]

@[simp]
/-
**CategoryTheory.Biprod.ofComponents_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasBinaryBiproducts C] 
{X₁ X₂ Y₁ Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂)   (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ 
Y₂),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Biprod.ofComponents f₁
₁ f₁₂ f₂₁ f₂₂)       CategoryTheory.Limits.biprod.fst =     CategoryTheory.Categ
oryStruct.comp CategoryTheory.Limits.biprod.fst f₁₁ +       CategoryTheory.Categ
oryStruct.comp CategoryTheory.Limits.biprod.snd f₂₁
参数：f₁₁ : X₁ ⟶ Y₁；f₁₂ : X₁ ⟶ Y₂；f₂₁ : X₂ ⟶ Y₁；f₂₂ : X₂ ⟶ Y₂；CategoryTheory.Biprod
.ofComponents f₁₁ f₁₂ f₂₁ f₂₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Biprod.ofComponents_fst :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.fst = biprod.fst ≫ f₁₁ + biprod.snd ≫ f₂₁ := by
  simp [Biprod.ofComponents]

@[simp]
/-
**CategoryTheory.Biprod.ofComponents_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasBinaryBiproducts C] 
{X₁ X₂ Y₁ Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂)   (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ 
Y₂),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Biprod.ofComponents f₁
₁ f₁₂ f₂₁ f₂₂)       CategoryTheory.Limits.biprod.snd =     CategoryTheory.Categ
oryStruct.comp CategoryTheory.Limits.biprod.fst f₁₂ +       CategoryTheory.Categ
oryStruct.comp CategoryTheory.Limits.biprod.snd f₂₂
参数：f₁₁ : X₁ ⟶ Y₁；f₁₂ : X₁ ⟶ Y₂；f₂₁ : X₂ ⟶ Y₁；f₂₂ : X₂ ⟶ Y₂；CategoryTheory.Biprod
.ofComponents f₁₁ f₁₂ f₂₁ f₂₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Biprod.ofComponents_snd :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.snd = biprod.fst ≫ f₁₂ + biprod.snd ≫ f₂₂ := by
  simp [Biprod.ofComponents]

@[simp]
/-
**CategoryTheory.Biprod.ofComponents_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasBinaryBiproducts C] 
{X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂),   CategoryTheory.Biprod.ofComponents 
      (CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.inl      
   (CategoryTheory.CategoryStruct.comp f CategoryTheory.Limits.biprod.fst))     
  (CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.inl         (
CategoryTheory.CategoryStruct.comp f CategoryTheory.Limits.biprod.snd))       (C
ategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.inr         (Cate
goryTheory.CategoryStruct.comp f CategoryTheory.Limits.biprod.fst))       (Categ
oryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.inr         (Category
Theory.CategoryStruct.comp f CategoryTheory.Limits.biprod.snd)) =     f
参数：f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂；CategoryTheory.CategoryStruct.comp CategoryTheory.Limit
s.biprod.inl         (CategoryTheory.CategoryStruct.comp f CategoryTheory.Limits
.biprod.fst)；CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.inl
         (CategoryTheory.CategoryStruct.comp f CategoryTheory.Limits.biprod.snd)
；CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.inr         (Ca
tegoryTheory.CategoryStruct.comp f CategoryTheory.Limits.biprod.fst)；CategoryThe
ory.CategoryStruct.comp CategoryTheory.Limits.biprod.inr         (CategoryTheory
.CategoryStruct.comp f CategoryTheory.Limits.biprod.snd)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Biprod.inl_ofComponents`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2 : Cat
egoryTheory.Limits.HasBinary…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Limits.biprod.inl_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.biprod.inr_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.inl_snd`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.biprod.inr_snd`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Biprod.inr_ofComponents`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2 : Cat
egoryTheory.Limits.HasBinary…
-/
theorem Biprod.ofComponents_eq (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) :
    Biprod.ofComponents (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd)
        (biprod.inr ≫ f ≫ biprod.fst) (biprod.inr ≫ f ≫ biprod.snd) =
      f := by
  ext <;>
    simp only [Category.comp_id, biprod.inr_fst, biprod.inr_snd, biprod.inl_snd, add_zero, zero_add,
      Biprod.inl_ofComponents, Biprod.inr_ofComponents, Category.assoc,
      comp_zero, biprod.inl_fst, Preadditive.add_comp]

@[simp]
/-
**CategoryTheory.Biprod.ofComponents_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasBinaryBiproducts C] 
{X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂)   (f₂₁ : X₂ ⟶ Y₁) (f₂₂ :
 X₂ ⟶ Y₂) (g₁₁ : Y₁ ⟶ Z₁) (g₁₂ : Y₁ ⟶ Z₂) (g₂₁ : Y₂ ⟶ Z₁) (g₂₂ : Y₂ ⟶ Z₂),   Cat
egoryTheory.CategoryStruct.comp (CategoryTheory.Biprod.ofComponents f₁₁ f₁₂ f₂₁ 
f₂₂)       (CategoryTheory.Biprod.ofComponents g₁₁ g₁₂ g₂₁ g₂₂) =     CategoryTh
eory.Biprod.ofComponents       (CategoryTheory.CategoryStruct.comp f₁₁ g₁₁ + Cat
egoryTheory.CategoryStruct.comp f₁₂ g₂₁)       (CategoryTheory.CategoryStruct.co
mp f₁₁ g₁₂ + CategoryTheory.CategoryStruct.comp f₁₂ g₂₂)       (CategoryTheory.C
ategoryStruct.comp f₂₁ g₁₁ + CategoryTheory.CategoryStruct.comp f₂₂ g₂₁)       (
CategoryTheory.CategoryStruct.comp f₂₁ g₁₂ + CategoryTheory.CategoryStruct.comp 
f₂₂ g₂₂)
参数：f₁₁ : X₁ ⟶ Y₁；f₁₂ : X₁ ⟶ Y₂；f₂₁ : X₂ ⟶ Y₁；f₂₂ : X₂ ⟶ Y₂；g₁₁ : Y₁ ⟶ Z₁；g₁₂ : Y
₁ ⟶ Z₂；g₂₁ : Y₂ ⟶ Z₁；g₂₂ : Y₂ ⟶ Z₂；CategoryTheory.Biprod.ofComponents f₁₁ f₁₂ f₂
₁ f₂₂；CategoryTheory.Biprod.ofComponents g₁₁ g₁₂ g₂₁ g₂₂；CategoryTheory.Category
Struct.comp f₁₁ g₁₁ + CategoryTheory.CategoryStruct.comp f₁₂ g₂₁；CategoryTheory.
CategoryStruct.comp f₁₁ g₁₂ + CategoryTheory.CategoryStruct.comp f₁₂ g₂₂；Categor
yTheory.CategoryStruct.comp f₂₁ g₁₁ + CategoryTheory.CategoryStruct.comp f₂₂ g₂₁
；CategoryTheory.CategoryStruct.comp f₂₁ g₁₂ + CategoryTheory.CategoryStruct.comp
 f₂₂ g₂₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.inl_fst_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.biprod.inr_fst_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.Limits.biprod.inl_snd_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.biprod.inr_snd_assoc`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Limits.biprod.inl_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.biprod.inr_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.inl_snd`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.biprod.inr_snd`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
-/
theorem Biprod.ofComponents_comp {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂)
    (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) (g₁₁ : Y₁ ⟶ Z₁) (g₁₂ : Y₁ ⟶ Z₂) (g₂₁ : Y₂ ⟶ Z₁)
    (g₂₂ : Y₂ ⟶ Z₂) :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ Biprod.ofComponents g₁₁ g₁₂ g₂₁ g₂₂ =
      Biprod.ofComponents (f₁₁ ≫ g₁₁ + f₁₂ ≫ g₂₁) (f₁₁ ≫ g₁₂ + f₁₂ ≫ g₂₂) (f₂₁ ≫ g₁₁ + f₂₂ ≫ g₂₁)
        (f₂₁ ≫ g₁₂ + f₂₂ ≫ g₂₂) := by
  dsimp [Biprod.ofComponents]
  ext <;>
    simp only [add_comp, comp_add, add_zero, zero_add, biprod.inl_fst,
      biprod.inl_snd, biprod.inr_fst, biprod.inr_snd, biprod.inl_fst_assoc, biprod.inl_snd_assoc,
      biprod.inr_fst_assoc, biprod.inr_snd_assoc, comp_zero, zero_comp, Category.assoc]

/-- The unipotent upper triangular matrix
```
(1 r)
(0 1)
```
as an isomorphism.
-/
@[simps]
/-
**CategoryTheory.Biprod.unipotentUpper** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Biprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.HasBinary
Biproducts C] → {X₁ X₂ : C} → (X₁ ⟶ X₂) → (X₁ ⊞ X₂ ≅ X₁ ⊞ X₂)
参数：X₁ ⟶ X₂；X₁ ⊞ X₂ ≅ X₁ ⊞ X₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unipotent upper triangular matrix
```
(1 r)
(0 1)
```
as an isomorphism.
-/
def Biprod.unipotentUpper {X₁ X₂ : C} (r : X₁ ⟶ X₂) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ where
  hom := Biprod.ofComponents (𝟙 _) r 0 (𝟙 _)
  inv := Biprod.ofComponents (𝟙 _) (-r) 0 (𝟙 _)

/-- The unipotent lower triangular matrix
```
(1 0)
(r 1)
```
as an isomorphism.
-/
@[simps]
/-
**CategoryTheory.Biprod.unipotentLower** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Biprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.HasBinary
Biproducts C] → {X₁ X₂ : C} → (X₂ ⟶ X₁) → (X₁ ⊞ X₂ ≅ X₁ ⊞ X₂)
参数：X₂ ⟶ X₁；X₁ ⊞ X₂ ≅ X₁ ⊞ X₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unipotent lower triangular matrix
```
(1 0)
(r 1)
```
as an isomorphism.
-/
def Biprod.unipotentLower {X₁ X₂ : C} (r : X₂ ⟶ X₁) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ where
  hom := Biprod.ofComponents (𝟙 _) 0 r (𝟙 _)
  inv := Biprod.ofComponents (𝟙 _) 0 (-r) (𝟙 _)

/-- If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
via Gaussian elimination.

(This is the version of `Biprod.gaussian` written in terms of components.)
-/
/-
**CategoryTheory.Biprod.gaussian'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bipr
od`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.HasBinary
Biproducts C] →         {X₁ X₂ Y₁ Y₂ : C} →           (f₁₁ : X₁ ⟶ Y₁) →         
    (f₁₂ : X₁ ⟶ Y₂) →               (f₂₁ : X₂ ⟶ Y₁) →                 (f₂₂ : X₂ 
⟶ Y₂) →                   [CategoryTheory.IsIso f₁₁] →                     (L : 
X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) ×'                       (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) ×'          
               (g₂₂ : X₂ ⟶ Y₂) ×'                           CategoryTheory.Categ
oryStruct.comp L.hom                               (CategoryTheory.CategoryStruc
t.comp (CategoryTheory.Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂)                     
            R.hom) =                             CategoryTheory.Limits.biprod.ma
p f₁₁ g₂₂
参数：f₁₁ : X₁ ⟶ Y₁；f₁₂ : X₁ ⟶ Y₂；f₂₁ : X₂ ⟶ Y₁；f₂₂ : X₂ ⟶ Y₂；L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂
；R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂；g₂₂ : X₂ ⟶ Y₂；CategoryTheory.CategoryStruct.comp (Categor
yTheory.Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂)                                 R.h
om。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism
,
then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁
 ⊞ Y₂`
so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
via Gaussian elimination.

(This is the version of `Biprod.gaussian` written in terms of components.)
-/
def Biprod.gaussian' [IsIso f₁₁] :
    Σ' (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) (g₂₂ : X₂ ⟶ Y₂),
      L.hom ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ R.hom = biprod.map f₁₁ g₂₂ :=
  ⟨Biprod.unipotentLower (-f₂₁ ≫ inv f₁₁), Biprod.unipotentUpper (-inv f₁₁ ≫ f₁₂),
    f₂₂ - f₂₁ ≫ inv f₁₁ ≫ f₁₂, by ext <;> simp; abel⟩

/-- If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
via Gaussian elimination.
-/
/-
**CategoryTheory.Biprod.gaussian** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bipro
d`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.HasBinary
Biproducts C] →         {X₁ X₂ Y₁ Y₂ : C} →           (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) → 
            [CategoryTheory.IsIso                   (CategoryTheory.CategoryStru
ct.comp CategoryTheory.Limits.biprod.inl                     (CategoryTheory.Cat
egoryStruct.comp f CategoryTheory.Limits.biprod.fst))] →               (L : X₁ ⊞
 X₂ ≅ X₁ ⊞ X₂) ×'                 (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) ×'                   (
g₂₂ : X₂ ⟶ Y₂) ×'                     CategoryTheory.CategoryStruct.comp L.hom (
CategoryTheory.CategoryStruct.comp f R.hom) =                       CategoryTheo
ry.Limits.biprod.map                         (CategoryTheory.CategoryStruct.comp
 CategoryTheory.Limits.biprod.inl                           (CategoryTheory.Cate
goryStruct.comp f CategoryTheory.Limits.biprod.fst))                         g₂₂
参数：f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂；CategoryTheory.CategoryStruct.comp CategoryTheory.Limit
s.biprod.inl                     (CategoryTheory.CategoryStruct.comp f CategoryT
heory.Limits.biprod.fst)；L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂；R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂；g₂₂ : X₂ ⟶ 
Y₂；CategoryTheory.CategoryStruct.comp f R.hom；CategoryTheory.CategoryStruct.comp
 CategoryTheory.Limits.biprod.inl                           (CategoryTheory.Cate
goryStruct.comp f CategoryTheory.Limits.biprod.fst)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism
,
then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁
 ⊞ Y₂`
so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
via Gaussian elimination.
-/
def Biprod.gaussian (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) [IsIso (biprod.inl ≫ f ≫ biprod.fst)] :
    Σ' (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) (g₂₂ : X₂ ⟶ Y₂),
      L.hom ≫ f ≫ R.hom = biprod.map (biprod.inl ≫ f ≫ biprod.fst) g₂₂ := by
  let :=
    Biprod.gaussian' (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd)
      (biprod.inr ≫ f ≫ biprod.fst) (biprod.inr ≫ f ≫ biprod.snd)
  rwa [Biprod.ofComponents_eq] at this

/-- If `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` via a two-by-two matrix whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
/-
**CategoryTheory.Biprod.isoElim'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bipro
d`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.HasBinary
Biproducts C] →         {X₁ X₂ Y₁ Y₂ : C} →           (f₁₁ : X₁ ⟶ Y₁) →         
    (f₁₂ : X₁ ⟶ Y₂) →               (f₂₁ : X₂ ⟶ Y₁) →                 (f₂₂ : X₂ 
⟶ Y₂) →                   [CategoryTheory.IsIso f₁₁] →                     [Cate
goryTheory.IsIso (CategoryTheory.Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂)] → X₂ ≅ Y₂
参数：f₁₁ : X₁ ⟶ Y₁；f₁₂ : X₁ ⟶ Y₂；f₂₁ : X₂ ⟶ Y₁；f₂₂ : X₂ ⟶ Y₂；CategoryTheory.Biprod
.ofComponents f₁₁ f₁₂ f₂₁ f₂₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` via a two-by-two matrix whose `X₁ ⟶ Y₁` entry is an isomo
rphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def Biprod.isoElim' [IsIso f₁₁] [IsIso (Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂)] : X₂ ≅ Y₂ := by
  obtain ⟨L, R, g, w⟩ := Biprod.gaussian' f₁₁ f₁₂ f₂₁ f₂₂
  letI : IsIso (biprod.map f₁₁ g) := by
    rw [← w]
    infer_instance
  letI : IsIso g := isIso_right_of_isIso_biprod_map f₁₁ g
  exact asIso g

/-- If `f` is an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
/-
**CategoryTheory.Biprod.isoElim** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Biprod
`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.HasBinary
Biproducts C] →         {X₁ X₂ Y₁ Y₂ : C} →           (f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂) → 
            [CategoryTheory.IsIso                   (CategoryTheory.CategoryStru
ct.comp CategoryTheory.Limits.biprod.inl                     (CategoryTheory.Cat
egoryStruct.comp f.hom CategoryTheory.Limits.biprod.fst))] →               X₂ ≅ 
Y₂
参数：f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂；CategoryTheory.CategoryStruct.comp CategoryTheory.Limit
s.biprod.inl                     (CategoryTheory.CategoryStruct.comp f.hom Categ
oryTheory.Limits.biprod.fst)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorp
hism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def Biprod.isoElim (f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂) [IsIso (biprod.inl ≫ f.hom ≫ biprod.fst)] : X₂ ≅ Y₂ :=
  letI :
    IsIso
      (Biprod.ofComponents (biprod.inl ≫ f.hom ≫ biprod.fst) (biprod.inl ≫ f.hom ≫ biprod.snd)
        (biprod.inr ≫ f.hom ≫ biprod.fst) (biprod.inr ≫ f.hom ≫ biprod.snd)) := by
    simp only [Biprod.ofComponents_eq]
    infer_instance
  Biprod.isoElim' (biprod.inl ≫ f.hom ≫ biprod.fst) (biprod.inl ≫ f.hom ≫ biprod.snd)
    (biprod.inr ≫ f.hom ≫ biprod.fst) (biprod.inr ≫ f.hom ≫ biprod.snd)
/-
**CategoryTheory.Biprod.column_nonzero_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Biprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasBinaryBiproducts C] 
{W X Y Z : C} (f : W ⊞ X ⟶ Y ⊞ Z) [CategoryTheory.IsIso f],   CategoryTheory.Cat
egoryStruct.id W = 0 ∨     CategoryTheory.CategoryStruct.comp CategoryTheory.Lim
its.biprod.inl           (CategoryTheory.CategoryStruct.comp f CategoryTheory.Li
mits.biprod.fst) ≠         0 ∨       CategoryTheory.CategoryStruct.comp Category
Theory.Limits.biprod.inl           (CategoryTheory.CategoryStruct.comp f Categor
yTheory.Limits.biprod.snd) ≠         0
参数：f : W ⊞ X ⟶ Y ⊞ Z；CategoryTheory.CategoryStruct.comp f CategoryTheory.Limits.
biprod.fst；CategoryTheory.CategoryStruct.comp f CategoryTheory.Limits.biprod.snd
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.total`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [inst_2
 : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.comp_add_assoc`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f
 : P ⟶ Q)   (g g' : Q ⟶ R) {Z :…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem Biprod.column_nonzero_of_iso {W X Y Z : C} (f : W ⊞ X ⟶ Y ⊞ Z) [IsIso f] :
    𝟙 W = 0 ∨ biprod.inl ≫ f ≫ biprod.fst ≠ 0 ∨ biprod.inl ≫ f ≫ biprod.snd ≠ 0 := by
  by_contra! ⟨nz, a₁, a₂⟩
  set x := biprod.inl ≫ f ≫ inv f ≫ biprod.fst
  have h₁ : x = 𝟙 W := by simp [x]
  have h₀ : x = 0 := by
    dsimp [x]
    rw [← Category.id_comp (inv f), Category.assoc, ← biprod.total]
    conv_lhs =>
      slice 2 3
      rw [comp_add]
    simp only [Category.assoc]
    rw [comp_add_assoc, add_comp]
    conv_lhs =>
      congr
      next => skip
      slice 1 3
      rw [a₂]
    simp only [zero_comp, add_zero]
    conv_lhs =>
      slice 1 3
      rw [a₁]
    simp only [zero_comp]
  exact nz (h₁.symm.trans h₀)

end

/-
**CategoryTheory.Biproduct.column_nonzero_of_iso'** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Biproduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] {σ τ : Type} [Finite τ]   {S : σ → C} [inst_3 : CategoryT
heory.Limits.HasBiproduct S] {T : τ → C}   [inst_4 : CategoryTheory.Limits.HasBi
product T] (s : σ) (f : ⨁ S ⟶ ⨁ T) [CategoryTheory.IsIso f],   (∀ (t : τ),      
 CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.biproduct.ι S s)     
      (CategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.biproduct.π T
 t)) =         0) →     CategoryTheory.CategoryStruct.id (S s) = 0
参数：s : σ；f : ⨁ S ⟶ ⨁ T；∀ (t : τ),       CategoryTheory.CategoryStruct.comp (Cate
goryTheory.Limits.biproduct.ι S s)           (CategoryTheory.CategoryStruct.comp
 f (CategoryTheory.Limits.biproduct.π T t)) =         0；S s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Limits.bicone_ι_π_self`：bicone_ι_π_self {F : J -> C} (B :
 Bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.total`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {J : Type}   [in
st_2 : Fintype J] {f : J → …
· 使用定理 `CategoryTheory.Preadditive.comp_sum_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {P Q R : C} 
  {J : Type u_1} (s : Finset J)…
-/
theorem Biproduct.column_nonzero_of_iso' {σ τ : Type} [Finite τ] {S : σ → C} [HasBiproduct S]
    {T : τ → C} [HasBiproduct T] (s : σ) (f : ⨁ S ⟶ ⨁ T) [IsIso f] :
    (∀ t : τ, biproduct.ι S s ≫ f ≫ biproduct.π T t = 0) → 𝟙 (S s) = 0 := by
  cases nonempty_fintype τ
  intro z
  have reassoced {t : τ} {W : C} (h : _ ⟶ W) :
    biproduct.ι S s ≫ f ≫ biproduct.π T t ≫ h = 0 ≫ h := by grind
  set x := biproduct.ι S s ≫ f ≫ inv f ≫ biproduct.π S s
  have h₁ : x = 𝟙 (S s) := by simp [x]
  have h₀ : x = 0 := by
    dsimp [x]
    rw [← Category.id_comp (inv f), Category.assoc, ← biproduct.total]
    simp only [comp_sum_assoc]
    grind [CategoryTheory.Limits.zero_comp, Finset.sum_const_zero]
  exact h₁.symm.trans h₀

/-- If `f : ⨁ S ⟶ ⨁ T` is an isomorphism, and `s` is a non-trivial summand of the source,
then there is some `t` in the target so that the `s, t` matrix entry of `f` is nonzero.
-/
/-
**CategoryTheory.Biproduct.columnNonzeroOfIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Biproduct`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       {σ τ : Type} →         [Fintype τ] →     
      {S : σ → C} →             [inst_3 : CategoryTheory.Limits.HasBiproduct S] 
→               {T : τ → C} →                 [inst_4 : CategoryTheory.Limits.Ha
sBiproduct T] →                   (s : σ) →                     CategoryTheory.C
ategoryStruct.id (S s) ≠ 0 →                       (f : ⨁ S ⟶ ⨁ T) →            
             [CategoryTheory.IsIso f] →                           Trunc         
                    ((t : τ) ×'                               CategoryTheory.Cat
egoryStruct.comp (CategoryTheory.Limits.biproduct.ι S s)                        
           (CategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.biproduc
t.π T t)) ≠                                 0)
参数：s : σ；S s；f : ⨁ S ⟶ ⨁ T；(t : τ) ×'                               CategoryTheo
ry.CategoryStruct.comp (CategoryTheory.Limits.biproduct.ι S s)                  
                 (CategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.bi
product.π T t)) ≠                                 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : ⨁ S ⟶ ⨁ T` is an isomorphism, and `s` is a non-trivial summand of the so
urce,
then there is some `t` in the target so that the `s, t` matrix entry of `f` is n
onzero.
-/
def Biproduct.columnNonzeroOfIso {σ τ : Type} [Fintype τ] {S : σ → C} [HasBiproduct S] {T : τ → C}
    [HasBiproduct T] (s : σ) (nz : 𝟙 (S s) ≠ 0) (f : ⨁ S ⟶ ⨁ T) [IsIso f] :
    Trunc (Σ' t : τ, biproduct.ι S s ≫ f ≫ biproduct.π T t ≠ 0) := by
  classical
    apply truncSigmaOfExists
    have t := Biproduct.column_nonzero_of_iso'.{v} s f
    by_contra h
    simp only [not_exists_not] at h
    exact nz (t h)

section Preadditive

variable {D : Type u'} [Category.{v'} D] [Preadditive.{v'} D]
variable (F : C ⥤ D) [PreservesZeroMorphisms F]

namespace Limits

section Finite

variable {J : Type*} [Finite J]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
preserves finite products. -/
/-
**CategoryTheory.Limits.preservesProduct_of_preservesBiproduct** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesProduct_of_preservesBiproduct {f : J -> C} [PreservesBiproduct f 
F] : PreservesLimit (Discrete.functor f) F where preserves hc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) fin
ite biproducts
preserves finite products.
-/
lemma preservesProduct_of_preservesBiproduct {f : J → C} [PreservesBiproduct f F] :
    PreservesLimit (Discrete.functor f) F where
  preserves hc :=
    let ⟨_⟩ := nonempty_fintype J
    ⟨IsLimit.ofIsoLimit
        ((IsLimit.postcomposeInvEquiv (Discrete.compNatIsoDiscrete _ _) _).symm
          (isBilimitOfPreserves F (biconeIsBilimitOfLimitConeOfIsLimit hc)).isLimit) <|
      Cone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

section

attribute [local instance] preservesProduct_of_preservesBiproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
preserves finite products. -/
/-
**CategoryTheory.Limits.preservesProductsOfShape_of_preservesBiproductsOfShape**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesProductsOfShape_of_preservesBiproductsOfShape [PreservesBiproduct
sOfShape J F] : PreservesLimitsOfShape (Discrete J) F where preservesLimit {_}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
· 使用引理 `CategoryTheory.Limits.preservesProduct_of_preservesBiproduct`：preservesP
roduct_of_preservesBiproduct {f : J -> C} [PreservesBiproduct f F] : PreservesLi
mit (Discrete.functor f) F where preserves hc
· 使用定理 `CategoryTheory.Limits.PreservesBiproductsOfShape.preserves`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Category
Theory.Category.{v₂, u₂} D}   {inst_2 : Category…

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) fin
ite biproducts
preserves finite products.
-/
lemma preservesProductsOfShape_of_preservesBiproductsOfShape [PreservesBiproductsOfShape J F] :
    PreservesLimitsOfShape (Discrete J) F where
  preservesLimit {_} := preservesLimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor between preadditive categories that preserves (zero morphisms and) finite products
preserves finite biproducts. -/
/-
**CategoryTheory.Limits.preservesBiproduct_of_preservesProduct** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBiproduct_of_preservesProduct {f : J -> C} [PreservesLimit (Discr
ete.functor f) F] : PreservesBiproduct f F where preserves {b} hb
参数：Discrete.functor f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) fin
ite products
preserves finite biproducts.
-/
lemma preservesBiproduct_of_preservesProduct {f : J → C} [PreservesLimit (Discrete.functor f) F] :
    PreservesBiproduct f F where
  preserves {b} hb :=
    let ⟨_⟩ := nonempty_fintype J
    ⟨isBilimitOfIsLimit _ <|
      IsLimit.ofIsoLimit
          ((IsLimit.postcomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) (F.mapCone b.toCone)).symm
            (isLimitOfPreserves F hb.isLimit)) <|
        Cone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

set_option backward.isDefEq.respectTransparency false in
/-- If the (product-like) biproduct comparison for `F` and `f` is a monomorphism, then `F`
preserves the biproduct of `f`. For the converse, see `mapBiproduct`. -/
/-
**CategoryTheory.Limits.preservesBiproduct_of_mono_biproductComparison** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBiproduct_of_mono_biproductComparison {f : J -> C} [HasBiproduct 
f] [HasBiproduct (F.obj ∘ f)] [Mono (biproductComparison F f)] : PreservesBiprod
uct f F
参数：F.obj ∘ f；biproductComparison F f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasProduct_of_hasBiproduct`：∀ {J : Type w} {C : Ty
pe uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biproduct.isoProduct_inv`：∀ {J : Type w} {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.isoProduct_hom`：∀ {J : Type w} {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Functor.biproductComparison_π`：biproductComparison_π (j :
 J) : biproductComparison F f ≫ biproduct.π _ j = F.map (biproduct.π f j)
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.piComparison_comp_π`：piComparison_comp_π [HasProdu
ct f] [HasProduct fun b => G.obj (f b)] (b : β) : piComparison G f ≫ Pi.π _ b = 
G.map (Pi.π f b)
· 使用定理 `CategoryTheory.isIso_of_mono_of_isSplitEpi`：isIso_of_mono_of_isSplitEpi 
{X Y : C} (f : X ⟶ Y) [Mono f] [IsSplitEpi f] : IsIso f
· 使用定理 `CategoryTheory.Functor.instIsSplitEpiBiproductComparison`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.PreservesProduct.of_iso_comparison`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesBiproduct_of_preservesProduct`：preservesB
iproduct_of_preservesProduct {f : J -> C} [PreservesLimit (Discrete.functor f) F
] : PreservesBiproduct f F where preserves {b} hb

--- 原说明 ---
If the (product-like) biproduct comparison for `F` and `f` is a monomorphism, th
en `F`
preserves the biproduct of `f`. For the converse, see `mapBiproduct`.
-/
lemma preservesBiproduct_of_mono_biproductComparison {f : J → C} [HasBiproduct f]
    [HasBiproduct (F.obj ∘ f)] [Mono (biproductComparison F f)] : PreservesBiproduct f F := by
  have : HasProduct fun b => F.obj (f b) := by
    change HasProduct (F.obj ∘ f)
    infer_instance
  have that : piComparison F f =
      (F.mapIso (biproduct.isoProduct f)).inv ≫
        biproductComparison F f ≫ (biproduct.isoProduct _).hom := by
    ext j
    convert! piComparison_comp_π F f j; simp [← Function.comp_def, ← Functor.map_comp]
  have : IsIso (biproductComparison F f) := isIso_of_mono_of_isSplitEpi _
  have : IsIso (piComparison F f) := by
    rw [that]
    infer_instance
  have := PreservesProduct.of_iso_comparison F f
  apply preservesBiproduct_of_preservesProduct

/-- If the (coproduct-like) biproduct comparison for `F` and `f` is an epimorphism, then `F`
preserves the biproduct of `F` and `f`. For the converse, see `mapBiproduct`. -/
/-
**CategoryTheory.Limits.preservesBiproduct_of_epi_biproductComparison'** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBiproduct_of_epi_biproductComparison' {f : J -> C} [HasBiproduct 
f] [HasBiproduct (F.obj ∘ f)] [Epi (biproductComparison' F f)] : PreservesBiprod
uct f F
参数：F.obj ∘ f；biproductComparison' F f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.splitEpiBiproductComparison_section_`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.IsIso.of_epi_section'`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (hf : CategoryTheory.SplitEpi f)
   [CategoryTheory.Epi hf.…
· 使用引理 `CategoryTheory.Limits.preservesBiproduct_of_mono_biproductComparison`：pr
eservesBiproduct_of_mono_biproductComparison {f : J -> C} [HasBiproduct f] [HasB
iproduct (F.obj ∘ f)] [Mono (biproductComparison F f)] : P…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f

--- 原说明 ---
If the (coproduct-like) biproduct comparison for `F` and `f` is an epimorphism, 
then `F`
preserves the biproduct of `F` and `f`. For the converse, see `mapBiproduct`.
-/
lemma preservesBiproduct_of_epi_biproductComparison' {f : J → C} [HasBiproduct f]
    [HasBiproduct (F.obj ∘ f)] [Epi (biproductComparison' F f)] : PreservesBiproduct f F := by
  have : Epi (splitEpiBiproductComparison F f).section_ := by simpa
  have : IsIso (biproductComparison F f) :=
    IsIso.of_epi_section' (splitEpiBiproductComparison F f)
  apply preservesBiproduct_of_mono_biproductComparison

/-- A functor between preadditive categories that preserves (zero morphisms and) finite products
preserves finite biproducts. -/
/-
**CategoryTheory.Limits.preservesBiproductsOfShape_of_preservesProductsOfShape**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBiproductsOfShape_of_preservesProductsOfShape [PreservesLimitsOfS
hape (Discrete J) F] : PreservesBiproductsOfShape J F where preserves {_}
参数：Discrete J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesBiproduct_of_preservesProduct`：preservesB
iproduct_of_preservesProduct {f : J -> C} [PreservesLimit (Discrete.functor f) F
] : PreservesBiproduct f F where preserves {b} hb
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) fin
ite products
preserves finite biproducts.
-/
lemma preservesBiproductsOfShape_of_preservesProductsOfShape
    [PreservesLimitsOfShape (Discrete J) F] :
    PreservesBiproductsOfShape J F where
  preserves {_} := preservesBiproduct_of_preservesProduct F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
preserves finite coproducts. -/
/-
**CategoryTheory.Limits.preservesCoproduct_of_preservesBiproduct** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesCoproduct_of_preservesBiproduct {f : J -> C} [PreservesBiproduct 
f F] : PreservesColimit (Discrete.functor f) F where preserves {c} hc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) fin
ite biproducts
preserves finite coproducts.
-/
lemma preservesCoproduct_of_preservesBiproduct {f : J → C} [PreservesBiproduct f F] :
    PreservesColimit (Discrete.functor f) F where
  preserves {c} hc :=
    let ⟨_⟩ := nonempty_fintype J
    ⟨IsColimit.ofIsoColimit
        ((IsColimit.precomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) _).symm
          (isBilimitOfPreserves F (biconeIsBilimitOfColimitCoconeOfIsColimit hc)).isColimit) <|
      Cocone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

section

attribute [local instance] preservesCoproduct_of_preservesBiproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
preserves finite coproducts. -/
/-
**CategoryTheory.Limits.preservesCoproductsOfShape_of_preservesBiproductsOfShape
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesCoproductsOfShape_of_preservesBiproductsOfShape [PreservesBiprodu
ctsOfShape J F] : PreservesColimitsOfShape (Discrete J) F where preservesColimit
 {_}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…
· 使用引理 `CategoryTheory.Limits.preservesCoproduct_of_preservesBiproduct`：preserve
sCoproduct_of_preservesBiproduct {f : J -> C} [PreservesBiproduct f F] : Preserv
esColimit (Discrete.functor f) F where preserves {c}…
· 使用定理 `CategoryTheory.Limits.PreservesBiproductsOfShape.preserves`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Category
Theory.Category.{v₂, u₂} D}   {inst_2 : Category…

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) fin
ite biproducts
preserves finite coproducts.
-/
lemma preservesCoproductsOfShape_of_preservesBiproductsOfShape [PreservesBiproductsOfShape J F] :
    PreservesColimitsOfShape (Discrete J) F where
  preservesColimit {_} := preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor between preadditive categories that preserves (zero morphisms and) finite coproducts
preserves finite biproducts. -/
/-
**CategoryTheory.Limits.preservesBiproduct_of_preservesCoproduct** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBiproduct_of_preservesCoproduct {f : J -> C} [PreservesColimit (D
iscrete.functor f) F] : PreservesBiproduct f F where preserves {b} hb
参数：Discrete.functor f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) fin
ite coproducts
preserves finite biproducts.
-/
lemma preservesBiproduct_of_preservesCoproduct {f : J → C}
    [PreservesColimit (Discrete.functor f) F] :
    PreservesBiproduct f F where
  preserves {b} hb :=
    let ⟨_⟩ := nonempty_fintype J
    ⟨isBilimitOfIsColimit _ <|
      IsColimit.ofIsoColimit
          ((IsColimit.precomposeInvEquiv (Discrete.compNatIsoDiscrete _ _)
                (F.mapCocone b.toCocone)).symm
            (isColimitOfPreserves F hb.isColimit)) <|
        Cocone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

/-- A functor between preadditive categories that preserves (zero morphisms and) finite coproducts
preserves finite biproducts. -/
/-
**CategoryTheory.Limits.preservesBiproductsOfShape_of_preservesCoproductsOfShape
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBiproductsOfShape_of_preservesCoproductsOfShape [PreservesColimit
sOfShape (Discrete J) F] : PreservesBiproductsOfShape J F where preserves {_}
参数：Discrete J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesBiproduct_of_preservesCoproduct`：preserve
sBiproduct_of_preservesCoproduct {f : J -> C} [PreservesColimit (Discrete.functo
r f) F] : PreservesBiproduct f F where preserves {b}…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) fin
ite coproducts
preserves finite biproducts.
-/
lemma preservesBiproductsOfShape_of_preservesCoproductsOfShape
    [PreservesColimitsOfShape (Discrete J) F] : PreservesBiproductsOfShape J F where
  preserves {_} := preservesBiproduct_of_preservesCoproduct F

end Finite

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
preserves binary products. -/
/-
**CategoryTheory.Limits.preservesBinaryProduct_of_preservesBinaryBiproduct** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryProduct_of_preservesBinaryBiproduct {X Y : C} [PreservesBin
aryBiproduct X Y F] : PreservesLimit (pair X Y) F where preserves {c} hc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) bin
ary biproducts
preserves binary products.
-/
lemma preservesBinaryProduct_of_preservesBinaryBiproduct {X Y : C}
    [PreservesBinaryBiproduct X Y F] :
    PreservesLimit (pair X Y) F where
  preserves {c} hc := ⟨IsLimit.ofIsoLimit
        ((IsLimit.postcomposeInvEquiv (diagramIsoPair _) _).symm
          (isBinaryBilimitOfPreserves F (binaryBiconeIsBilimitOfLimitConeOfIsLimit hc)).isLimit) <|
      Cone.ext (by dsimp; rfl) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp⟩

section

attribute [local instance] preservesBinaryProduct_of_preservesBinaryBiproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
preserves binary products. -/
/-
**CategoryTheory.Limits.preservesBinaryProducts_of_preservesBinaryBiproducts** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryProducts_of_preservesBinaryBiproducts [PreservesBinaryBipro
ducts F] : PreservesLimitsOfShape (Discrete WalkingPair) F where preservesLimit 
{_}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
· 使用引理 `CategoryTheory.Limits.preservesBinaryProduct_of_preservesBinaryBiproduct
`：preservesBinaryProduct_of_preservesBinaryBiproduct {X Y : C} [PreservesBinaryB
iproduct X Y F] : PreservesLimit (pair X Y) F where preserves …
· 使用定理 `CategoryTheory.Limits.PreservesBinaryBiproducts.preserves`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryT
heory.Category.{v₂, u₂} D}   {inst_2 : Category…

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) bin
ary biproducts
preserves binary products.
-/
lemma preservesBinaryProducts_of_preservesBinaryBiproducts [PreservesBinaryBiproducts F] :
    PreservesLimitsOfShape (Discrete WalkingPair) F where
  preservesLimit {_} := preservesLimit_of_iso_diagram _ (diagramIsoPair _).symm

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor between preadditive categories that preserves (zero morphisms and) binary products
preserves binary biproducts. -/
/-
**CategoryTheory.Limits.preservesBinaryBiproduct_of_preservesBinaryProduct** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryBiproduct_of_preservesBinaryProduct {X Y : C} [PreservesLim
it (pair X Y) F] : PreservesBinaryBiproduct X Y F where preserves {b} hb
参数：pair X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) bin
ary products
preserves binary biproducts.
-/
lemma preservesBinaryBiproduct_of_preservesBinaryProduct {X Y : C} [PreservesLimit (pair X Y) F] :
    PreservesBinaryBiproduct X Y F where
  preserves {b} hb := ⟨isBinaryBilimitOfIsLimit _ <| IsLimit.ofIsoLimit
          ((IsLimit.postcomposeHomEquiv (diagramIsoPair _) (F.mapCone b.toCone)).symm
            (isLimitOfPreserves F hb.isLimit)) <|
        Cone.ext (by dsimp; rfl) fun j => by
          rcases j with ⟨⟨⟩⟩ <;> simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- If the (product-like) biproduct comparison for `F`, `X` and `Y` is a monomorphism, then
`F` preserves the biproduct of `X` and `Y`. For the converse, see `map_biprod`. -/
/-
**CategoryTheory.Limits.preservesBinaryBiproduct_of_mono_biprodComparison** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryBiproduct_of_mono_biprodComparison {X Y : C} [HasBinaryBipr
oduct X Y] [HasBinaryBiproduct (F.obj X) (F.obj Y)] [Mono (biprodComparison F X 
Y)] : PreservesBinaryBiproduct X Y F
参数：F.obj X；F.obj Y；biprodComparison F X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasLimit_pair`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prodComparison_fst`：prodComparison_fst : prodCompa
rison F A B ≫ prod.fst = F.map prod.fst
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.isoProd_inv`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.biprod.isoProd_hom`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Functor.biprodComparison_fst`：biprodComparison_fst : bipr
odComparison F X Y ≫ biprod.fst = F.map biprod.fst
· 使用定理 `CategoryTheory.Functor.biprodComparison_snd`：biprodComparison_snd : bipr
odComparison F X Y ≫ biprod.snd = F.map biprod.snd
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.prodComparison_snd`：prodComparison_snd : prodCompa
rison F A B ≫ prod.snd = F.map prod.snd
· 使用定理 `CategoryTheory.isIso_of_mono_of_isSplitEpi`：isIso_of_mono_of_isSplitEpi 
{X Y : C} (f : X ⟶ Y) [Mono f] [IsSplitEpi f] : IsIso f
· 使用定理 `CategoryTheory.Functor.instIsSplitEpiBiprodComparison`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.PreservesLimitPair.of_iso_prod_comparison`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproduct_of_preservesBinaryProduct
`：preservesBinaryBiproduct_of_preservesBinaryProduct {X Y : C} [PreservesLimit (
pair X Y) F] : PreservesBinaryBiproduct X Y F where preserves …

--- 原说明 ---
If the (product-like) biproduct comparison for `F`, `X` and `Y` is a monomorphis
m, then
`F` preserves the biproduct of `X` and `Y`. For the converse, see `map_biprod`.
-/
lemma preservesBinaryBiproduct_of_mono_biprodComparison {X Y : C} [HasBinaryBiproduct X Y]
    [HasBinaryBiproduct (F.obj X) (F.obj Y)] [Mono (biprodComparison F X Y)] :
    PreservesBinaryBiproduct X Y F := by
  have that :
    prodComparison F X Y =
      (F.mapIso (biprod.isoProd X Y)).inv ≫ biprodComparison F X Y ≫ (biprod.isoProd _ _).hom := by
    ext <;> simp [← Functor.map_comp]
  have : IsIso (biprodComparison F X Y) := isIso_of_mono_of_isSplitEpi _
  have : IsIso (prodComparison F X Y) := by
    rw [that]
    infer_instance
  have := PreservesLimitPair.of_iso_prod_comparison F X Y
  apply preservesBinaryBiproduct_of_preservesBinaryProduct

/-- If the (coproduct-like) biproduct comparison for `F`, `X` and `Y` is an epimorphism, then
`F` preserves the biproduct of `X` and `Y`. For the converse, see `mapBiprod`. -/
/-
**CategoryTheory.Limits.preservesBinaryBiproduct_of_epi_biprodComparison'** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryBiproduct_of_epi_biprodComparison' {X Y : C} [HasBinaryBipr
oduct X Y] [HasBinaryBiproduct (F.obj X) (F.obj Y)] [Epi (biprodComparison' F X 
Y)] : PreservesBinaryBiproduct X Y F
参数：F.obj X；F.obj Y；biprodComparison' F X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.splitEpiBiprodComparison_section_`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.IsIso.of_epi_section'`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (hf : CategoryTheory.SplitEpi f)
   [CategoryTheory.Epi hf.…
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproduct_of_mono_biprodComparison`
：preservesBinaryBiproduct_of_mono_biprodComparison {X Y : C} [HasBinaryBiproduct
 X Y] [HasBinaryBiproduct (F.obj X) (F.obj Y)] [Mono (biprodC…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f

--- 原说明 ---
If the (coproduct-like) biproduct comparison for `F`, `X` and `Y` is an epimorph
ism, then
`F` preserves the biproduct of `X` and `Y`. For the converse, see `mapBiprod`.
-/
lemma preservesBinaryBiproduct_of_epi_biprodComparison' {X Y : C} [HasBinaryBiproduct X Y]
    [HasBinaryBiproduct (F.obj X) (F.obj Y)] [Epi (biprodComparison' F X Y)] :
    PreservesBinaryBiproduct X Y F := by
  have : Epi (splitEpiBiprodComparison F X Y).section_ := by simpa
  have : IsIso (biprodComparison F X Y) :=
    IsIso.of_epi_section' (splitEpiBiprodComparison F X Y)
  apply preservesBinaryBiproduct_of_mono_biprodComparison

/-- A functor between preadditive categories that preserves (zero morphisms and) binary products
preserves binary biproducts. -/
/-
**CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryBiproducts_of_preservesBinaryProducts [PreservesLimitsOfSha
pe (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where preserves {_} {
_}
参数：Discrete WalkingPair。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproduct_of_preservesBinaryProduct
`：preservesBinaryBiproduct_of_preservesBinaryProduct {X Y : C} [PreservesLimit (
pair X Y) F] : PreservesBinaryBiproduct X Y F where preserves …
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) bin
ary products
preserves binary biproducts.
-/
lemma preservesBinaryBiproducts_of_preservesBinaryProducts
    [PreservesLimitsOfShape (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where
  preserves {_} {_} := preservesBinaryBiproduct_of_preservesBinaryProduct F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
preserves binary coproducts. -/
/-
**CategoryTheory.Limits.preservesBinaryCoproduct_of_preservesBinaryBiproduct** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryCoproduct_of_preservesBinaryBiproduct {X Y : C} [PreservesB
inaryBiproduct X Y F] : PreservesColimit (pair X Y) F where preserves {c} hc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) bin
ary biproducts
preserves binary coproducts.
-/
lemma preservesBinaryCoproduct_of_preservesBinaryBiproduct {X Y : C}
    [PreservesBinaryBiproduct X Y F] :
    PreservesColimit (pair X Y) F where
  preserves {c} hc :=
    ⟨IsColimit.ofIsoColimit
        ((IsColimit.precomposeHomEquiv (diagramIsoPair _) _).symm
          (isBinaryBilimitOfPreserves F
              (binaryBiconeIsBilimitOfColimitCoconeOfIsColimit hc)).isColimit) <|
      Cocone.ext (by dsimp; rfl) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp⟩

section

attribute [local instance] preservesBinaryCoproduct_of_preservesBinaryBiproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
preserves binary coproducts. -/
/-
**CategoryTheory.Limits.preservesBinaryCoproducts_of_preservesBinaryBiproducts**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryCoproducts_of_preservesBinaryBiproducts [PreservesBinaryBip
roducts F] : PreservesColimitsOfShape (Discrete WalkingPair) F where preservesCo
limit {_}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…
· 使用引理 `CategoryTheory.Limits.preservesBinaryCoproduct_of_preservesBinaryBiprodu
ct`：preservesBinaryCoproduct_of_preservesBinaryBiproduct {X Y : C} [PreservesBin
aryBiproduct X Y F] : PreservesColimit (pair X Y) F where preser…
· 使用定理 `CategoryTheory.Limits.PreservesBinaryBiproducts.preserves`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryT
heory.Category.{v₂, u₂} D}   {inst_2 : Category…

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) bin
ary biproducts
preserves binary coproducts.
-/
lemma preservesBinaryCoproducts_of_preservesBinaryBiproducts [PreservesBinaryBiproducts F] :
    PreservesColimitsOfShape (Discrete WalkingPair) F where
  preservesColimit {_} := preservesColimit_of_iso_diagram _ (diagramIsoPair _).symm

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor between preadditive categories that preserves (zero morphisms and) binary coproducts
preserves binary biproducts. -/
/-
**CategoryTheory.Limits.preservesBinaryBiproduct_of_preservesBinaryCoproduct** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryBiproduct_of_preservesBinaryCoproduct {X Y : C} [PreservesC
olimit (pair X Y) F] : PreservesBinaryBiproduct X Y F where preserves {b} hb
参数：pair X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) bin
ary coproducts
preserves binary biproducts.
-/
lemma preservesBinaryBiproduct_of_preservesBinaryCoproduct {X Y : C}
    [PreservesColimit (pair X Y) F] :
    PreservesBinaryBiproduct X Y F where
  preserves {b} hb :=
    ⟨isBinaryBilimitOfIsColimit _ <|
      IsColimit.ofIsoColimit
          ((IsColimit.precomposeInvEquiv (diagramIsoPair _) (F.mapCocone b.toCocone)).symm
            (isColimitOfPreserves F hb.isColimit)) <|
        Cocone.ext (Iso.refl _) fun j => by
          rcases j with ⟨⟨⟩⟩ <;> simp⟩

/-- A functor between preadditive categories that preserves (zero morphisms and) binary coproducts
preserves binary biproducts. -/
/-
**CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryBiproducts_of_preservesBinaryCoproducts [PreservesColimitsO
fShape (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where preserves {
_} {_}
参数：Discrete WalkingPair。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproduct_of_preservesBinaryCoprodu
ct`：preservesBinaryBiproduct_of_preservesBinaryCoproduct {X Y : C} [PreservesCol
imit (pair X Y) F] : PreservesBinaryBiproduct X Y F where preser…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A functor between preadditive categories that preserves (zero morphisms and) bin
ary coproducts
preserves binary biproducts.
-/
lemma preservesBinaryBiproducts_of_preservesBinaryCoproducts
    [PreservesColimitsOfShape (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where
  preserves {_} {_} := preservesBinaryBiproduct_of_preservesBinaryCoproduct F

end Limits

end Preadditive

end CategoryTheory

