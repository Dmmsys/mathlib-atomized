/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Order.Fin.Basic
public import Mathlib.Util.Superscript

/-! # The simplex category

We construct a skeletal model of the simplex category, with an object `⦋n⦌` for each `n : ℕ`, and
morphisms `⦋n⦌ ⟶ ⦋m⦌` identify to monotone maps from `Fin (n + 1)` to `Fin (m + 1)`.

In `Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean`, we show that this category
is equivalent to `NonemptyFinLinOrd`.

## Remarks

We provide the following functions to work with these objects:
1. `SimplexCategory.mk` creates an object of `SimplexCategory` out of a natural number.
  Use the notation `⦋n⦌` in the `Simplicial` locale.
2. `SimplexCategory.len` gives the "length" of an object of `SimplexCategory`, as a natural.
3. `SimplexCategory.Hom.mk` makes a morphism out of a monotone map between `Fin`'s.
4. `SimplexCategory.Hom.toOrderHom` gives the underlying monotone map associated to a
  term of `SimplexCategory.Hom`.

## Notation

* `⦋n⦌` denotes the `n`-dimensional simplex. This notation is available with
  `open Simplicial`.
* `⦋m⦌ₙ` denotes the `m`-dimensional simplex in the `n`-truncated simplex category.
  The truncation proof `p : m ≤ n` can also be provided using the syntax `⦋m, p⦌ₙ`.
  This notation is available with `open SimplexCategory.Truncated`.
-/

@[expose] public section

universe v

open CategoryTheory

/-- The simplex category:
* for each `n : ℕ`, there is an object `⦋n⦌`;
* morphisms `⦋n⦌ ⟶ ⦋m⦌` are monotone functions `Fin (n+1) → Fin (m+1)`
-/
@[ext]
/-
**SimplexCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The simplex category:
* for each `n : ℕ`, there is an object `⦋n⦌`;
* morphisms `⦋n⦌ ⟶ ⦋m⦌` are monotone functions `Fin (n+1) → Fin (m+1)`
-/
structure SimplexCategory : Type where
  /-- Constructor `ℕ → SimplexCategory`. -/
  mk ::
  /-- The length of an object in `SimplexCategory` -/
  len : ℕ

namespace SimplexCategory

/-- the `n`-dimensional simplex can be denoted `⦋n⦌` -/
scoped[Simplicial] notation "⦋" n "⦌" => SimplexCategory.mk n

open Simplicial

/-
**SimplexCategory.len_mk** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：len_mk (n : Nat) : ⦋n⦌.len = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem len_mk (n : ℕ) : ⦋n⦌.len = n := rfl

@[simp]
/-
**SimplexCategory.mk_len** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory`。
形式化陈述：mk_len (n : SimplexCategory) : ⦋n.len⦌ = n
参数：n : SimplexCategory。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_len (n : SimplexCategory) : ⦋n.len⦌ = n :=
  rfl

/-- Morphisms in the `SimplexCategory`. -/
/-
**SimplexCategory.Hom** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：SimplexCategory → SimplexCategory → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms in the `SimplexCategory`.
-/
protected def Hom (a b : SimplexCategory) :=
  Fin (a.len + 1) →o Fin (b.len + 1)

namespace Hom

/-- Make a morphism in `SimplexCategory` from a monotone map of `Fin`'s. -/
/-
**SimplexCategory.Hom.mk** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory.Hom`。
形式化陈述：mk {a b : SimplexCategory} (f : Fin (a.len + 1) ->o Fin (b.len + 1)) : Sim
plexCategory.Hom a b
参数：f : Fin (a.len + 1) ->o Fin (b.len + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a morphism in `SimplexCategory` from a monotone map of `Fin`'s.
-/
def mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) : SimplexCategory.Hom a b :=
  f

/-- Recover the monotone map from a morphism in the simplex category. -/
/-
**SimplexCategory.Hom.toOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory.Hom`
。
形式化陈述：toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) : Fin (a.
len + 1) ->o Fin (b.len + 1)
参数：f : SimplexCategory.Hom a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recover the monotone map from a morphism in the simplex category.
-/
def toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) :
    Fin (a.len + 1) →o Fin (b.len + 1) :=
  f
/-
**SimplexCategory.Hom.ext'** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.Hom`。
形式化陈述：ext' {a b : SimplexCategory} (f g : SimplexCategory.Hom a b) : f.toOrderHo
m = g.toOrderHom -> f = g
参数：f g : SimplexCategory.Hom a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ext' {a b : SimplexCategory} (f g : SimplexCategory.Hom a b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  id

@[simp]
/-
**SimplexCategory.Hom.mk_toOrderHom** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.H
om`。
形式化陈述：mk_toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) : mk f
.toOrderHom = f
参数：f : SimplexCategory.Hom a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) : mk f.toOrderHom = f :=
  rfl

@[simp]
/-
**SimplexCategory.Hom.toOrderHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.H
om`。
形式化陈述：toOrderHom_mk {a b : SimplexCategory} (f : Fin (a.len + 1) ->o Fin (b.len 
+ 1)) : (mk f).toOrderHom = f
参数：f : Fin (a.len + 1) ->o Fin (b.len + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOrderHom_mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) :
    (mk f).toOrderHom = f :=
  rfl
/-
**SimplexCategory.Hom.mk_toOrderHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCate
gory.Hom`。
形式化陈述：mk_toOrderHom_apply {a b : SimplexCategory} (f : Fin (a.len + 1) ->o Fin (
b.len + 1)) (i : Fin (a.len + 1)) : (mk f).toOrderHom i = f i
参数：f : Fin (a.len + 1) ->o Fin (b.len + 1)；i : Fin (a.len + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_toOrderHom_apply {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1))
    (i : Fin (a.len + 1)) : (mk f).toOrderHom i = f i :=
  rfl

/-- Identity morphisms of `SimplexCategory`. -/
@[simp]
/-
**SimplexCategory.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory.Hom`。
形式化陈述：id (a : SimplexCategory) : SimplexCategory.Hom a a
参数：a : SimplexCategory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity morphisms of `SimplexCategory`.
-/
def id (a : SimplexCategory) : SimplexCategory.Hom a a :=
  mk OrderHom.id

/-- Composition of morphisms of `SimplexCategory`. -/
@[simp]
/-
**SimplexCategory.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory.Hom`。
形式化陈述：comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexC
ategory.Hom a b) : SimplexCategory.Hom a c
参数：f : SimplexCategory.Hom b c；g : SimplexCategory.Hom a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms of `SimplexCategory`.
-/
def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
    SimplexCategory.Hom a c :=
  mk <| f.toOrderHom.comp g.toOrderHom

end Hom

attribute [irreducible] SimplexCategory.Hom

/-
**SimplexCategory.smallCategory** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
形式化陈述：smallCategory : SmallCategory.{0} SimplexCategory where Hom n m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smallCategory : SmallCategory.{0} SimplexCategory where
  Hom n m := SimplexCategory.Hom n m
  id _ := SimplexCategory.Hom.id _
  comp f g := SimplexCategory.Hom.comp g f

@[simp]
/-
**SimplexCategory.id_toOrderHom** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：id_toOrderHom (a : SimplexCategory) : Hom.toOrderHom (𝟙 a) = OrderHom.id
参数：a : SimplexCategory。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_toOrderHom (a : SimplexCategory) :
    Hom.toOrderHom (𝟙 a) = OrderHom.id := rfl

@[simp]
/-
**SimplexCategory.comp_toOrderHom** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：comp_toOrderHom {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g
).toOrderHom = g.toOrderHom.comp f.toOrderHom
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_toOrderHom {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).toOrderHom = g.toOrderHom.comp f.toOrderHom := rfl

@[ext]
/-
**SimplexCategory.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.Hom`。
形式化陈述：∀ {a b : SimplexCategory} (f g : a ⟶ b), SimplexCategory.Hom.toOrderHom f 
= SimplexCategory.Hom.toOrderHom g → f = g
参数：f g : a ⟶ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext'`：ext' {a b : SimplexCategory} (f g : SimplexCat
egory.Hom a b) : f.toOrderHom = g.toOrderHom -> f = g
-/
theorem Hom.ext {a b : SimplexCategory} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  Hom.ext' _ _

/-- Homs in `SimplexCategory` are equivalent to order-preserving functions of finite linear
orders. -/
/-
**SimplexCategory.homEquivOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：homEquivOrderHom {a b : SimplexCategory} : (a ⟶ b) ≃ (Fin (a.len + 1) ->o 
Fin (b.len + 1)) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homs in `SimplexCategory` are equivalent to order-preserving functions of finite
 linear
orders.
-/
def homEquivOrderHom {a b : SimplexCategory} :
    (a ⟶ b) ≃ (Fin (a.len + 1) →o Fin (b.len + 1)) where
  toFun := Hom.toOrderHom
  invFun := Hom.mk

/-- Homs in `SimplexCategory` are equivalent to functors between finite linear orders. -/
/-
**SimplexCategory.homEquivFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：homEquivFunctor {a b : SimplexCategory} : (a ⟶ b) ≃ (Fin (a.len + 1) ⥤ Fin
 (b.len + 1))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Homs in `SimplexCategory` are equivalent to functors between finite linear order
s.
-/
def homEquivFunctor {a b : SimplexCategory} :
    (a ⟶ b) ≃ (Fin (a.len + 1) ⥤ Fin (b.len + 1)) :=
  SimplexCategory.homEquivOrderHom.trans OrderHom.equivFunctor

/-- The truncated simplex category. -/
/-
**SimplexCategory.Truncated** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimplexCategory`。
形式化陈述：Truncated (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The truncated simplex category.
-/
abbrev Truncated (n : ℕ) :=
  ObjectProperty.FullSubcategory fun a : SimplexCategory => a.len ≤ n

namespace Truncated

/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory.Truncate
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n} : Inhabited (Truncated n) :=
  ⟨⟨⦋0⦌, by simp⟩⟩

/-- The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
/-
**SimplexCategory.Truncated.inclusion** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimplexCatego
ry.Truncated`。
形式化陈述：inclusion (n : Nat) : SimplexCategory.Truncated n ⥤ SimplexCategory
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
abbrev inclusion (n : ℕ) : SimplexCategory.Truncated n ⥤ SimplexCategory :=
  ObjectProperty.ι _

/-- A proof that the full subcategory inclusion is fully faithful -/
/-
**SimplexCategory.Truncated.inclusion.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `S
implexCategory.Truncated.inclusion`。
形式化陈述：(n : ℕ) → (SimplexCategory.Truncated.inclusion n).op.FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proof that the full subcategory inclusion is fully faithful
-/
noncomputable def inclusion.fullyFaithful (n : ℕ) :
    (inclusion n : Truncated n ⥤ _).op.FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

@[ext]
/-
**SimplexCategory.Truncated.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.T
runcated.Hom`。
形式化陈述：∀ {n : ℕ} {a b : SimplexCategory.Truncated n} (f g : a ⟶ b),   SimplexCate
gory.Hom.toOrderHom f.hom = SimplexCategory.Hom.toOrderHom g.hom → f = g
参数：f g : a ⟶ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
-/
theorem Hom.ext {n} {a b : Truncated n} (f g : a ⟶ b)
    (h : f.hom.toOrderHom = g.hom.toOrderHom) : f = g :=
  ObjectProperty.hom_ext _ (SimplexCategory.Hom.ext _ _ h)

/-- A quick attempt to prove that `⦋m⦌` is `n`-truncated (`⦋m⦌.len ≤ n`). -/
scoped macro "trunc" : tactic =>
  `(tactic| first | assumption | dsimp only [SimplexCategory.len_mk] <;> lia)

open Mathlib.Tactic (subscriptTerm) in
/-- For `m ≤ n`, `⦋m⦌ₙ` is the `m`-dimensional simplex in `Truncated n`. The
proof `p : m ≤ n` can also be provided using the syntax `⦋m, p⦌ₙ`. -/
scoped syntax:max (name := mkNotation)
  "⦋" term ("," term)? "⦌" noWs subscriptTerm : term
scoped macro_rules
  | `(⦋$m:term⦌$n:subscript) =>
    `((⟨SimplexCategory.mk $m, by first | trunc |
      fail "Failed to prove truncation property. Try writing `⦋m, by ...⦌ₙ`."⟩ :
      SimplexCategory.Truncated $n))
  | `(⦋$m:term, $p:term⦌$n:subscript) =>
    `((⟨SimplexCategory.mk $m, $p⟩ : SimplexCategory.Truncated $n))

/-- Make a morphism in `Truncated n` from a morphism in `SimplexCategory`. This
is equivalent to `@id (⦋a⦌ₙ ⟶ ⦋b⦌ₙ) f`. -/
/-
**SimplexCategory.Truncated.Hom.tr** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory.Tr
uncated.Hom`。
形式化陈述：{n : ℕ} →   {a b : SimplexCategory} →     (a ⟶ b) →       (ha : autoParam 
(a.len ≤ n) SimplexCategory.Truncated.Hom.tr._auto_1) →         (hb : autoParam 
(b.len ≤ n) SimplexCategory.Truncated.Hom.tr._auto_3) →           { obj := a, pr
operty := ha } ⟶ { obj := b, property := hb }
参数：a ⟶ b；ha : autoParam (a.len ≤ n) SimplexCategory.Truncated.Hom.tr._auto_1；hb 
: autoParam (b.len ≤ n) SimplexCategory.Truncated.Hom.tr._auto_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a morphism in `Truncated n` from a morphism in `SimplexCategory`. This
is equivalent to `@id (⦋a⦌ₙ ⟶ ⦋b⦌ₙ) f`.
-/
abbrev Hom.tr {n : ℕ} {a b : SimplexCategory} (f : a ⟶ b)
    (ha : a.len ≤ n := by trunc) (hb : b.len ≤ n := by trunc) :
    (⟨a, ha⟩ : Truncated n) ⟶ ⟨b, hb⟩ :=
  ObjectProperty.homMk f

@[simp]
/-
**SimplexCategory.Truncated.Hom.tr_id** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory
.Truncated.Hom`。
形式化陈述：∀ {n : ℕ} (a : SimplexCategory) (ha : autoParam (a.len ≤ n) SimplexCategor
y.Truncated.Hom.tr_id._auto_1),   SimplexCategory.Truncated.Hom.tr (CategoryTheo
ry.CategoryStruct.id a) ha ha =     CategoryTheory.CategoryStruct.id { obj := a,
 property := ha }
参数：a : SimplexCategory；ha : autoParam (a.len ≤ n) SimplexCategory.Truncated.Hom.
tr_id._auto_1；CategoryTheory.CategoryStruct.id a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.tr_id {n : ℕ} (a : SimplexCategory) (ha : a.len ≤ n := by trunc) :
    Hom.tr (𝟙 a) ha = 𝟙 _ := rfl

@[reassoc]
/-
**SimplexCategory.Truncated.Hom.tr_comp** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCatego
ry.Truncated.Hom`。
形式化陈述：∀ {n : ℕ} {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)   (ha : autoPa
ram (a.len ≤ n) SimplexCategory.Truncated.Hom.tr_comp._auto_1)   (hb : autoParam
 (b.len ≤ n) SimplexCategory.Truncated.Hom.tr_comp._auto_3)   (hc : autoParam (c
.len ≤ n) SimplexCategory.Truncated.Hom.tr_comp._auto_5),   SimplexCategory.Trun
cated.Hom.tr (CategoryTheory.CategoryStruct.comp f g) ha hc =     CategoryTheory
.CategoryStruct.comp (SimplexCategory.Truncated.Hom.tr f ha hb)       (SimplexCa
tegory.Truncated.Hom.tr g hb hc)
参数：f : a ⟶ b；g : b ⟶ c；ha : autoParam (a.len ≤ n) SimplexCategory.Truncated.Hom.
tr_comp._auto_1；hb : autoParam (b.len ≤ n) SimplexCategory.Truncated.Hom.tr_comp
._auto_3；hc : autoParam (c.len ≤ n) SimplexCategory.Truncated.Hom.tr_comp._auto_
5；CategoryTheory.CategoryStruct.comp f g；SimplexCategory.Truncated.Hom.tr f ha h
b；SimplexCategory.Truncated.Hom.tr g hb hc。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.tr_comp {n : ℕ} {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (ha : a.len ≤ n := by trunc) (hb : b.len ≤ n := by trunc)
    (hc : c.len ≤ n := by trunc) :
    tr (f ≫ g) = tr f ≫ tr g :=
  rfl

@[reassoc]
/-
**SimplexCategory.Truncated.Hom.tr_comp'** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCateg
ory.Truncated.Hom`。
形式化陈述：∀ {n : ℕ} {a b c : SimplexCategory} (f : a ⟶ b) {hb : b.len ≤ n} {hc : c.l
en ≤ n}   (g : { obj := b, property := hb } ⟶ { obj := c, property := hc })   (h
a : autoParam (a.len ≤ n) SimplexCategory.Truncated.Hom.tr_comp'._auto_1),   Sim
plexCategory.Truncated.Hom.tr (CategoryTheory.CategoryStruct.comp f g.hom) ha hc
 =     CategoryTheory.CategoryStruct.comp (SimplexCategory.Truncated.Hom.tr f ha
 hb) g
参数：f : a ⟶ b；g : { obj := b, property := hb } ⟶ { obj := c, property := hc }；ha 
: autoParam (a.len ≤ n) SimplexCategory.Truncated.Hom.tr_comp'._auto_1；CategoryT
heory.CategoryStruct.comp f g.hom；SimplexCategory.Truncated.Hom.tr f ha hb。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.tr_comp' {n : ℕ} {a b c : SimplexCategory} (f : a ⟶ b) {hb : b.len ≤ n}
    {hc : c.len ≤ n} (g : (⟨b, hb⟩ : Truncated n) ⟶ ⟨c, hc⟩) (ha : a.len ≤ n := by trunc) :
    tr (f ≫ g.hom) = tr f ≫ g :=
  rfl

/-- The inclusion of `Truncated n` into `Truncated m` when `n ≤ m`. -/
/-
**SimplexCategory.Truncated.incl** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimplexCategory.Tr
uncated`。
形式化陈述：incl (n m : Nat) (h : n <= m
参数：n m : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of `Truncated n` into `Truncated m` when `n ≤ m`.
-/
abbrev incl (n m : ℕ) (h : n ≤ m := by lia) : Truncated n ⥤ Truncated m :=
  ObjectProperty.ιOfLE (fun _ h' ↦ h'.trans h)

/-- For all `n ≤ m`, `inclusion n` factors through `Truncated m`. -/
/-
**SimplexCategory.Truncated.inclCompInclusion** 是 Mathlib 中的一个定义，位于命名空间 `Simplex
Category.Truncated`。
形式化陈述：inclCompInclusion {n m : Nat} (h : n <= m) : incl n m ⋙ inclusion m ≅ incl
usion n
参数：h : n <= m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For all `n ≤ m`, `inclusion n` factors through `Truncated m`.
-/
def inclCompInclusion {n m : ℕ} (h : n ≤ m) :
    incl n m ⋙ inclusion m ≅ inclusion n :=
  Iso.refl _

end Truncated

end SimplexCategory

