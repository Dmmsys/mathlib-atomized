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
/--
Definition of `SimplexCategory` / `SimplexCategory` 的定义

English:
structure SimplexCategory
  parameters: : Type where
  axioms and operations (2):
    - mk : :
    - len : Nat

中文:
结构 SimplexCategory
  参数: : Type where
  公理与运算 (2 个):
    - mk : :
    - len : 自然数
-/
structure SimplexCategory : Type where
  /-- Constructor `ℕ → SimplexCategory`. -/
  mk ::
  /-- The length of an object in `SimplexCategory` -/
  len : Nat

namespace SimplexCategory

/-- the `n`-dimensional simplex can be denoted `⦋n⦌` -/
scoped[Simplicial] notation "⦋" n "⦌" => SimplexCategory.mk n

open Simplicial

/--
theorem `len_mk` / 定理 `len_mk`

English:
theorem len_mk
  given: (n : Nat)
  statement: ⦋n⦌.len = n
  proof: rfl

@[simp]

中文:
定理 len_mk
  条件: (n : 自然数)
  结论: ⦋n⦌.len = n
  证明: rfl

@[simp]
-/
theorem len_mk (n : Nat) : ⦋n⦌.len = n := rfl

@[simp]
/--
theorem `mk_len` / 定理 `mk_len`

English:
theorem mk_len
  given: (n : SimplexCategory)
  statement: ⦋n.len⦌ = n
  proof: rfl

中文:
定理 mk_len
  条件: (n : SimplexCategory)
  结论: ⦋n.len⦌ = n
  证明: rfl
-/
theorem mk_len (n : SimplexCategory) : ⦋n.len⦌ = n :=
  rfl

/--
Definition of `Hom` / `Hom` 的定义

English:
definition Hom
  signature: (a b : SimplexCategory)
  body: Fin (a.len + 1) ->o Fin (b.len + 1)

中文:
定义 Hom
  签名: (a b : SimplexCategory)
  定义体: Fin (a.len + 1) ->o Fin (b.len + 1)
-/
protected def Hom (a b : SimplexCategory) :=
  Fin (a.len + 1) ->o Fin (b.len + 1)

namespace Hom

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {a b : SimplexCategory} (f : Fin (a.len + 1) ->o Fin (b.len + 1))
  body: f

中文:
定义 mk
  签名: {a b : SimplexCategory} (f : Fin (a.len + 1) ->o Fin (b.len + 1))
  定义体: f
-/
def mk {a b : SimplexCategory} (f : Fin (a.len + 1) ->o Fin (b.len + 1)) : SimplexCategory.Hom a b :=
  f

/--
Definition of `toOrderHom` / `toOrderHom` 的定义

English:
definition toOrderHom
  signature: {a b : SimplexCategory} (f : SimplexCategory.Hom a b)
  body: f

中文:
定义 toOrderHom
  签名: {a b : SimplexCategory} (f : SimplexCategory.Hom a b)
  定义体: f
-/
def toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) :
    Fin (a.len + 1) ->o Fin (b.len + 1) :=
  f

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {a b : SimplexCategory} (f g : SimplexCategory.Hom a b)
  proof: id

@[simp]

中文:
定理 ext'
  条件: {a b : SimplexCategory} (f g : SimplexCategory.Hom a b)
  证明: id

@[simp]
-/
theorem ext' {a b : SimplexCategory} (f g : SimplexCategory.Hom a b) :
    f.toOrderHom = g.toOrderHom -> f = g :=
  id

@[simp]
/--
theorem `mk_toOrderHom` / 定理 `mk_toOrderHom`

English:
theorem mk_toOrderHom
  given: {a b : SimplexCategory} (f : SimplexCategory.Hom a b)
  statement: mk f.toOrderHom = f
  proof: rfl

@[simp]

中文:
定理 mk_toOrderHom
  条件: {a b : SimplexCategory} (f : SimplexCategory.Hom a b)
  结论: mk f.toOrderHom = f
  证明: rfl

@[simp]
-/
theorem mk_toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) : mk f.toOrderHom = f :=
  rfl

@[simp]
/--
theorem `toOrderHom_mk` / 定理 `toOrderHom_mk`

English:
theorem toOrderHom_mk
  given: {a b : SimplexCategory} (f : Fin (a.len + 1) ->o Fin (b.len + 1))
  proof: rfl

中文:
定理 toOrderHom_mk
  条件: {a b : SimplexCategory} (f : Fin (a.len + 1) ->o Fin (b.len + 1))
  证明: rfl
-/
theorem toOrderHom_mk {a b : SimplexCategory} (f : Fin (a.len + 1) ->o Fin (b.len + 1)) :
    (mk f).toOrderHom = f :=
  rfl

/--
theorem `mk_toOrderHom_apply` / 定理 `mk_toOrderHom_apply`

English:
theorem mk_toOrderHom_apply
  statement: {a b : SimplexCategory} (f : Fin (a.len + 1) ->o Fin (b.len + 1))
  proof: rfl

中文:
定理 mk_toOrderHom_apply
  结论: {a b : SimplexCategory} (f : Fin (a.len + 1) ->o Fin (b.len + 1))
  证明: rfl
-/
theorem mk_toOrderHom_apply {a b : SimplexCategory} (f : Fin (a.len + 1) ->o Fin (b.len + 1))
    (i : Fin (a.len + 1)) : (mk f).toOrderHom i = f i :=
  rfl

/-- Identity morphisms of `SimplexCategory`. -/
@[simp]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (a : SimplexCategory)
  body: mk OrderHom.id

中文:
定义 id
  签名: (a : SimplexCategory)
  定义体: mk OrderHom.id

Depends on / 依赖: OrderHom, OrderHom.id
-/
def id (a : SimplexCategory) : SimplexCategory.Hom a a :=
  mk OrderHom.id

/-- Composition of morphisms of `SimplexCategory`. -/
@[simp]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b)
  body: mk f.toOrderHom.comp g.toOrderHom

中文:
定义 comp
  签名: {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b)
  定义体: mk f.toOrderHom.comp g.toOrderHom

Depends on / 依赖: f.toOrderHom.comp, g.toOrderHom, toOrderHom
-/
def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
    SimplexCategory.Hom a c :=
mk f.toOrderHom.comp g.toOrderHom

end Hom

attribute [irreducible] SimplexCategory.Hom

/--
Instance `smallCategory` / 实例 `smallCategory`

English:
instance smallCategory
  signature: : SmallCategory.{0} SimplexCategory where
  body: SimplexCategory.Hom n m
  id _ := SimplexCategory.Hom.id _
  comp f g := SimplexCategory.Hom.comp g f

@[simp]

中文:
实例 smallCategory
  签名: : SmallCategory.{0} SimplexCategory where
  定义体: SimplexCategory.Hom n m
  id _ := SimplexCategory.Hom.id _
  comp f g := SimplexCategory.Hom.comp g f

@[simp]

Depends on / 依赖: SimplexCategory, SimplexCategory.Hom
-/
instance smallCategory : SmallCategory.{0} SimplexCategory where
  Hom n m := SimplexCategory.Hom n m
  id _ := SimplexCategory.Hom.id _
  comp f g := SimplexCategory.Hom.comp g f

@[simp]
/--
lemma `id_toOrderHom` / 引理 `id_toOrderHom`

English:
lemma id_toOrderHom
  given: (a : SimplexCategory)
  proof: rfl

@[simp]

中文:
引理 id_toOrderHom
  条件: (a : SimplexCategory)
  证明: rfl

@[simp]
-/
lemma id_toOrderHom (a : SimplexCategory) :
    Hom.toOrderHom (𝟙 a) = OrderHom.id := rfl

@[simp]
/--
lemma `comp_toOrderHom` / 引理 `comp_toOrderHom`

English:
lemma comp_toOrderHom
  given: {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
  proof: rfl

@[ext]

中文:
引理 comp_toOrderHom
  条件: {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
  证明: rfl

@[ext]
-/
lemma comp_toOrderHom {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).toOrderHom = g.toOrderHom.comp f.toOrderHom := rfl

@[ext]
/--
theorem `Hom.ext` / 定理 `Hom.ext`

English:
theorem Hom.ext
  given: {a b : SimplexCategory} (f g : a ⟶ b)
  proof: Hom.ext' _ _

中文:
定理 Hom.ext
  条件: {a b : SimplexCategory} (f g : a ⟶ b)
  证明: Hom.ext' _ _

Depends on / 依赖: Hom.ext
-/
theorem Hom.ext {a b : SimplexCategory} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom -> f = g :=
  Hom.ext' _ _

/--
Definition of `homEquivOrderHom` / `homEquivOrderHom` 的定义

English:
definition homEquivOrderHom
  signature: {a b : SimplexCategory}
  body: Hom.toOrderHom
  invFun := Hom.mk

中文:
定义 homEquivOrderHom
  签名: {a b : SimplexCategory}
  定义体: Hom.toOrderHom
  invFun := Hom.mk

Depends on / 依赖: Hom.toOrderHom, toOrderHom
-/
def homEquivOrderHom {a b : SimplexCategory} :
    (a ⟶ b) ≃ (Fin (a.len + 1) ->o Fin (b.len + 1)) where
  toFun := Hom.toOrderHom
  invFun := Hom.mk

/--
Definition of `homEquivFunctor` / `homEquivFunctor` 的定义

English:
definition homEquivFunctor
  signature: {a b : SimplexCategory}
  body: SimplexCategory.homEquivOrderHom.trans OrderHom.equivFunctor

中文:
定义 homEquivFunctor
  签名: {a b : SimplexCategory}
  定义体: SimplexCategory.homEquivOrderHom.trans OrderHom.equivFunctor

Depends on / 依赖: OrderHom, OrderHom.equivFunctor, SimplexCategory, SimplexCategory.homEquivOrderHom.trans, equivFunctor, homEquivOrderHom
-/
def homEquivFunctor {a b : SimplexCategory} :
    (a ⟶ b) ≃ (Fin (a.len + 1) ⥤ Fin (b.len + 1)) :=
  SimplexCategory.homEquivOrderHom.trans OrderHom.equivFunctor

/--
Definition of `Truncated` / `Truncated` 的定义

English:
abbreviation Truncated
  signature: (n : Nat)
  body: ObjectProperty.FullSubcategory fun a : SimplexCategory => a.len <= n

中文:
缩写 Truncated
  签名: (n : 自然数)
  定义体: ObjectProperty.FullSubcategory fun a : SimplexCategory => a.len <= n

Depends on / 依赖: FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory, SimplexCategory, a.len
-/
abbrev Truncated (n : Nat) :=
  ObjectProperty.FullSubcategory fun a : SimplexCategory => a.len <= n

namespace Truncated

instance {n} : Inhabited (Truncated n) :=
  ⟨⟨⦋0⦌, by simp⟩⟩

/--
Definition of `inclusion` / `inclusion` 的定义

English:
abbreviation inclusion
  signature: (n : Nat)
  body: ObjectProperty.ι _

中文:
缩写 inclusion
  签名: (n : 自然数)
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
abbrev inclusion (n : Nat) : SimplexCategory.Truncated n ⥤ SimplexCategory :=
  ObjectProperty.ι _

/--
Definition of `inclusion.fullyFaithful` / `inclusion.fullyFaithful` 的定义

English:
definition inclusion.fullyFaithful
  signature: (n : Nat)
  body: Functor.FullyFaithful.ofFullyFaithful _

@[ext]

中文:
定义 inclusion.fullyFaithful
  签名: (n : 自然数)
  定义体: Functor.FullyFaithful.ofFullyFaithful _

@[ext]

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.ofFullyFaithful, ofFullyFaithful
-/
noncomputable def inclusion.fullyFaithful (n : Nat) :
    (inclusion n : Truncated n ⥤ _).op.FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

@[ext]
/--
theorem `Hom.ext` / 定理 `Hom.ext`

English:
theorem Hom.ext
  statement: {n} {a b : Truncated n} (f g : a ⟶ b)
  proof: ObjectProperty.hom_ext _ (SimplexCategory.Hom.ext _ _ h)

中文:
定理 Hom.ext
  结论: {n} {a b : Truncated n} (f g : a ⟶ b)
  证明: ObjectProperty.hom_ext _ (SimplexCategory.Hom.ext _ _ h)
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
SimplexCategory.Truncated n))
  | `(⦋$m:term, $p:term⦌$n:subscript) =>
    `((⟨SimplexCategory.mk $m, $p⟩ : SimplexCategory.Truncated $n))

/--
Definition of `Hom.tr` / `Hom.tr` 的定义

English:
abbreviation Hom.tr
  signature: {n : Nat} {a b : SimplexCategory} (f : a ⟶ b)
  body: ObjectProperty.homMk f

@[simp]

中文:
缩写 Hom.tr
  签名: {n : 自然数} {a b : SimplexCategory} (f : a ⟶ b)
  定义体: ObjectProperty.homMk f

@[simp]

Depends on / 依赖: ObjectProperty, ObjectProperty.homMk, Truncated, b.len
-/
abbrev Hom.tr {n : Nat} {a b : SimplexCategory} (f : a ⟶ b)
    (ha : a.len <= n := by trunc) (hb : b.len <= n := by trunc) :
    (⟨a, ha⟩ : Truncated n) ⟶ ⟨b, hb⟩ :=
  ObjectProperty.homMk f

@[simp]
/--
lemma `Hom.tr_id` / 引理 `Hom.tr_id`

English:
lemma Hom.tr_id
  given: {n : Nat} (a : SimplexCategory) (ha : a.len <= n := by trunc)
  proof: rfl

@[reassoc]

中文:
引理 Hom.tr_id
  条件: {n : 自然数} (a : SimplexCategory) (ha : a.len <= n := by trunc)
  证明: rfl

@[reassoc]

Depends on / 依赖: Hom.tr
-/
lemma Hom.tr_id {n : Nat} (a : SimplexCategory) (ha : a.len <= n := by trunc) :
    Hom.tr (𝟙 a) ha = 𝟙 _ := rfl

@[reassoc]
/--
lemma `Hom.tr_comp` / 引理 `Hom.tr_comp`

English:
lemma Hom.tr_comp
  statement: {n : Nat} {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
  proof: rfl

@[reassoc]

中文:
引理 Hom.tr_comp
  结论: {n : 自然数} {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
  证明: rfl

@[reassoc]

Depends on / 依赖: b.len, c.len
-/
lemma Hom.tr_comp {n : Nat} {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (ha : a.len <= n := by trunc) (hb : b.len <= n := by trunc)
    (hc : c.len <= n := by trunc) :
    tr (f ≫ g) = tr f ≫ tr g :=
  rfl

@[reassoc]
/--
lemma `Hom.tr_comp'` / 引理 `Hom.tr_comp'`

English:
lemma Hom.tr_comp'
  statement: {n : Nat} {a b c : SimplexCategory} (f : a ⟶ b) {hb : b.len <= n}
  proof: rfl

中文:
引理 Hom.tr_comp'
  结论: {n : 自然数} {a b c : SimplexCategory} (f : a ⟶ b) {hb : b.len <= n}
  证明: rfl

Depends on / 依赖: g.hom
-/
lemma Hom.tr_comp' {n : Nat} {a b c : SimplexCategory} (f : a ⟶ b) {hb : b.len <= n}
    {hc : c.len <= n} (g : (⟨b, hb⟩ : Truncated n) ⟶ ⟨c, hc⟩) (ha : a.len <= n := by trunc) :
    tr (f ≫ g.hom) = tr f ≫ g :=
  rfl

/--
Definition of `incl` / `incl` 的定义

English:
abbreviation incl
  signature: (n m : Nat) (h : n <= m := by lia)
  body: ObjectProperty.ιOfLE (fun _ h' => h'.trans h)

中文:
缩写 incl
  签名: (n m : 自然数) (h : n <= m := by lia)
  定义体: ObjectProperty.ιOfLE (fun _ h' => h'.trans h)

Depends on / 依赖: ObjectProperty, Truncated
-/
abbrev incl (n m : Nat) (h : n <= m := by lia) : Truncated n ⥤ Truncated m :=
  ObjectProperty.ιOfLE (fun _ h' => h'.trans h)

/--
Definition of `inclCompInclusion` / `inclCompInclusion` 的定义

English:
definition inclCompInclusion
  signature: {n m : Nat} (h : n <= m)
  body: Iso.refl _

中文:
定义 inclCompInclusion
  签名: {n m : 自然数} (h : n <= m)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def inclCompInclusion {n m : Nat} (h : n <= m) :
    incl n m ⋙ inclusion m ≅ inclusion n :=
  Iso.refl _

end Truncated

end SimplexCategory
