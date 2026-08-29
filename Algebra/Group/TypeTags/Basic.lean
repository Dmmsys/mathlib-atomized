/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Equiv.Defs

/-!
# Type tags that turn additive structures into multiplicative, and vice versa

We define two type tags:

* `Additive α`: turns any multiplicative structure on `α` into the corresponding
  additive structure on `Additive α`;
* `Multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `Multiplicative α`.

We also define instances `Additive.*` and `Multiplicative.*` that actually transfer the structures.

## See also

This file is similar to `Mathlib/Order/Synonym.lean`.

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered MonoidHom Finite

universe u v

variable {α : Type u} {β : Type v}

/--
Definition of `Additive` / `Additive` 的定义

English:
definition Additive
  signature: (α : Type*)
  body: α

中文:
定义 Additive
  签名: (α : 类型)
  定义体: α
-/
def Additive (α : Type*) := α

/--
Definition of `Multiplicative` / `Multiplicative` 的定义

English:
definition Multiplicative
  signature: (α : Type*)
  body: α

中文:
定义 Multiplicative
  签名: (α : 类型)
  定义体: α
-/
def Multiplicative (α : Type*) := α

namespace Additive

/-- Reinterpret `x : α` as an element of `Additive α`. -/
@[implicit_reducible]
/--
Definition of `ofMul` / `ofMul` 的定义

English:
definition ofMul
  signature: : α ≃ Additive α
  body: ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

中文:
定义 ofMul
  签名: : α ≃ Additive α
  定义体: ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
-/
def ofMul : α ≃ Additive α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

/-- Reinterpret `x : Additive α` as an element of `α`. -/
@[implicit_reducible]
/--
Definition of `toMul` / `toMul` 的定义

English:
definition toMul
  signature: : Additive α ≃ α
  body: ofMul.symm

@[simp]

中文:
定义 toMul
  签名: : Additive α ≃ α
  定义体: ofMul.symm

@[simp]

Depends on / 依赖: ofMul.symm
-/
def toMul : Additive α ≃ α := ofMul.symm

@[simp]
/--
theorem `ofMul_symm_eq` / 定理 `ofMul_symm_eq`

English:
theorem ofMul_symm_eq
  statement: (@ofMul α).symm = toMul
  proof: rfl

@[simp]

中文:
定理 ofMul_symm_eq
  结论: (@ofMul α).symm = toMul
  证明: rfl

@[simp]
-/
theorem ofMul_symm_eq : (@ofMul α).symm = toMul :=
  rfl

@[simp]
/--
theorem `toMul_symm_eq` / 定理 `toMul_symm_eq`

English:
theorem toMul_symm_eq
  statement: (@toMul α).symm = ofMul
  proof: rfl

中文:
定理 toMul_symm_eq
  结论: (@toMul α).symm = ofMul
  证明: rfl
-/
theorem toMul_symm_eq : (@toMul α).symm = ofMul :=
  rfl

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {a b : Additive α} (hab : a.toMul = b.toMul)
  statement: a = b
  proof: hab

@[simp]

中文:
引理 ext
  条件: {a b : Additive α} (hab : a.toMul = b.toMul)
  结论: a = b
  证明: hab

@[simp]
-/
@[ext] lemma ext {a b : Additive α} (hab : a.toMul = b.toMul) : a = b := hab

@[simp]
/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {p : Additive α -> Prop}
  statement: (forall a, p a) ↔ forall a, p (ofMul a)
  proof: Iff.rfl

@[simp]

中文:
引理 «forall»
  条件: {p : Additive α -> 命题}
  结论: (对任意 a, p a) ↔ 对任意 a, p (ofMul a)
  证明: Iff.rfl

@[simp]
-/
protected lemma «forall» {p : Additive α -> Prop} : (forall a, p a) ↔ forall a, p (ofMul a) := Iff.rfl

@[simp]
/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {p : Additive α -> Prop}
  statement: (exists a, p a) ↔ exists a, p (ofMul a)
  proof: Iff.rfl

中文:
引理 «exists»
  条件: {p : Additive α -> 命题}
  结论: (存在 a, p a) ↔ 存在 a, p (ofMul a)
  证明: Iff.rfl
-/
protected lemma «exists» {p : Additive α -> Prop} : (exists a, p a) ↔ exists a, p (ofMul a) := Iff.rfl

/-- Recursion principle for `Additive`, supported by `cases` and `induction`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {motive : Additive α -> Sort*} (ofMul : forall a, motive (ofMul a))
  body: fun a => ofMul (a.toMul)

中文:
定义 rec
  签名: {motive : Additive α -> Sort*} (ofMul : 对任意 a, motive (ofMul a))
  定义体: fun a => ofMul (a.toMul)

Depends on / 依赖: a.toMul
-/
def rec {motive : Additive α -> Sort*} (ofMul : forall a, motive (ofMul a)) : forall a, motive a :=
  fun a => ofMul (a.toMul)

end Additive

namespace Multiplicative

/-- Reinterpret `x : α` as an element of `Multiplicative α`. -/
@[implicit_reducible]
/--
Definition of `ofAdd` / `ofAdd` 的定义

English:
definition ofAdd
  signature: : α ≃ Multiplicative α
  body: ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

中文:
定义 ofAdd
  签名: : α ≃ Multiplicative α
  定义体: ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
-/
def ofAdd : α ≃ Multiplicative α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

/-- Reinterpret `x : Multiplicative α` as an element of `α`. -/
@[implicit_reducible]
/--
Definition of `toAdd` / `toAdd` 的定义

English:
definition toAdd
  signature: : Multiplicative α ≃ α
  body: ofAdd.symm

@[simp]

中文:
定义 toAdd
  签名: : Multiplicative α ≃ α
  定义体: ofAdd.symm

@[simp]

Depends on / 依赖: ofAdd.symm
-/
def toAdd : Multiplicative α ≃ α := ofAdd.symm

@[simp]
/--
theorem `ofAdd_symm_eq` / 定理 `ofAdd_symm_eq`

English:
theorem ofAdd_symm_eq
  statement: (@ofAdd α).symm = toAdd
  proof: rfl

@[simp]

中文:
定理 ofAdd_symm_eq
  结论: (@ofAdd α).symm = toAdd
  证明: rfl

@[simp]
-/
theorem ofAdd_symm_eq : (@ofAdd α).symm = toAdd :=
  rfl

@[simp]
/--
theorem `toAdd_symm_eq` / 定理 `toAdd_symm_eq`

English:
theorem toAdd_symm_eq
  statement: (@toAdd α).symm = ofAdd
  proof: rfl

中文:
定理 toAdd_symm_eq
  结论: (@toAdd α).symm = ofAdd
  证明: rfl
-/
theorem toAdd_symm_eq : (@toAdd α).symm = ofAdd :=
  rfl

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {a b : Multiplicative α} (hab : a.toAdd = b.toAdd)
  statement: a = b
  proof: hab

@[simp]

中文:
引理 ext
  条件: {a b : Multiplicative α} (hab : a.toAdd = b.toAdd)
  结论: a = b
  证明: hab

@[simp]
-/
@[ext] lemma ext {a b : Multiplicative α} (hab : a.toAdd = b.toAdd) : a = b := hab

@[simp]
/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {p : Multiplicative α -> Prop}
  statement: (forall a, p a) ↔ forall a, p (ofAdd a)
  proof: Iff.rfl

@[simp]

中文:
引理 «forall»
  条件: {p : Multiplicative α -> 命题}
  结论: (对任意 a, p a) ↔ 对任意 a, p (ofAdd a)
  证明: Iff.rfl

@[simp]
-/
protected lemma «forall» {p : Multiplicative α -> Prop} : (forall a, p a) ↔ forall a, p (ofAdd a) := Iff.rfl

@[simp]
/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {p : Multiplicative α -> Prop}
  statement: (exists a, p a) ↔ exists a, p (ofAdd a)
  proof: Iff.rfl

中文:
引理 «exists»
  条件: {p : Multiplicative α -> 命题}
  结论: (存在 a, p a) ↔ 存在 a, p (ofAdd a)
  证明: Iff.rfl
-/
protected lemma «exists» {p : Multiplicative α -> Prop} : (exists a, p a) ↔ exists a, p (ofAdd a) := Iff.rfl

/-- Recursion principle for `Multiplicative`, supported by `cases` and `induction`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {motive : Multiplicative α -> Sort*} (ofAdd : forall a, motive (ofAdd a))
  body: fun a => ofAdd (a.toAdd)

中文:
定义 rec
  签名: {motive : Multiplicative α -> Sort*} (ofAdd : 对任意 a, motive (ofAdd a))
  定义体: fun a => ofAdd (a.toAdd)

Depends on / 依赖: a.toAdd
-/
def rec {motive : Multiplicative α -> Sort*} (ofAdd : forall a, motive (ofAdd a)) : forall a, motive a :=
  fun a => ofAdd (a.toAdd)

end Multiplicative

open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

@[simp]
/--
theorem `toAdd_ofAdd` / 定理 `toAdd_ofAdd`

English:
theorem toAdd_ofAdd
  given: (x : α)
  statement: (ofAdd x).toAdd = x
  proof: rfl

@[simp]

中文:
定理 toAdd_ofAdd
  条件: (x : α)
  结论: (ofAdd x).toAdd = x
  证明: rfl

@[simp]
-/
theorem toAdd_ofAdd (x : α) : (ofAdd x).toAdd = x :=
  rfl

@[simp]
/--
theorem `ofAdd_toAdd` / 定理 `ofAdd_toAdd`

English:
theorem ofAdd_toAdd
  given: (x : Multiplicative α)
  statement: ofAdd x.toAdd = x
  proof: rfl

@[simp]

中文:
定理 ofAdd_toAdd
  条件: (x : Multiplicative α)
  结论: ofAdd x.toAdd = x
  证明: rfl

@[simp]
-/
theorem ofAdd_toAdd (x : Multiplicative α) : ofAdd x.toAdd = x :=
  rfl

@[simp]
/--
theorem `toMul_ofMul` / 定理 `toMul_ofMul`

English:
theorem toMul_ofMul
  given: (x : α)
  statement: (ofMul x).toMul = x
  proof: rfl

@[simp]

中文:
定理 toMul_ofMul
  条件: (x : α)
  结论: (ofMul x).toMul = x
  证明: rfl

@[simp]
-/
theorem toMul_ofMul (x : α) : (ofMul x).toMul = x :=
  rfl

@[simp]
/--
theorem `ofMul_toMul` / 定理 `ofMul_toMul`

English:
theorem ofMul_toMul
  given: (x : Additive α)
  statement: ofMul x.toMul = x
  proof: rfl

中文:
定理 ofMul_toMul
  条件: (x : Additive α)
  结论: ofMul x.toMul = x
  证明: rfl
-/
theorem ofMul_toMul (x : Additive α) : ofMul x.toMul = x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : Subsingleton (Additive α)
  body: toMul.injective.subsingleton

中文:
实例 [Subsingleton
  签名: α] : Subsingleton (Additive α)
  定义体: toMul.injective.subsingleton

Depends on / 依赖: injective, subsingleton, toMul.injective.subsingleton
-/
instance [Subsingleton α] : Subsingleton (Additive α) := toMul.injective.subsingleton
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : Subsingleton (Multiplicative α)
  body: toAdd.injective.subsingleton

中文:
实例 [Subsingleton
  签名: α] : Subsingleton (Multiplicative α)
  定义体: toAdd.injective.subsingleton

Depends on / 依赖: injective, subsingleton, toAdd.injective.subsingleton
-/
instance [Subsingleton α] : Subsingleton (Multiplicative α) := toAdd.injective.subsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Additive α)
  body: ⟨ofMul default⟩

中文:
实例 [Inhabited
  签名: α] : Inhabited (Additive α)
  定义体: ⟨ofMul default⟩
-/
instance [Inhabited α] : Inhabited (Additive α) :=
  ⟨ofMul default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Multiplicative α)
  body: ⟨ofAdd default⟩

中文:
实例 [Inhabited
  签名: α] : Inhabited (Multiplicative α)
  定义体: ⟨ofAdd default⟩
-/
instance [Inhabited α] : Inhabited (Multiplicative α) :=
  ⟨ofAdd default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: α] : Unique (Additive α)
  body: toMul.unique

中文:
实例 [Unique
  签名: α] : Unique (Additive α)
  定义体: toMul.unique

Depends on / 依赖: toMul.unique, unique
-/
instance [Unique α] : Unique (Additive α) := toMul.unique
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: α] : Unique (Multiplicative α)
  body: toAdd.unique

中文:
实例 [Unique
  签名: α] : Unique (Multiplicative α)
  定义体: toAdd.unique

Depends on / 依赖: toAdd.unique, unique
-/
instance [Unique α] : Unique (Multiplicative α) := toAdd.unique

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : DecidableEq α] : DecidableEq (Multiplicative α)
  body: h

中文:
实例 [h
  签名: : DecidableEq α] : DecidableEq (Multiplicative α)
  定义体: h
-/
instance [h : DecidableEq α] : DecidableEq (Multiplicative α) := h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : DecidableEq α] : DecidableEq (Additive α)
  body: h

中文:
实例 [h
  签名: : DecidableEq α] : DecidableEq (Additive α)
  定义体: h
-/
instance [h : DecidableEq α] : DecidableEq (Additive α) := h

/--
Instance `Additive.instNontrivial` / 实例 `Additive.instNontrivial`

English:
instance Additive.instNontrivial
  signature: [Nontrivial α]
  body: ofMul.injective.nontrivial

中文:
实例 Additive.instNontrivial
  签名: [Nontrivial α]
  定义体: ofMul.injective.nontrivial

Depends on / 依赖: injective, nontrivial, ofMul.injective.nontrivial
-/
instance Additive.instNontrivial [Nontrivial α] : Nontrivial (Additive α) :=
  ofMul.injective.nontrivial

/--
Instance `Multiplicative.instNontrivial` / 实例 `Multiplicative.instNontrivial`

English:
instance Multiplicative.instNontrivial
  signature: [Nontrivial α]
  body: ofAdd.injective.nontrivial

中文:
实例 Multiplicative.instNontrivial
  签名: [Nontrivial α]
  定义体: ofAdd.injective.nontrivial

Depends on / 依赖: injective, nontrivial, ofAdd.injective.nontrivial
-/
instance Multiplicative.instNontrivial [Nontrivial α] : Nontrivial (Multiplicative α) :=
  ofAdd.injective.nontrivial

/--
Instance `Additive.add` / 实例 `Additive.add`

English:
instance Additive.add
  signature: [Mul α]
  body: ofMul (x.toMul * y.toMul)

中文:
实例 Additive.add
  签名: [Mul α]
  定义体: ofMul (x.toMul * y.toMul)

Depends on / 依赖: x.toMul, y.toMul
-/
instance Additive.add [Mul α] : Add (Additive α) where
  add x y := ofMul (x.toMul * y.toMul)

/--
Instance `Multiplicative.mul` / 实例 `Multiplicative.mul`

English:
instance Multiplicative.mul
  signature: [Add α]
  body: ofAdd (x.toAdd + y.toAdd)

@[simp]

中文:
实例 Multiplicative.mul
  签名: [Add α]
  定义体: ofAdd (x.toAdd + y.toAdd)

@[simp]

Depends on / 依赖: x.toAdd, y.toAdd
-/
instance Multiplicative.mul [Add α] : Mul (Multiplicative α) where
  mul x y := ofAdd (x.toAdd + y.toAdd)

@[simp]
/--
theorem `ofAdd_add` / 定理 `ofAdd_add`

English:
theorem ofAdd_add
  given: [Add α] (x y : α)
  statement: ofAdd (x + y) = ofAdd x * ofAdd y
  proof: rfl

@[simp]

中文:
定理 ofAdd_add
  条件: [Add α] (x y : α)
  结论: ofAdd (x + y) = ofAdd x * ofAdd y
  证明: rfl

@[simp]
-/
theorem ofAdd_add [Add α] (x y : α) : ofAdd (x + y) = ofAdd x * ofAdd y := rfl

@[simp]
/--
theorem `toAdd_mul` / 定理 `toAdd_mul`

English:
theorem toAdd_mul
  given: [Add α] (x y : Multiplicative α)
  statement: (x * y).toAdd = x.toAdd + y.toAdd
  proof: rfl

@[simp]

中文:
定理 toAdd_mul
  条件: [Add α] (x y : Multiplicative α)
  结论: (x * y).toAdd = x.toAdd + y.toAdd
  证明: rfl

@[simp]
-/
theorem toAdd_mul [Add α] (x y : Multiplicative α) : (x * y).toAdd = x.toAdd + y.toAdd := rfl

@[simp]
/--
theorem `ofMul_mul` / 定理 `ofMul_mul`

English:
theorem ofMul_mul
  given: [Mul α] (x y : α)
  statement: ofMul (x * y) = ofMul x + ofMul y
  proof: rfl

@[simp]

中文:
定理 ofMul_mul
  条件: [Mul α] (x y : α)
  结论: ofMul (x * y) = ofMul x + ofMul y
  证明: rfl

@[simp]
-/
theorem ofMul_mul [Mul α] (x y : α) : ofMul (x * y) = ofMul x + ofMul y := rfl

@[simp]
/--
theorem `toMul_add` / 定理 `toMul_add`

English:
theorem toMul_add
  given: [Mul α] (x y : Additive α)
  statement: (x + y).toMul = x.toMul * y.toMul
  proof: rfl

中文:
定理 toMul_add
  条件: [Mul α] (x y : Additive α)
  结论: (x + y).toMul = x.toMul * y.toMul
  证明: rfl
-/
theorem toMul_add [Mul α] (x y : Additive α) : (x + y).toMul = x.toMul * y.toMul := rfl

/--
Instance `Additive.addSemigroup` / 实例 `Additive.addSemigroup`

English:
instance Additive.addSemigroup
  signature: [Semigroup α]
  body: { Additive.add with add_assoc := @mul_assoc α _ }

中文:
实例 Additive.addSemigroup
  签名: [Semigroup α]
  定义体: { Additive.add with add_assoc := @mul_assoc α _ }

Depends on / 依赖: Additive, Additive.add, add_assoc, mul_assoc
-/
instance Additive.addSemigroup [Semigroup α] : AddSemigroup (Additive α) :=
  { Additive.add with add_assoc := @mul_assoc α _ }

/--
Instance `Multiplicative.semigroup` / 实例 `Multiplicative.semigroup`

English:
instance Multiplicative.semigroup
  signature: [AddSemigroup α]
  body: { Multiplicative.mul with mul_assoc := @add_assoc α _ }

中文:
实例 Multiplicative.semigroup
  签名: [AddSemigroup α]
  定义体: { Multiplicative.mul with mul_assoc := @add_assoc α _ }

Depends on / 依赖: Multiplicative, Multiplicative.mul, add_assoc, mul_assoc
-/
instance Multiplicative.semigroup [AddSemigroup α] : Semigroup (Multiplicative α) :=
  { Multiplicative.mul with mul_assoc := @add_assoc α _ }

/--
Instance `Additive.addCommSemigroup` / 实例 `Additive.addCommSemigroup`

English:
instance Additive.addCommSemigroup
  signature: [CommSemigroup α]
  body: { Additive.addSemigroup with add_comm := @mul_comm α _ }

中文:
实例 Additive.addCommSemigroup
  签名: [CommSemigroup α]
  定义体: { Additive.addSemigroup with add_comm := @mul_comm α _ }

Depends on / 依赖: Additive, Additive.addSemigroup, addSemigroup, add_comm, mul_comm
-/
instance Additive.addCommSemigroup [CommSemigroup α] : AddCommSemigroup (Additive α) :=
  { Additive.addSemigroup with add_comm := @mul_comm α _ }

/--
Instance `Multiplicative.commSemigroup` / 实例 `Multiplicative.commSemigroup`

English:
instance Multiplicative.commSemigroup
  signature: [AddCommSemigroup α]
  body: { Multiplicative.semigroup with mul_comm := @add_comm α _ }

中文:
实例 Multiplicative.commSemigroup
  签名: [AddCommSemigroup α]
  定义体: { Multiplicative.semigroup with mul_comm := @add_comm α _ }

Depends on / 依赖: Multiplicative, Multiplicative.semigroup, add_comm, mul_comm, semigroup
-/
instance Multiplicative.commSemigroup [AddCommSemigroup α] : CommSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup with mul_comm := @add_comm α _ }

/--
Instance `Additive.isLeftCancelAdd` / 实例 `Additive.isLeftCancelAdd`

English:
instance Additive.isLeftCancelAdd
  signature: [Mul α] [IsLeftCancelMul α]
  body: ⟨@mul_left_cancel α _ _⟩

中文:
实例 Additive.isLeftCancelAdd
  签名: [Mul α] [IsLeftCancelMul α]
  定义体: ⟨@mul_left_cancel α _ _⟩

Depends on / 依赖: mul_left_cancel
-/
instance Additive.isLeftCancelAdd [Mul α] [IsLeftCancelMul α] : IsLeftCancelAdd (Additive α) :=
  ⟨@mul_left_cancel α _ _⟩

/--
Instance `Multiplicative.isLeftCancelMul` / 实例 `Multiplicative.isLeftCancelMul`

English:
instance Multiplicative.isLeftCancelMul
  signature: [Add α] [IsLeftCancelAdd α]
  body: ⟨@add_left_cancel α _ _⟩

中文:
实例 Multiplicative.isLeftCancelMul
  签名: [Add α] [IsLeftCancelAdd α]
  定义体: ⟨@add_left_cancel α _ _⟩

Depends on / 依赖: add_left_cancel
-/
instance Multiplicative.isLeftCancelMul [Add α] [IsLeftCancelAdd α] :
    IsLeftCancelMul (Multiplicative α) :=
  ⟨@add_left_cancel α _ _⟩

/--
Instance `Additive.isRightCancelAdd` / 实例 `Additive.isRightCancelAdd`

English:
instance Additive.isRightCancelAdd
  signature: [Mul α] [IsRightCancelMul α]
  body: ⟨fun _ _ _ => mul_right_cancel (G := α)⟩

中文:
实例 Additive.isRightCancelAdd
  签名: [Mul α] [IsRightCancelMul α]
  定义体: ⟨fun _ _ _ => mul_right_cancel (G := α)⟩

Depends on / 依赖: mul_right_cancel
-/
instance Additive.isRightCancelAdd [Mul α] [IsRightCancelMul α] : IsRightCancelAdd (Additive α) :=
  ⟨fun _ _ _ => mul_right_cancel (G := α)⟩

/--
Instance `Multiplicative.isRightCancelMul` / 实例 `Multiplicative.isRightCancelMul`

English:
instance Multiplicative.isRightCancelMul
  signature: [Add α] [IsRightCancelAdd α]
  body: ⟨fun _ _ _ => add_right_cancel (G := α)⟩

中文:
实例 Multiplicative.isRightCancelMul
  签名: [Add α] [IsRightCancelAdd α]
  定义体: ⟨fun _ _ _ => add_right_cancel (G := α)⟩

Depends on / 依赖: add_right_cancel
-/
instance Multiplicative.isRightCancelMul [Add α] [IsRightCancelAdd α] :
    IsRightCancelMul (Multiplicative α) :=
  ⟨fun _ _ _ => add_right_cancel (G := α)⟩

/--
Instance `Additive.isCancelAdd` / 实例 `Additive.isCancelAdd`

English:
instance Additive.isCancelAdd
  signature: [Mul α] [IsCancelMul α]
  body: ⟨⟩

中文:
实例 Additive.isCancelAdd
  签名: [Mul α] [IsCancelMul α]
  定义体: ⟨⟩
-/
instance Additive.isCancelAdd [Mul α] [IsCancelMul α] : IsCancelAdd (Additive α) :=
  ⟨⟩

/--
Instance `Multiplicative.isCancelMul` / 实例 `Multiplicative.isCancelMul`

English:
instance Multiplicative.isCancelMul
  signature: [Add α] [IsCancelAdd α]
  body: ⟨⟩

中文:
实例 Multiplicative.isCancelMul
  签名: [Add α] [IsCancelAdd α]
  定义体: ⟨⟩
-/
instance Multiplicative.isCancelMul [Add α] [IsCancelAdd α] : IsCancelMul (Multiplicative α) :=
  ⟨⟩

/--
Instance `Additive.addLeftCancelSemigroup` / 实例 `Additive.addLeftCancelSemigroup`

English:
instance Additive.addLeftCancelSemigroup
  signature: [LeftCancelSemigroup α]
  body: { Additive.addSemigroup, Additive.isLeftCancelAdd with }

中文:
实例 Additive.addLeftCancelSemigroup
  签名: [LeftCancelSemigroup α]
  定义体: { Additive.addSemigroup, Additive.isLeftCancelAdd with }

Depends on / 依赖: Additive, Additive.addSemigroup, Additive.isLeftCancelAdd, addSemigroup, isLeftCancelAdd
-/
instance Additive.addLeftCancelSemigroup [LeftCancelSemigroup α] :
    AddLeftCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.isLeftCancelAdd with }

/--
Instance `Multiplicative.leftCancelSemigroup` / 实例 `Multiplicative.leftCancelSemigroup`

English:
instance Multiplicative.leftCancelSemigroup
  signature: [AddLeftCancelSemigroup α]
  body: { Multiplicative.semigroup, Multiplicative.isLeftCancelMul with }

中文:
实例 Multiplicative.leftCancelSemigroup
  签名: [AddLeftCancelSemigroup α]
  定义体: { Multiplicative.semigroup, Multiplicative.isLeftCancelMul with }

Depends on / 依赖: Multiplicative, Multiplicative.isLeftCancelMul, Multiplicative.semigroup, isLeftCancelMul, semigroup
-/
instance Multiplicative.leftCancelSemigroup [AddLeftCancelSemigroup α] :
    LeftCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.isLeftCancelMul with }

/--
Instance `Additive.addRightCancelSemigroup` / 实例 `Additive.addRightCancelSemigroup`

English:
instance Additive.addRightCancelSemigroup
  signature: [RightCancelSemigroup α]
  body: { Additive.addSemigroup, Additive.isRightCancelAdd with }

中文:
实例 Additive.addRightCancelSemigroup
  签名: [RightCancelSemigroup α]
  定义体: { Additive.addSemigroup, Additive.isRightCancelAdd with }

Depends on / 依赖: Additive, Additive.addSemigroup, Additive.isRightCancelAdd, addSemigroup, isRightCancelAdd
-/
instance Additive.addRightCancelSemigroup [RightCancelSemigroup α] :
    AddRightCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.isRightCancelAdd with }

/--
Instance `Multiplicative.rightCancelSemigroup` / 实例 `Multiplicative.rightCancelSemigroup`

English:
instance Multiplicative.rightCancelSemigroup
  signature: [AddRightCancelSemigroup α]
  body: { Multiplicative.semigroup, Multiplicative.isRightCancelMul with }

中文:
实例 Multiplicative.rightCancelSemigroup
  签名: [AddRightCancelSemigroup α]
  定义体: { Multiplicative.semigroup, Multiplicative.isRightCancelMul with }

Depends on / 依赖: Multiplicative, Multiplicative.isRightCancelMul, Multiplicative.semigroup, isRightCancelMul, semigroup
-/
instance Multiplicative.rightCancelSemigroup [AddRightCancelSemigroup α] :
    RightCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.isRightCancelMul with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: α] : Zero (Additive α)
  body: ⟨Additive.ofMul 1⟩

@[simp]

中文:
实例 [One
  签名: α] : Zero (Additive α)
  定义体: ⟨Additive.ofMul 1⟩

@[simp]

Depends on / 依赖: Additive, Additive.ofMul
-/
instance [One α] : Zero (Additive α) :=
  ⟨Additive.ofMul 1⟩

@[simp]
/--
theorem `ofMul_one` / 定理 `ofMul_one`

English:
theorem ofMul_one
  given: [One α]
  statement: @Additive.ofMul α 1 = 0
  proof: rfl

@[simp]

中文:
定理 ofMul_one
  条件: [One α]
  结论: @Additive.ofMul α 1 = 0
  证明: rfl

@[simp]
-/
theorem ofMul_one [One α] : @Additive.ofMul α 1 = 0 := rfl

@[simp]
/--
theorem `ofMul_eq_zero` / 定理 `ofMul_eq_zero`

English:
theorem ofMul_eq_zero
  given: {A : Type*} [One A] {x : A}
  statement: Additive.ofMul x = 0 ↔ x = 1
  proof: Iff.rfl

@[simp]

中文:
定理 ofMul_eq_zero
  条件: {A : 类型} [One A] {x : A}
  结论: Additive.ofMul x = 0 ↔ x = 1
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem ofMul_eq_zero {A : Type*} [One A] {x : A} : Additive.ofMul x = 0 ↔ x = 1 := Iff.rfl

@[simp]
/--
theorem `toMul_zero` / 定理 `toMul_zero`

English:
theorem toMul_zero
  given: [One α]
  statement: (0 : Additive α).toMul = 1
  proof: rfl

@[simp]

中文:
定理 toMul_zero
  条件: [One α]
  结论: (0 : Additive α).toMul = 1
  证明: rfl

@[simp]
-/
theorem toMul_zero [One α] : (0 : Additive α).toMul = 1 := rfl

@[simp]
/--
lemma `toMul_eq_one` / 引理 `toMul_eq_one`

English:
lemma toMul_eq_one
  given: {α : Type*} [One α] {x : Additive α}
  proof: Iff.rfl

中文:
引理 toMul_eq_one
  条件: {α : 类型} [One α] {x : Additive α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma toMul_eq_one {α : Type*} [One α] {x : Additive α} :
    x.toMul = 1 ↔ x = 0 :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: α] : One (Multiplicative α)
  body: ⟨Multiplicative.ofAdd 0⟩

@[simp]

中文:
实例 [Zero
  签名: α] : One (Multiplicative α)
  定义体: ⟨Multiplicative.ofAdd 0⟩

@[simp]

Depends on / 依赖: Multiplicative, Multiplicative.ofAdd
-/
instance [Zero α] : One (Multiplicative α) :=
  ⟨Multiplicative.ofAdd 0⟩

@[simp]
/--
theorem `ofAdd_zero` / 定理 `ofAdd_zero`

English:
theorem ofAdd_zero
  given: [Zero α]
  statement: @Multiplicative.ofAdd α 0 = 1
  proof: rfl

@[simp]

中文:
定理 ofAdd_zero
  条件: [Zero α]
  结论: @Multiplicative.ofAdd α 0 = 1
  证明: rfl

@[simp]
-/
theorem ofAdd_zero [Zero α] : @Multiplicative.ofAdd α 0 = 1 :=
  rfl

@[simp]
/--
theorem `ofAdd_eq_one` / 定理 `ofAdd_eq_one`

English:
theorem ofAdd_eq_one
  given: {A : Type*} [Zero A] {x : A}
  statement: Multiplicative.ofAdd x = 1 ↔ x = 0
  proof: Iff.rfl

@[simp]

中文:
定理 ofAdd_eq_one
  条件: {A : 类型} [Zero A] {x : A}
  结论: Multiplicative.ofAdd x = 1 ↔ x = 0
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem ofAdd_eq_one {A : Type*} [Zero A] {x : A} : Multiplicative.ofAdd x = 1 ↔ x = 0 :=
  Iff.rfl

@[simp]
/--
theorem `toAdd_one` / 定理 `toAdd_one`

English:
theorem toAdd_one
  given: [Zero α]
  statement: (1 : Multiplicative α).toAdd = 0
  proof: rfl

@[simp]

中文:
定理 toAdd_one
  条件: [Zero α]
  结论: (1 : Multiplicative α).toAdd = 0
  证明: rfl

@[simp]
-/
theorem toAdd_one [Zero α] : (1 : Multiplicative α).toAdd = 0 :=
  rfl

@[simp]
/--
lemma `toAdd_eq_zero` / 引理 `toAdd_eq_zero`

English:
lemma toAdd_eq_zero
  given: {α : Type*} [Zero α] {x : Multiplicative α}
  proof: Iff.rfl

中文:
引理 toAdd_eq_zero
  条件: {α : 类型} [Zero α] {x : Multiplicative α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma toAdd_eq_zero {α : Type*} [Zero α] {x : Multiplicative α} :
    x.toAdd = 0 ↔ x = 1 :=
  Iff.rfl

/--
Instance `Additive.addZeroClass` / 实例 `Additive.addZeroClass`

English:
instance Additive.addZeroClass
  signature: [MulOneClass α]
  body: @one_mul α _
  add_zero := @mul_one α _

中文:
实例 Additive.addZeroClass
  签名: [MulOneClass α]
  定义体: @one_mul α _
  add_zero := @mul_one α _

Depends on / 依赖: one_mul
-/
instance Additive.addZeroClass [MulOneClass α] : AddZeroClass (Additive α) where
  zero_add := @one_mul α _
  add_zero := @mul_one α _

/--
Instance `Multiplicative.mulOneClass` / 实例 `Multiplicative.mulOneClass`

English:
instance Multiplicative.mulOneClass
  signature: [AddZeroClass α]
  body: @zero_add α _
  mul_one := @add_zero α _

中文:
实例 Multiplicative.mulOneClass
  签名: [AddZeroClass α]
  定义体: @zero_add α _
  mul_one := @add_zero α _

Depends on / 依赖: zero_add
-/
instance Multiplicative.mulOneClass [AddZeroClass α] : MulOneClass (Multiplicative α) where
  one_mul := @zero_add α _
  mul_one := @add_zero α _

/--
Instance `Additive.addMonoid` / 实例 `Additive.addMonoid`

English:
instance Additive.addMonoid
  signature: [h : Monoid α]
  body: ofMul (a.toMul ^ n)
  nsmul_zero := h.npow_zero
  nsmul_succ := h.npow_succ

中文:
实例 Additive.addMonoid
  签名: [h : Monoid α]
  定义体: ofMul (a.toMul ^ n)
  nsmul_zero := h.npow_zero
  nsmul_succ := h.npow_succ

Depends on / 依赖: a.toMul
-/
instance Additive.addMonoid [h : Monoid α] : AddMonoid (Additive α) where
  nsmul n a := ofMul (a.toMul ^ n)
  nsmul_zero := h.npow_zero
  nsmul_succ := h.npow_succ

/--
Instance `Multiplicative.monoid` / 实例 `Multiplicative.monoid`

English:
instance Multiplicative.monoid
  signature: [h : AddMonoid α]
  body: ofAdd (n • a.toAdd)
  npow_zero := h.nsmul_zero
  npow_succ := h.nsmul_succ

@[simp]

中文:
实例 Multiplicative.monoid
  签名: [h : AddMonoid α]
  定义体: ofAdd (n • a.toAdd)
  npow_zero := h.nsmul_zero
  npow_succ := h.nsmul_succ

@[simp]

Depends on / 依赖: a.toAdd
-/
instance Multiplicative.monoid [h : AddMonoid α] : Monoid (Multiplicative α) where
  npow n a := ofAdd (n • a.toAdd)
  npow_zero := h.nsmul_zero
  npow_succ := h.nsmul_succ

@[simp]
/--
theorem `ofMul_pow` / 定理 `ofMul_pow`

English:
theorem ofMul_pow
  given: [Monoid α] (n : Nat) (a : α)
  statement: ofMul (a ^ n) = n • ofMul a
  proof: rfl

@[simp]

中文:
定理 ofMul_pow
  条件: [Monoid α] (n : 自然数) (a : α)
  结论: ofMul (a ^ n) = n • ofMul a
  证明: rfl

@[simp]
-/
theorem ofMul_pow [Monoid α] (n : Nat) (a : α) : ofMul (a ^ n) = n • ofMul a :=
  rfl

@[simp]
/--
theorem `toMul_nsmul` / 定理 `toMul_nsmul`

English:
theorem toMul_nsmul
  given: [Monoid α] (n : Nat) (a : Additive α)
  statement: (n • a).toMul = a.toMul ^ n
  proof: rfl

@[simp]

中文:
定理 toMul_nsmul
  条件: [Monoid α] (n : 自然数) (a : Additive α)
  结论: (n • a).toMul = a.toMul ^ n
  证明: rfl

@[simp]
-/
theorem toMul_nsmul [Monoid α] (n : Nat) (a : Additive α) : (n • a).toMul = a.toMul ^ n :=
  rfl

@[simp]
/--
theorem `ofAdd_nsmul` / 定理 `ofAdd_nsmul`

English:
theorem ofAdd_nsmul
  given: [AddMonoid α] (n : Nat) (a : α)
  statement: ofAdd (n • a) = ofAdd a ^ n
  proof: rfl

@[simp]

中文:
定理 ofAdd_nsmul
  条件: [AddMonoid α] (n : 自然数) (a : α)
  结论: ofAdd (n • a) = ofAdd a ^ n
  证明: rfl

@[simp]
-/
theorem ofAdd_nsmul [AddMonoid α] (n : Nat) (a : α) : ofAdd (n • a) = ofAdd a ^ n :=
  rfl

@[simp]
/--
theorem `toAdd_pow` / 定理 `toAdd_pow`

English:
theorem toAdd_pow
  given: [AddMonoid α] (a : Multiplicative α) (n : Nat)
  statement: (a ^ n).toAdd = n • a.toAdd
  proof: rfl

中文:
定理 toAdd_pow
  条件: [AddMonoid α] (a : Multiplicative α) (n : 自然数)
  结论: (a ^ n).toAdd = n • a.toAdd
  证明: rfl
-/
theorem toAdd_pow [AddMonoid α] (a : Multiplicative α) (n : Nat) : (a ^ n).toAdd = n • a.toAdd :=
  rfl

section Monoid
variable [Monoid α]

@[simp]
/--
lemma `isAddLeftRegular_ofMul` / 引理 `isAddLeftRegular_ofMul`

English:
lemma isAddLeftRegular_ofMul
  given: {a : α}
  statement: IsAddLeftRegular (Additive.ofMul a) ↔ IsLeftRegular a
  proof: .rfl

@[simp]

中文:
引理 isAddLeftRegular_ofMul
  条件: {a : α}
  结论: IsAddLeftRegular (Additive.ofMul a) ↔ IsLeftRegular a
  证明: .rfl

@[simp]
-/
lemma isAddLeftRegular_ofMul {a : α} : IsAddLeftRegular (Additive.ofMul a) ↔ IsLeftRegular a := .rfl

@[simp]
/--
lemma `isLeftRegular_toMul` / 引理 `isLeftRegular_toMul`

English:
lemma isLeftRegular_toMul
  given: {a : Additive α}
  statement: IsLeftRegular a.toMul ↔ IsAddLeftRegular a
  proof: .rfl

@[simp]

中文:
引理 isLeftRegular_toMul
  条件: {a : Additive α}
  结论: IsLeftRegular a.toMul ↔ IsAddLeftRegular a
  证明: .rfl

@[simp]
-/
lemma isLeftRegular_toMul {a : Additive α} : IsLeftRegular a.toMul ↔ IsAddLeftRegular a := .rfl

@[simp]
/--
lemma `isAddRightRegular_ofMul` / 引理 `isAddRightRegular_ofMul`

English:
lemma isAddRightRegular_ofMul
  given: {a : α}
  statement: IsAddRightRegular (Additive.ofMul a) ↔ IsRightRegular a
  proof: .rfl

@[simp]

中文:
引理 isAddRightRegular_ofMul
  条件: {a : α}
  结论: IsAddRightRegular (Additive.ofMul a) ↔ IsRightRegular a
  证明: .rfl

@[simp]
-/
lemma isAddRightRegular_ofMul {a : α} : IsAddRightRegular (Additive.ofMul a) ↔ IsRightRegular a :=
  .rfl

@[simp]
/--
lemma `isRightRegular_toMul` / 引理 `isRightRegular_toMul`

English:
lemma isRightRegular_toMul
  given: {a : Additive α}
  statement: IsRightRegular a.toMul ↔ IsAddRightRegular a
  proof: .rfl

中文:
引理 isRightRegular_toMul
  条件: {a : Additive α}
  结论: IsRightRegular a.toMul ↔ IsAddRightRegular a
  证明: .rfl
-/
lemma isRightRegular_toMul {a : Additive α} : IsRightRegular a.toMul ↔ IsAddRightRegular a := .rfl

/--
lemma `isAddRegular_ofMul` / 引理 `isAddRegular_ofMul`

English:
lemma isAddRegular_ofMul
  given: {a : α}
  statement: IsAddRegular (Additive.ofMul a) ↔ IsRegular a
  proof: by
  simp [isAddRegular_iff, isRegular_iff]

中文:
引理 isAddRegular_ofMul
  条件: {a : α}
  结论: IsAddRegular (Additive.ofMul a) ↔ IsRegular a
  证明: by
  simp [isAddRegular_iff, isRegular_iff]
-/
@[simp] lemma isAddRegular_ofMul {a : α} : IsAddRegular (Additive.ofMul a) ↔ IsRegular a := by
  simp [isAddRegular_iff, isRegular_iff]

/--
lemma `isRegular_toMul` / 引理 `isRegular_toMul`

English:
lemma isRegular_toMul
  given: {a : Additive α}
  statement: IsRegular a.toMul ↔ IsAddRegular a
  proof: by
  simp [isAddRegular_iff, isRegular_iff]

中文:
引理 isRegular_toMul
  条件: {a : Additive α}
  结论: IsRegular a.toMul ↔ IsAddRegular a
  证明: by
  simp [isAddRegular_iff, isRegular_iff]
-/
@[simp] lemma isRegular_toMul {a : Additive α} : IsRegular a.toMul ↔ IsAddRegular a := by
  simp [isAddRegular_iff, isRegular_iff]

end Monoid

section AddMonoid
variable [AddMonoid α]

@[simp]
/--
lemma `isLeftRegular_ofAdd` / 引理 `isLeftRegular_ofAdd`

English:
lemma isLeftRegular_ofAdd
  given: {a : α}
  statement: IsLeftRegular (Multiplicative.ofAdd a) ↔ IsAddLeftRegular a
  proof: .rfl

@[simp]

中文:
引理 isLeftRegular_ofAdd
  条件: {a : α}
  结论: IsLeftRegular (Multiplicative.ofAdd a) ↔ IsAddLeftRegular a
  证明: .rfl

@[simp]
-/
lemma isLeftRegular_ofAdd {a : α} : IsLeftRegular (Multiplicative.ofAdd a) ↔ IsAddLeftRegular a :=
  .rfl

@[simp]
/--
lemma `isAddLeftRegular_toAdd` / 引理 `isAddLeftRegular_toAdd`

English:
lemma isAddLeftRegular_toAdd
  given: {a : Multiplicative α}
  statement: IsAddLeftRegular a.toAdd ↔ IsLeftRegular a
  proof: .rfl

@[simp]

中文:
引理 isAddLeftRegular_toAdd
  条件: {a : Multiplicative α}
  结论: IsAddLeftRegular a.toAdd ↔ IsLeftRegular a
  证明: .rfl

@[simp]
-/
lemma isAddLeftRegular_toAdd {a : Multiplicative α} : IsAddLeftRegular a.toAdd ↔ IsLeftRegular a :=
  .rfl

@[simp]
/--
lemma `isRightRegular_ofAdd` / 引理 `isRightRegular_ofAdd`

English:
lemma isRightRegular_ofAdd
  given: {a : α}
  proof: .rfl

中文:
引理 isRightRegular_ofAdd
  条件: {a : α}
  证明: .rfl
-/
lemma isRightRegular_ofAdd {a : α} :
    IsRightRegular (Multiplicative.ofAdd a) ↔ IsAddRightRegular a := .rfl

/--
lemma `isAddRightRegular_toAdd` / 引理 `isAddRightRegular_toAdd`

English:
lemma isAddRightRegular_toAdd
  given: {a : Multiplicative α}
  proof: .rfl

中文:
引理 isAddRightRegular_toAdd
  条件: {a : Multiplicative α}
  证明: .rfl
-/
@[simp] lemma isAddRightRegular_toAdd {a : Multiplicative α} :
    IsAddRightRegular a.toAdd ↔ IsRightRegular a := .rfl

/--
lemma `isRegular_ofAdd` / 引理 `isRegular_ofAdd`

English:
lemma isRegular_ofAdd
  given: {a : α}
  statement: IsRegular (Multiplicative.ofAdd a) ↔ IsAddRegular a
  proof: by
  simp [isAddRegular_iff, isRegular_iff]

中文:
引理 isRegular_ofAdd
  条件: {a : α}
  结论: IsRegular (Multiplicative.ofAdd a) ↔ IsAddRegular a
  证明: by
  simp [isAddRegular_iff, isRegular_iff]
-/
@[simp] lemma isRegular_ofAdd {a : α} : IsRegular (Multiplicative.ofAdd a) ↔ IsAddRegular a := by
  simp [isAddRegular_iff, isRegular_iff]

/--
lemma `isAddRegular_toAdd` / 引理 `isAddRegular_toAdd`

English:
lemma isAddRegular_toAdd
  given: {a : Multiplicative α}
  statement: IsAddRegular a.toAdd ↔ IsRegular a
  proof: by
  simp [isAddRegular_iff, isRegular_iff]

中文:
引理 isAddRegular_toAdd
  条件: {a : Multiplicative α}
  结论: IsAddRegular a.toAdd ↔ IsRegular a
  证明: by
  simp [isAddRegular_iff, isRegular_iff]
-/
@[simp] lemma isAddRegular_toAdd {a : Multiplicative α} : IsAddRegular a.toAdd ↔ IsRegular a := by
  simp [isAddRegular_iff, isRegular_iff]

end AddMonoid

/--
Instance `Additive.addLeftCancelMonoid` / 实例 `Additive.addLeftCancelMonoid`

English:
instance Additive.addLeftCancelMonoid
  signature: [LeftCancelMonoid α]
  body: { Additive.addMonoid, Additive.addLeftCancelSemigroup with }

中文:
实例 Additive.addLeftCancelMonoid
  签名: [LeftCancelMonoid α]
  定义体: { Additive.addMonoid, Additive.addLeftCancelSemigroup with }

Depends on / 依赖: Additive, Additive.addLeftCancelSemigroup, Additive.addMonoid, addLeftCancelSemigroup, addMonoid
-/
instance Additive.addLeftCancelMonoid [LeftCancelMonoid α] : AddLeftCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addLeftCancelSemigroup with }

/--
Instance `Multiplicative.leftCancelMonoid` / 实例 `Multiplicative.leftCancelMonoid`

English:
instance Multiplicative.leftCancelMonoid
  signature: [AddLeftCancelMonoid α]
  body: { Multiplicative.monoid, Multiplicative.leftCancelSemigroup with }

中文:
实例 Multiplicative.leftCancelMonoid
  签名: [AddLeftCancelMonoid α]
  定义体: { Multiplicative.monoid, Multiplicative.leftCancelSemigroup with }

Depends on / 依赖: Multiplicative, Multiplicative.leftCancelSemigroup, Multiplicative.monoid, leftCancelSemigroup, monoid
-/
instance Multiplicative.leftCancelMonoid [AddLeftCancelMonoid α] :
    LeftCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.leftCancelSemigroup with }

/--
Instance `Additive.addRightCancelMonoid` / 实例 `Additive.addRightCancelMonoid`

English:
instance Additive.addRightCancelMonoid
  signature: [RightCancelMonoid α]
  body: { Additive.addMonoid, Additive.addRightCancelSemigroup with }

中文:
实例 Additive.addRightCancelMonoid
  签名: [RightCancelMonoid α]
  定义体: { Additive.addMonoid, Additive.addRightCancelSemigroup with }

Depends on / 依赖: Additive, Additive.addMonoid, Additive.addRightCancelSemigroup, addMonoid, addRightCancelSemigroup
-/
instance Additive.addRightCancelMonoid [RightCancelMonoid α] : AddRightCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addRightCancelSemigroup with }

/--
Instance `Multiplicative.rightCancelMonoid` / 实例 `Multiplicative.rightCancelMonoid`

English:
instance Multiplicative.rightCancelMonoid
  signature: [AddRightCancelMonoid α]
  body: { Multiplicative.monoid, Multiplicative.rightCancelSemigroup with }

中文:
实例 Multiplicative.rightCancelMonoid
  签名: [AddRightCancelMonoid α]
  定义体: { Multiplicative.monoid, Multiplicative.rightCancelSemigroup with }

Depends on / 依赖: Multiplicative, Multiplicative.monoid, Multiplicative.rightCancelSemigroup, monoid, rightCancelSemigroup
-/
instance Multiplicative.rightCancelMonoid [AddRightCancelMonoid α] :
    RightCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.rightCancelSemigroup with }

/--
Instance `Additive.addCommMonoid` / 实例 `Additive.addCommMonoid`

English:
instance Additive.addCommMonoid
  signature: [CommMonoid α]
  body: { Additive.addMonoid, Additive.addCommSemigroup with }

中文:
实例 Additive.addCommMonoid
  签名: [CommMonoid α]
  定义体: { Additive.addMonoid, Additive.addCommSemigroup with }

Depends on / 依赖: Additive, Additive.addCommSemigroup, Additive.addMonoid, addCommSemigroup, addMonoid
-/
instance Additive.addCommMonoid [CommMonoid α] : AddCommMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addCommSemigroup with }

/--
Instance `Multiplicative.commMonoid` / 实例 `Multiplicative.commMonoid`

English:
instance Multiplicative.commMonoid
  signature: [AddCommMonoid α]
  body: { Multiplicative.monoid, Multiplicative.commSemigroup with }

中文:
实例 Multiplicative.commMonoid
  签名: [AddCommMonoid α]
  定义体: { Multiplicative.monoid, Multiplicative.commSemigroup with }

Depends on / 依赖: Multiplicative, Multiplicative.commSemigroup, Multiplicative.monoid, commSemigroup, monoid
-/
instance Multiplicative.commMonoid [AddCommMonoid α] : CommMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.commSemigroup with }

/--
Instance `Additive.instAddCancelCommMonoid` / 实例 `Additive.instAddCancelCommMonoid`

English:
instance Additive.instAddCancelCommMonoid
  signature: [CancelCommMonoid α]

中文:
实例 Additive.instAddCancelCommMonoid
  签名: [CancelCommMonoid α]
-/
instance Additive.instAddCancelCommMonoid [CancelCommMonoid α] :
    AddCancelCommMonoid (Additive α) where

/--
Instance `Multiplicative.instCancelCommMonoid` / 实例 `Multiplicative.instCancelCommMonoid`

English:
instance Multiplicative.instCancelCommMonoid
  signature: [AddCancelCommMonoid α]

中文:
实例 Multiplicative.instCancelCommMonoid
  签名: [AddCancelCommMonoid α]
-/
instance Multiplicative.instCancelCommMonoid [AddCancelCommMonoid α] :
    CancelCommMonoid (Multiplicative α) where

/--
Instance `Additive.neg` / 实例 `Additive.neg`

English:
instance Additive.neg
  signature: [Inv α]
  body: ⟨fun x => ofAdd x.toMul⁻¹⟩

@[simp]

中文:
实例 Additive.neg
  签名: [Inv α]
  定义体: ⟨fun x => ofAdd x.toMul⁻¹⟩

@[simp]

Depends on / 依赖: x.toMul
-/
instance Additive.neg [Inv α] : Neg (Additive α) :=
  ⟨fun x => ofAdd x.toMul⁻¹⟩

@[simp]
/--
theorem `ofMul_inv` / 定理 `ofMul_inv`

English:
theorem ofMul_inv
  given: [Inv α] (x : α)
  statement: ofMul x⁻¹ = -ofMul x
  proof: rfl

@[simp]

中文:
定理 ofMul_inv
  条件: [Inv α] (x : α)
  结论: ofMul x⁻¹ = -ofMul x
  证明: rfl

@[simp]
-/
theorem ofMul_inv [Inv α] (x : α) : ofMul x⁻¹ = -ofMul x :=
  rfl

@[simp]
/--
theorem `toMul_neg` / 定理 `toMul_neg`

English:
theorem toMul_neg
  given: [Inv α] (x : Additive α)
  statement: (-x).toMul = x.toMul⁻¹
  proof: rfl

中文:
定理 toMul_neg
  条件: [Inv α] (x : Additive α)
  结论: (-x).toMul = x.toMul⁻¹
  证明: rfl
-/
theorem toMul_neg [Inv α] (x : Additive α) : (-x).toMul = x.toMul⁻¹ :=
  rfl

/--
Instance `Multiplicative.inv` / 实例 `Multiplicative.inv`

English:
instance Multiplicative.inv
  signature: [Neg α]
  body: ⟨fun x => ofMul (-x.toAdd)⟩

@[simp]

中文:
实例 Multiplicative.inv
  签名: [Neg α]
  定义体: ⟨fun x => ofMul (-x.toAdd)⟩

@[simp]

Depends on / 依赖: x.toAdd
-/
instance Multiplicative.inv [Neg α] : Inv (Multiplicative α) :=
  ⟨fun x => ofMul (-x.toAdd)⟩

@[simp]
/--
theorem `ofAdd_neg` / 定理 `ofAdd_neg`

English:
theorem ofAdd_neg
  given: [Neg α] (x : α)
  statement: ofAdd (-x) = (ofAdd x)⁻¹
  proof: rfl

@[simp]

中文:
定理 ofAdd_neg
  条件: [Neg α] (x : α)
  结论: ofAdd (-x) = (ofAdd x)⁻¹
  证明: rfl

@[simp]
-/
theorem ofAdd_neg [Neg α] (x : α) : ofAdd (-x) = (ofAdd x)⁻¹ :=
  rfl

@[simp]
/--
theorem `toAdd_inv` / 定理 `toAdd_inv`

English:
theorem toAdd_inv
  given: [Neg α] (x : Multiplicative α)
  statement: x⁻¹.toAdd = -x.toAdd
  proof: rfl

中文:
定理 toAdd_inv
  条件: [Neg α] (x : Multiplicative α)
  结论: x⁻¹.toAdd = -x.toAdd
  证明: rfl
-/
theorem toAdd_inv [Neg α] (x : Multiplicative α) : x⁻¹.toAdd = -x.toAdd :=
  rfl

/--
Instance `Additive.sub` / 实例 `Additive.sub`

English:
instance Additive.sub
  signature: [Div α]
  body: ofMul (x.toMul / y.toMul)

中文:
实例 Additive.sub
  签名: [Div α]
  定义体: ofMul (x.toMul / y.toMul)

Depends on / 依赖: x.toMul, y.toMul
-/
instance Additive.sub [Div α] : Sub (Additive α) where
  sub x y := ofMul (x.toMul / y.toMul)

/--
Instance `Multiplicative.div` / 实例 `Multiplicative.div`

English:
instance Multiplicative.div
  signature: [Sub α]
  body: ofAdd (x.toAdd - y.toAdd)

@[simp]

中文:
实例 Multiplicative.div
  签名: [Sub α]
  定义体: ofAdd (x.toAdd - y.toAdd)

@[simp]

Depends on / 依赖: x.toAdd, y.toAdd
-/
instance Multiplicative.div [Sub α] : Div (Multiplicative α) where
  div x y := ofAdd (x.toAdd - y.toAdd)

@[simp]
/--
theorem `ofAdd_sub` / 定理 `ofAdd_sub`

English:
theorem ofAdd_sub
  given: [Sub α] (x y : α)
  statement: ofAdd (x - y) = ofAdd x / ofAdd y
  proof: rfl

@[simp]

中文:
定理 ofAdd_sub
  条件: [Sub α] (x y : α)
  结论: ofAdd (x - y) = ofAdd x / ofAdd y
  证明: rfl

@[simp]
-/
theorem ofAdd_sub [Sub α] (x y : α) : ofAdd (x - y) = ofAdd x / ofAdd y :=
  rfl

@[simp]
/--
theorem `toAdd_div` / 定理 `toAdd_div`

English:
theorem toAdd_div
  given: [Sub α] (x y : Multiplicative α)
  statement: (x / y).toAdd = x.toAdd - y.toAdd
  proof: rfl

@[simp]

中文:
定理 toAdd_div
  条件: [Sub α] (x y : Multiplicative α)
  结论: (x / y).toAdd = x.toAdd - y.toAdd
  证明: rfl

@[simp]
-/
theorem toAdd_div [Sub α] (x y : Multiplicative α) : (x / y).toAdd = x.toAdd - y.toAdd :=
  rfl

@[simp]
/--
theorem `ofMul_div` / 定理 `ofMul_div`

English:
theorem ofMul_div
  given: [Div α] (x y : α)
  statement: ofMul (x / y) = ofMul x - ofMul y
  proof: rfl

@[simp]

中文:
定理 ofMul_div
  条件: [Div α] (x y : α)
  结论: ofMul (x / y) = ofMul x - ofMul y
  证明: rfl

@[simp]
-/
theorem ofMul_div [Div α] (x y : α) : ofMul (x / y) = ofMul x - ofMul y :=
  rfl

@[simp]
/--
theorem `toMul_sub` / 定理 `toMul_sub`

English:
theorem toMul_sub
  given: [Div α] (x y : Additive α)
  statement: (x - y).toMul = x.toMul / y.toMul
  proof: rfl

中文:
定理 toMul_sub
  条件: [Div α] (x y : Additive α)
  结论: (x - y).toMul = x.toMul / y.toMul
  证明: rfl
-/
theorem toMul_sub [Div α] (x y : Additive α) : (x - y).toMul = x.toMul / y.toMul :=
  rfl

/--
Instance `Additive.involutiveNeg` / 实例 `Additive.involutiveNeg`

English:
instance Additive.involutiveNeg
  signature: [InvolutiveInv α]
  body: { Additive.neg with neg_neg := @inv_inv α _ }

中文:
实例 Additive.involutiveNeg
  签名: [InvolutiveInv α]
  定义体: { Additive.neg with neg_neg := @inv_inv α _ }

Depends on / 依赖: Additive, Additive.neg, inv_inv, neg_neg
-/
instance Additive.involutiveNeg [InvolutiveInv α] : InvolutiveNeg (Additive α) :=
  { Additive.neg with neg_neg := @inv_inv α _ }

/--
Instance `Multiplicative.involutiveInv` / 实例 `Multiplicative.involutiveInv`

English:
instance Multiplicative.involutiveInv
  signature: [InvolutiveNeg α]
  body: { Multiplicative.inv with inv_inv := @neg_neg α _ }

中文:
实例 Multiplicative.involutiveInv
  签名: [InvolutiveNeg α]
  定义体: { Multiplicative.inv with inv_inv := @neg_neg α _ }

Depends on / 依赖: Multiplicative, Multiplicative.inv, inv_inv, neg_neg
-/
instance Multiplicative.involutiveInv [InvolutiveNeg α] : InvolutiveInv (Multiplicative α) :=
  { Multiplicative.inv with inv_inv := @neg_neg α _ }

/--
Instance `Additive.subNegMonoid` / 实例 `Additive.subNegMonoid`

English:
instance Additive.subNegMonoid
  signature: [h : DivInvMonoid α]
  body: h.div_eq_mul_inv
  zsmul n a := ofMul (a.toMul ^ n)
  zsmul_zero' := h.zpow_zero'
  zsmul_succ' := h.zpow_succ'
  zsmul_neg' := h.zpow_neg'

中文:
实例 Additive.subNegMonoid
  签名: [h : DivInvMonoid α]
  定义体: h.div_eq_mul_inv
  zsmul n a := ofMul (a.toMul ^ n)
  zsmul_zero' := h.zpow_zero'
  zsmul_succ' := h.zpow_succ'
  zsmul_neg' := h.zpow_neg'

Depends on / 依赖: div_eq_mul_inv, h.div_eq_mul_inv
-/
instance Additive.subNegMonoid [h : DivInvMonoid α] : SubNegMonoid (Additive α) where
  sub_eq_add_neg := h.div_eq_mul_inv
  zsmul n a := ofMul (a.toMul ^ n)
  zsmul_zero' := h.zpow_zero'
  zsmul_succ' := h.zpow_succ'
  zsmul_neg' := h.zpow_neg'

/--
Instance `Multiplicative.divInvMonoid` / 实例 `Multiplicative.divInvMonoid`

English:
instance Multiplicative.divInvMonoid
  signature: [h : SubNegMonoid α]
  body: h.sub_eq_add_neg
  zpow n a := ofAdd (n • a.toAdd)
  zpow_zero' := h.zsmul_zero'
  zpow_succ' := h.zsmul_succ'
  zpow_neg' := h.zsmul_neg'

@[simp]

中文:
实例 Multiplicative.divInvMonoid
  签名: [h : SubNegMonoid α]
  定义体: h.sub_eq_add_neg
  zpow n a := ofAdd (n • a.toAdd)
  zpow_zero' := h.zsmul_zero'
  zpow_succ' := h.zsmul_succ'
  zpow_neg' := h.zsmul_neg'

@[simp]

Depends on / 依赖: h.sub_eq_add_neg, sub_eq_add_neg
-/
instance Multiplicative.divInvMonoid [h : SubNegMonoid α] : DivInvMonoid (Multiplicative α) where
  div_eq_mul_inv := h.sub_eq_add_neg
  zpow n a := ofAdd (n • a.toAdd)
  zpow_zero' := h.zsmul_zero'
  zpow_succ' := h.zsmul_succ'
  zpow_neg' := h.zsmul_neg'

@[simp]
/--
theorem `ofMul_zpow` / 定理 `ofMul_zpow`

English:
theorem ofMul_zpow
  given: [DivInvMonoid α] (z : Int) (a : α)
  statement: ofMul (a ^ z) = z • ofMul a
  proof: rfl

@[simp]

中文:
定理 ofMul_zpow
  条件: [DivInvMonoid α] (z : 整数) (a : α)
  结论: ofMul (a ^ z) = z • ofMul a
  证明: rfl

@[simp]
-/
theorem ofMul_zpow [DivInvMonoid α] (z : Int) (a : α) : ofMul (a ^ z) = z • ofMul a :=
  rfl

@[simp]
/--
theorem `toMul_zsmul` / 定理 `toMul_zsmul`

English:
theorem toMul_zsmul
  given: [DivInvMonoid α] (z : Int) (a : Additive α)
  statement: (z • a).toMul = a.toMul ^ z
  proof: rfl

@[simp]

中文:
定理 toMul_zsmul
  条件: [DivInvMonoid α] (z : 整数) (a : Additive α)
  结论: (z • a).toMul = a.toMul ^ z
  证明: rfl

@[simp]
-/
theorem toMul_zsmul [DivInvMonoid α] (z : Int) (a : Additive α) : (z • a).toMul = a.toMul ^ z :=
  rfl

@[simp]
/--
theorem `ofAdd_zsmul` / 定理 `ofAdd_zsmul`

English:
theorem ofAdd_zsmul
  given: [SubNegMonoid α] (z : Int) (a : α)
  statement: ofAdd (z • a) = ofAdd a ^ z
  proof: rfl

@[simp]

中文:
定理 ofAdd_zsmul
  条件: [SubNegMonoid α] (z : 整数) (a : α)
  结论: ofAdd (z • a) = ofAdd a ^ z
  证明: rfl

@[simp]
-/
theorem ofAdd_zsmul [SubNegMonoid α] (z : Int) (a : α) : ofAdd (z • a) = ofAdd a ^ z :=
  rfl

@[simp]
/--
theorem `toAdd_zpow` / 定理 `toAdd_zpow`

English:
theorem toAdd_zpow
  given: [SubNegMonoid α] (a : Multiplicative α) (z : Int)
  statement: (a ^ z).toAdd = z • a.toAdd
  proof: rfl

中文:
定理 toAdd_zpow
  条件: [SubNegMonoid α] (a : Multiplicative α) (z : 整数)
  结论: (a ^ z).toAdd = z • a.toAdd
  证明: rfl
-/
theorem toAdd_zpow [SubNegMonoid α] (a : Multiplicative α) (z : Int) : (a ^ z).toAdd = z • a.toAdd :=
  rfl

/--
Instance `Additive.subtractionMonoid` / 实例 `Additive.subtractionMonoid`

English:
instance Additive.subtractionMonoid
  signature: [DivisionMonoid α]
  body: { Additive.subNegMonoid, Additive.involutiveNeg with
    neg_add_rev := @mul_inv_rev α _
    neg_eq_of_add := @inv_eq_of_mul_eq_one_right α _ }

中文:
实例 Additive.subtractionMonoid
  签名: [DivisionMonoid α]
  定义体: { Additive.subNegMonoid, Additive.involutiveNeg with
    neg_add_rev := @mul_inv_rev α _
    neg_eq_of_add := @inv_eq_of_mul_eq_one_right α _ }

Depends on / 依赖: Additive, Additive.involutiveNeg, Additive.subNegMonoid, inv_eq_of_mul_eq_one_right, involutiveNeg, mul_inv_rev, neg_add_rev, neg_eq_of_add, subNegMonoid
-/
instance Additive.subtractionMonoid [DivisionMonoid α] : SubtractionMonoid (Additive α) :=
  { Additive.subNegMonoid, Additive.involutiveNeg with
    neg_add_rev := @mul_inv_rev α _
    neg_eq_of_add := @inv_eq_of_mul_eq_one_right α _ }

/--
Instance `Multiplicative.divisionMonoid` / 实例 `Multiplicative.divisionMonoid`

English:
instance Multiplicative.divisionMonoid
  signature: [SubtractionMonoid α]
  body: { Multiplicative.divInvMonoid, Multiplicative.involutiveInv with
    mul_inv_rev := @neg_add_rev α _
    inv_eq_of_mul := @neg_eq_of_add_eq_zero_right α _ }

中文:
实例 Multiplicative.divisionMonoid
  签名: [SubtractionMonoid α]
  定义体: { Multiplicative.divInvMonoid, Multiplicative.involutiveInv with
    mul_inv_rev := @neg_add_rev α _
    inv_eq_of_mul := @neg_eq_of_add_eq_zero_right α _ }

Depends on / 依赖: Multiplicative, Multiplicative.divInvMonoid, Multiplicative.involutiveInv, divInvMonoid, inv_eq_of_mul, involutiveInv, mul_inv_rev, neg_add_rev, neg_eq_of_add_eq_zero_right
-/
instance Multiplicative.divisionMonoid [SubtractionMonoid α] : DivisionMonoid (Multiplicative α) :=
  { Multiplicative.divInvMonoid, Multiplicative.involutiveInv with
    mul_inv_rev := @neg_add_rev α _
    inv_eq_of_mul := @neg_eq_of_add_eq_zero_right α _ }

/--
Instance `Additive.subtractionCommMonoid` / 实例 `Additive.subtractionCommMonoid`

English:
instance Additive.subtractionCommMonoid
  signature: [DivisionCommMonoid α]
  body: { Additive.subtractionMonoid, Additive.addCommSemigroup with }

中文:
实例 Additive.subtractionCommMonoid
  签名: [DivisionCommMonoid α]
  定义体: { Additive.subtractionMonoid, Additive.addCommSemigroup with }

Depends on / 依赖: Additive, Additive.addCommSemigroup, Additive.subtractionMonoid, addCommSemigroup, subtractionMonoid
-/
instance Additive.subtractionCommMonoid [DivisionCommMonoid α] :
    SubtractionCommMonoid (Additive α) :=
  { Additive.subtractionMonoid, Additive.addCommSemigroup with }

/--
Instance `Multiplicative.divisionCommMonoid` / 实例 `Multiplicative.divisionCommMonoid`

English:
instance Multiplicative.divisionCommMonoid
  signature: [SubtractionCommMonoid α]
  body: { Multiplicative.divisionMonoid, Multiplicative.commSemigroup with }

中文:
实例 Multiplicative.divisionCommMonoid
  签名: [SubtractionCommMonoid α]
  定义体: { Multiplicative.divisionMonoid, Multiplicative.commSemigroup with }

Depends on / 依赖: Multiplicative, Multiplicative.commSemigroup, Multiplicative.divisionMonoid, commSemigroup, divisionMonoid
-/
instance Multiplicative.divisionCommMonoid [SubtractionCommMonoid α] :
    DivisionCommMonoid (Multiplicative α) :=
  { Multiplicative.divisionMonoid, Multiplicative.commSemigroup with }

/--
Instance `Additive.addGroup` / 实例 `Additive.addGroup`

English:
instance Additive.addGroup
  signature: [Group α]
  body: { Additive.subNegMonoid with neg_add_cancel := @inv_mul_cancel α _ }

中文:
实例 Additive.addGroup
  签名: [Group α]
  定义体: { Additive.subNegMonoid with neg_add_cancel := @inv_mul_cancel α _ }

Depends on / 依赖: Additive, Additive.subNegMonoid, inv_mul_cancel, neg_add_cancel, subNegMonoid
-/
instance Additive.addGroup [Group α] : AddGroup (Additive α) :=
  { Additive.subNegMonoid with neg_add_cancel := @inv_mul_cancel α _ }

/--
Instance `Multiplicative.group` / 实例 `Multiplicative.group`

English:
instance Multiplicative.group
  signature: [AddGroup α]
  body: { Multiplicative.divInvMonoid with inv_mul_cancel := @neg_add_cancel α _ }

中文:
实例 Multiplicative.group
  签名: [AddGroup α]
  定义体: { Multiplicative.divInvMonoid with inv_mul_cancel := @neg_add_cancel α _ }

Depends on / 依赖: Multiplicative, Multiplicative.divInvMonoid, divInvMonoid, inv_mul_cancel, neg_add_cancel
-/
instance Multiplicative.group [AddGroup α] : Group (Multiplicative α) :=
  { Multiplicative.divInvMonoid with inv_mul_cancel := @neg_add_cancel α _ }

/--
Instance `Additive.addCommGroup` / 实例 `Additive.addCommGroup`

English:
instance Additive.addCommGroup
  signature: [CommGroup α]
  body: { Additive.addGroup, Additive.addCommMonoid with }

中文:
实例 Additive.addCommGroup
  签名: [CommGroup α]
  定义体: { Additive.addGroup, Additive.addCommMonoid with }

Depends on / 依赖: Additive, Additive.addCommMonoid, Additive.addGroup, addCommMonoid, addGroup
-/
instance Additive.addCommGroup [CommGroup α] : AddCommGroup (Additive α) :=
  { Additive.addGroup, Additive.addCommMonoid with }

/--
Instance `Multiplicative.commGroup` / 实例 `Multiplicative.commGroup`

English:
instance Multiplicative.commGroup
  signature: [AddCommGroup α]
  body: { Multiplicative.group, Multiplicative.commMonoid with }

中文:
实例 Multiplicative.commGroup
  签名: [AddCommGroup α]
  定义体: { Multiplicative.group, Multiplicative.commMonoid with }

Depends on / 依赖: Multiplicative, Multiplicative.commMonoid, Multiplicative.group, commMonoid
-/
instance Multiplicative.commGroup [AddCommGroup α] : CommGroup (Multiplicative α) :=
  { Multiplicative.group, Multiplicative.commMonoid with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [IsMulTorsionFree α] : IsAddTorsionFree (Additive α) where
  body: pow_left_injective (M := α)

中文:
实例 [Monoid
  签名: α] [IsMulTorsionFree α] : IsAddTorsionFree (Additive α) where
  定义体: pow_left_injective (M := α)

Depends on / 依赖: pow_left_injective
-/
instance [Monoid α] [IsMulTorsionFree α] : IsAddTorsionFree (Additive α) where
  nsmul_right_injective _ := pow_left_injective (M := α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: α] [IsAddTorsionFree α] : IsMulTorsionFree (Multiplicative α) where
  body: nsmul_right_injective (M := α)

中文:
实例 [AddMonoid
  签名: α] [IsAddTorsionFree α] : IsMulTorsionFree (Multiplicative α) where
  定义体: nsmul_right_injective (M := α)

Depends on / 依赖: nsmul_right_injective
-/
instance [AddMonoid α] [IsAddTorsionFree α] : IsMulTorsionFree (Multiplicative α) where
  pow_left_injective _ := nsmul_right_injective (M := α)

/--
Instance `Additive.coeToFun` / 实例 `Additive.coeToFun`

English:
instance Additive.coeToFun
  signature: {α : Type*} {β : α -> Sort*} [CoeFun α β]
  body: ⟨fun a => CoeFun.coe a.toMul⟩

中文:
实例 Additive.coeToFun
  签名: {α : 类型} {β : α -> Sort*} [CoeFun α β]
  定义体: ⟨fun a => CoeFun.coe a.toMul⟩

Depends on / 依赖: CoeFun, CoeFun.coe, a.toMul
-/
instance Additive.coeToFun {α : Type*} {β : α -> Sort*} [CoeFun α β] :
    CoeFun (Additive α) fun a => β a.toMul :=
  ⟨fun a => CoeFun.coe a.toMul⟩

/--
Instance `Multiplicative.coeToFun` / 实例 `Multiplicative.coeToFun`

English:
instance Multiplicative.coeToFun
  signature: {α : Type*} {β : α -> Sort*} [CoeFun α β]
  body: ⟨fun a => CoeFun.coe a.toAdd⟩

中文:
实例 Multiplicative.coeToFun
  签名: {α : 类型} {β : α -> Sort*} [CoeFun α β]
  定义体: ⟨fun a => CoeFun.coe a.toAdd⟩

Depends on / 依赖: CoeFun, CoeFun.coe, a.toAdd
-/
instance Multiplicative.coeToFun {α : Type*} {β : α -> Sort*} [CoeFun α β] :
    CoeFun (Multiplicative α) fun a => β a.toAdd :=
  ⟨fun a => CoeFun.coe a.toAdd⟩

/--
lemma `Pi.mulSingle_multiplicativeOfAdd_eq` / 引理 `Pi.mulSingle_multiplicativeOfAdd_eq`

English:
lemma Pi.mulSingle_multiplicativeOfAdd_eq
  statement: {ι : Type*} [DecidableEq ι] {M : ι -> Type*}
  proof: by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [mulSingle, ne_eq, h, not_false_eq_true, Function.update_of_ne, one_apply, single,
      zero_apply, ofAdd_zero]

中文:
引理 Pi.mulSingle_multiplicativeOfAdd_eq
  结论: {ι : 类型} [DecidableEq ι] {M : ι -> 类型}
  证明: by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [mulSingle, ne_eq, h, not_false_eq_true, Function.update_of_ne, one_apply, single,
      zero_apply, ofAdd_zero]

Depends on / 依赖: Function, Function.update_of_ne, Multiplicative, Pi.single, eq_or_ne, mulSingle, mulSingle_eq_same, ne_eq, not_false_eq_true, ofAdd_zero, one_apply, single, single_eq_same, update_of_ne, zero_apply
-/
lemma Pi.mulSingle_multiplicativeOfAdd_eq {ι : Type*} [DecidableEq ι] {M : ι -> Type*}
    [(i : ι) -> AddMonoid (M i)] (i : ι) (a : M i) (j : ι) :
    Pi.mulSingle (M := fun i => Multiplicative (M i)) i (.ofAdd a) j = .ofAdd (Pi.single i a j) := by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [mulSingle, ne_eq, h, not_false_eq_true, Function.update_of_ne, one_apply, single,
      zero_apply, ofAdd_zero]

/--
lemma `Pi.single_additiveOfMul_eq` / 引理 `Pi.single_additiveOfMul_eq`

English:
lemma Pi.single_additiveOfMul_eq
  statement: {ι : Type*} [DecidableEq ι] {M : ι -> Type*}
  proof: by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [single, ne_eq, h, not_false_eq_true, Function.update_of_ne, zero_apply, mulSingle,
      one_apply, ofMul_one]

中文:
引理 Pi.single_additiveOfMul_eq
  结论: {ι : 类型} [DecidableEq ι] {M : ι -> 类型}
  证明: by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [single, ne_eq, h, not_false_eq_true, Function.update_of_ne, zero_apply, mulSingle,
      one_apply, ofMul_one]

Depends on / 依赖: Additive, Function, Function.update_of_ne, Pi.mulSingle, eq_or_ne, mulSingle, mulSingle_eq_same, ne_eq, not_false_eq_true, ofMul_one, one_apply, single, single_eq_same, update_of_ne, zero_apply
-/
lemma Pi.single_additiveOfMul_eq {ι : Type*} [DecidableEq ι] {M : ι -> Type*}
    [(i : ι) -> Monoid (M i)] (i : ι) (a : M i) (j : ι) :
    Pi.single (M := fun i => Additive (M i)) i (.ofMul a) j = .ofMul (Pi.mulSingle i a j) := by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [single, ne_eq, h, not_false_eq_true, Function.update_of_ne, zero_apply, mulSingle,
      one_apply, ofMul_one]
