/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.GradedObject.Trifunctor

/-! # Signs in constructions on homological complexes

In this file, we shall introduce various typeclasses which will allow
the construction of the total complex of a bicomplex and of the
monoidal category structure on categories of homological complexes (TODO).

The most important definition is that of `TotalComplexShape c₁ c₂ c₁₂` given
three complex shapes `c₁`, `c₂`, `c₁₂`: it allows the definition of a total
complex functor `HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₁₂` (at least
when suitable coproducts exist).

In particular, we construct an instance of `TotalComplexShape c c c` when `c : ComplexShape I`
and `I` is an additive monoid equipped with a group homomorphism `ε' : Multiplicative I → ℤˣ`
satisfying certain properties (see `ComplexShape.TensorSigns`).

-/

@[expose] public section

assert_not_exists Field TwoSidedIdeal

variable {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)

/--
Definition of `TotalComplexShape` / `TotalComplexShape` 的定义

English:
class TotalComplexShape
  parameters: where
  axioms and operations (6):
    - π : I₁ × I₂ -> I₁₂
    - ε₁ : I₁ × I₂ -> Intˣ
    - ε₂ : I₁ × I₂ -> Intˣ
    - rel₁({i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂)) : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁', i₂⟩)
    - rel₂((i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂')) : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁, i₂'⟩)
    - ε₂_ε₁({i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂')) : ε₂ ⟨i₁, i₂⟩ * ε₁ ⟨i₁, i₂'⟩ = - ε₁ ⟨i₁, i₂⟩ * ε₂ ⟨i₁', i₂⟩

中文:
类 TotalComplexShape
  参数: where
  公理与运算 (6 个):
    - π : I₁ × I₂ -> I₁₂
    - ε₁ : I₁ × I₂ -> 整数ˣ
    - ε₂ : I₁ × I₂ -> 整数ˣ
    - rel₁({i₁ i₁' : I₁} (h : c₁.关系 i₁ i₁') (i₂ : I₂)) : c₁₂.关系 (π ⟨i₁, i₂⟩) (π ⟨i₁', i₂⟩)
    - rel₂((i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.关系 i₂ i₂')) : c₁₂.关系 (π ⟨i₁, i₂⟩) (π ⟨i₁, i₂'⟩)
    - ε₂_ε₁({i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.关系 i₁ i₁') (h₂ : c₂.关系 i₂ i₂')) : ε₂ ⟨i₁, i₂⟩ * ε₁ ⟨i₁, i₂'⟩ = - ε₁ ⟨i₁, i₂⟩ * ε₂ ⟨i₁', i₂⟩
-/
class TotalComplexShape where
  /-- a map on indices -/
  π : I₁ × I₂ -> I₁₂
  /-- the sign of the horizontal differential in the total complex -/
  ε₁ : I₁ × I₂ -> Intˣ
  /-- the sign of the vertical differential in the total complex -/
  ε₂ : I₁ × I₂ -> Intˣ
  rel₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁', i₂⟩)
  rel₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁, i₂'⟩)
  ε₂_ε₁ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₂ ⟨i₁, i₂⟩ * ε₁ ⟨i₁, i₂'⟩ = - ε₁ ⟨i₁, i₂⟩ * ε₂ ⟨i₁', i₂⟩

namespace ComplexShape

variable [TotalComplexShape c₁ c₂ c₁₂]

/--
Definition of `π` / `π` 的定义

English:
abbreviation π
  signature: (i : I₁ × I₂)
  body: TotalComplexShape.π c₁ c₂ c₁₂ i

中文:
缩写 π
  签名: (i : I₁ × I₂)
  定义体: TotalComplexShape.π c₁ c₂ c₁₂ i

Depends on / 依赖: TotalComplexShape
-/
abbrev π (i : I₁ × I₂) : I₁₂ := TotalComplexShape.π c₁ c₂ c₁₂ i

/--
Definition of `ε₁` / `ε₁` 的定义

English:
abbreviation ε₁
  signature: (i : I₁ × I₂)
  body: TotalComplexShape.ε₁ c₁ c₂ c₁₂ i

中文:
缩写 ε₁
  签名: (i : I₁ × I₂)
  定义体: TotalComplexShape.ε₁ c₁ c₂ c₁₂ i

Depends on / 依赖: TotalComplexShape
-/
abbrev ε₁ (i : I₁ × I₂) : Intˣ := TotalComplexShape.ε₁ c₁ c₂ c₁₂ i

/--
Definition of `ε₂` / `ε₂` 的定义

English:
abbreviation ε₂
  signature: (i : I₁ × I₂)
  body: TotalComplexShape.ε₂ c₁ c₂ c₁₂ i

中文:
缩写 ε₂
  签名: (i : I₁ × I₂)
  定义体: TotalComplexShape.ε₂ c₁ c₂ c₁₂ i

Depends on / 依赖: TotalComplexShape
-/
abbrev ε₂ (i : I₁ × I₂) : Intˣ := TotalComplexShape.ε₂ c₁ c₂ c₁₂ i

variable {c₁}

/--
lemma `rel_π₁` / 引理 `rel_π₁`

English:
lemma rel_π₁
  given: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂)
  proof: TotalComplexShape.rel₁ h i₂

中文:
引理 rel_π₁
  条件: {i₁ i₁' : I₁} (h : c₁.关系 i₁ i₁') (i₂ : I₂)
  证明: TotalComplexShape.rel₁ h i₂

Depends on / 依赖: TotalComplexShape, TotalComplexShape.rel
-/
lemma rel_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.Rel (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) (π c₁ c₂ c₁₂ ⟨i₁', i₂⟩) :=
  TotalComplexShape.rel₁ h i₂

/--
lemma `next_π₁` / 引理 `next_π₁`

English:
lemma next_π₁
  given: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂)
  proof: c₁₂.next_eq' (rel_π₁ c₂ c₁₂ h i₂)

中文:
引理 next_π₁
  条件: {i₁ i₁' : I₁} (h : c₁.关系 i₁ i₁') (i₂ : I₂)
  证明: c₁₂.next_eq' (rel_π₁ c₂ c₁₂ h i₂)

Depends on / 依赖: next_eq
-/
lemma next_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.next (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ :=
  c₁₂.next_eq' (rel_π₁ c₂ c₁₂ h i₂)

/--
lemma `prev_π₁` / 引理 `prev_π₁`

English:
lemma prev_π₁
  given: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂)
  proof: c₁₂.prev_eq' (rel_π₁ c₂ c₁₂ h i₂)

中文:
引理 prev_π₁
  条件: {i₁ i₁' : I₁} (h : c₁.关系 i₁ i₁') (i₂ : I₂)
  证明: c₁₂.prev_eq' (rel_π₁ c₂ c₁₂ h i₂)

Depends on / 依赖: prev_eq
-/
lemma prev_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.prev (π c₁ c₂ c₁₂ ⟨i₁', i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ :=
  c₁₂.prev_eq' (rel_π₁ c₂ c₁₂ h i₂)

variable (c₁) {c₂}

/--
lemma `rel_π₂` / 引理 `rel_π₂`

English:
lemma rel_π₂
  given: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂')
  proof: TotalComplexShape.rel₂ i₁ h

中文:
引理 rel_π₂
  条件: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.关系 i₂ i₂')
  证明: TotalComplexShape.rel₂ i₁ h

Depends on / 依赖: TotalComplexShape, TotalComplexShape.rel
-/
lemma rel_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.Rel (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) (π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩) :=
  TotalComplexShape.rel₂ i₁ h

/--
lemma `next_π₂` / 引理 `next_π₂`

English:
lemma next_π₂
  given: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂')
  proof: c₁₂.next_eq' (rel_π₂ c₁ c₁₂ i₁ h)

中文:
引理 next_π₂
  条件: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.关系 i₂ i₂')
  证明: c₁₂.next_eq' (rel_π₂ c₁ c₁₂ i₁ h)

Depends on / 依赖: next_eq
-/
lemma next_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.next (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ :=
  c₁₂.next_eq' (rel_π₂ c₁ c₁₂ i₁ h)

/--
lemma `prev_π₂` / 引理 `prev_π₂`

English:
lemma prev_π₂
  given: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂')
  proof: c₁₂.prev_eq' (rel_π₂ c₁ c₁₂ i₁ h)

中文:
引理 prev_π₂
  条件: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.关系 i₂ i₂')
  证明: c₁₂.prev_eq' (rel_π₂ c₁ c₁₂ i₁ h)

Depends on / 依赖: prev_eq
-/
lemma prev_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.prev (π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ :=
  c₁₂.prev_eq' (rel_π₂ c₁ c₁₂ i₁ h)

variable {c₁}

/--
lemma `ε₂_ε₁` / 引理 `ε₂_ε₁`

English:
lemma ε₂_ε₁
  given: {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂')
  proof: TotalComplexShape.ε₂_ε₁ h₁ h₂

中文:
引理 ε₂_ε₁
  条件: {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.关系 i₁ i₁') (h₂ : c₂.关系 i₂ i₂')
  证明: TotalComplexShape.ε₂_ε₁ h₁ h₂

Depends on / 依赖: TotalComplexShape
-/
lemma ε₂_ε₁ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ =
      - ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₂ c₁ c₂ c₁₂ ⟨i₁', i₂⟩ :=
  TotalComplexShape.ε₂_ε₁ h₁ h₂

/--
lemma `ε₁_ε₂` / 引理 `ε₁_ε₂`

English:
lemma ε₁_ε₂
  given: {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂')
  proof: Eq.trans (mul_one _).symm (by
    rw [← Int.units_mul_self (ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁]; rw [i₂'))]; rw [mul_assoc]
    conv_lhs =>
      arg 2
      rw [← mul_assoc]; rw [ε₂_ε₁ c₁₂ h₁ h₂]
    rw [neg_mul]; rw [neg_mul]; rw [neg_mul]; rw [mul_neg]; rw [neg_inj]; rw [← mul_assoc]; rw [← mul_assoc]

中文:
引理 ε₁_ε₂
  条件: {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.关系 i₁ i₁') (h₂ : c₂.关系 i₂ i₂')
  证明: Eq.trans (mul_one _).symm (by
    rw [← Int.units_mul_self (ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁]; rw [i₂'))]; rw [mul_assoc]
    conv_lhs =>
      arg 2
      rw [← mul_assoc]; rw [ε₂_ε₁ c₁₂ h₁ h₂]
    rw [neg_mul]; rw [neg_mul]; rw [neg_mul]; rw [mul_neg]; rw [neg_inj]; rw [← mul_assoc]; rw [← mul_assoc]

Depends on / 依赖: ComplexShape, Eq.trans, Int.units_mul_self, conv_lhs, mul_assoc, mul_neg, mul_one, neg_inj, neg_mul, one_mul, units_mul_self
-/
lemma ε₁_ε₂ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ =
      - ε₂ c₁ c₂ c₁₂ ⟨i₁', i₂⟩ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ :=
  Eq.trans (mul_one _).symm (by
    rw [← Int.units_mul_self (ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁]; rw [i₂'))]; rw [mul_assoc]
    conv_lhs =>
      arg 2
      rw [← mul_assoc]; rw [ε₂_ε₁ c₁₂ h₁ h₂]
    rw [neg_mul]; rw [neg_mul]; rw [neg_mul]; rw [mul_neg]; rw [neg_inj]; rw [← mul_assoc]; rw [← mul_assoc]; rw [Int.units_mul_self]; rw [one_mul])

section

variable {I : Type*} [AddMonoid I] (c : ComplexShape I)

/--
Definition of `TensorSigns` / `TensorSigns` 的定义

English:
class TensorSigns
  parameters: where
  axioms and operations (4):
    - ε' : Multiplicative I ->* Intˣ
    - rel_add((p q r : I) (hpq : c.Rel p q)) : c.Rel (p + r) (q + r)
    - add_rel((p q r : I) (hpq : c.Rel p q)) : c.Rel (r + p) (r + q)
    - ε'_succ((p q : I) (hpq : c.Rel p q)) : ε' q = - ε' p

中文:
类 张量符号
  参数: where
  公理与运算 (4 个):
    - ε' : Multiplicative I ->* 整数ˣ
    - rel_add((p q r : I) (hpq : c.关系 p q)) : c.关系 (p + r) (q + r)
    - add_rel((p q r : I) (hpq : c.关系 p q)) : c.关系 (r + p) (r + q)
    - ε'_succ((p q : I) (hpq : c.关系 p q)) : ε' q = - ε' p
-/
class TensorSigns where
  /-- the signs which appear in the vertical differential of the total complex -/
  ε' : Multiplicative I ->* Intˣ
  rel_add (p q r : I) (hpq : c.Rel p q) : c.Rel (p + r) (q + r)
  add_rel (p q r : I) (hpq : c.Rel p q) : c.Rel (r + p) (r + q)
  ε'_succ (p q : I) (hpq : c.Rel p q) : ε' q = - ε' p

variable [TensorSigns c]

/--
Definition of `ε` / `ε` 的定义

English:
abbreviation ε
  signature: (i : I)
  body: TensorSigns.ε' c i

中文:
缩写 ε
  签名: (i : I)
  定义体: TensorSigns.ε' c i

Depends on / 依赖: CochainComplex, DerivedCategory, DerivedCategory.Q.obj, IsStrictlyLE, K.IsStrictlyLE, TensorSigns
-/
abbrev ε (i : I) : Intˣ := TensorSigns.ε' c i

/--
lemma `rel_add` / 引理 `rel_add`

English:
lemma rel_add
  given: {p q : I} (hpq : c.Rel p q) (r : I)
  statement: c.Rel (p + r) (q + r)
  proof: TensorSigns.rel_add _ _ _ hpq

中文:
引理 rel_add
  条件: {p q : I} (hpq : c.关系 p q) (r : I)
  结论: c.关系 (p + r) (q + r)
  证明: TensorSigns.rel_add _ _ _ hpq

Depends on / 依赖: TensorSigns, TensorSigns.rel_add, rel_add
-/
lemma rel_add {p q : I} (hpq : c.Rel p q) (r : I) : c.Rel (p + r) (q + r) :=
  TensorSigns.rel_add _ _ _ hpq

/--
lemma `add_rel` / 引理 `add_rel`

English:
lemma add_rel
  given: (r : I) {p q : I} (hpq : c.Rel p q)
  statement: c.Rel (r + p) (r + q)
  proof: TensorSigns.add_rel _ _ _ hpq

@[simp]

中文:
引理 add_rel
  条件: (r : I) {p q : I} (hpq : c.关系 p q)
  结论: c.关系 (r + p) (r + q)
  证明: TensorSigns.add_rel _ _ _ hpq

@[simp]

Depends on / 依赖: TensorSigns, TensorSigns.add_rel, add_rel
-/
lemma add_rel (r : I) {p q : I} (hpq : c.Rel p q) : c.Rel (r + p) (r + q) :=
  TensorSigns.add_rel _ _ _ hpq

@[simp]
/--
lemma `ε_zero` / 引理 `ε_zero`

English:
lemma ε_zero
  statement: c.ε 0 = 1
  proof: by
  apply map_one

中文:
引理 ε_zero
  结论: c.ε 0 = 1
  证明: by
  apply map_one

Depends on / 依赖: map_one
-/
lemma ε_zero : c.ε 0 = 1 := by
  apply map_one

/--
lemma `ε_succ` / 引理 `ε_succ`

English:
lemma ε_succ
  given: {p q : I} (hpq : c.Rel p q)
  statement: c.ε q = - c.ε p
  proof: TensorSigns.ε'_succ p q hpq

中文:
引理 ε_succ
  条件: {p q : I} (hpq : c.关系 p q)
  结论: c.ε q = - c.ε p
  证明: TensorSigns.ε'_succ p q hpq

Depends on / 依赖: TensorSigns, _succ
-/
lemma ε_succ {p q : I} (hpq : c.Rel p q) : c.ε q = - c.ε p :=
  TensorSigns.ε'_succ p q hpq

/--
lemma `ε_add` / 引理 `ε_add`

English:
lemma ε_add
  given: (p q : I)
  statement: c.ε (p + q) = c.ε p * c.ε q
  proof: by
  apply map_mul

中文:
引理 ε_add
  条件: (p q : I)
  结论: c.ε (p + q) = c.ε p * c.ε q
  证明: by
  apply map_mul

Depends on / 依赖: map_mul
-/
lemma ε_add (p q : I) : c.ε (p + q) = c.ε p * c.ε q := by
  apply map_mul

/--
lemma `next_add` / 引理 `next_add`

English:
lemma next_add
  given: (p q : I) (hp : c.Rel p (c.next p))
  proof: c.next_eq' (c.rel_add hp q)

中文:
引理 next_add
  条件: (p q : I) (hp : c.关系 p (c.next p))
  证明: c.next_eq' (c.rel_add hp q)

Depends on / 依赖: c.next_eq, c.rel_add, next_eq, rel_add
-/
lemma next_add (p q : I) (hp : c.Rel p (c.next p)) :
    c.next (p + q) = c.next p + q :=
  c.next_eq' (c.rel_add hp q)

/--
lemma `next_add'` / 引理 `next_add'`

English:
lemma next_add'
  given: (p q : I) (hq : c.Rel q (c.next q))
  proof: c.next_eq' (c.add_rel p hq)

@[simps]

中文:
引理 next_add'
  条件: (p q : I) (hq : c.关系 q (c.next q))
  证明: c.next_eq' (c.add_rel p hq)

@[simps]

Depends on / 依赖: add_rel, c.add_rel, c.next_eq, next_eq
-/
lemma next_add' (p q : I) (hq : c.Rel q (c.next q)) :
    c.next (p + q) = p + c.next q :=
  c.next_eq' (c.add_rel p hq)

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TotalComplexShape c c c
  body: fun ⟨p, q⟩ => p + q
  ε₁ := fun _ => 1
  ε₂ := fun ⟨p, _⟩ => c.ε p
  rel₁ h q := c.rel_add h q
  rel₂ p _ _ h := c.add_rel p h
  ε₂_ε₁ h _ := by
    dsimp
    rw [neg_mul]; rw [one_mul]; rw [mul_one]; rw [c.ε_succ h]; rw [neg_neg]

中文:
实例 :
  签名: TotalComplexShape c c c
  定义体: fun ⟨p, q⟩ => p + q
  ε₁ := fun _ => 1
  ε₂ := fun ⟨p, _⟩ => c.ε p
  rel₁ h q := c.rel_add h q
  rel₂ p _ _ h := c.add_rel p h
  ε₂_ε₁ h _ := by
    dsimp
    rw [neg_mul]; rw [one_mul]; rw [mul_one]; rw [c.ε_succ h]; rw [neg_neg]
-/
instance : TotalComplexShape c c c where
  π := fun ⟨p, q⟩ => p + q
  ε₁ := fun _ => 1
  ε₂ := fun ⟨p, _⟩ => c.ε p
  rel₁ h q := c.rel_add h q
  rel₂ p _ _ h := c.add_rel p h
  ε₂_ε₁ h _ := by
    dsimp
    rw [neg_mul]; rw [one_mul]; rw [mul_one]; rw [c.ε_succ h]; rw [neg_neg]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TensorSigns (ComplexShape.down Nat)
  body: MonoidHom.mk' (fun (i : Nat) => (-1 : Intˣ) ^ i) (pow_add (-1 : Intˣ))
  rel_add p q r (hpq : q + 1 = p) := by dsimp; lia
  add_rel p q r (hpq : q + 1 = p) := by dsimp; lia
  ε'_succ := by
    rintro _ q rfl
    dsimp
    rw [pow_add]; rw [pow_one]; rw [mul_neg]; rw [mul_one]; rw [neg_neg]

@[simp]

中文:
实例 :
  签名: 张量符号 (余mplexShape.down 自然数)
  定义体: MonoidHom.mk' (fun (i : Nat) => (-1 : Intˣ) ^ i) (pow_add (-1 : Intˣ))
  rel_add p q r (hpq : q + 1 = p) := by dsimp; lia
  add_rel p q r (hpq : q + 1 = p) := by dsimp; lia
  ε'_succ := by
    rintro _ q rfl
    dsimp
    rw [pow_add]; rw [pow_one]; rw [mul_neg]; rw [mul_one]; rw [neg_neg]

@[simp]

Depends on / 依赖: MonoidHom, MonoidHom.mk, infer_instance, isGE_Q_obj_iff, pow_add
-/
instance : TensorSigns (ComplexShape.down Nat) where
  ε' := MonoidHom.mk' (fun (i : Nat) => (-1 : Intˣ) ^ i) (pow_add (-1 : Intˣ))
  rel_add p q r (hpq : q + 1 = p) := by dsimp; lia
  add_rel p q r (hpq : q + 1 = p) := by dsimp; lia
  ε'_succ := by
    rintro _ q rfl
    dsimp
    rw [pow_add]; rw [pow_one]; rw [mul_neg]; rw [mul_one]; rw [neg_neg]

@[simp]
/--
lemma `ε_down_Nat` / 引理 `ε_down_Nat`

English:
lemma ε_down_Nat
  given: (n : Nat)
  statement: (ComplexShape.down Nat).ε n = (-1 : Intˣ) ^ n
  proof: rfl

中文:
引理 ε_down_自然数
  条件: (n : 自然数)
  结论: (余mplexShape.down 自然数).ε n = (-1 : 整数ˣ) ^ n
  证明: rfl

Depends on / 依赖: infer_instance, isLE_Q_obj_iff
-/
lemma ε_down_Nat (n : Nat) : (ComplexShape.down Nat).ε n = (-1 : Intˣ) ^ n := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TensorSigns (ComplexShape.up Int)
  body: MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : p + 1 = q) := by dsimp; lia
  add_rel p q r (hpq : p + 1 = q) := by dsimp; lia
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [Int.negOnePow_succ]

@[simp]

中文:
实例 :
  签名: 张量符号 (余mplexShape.up 整数)
  定义体: MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : p + 1 = q) := by dsimp; lia
  add_rel p q r (hpq : p + 1 = q) := by dsimp; lia
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [Int.negOnePow_succ]

@[simp]

Depends on / 依赖: Functor, Functor.comp_obj, Int.negOnePow, Int.negOnePow_add, MonoidHom, MonoidHom.mk, TStructure, TStructure.t.isGE_of_iso, comp_obj, e.symm, isGE_of_iso, negOnePow, negOnePow_add, singleFunctorIsoCompQ
-/
instance : TensorSigns (ComplexShape.up Int) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : p + 1 = q) := by dsimp; lia
  add_rel p q r (hpq : p + 1 = q) := by dsimp; lia
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [Int.negOnePow_succ]

@[simp]
/--
lemma `ε_up_Int` / 引理 `ε_up_Int`

English:
lemma ε_up_Int
  given: (n : Int)
  statement: (ComplexShape.up Int).ε n = n.negOnePow
  proof: rfl

中文:
引理 ε_up_整数
  条件: (n : 整数)
  结论: (余mplexShape.up 整数).ε n = n.negOnePow
  证明: rfl

Depends on / 依赖: Functor, Functor.comp_obj, TStructure, TStructure.t.isLE_of_iso, comp_obj, e.symm, isLE_of_iso, singleFunctorIsoCompQ
-/
lemma ε_up_Int (n : Int) : (ComplexShape.up Int).ε n = n.negOnePow := rfl

end

section

variable (c₁ c₂)
variable [TotalComplexShape c₁₂ c₃ c] [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c]

/--
Definition of `Associative` / `Associative` 的定义

English:
class Associative
  parameters: : Prop where
  axioms and operations (4):
    - assoc((i₁ : I₁) (i₂ : I₂) (i₃ : I₃)) : π c₁₂ c₃ c ⟨π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃⟩ = π c₁ c₂₃ c ⟨i₁, π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩
    - ε₁_eq_mul((i₁ : I₁) (i₂ : I₂) (i₃ : I₃)) : ε₁ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) = ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₁ c₁ c₂ c₁₂ (i₁, i₂)
    - ε₂_ε₁((i₁ : I₁) (i₂ : I₂) (i₃ : I₃)) : ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₁ c₂ c₃ c₂₃ (i₂, i₃) = ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₂ c₁ c₂ c₁₂ (i₁, i₂)
    - ε₂_eq_mul((i₁ : I₁) (i₂ : I₂) (i₃ : I₃)) : ε₂ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) = (ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₂ c₂ c₃ c₂₃ (i₂, i₃))

中文:
类 结合
  参数: : 命题 where
  公理与运算 (4 个):
    - assoc((i₁ : I₁) (i₂ : I₂) (i₃ : I₃)) : π c₁₂ c₃ c ⟨π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃⟩ = π c₁ c₂₃ c ⟨i₁, π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩
    - ε₁_eq_mul((i₁ : I₁) (i₂ : I₂) (i₃ : I₃)) : ε₁ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) = ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₁ c₁ c₂ c₁₂ (i₁, i₂)
    - ε₂_ε₁((i₁ : I₁) (i₂ : I₂) (i₃ : I₃)) : ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₁ c₂ c₃ c₂₃ (i₂, i₃) = ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₂ c₁ c₂ c₁₂ (i₁, i₂)
    - ε₂_eq_mul((i₁ : I₁) (i₂ : I₂) (i₃ : I₃)) : ε₂ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) = (ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₂ c₂ c₃ c₂₃ (i₂, i₃))
-/
class Associative : Prop where
  assoc (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    π c₁₂ c₃ c ⟨π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃⟩ = π c₁ c₂₃ c ⟨i₁, π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩
  ε₁_eq_mul (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₁ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) =
      ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₁ c₁ c₂ c₁₂ (i₁, i₂)
  ε₂_ε₁ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₁ c₂ c₃ c₂₃ (i₂, i₃) =
      ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₂ c₁ c₂ c₁₂ (i₁, i₂)
  ε₂_eq_mul (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₂ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) =
      (ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₂ c₂ c₃ c₂₃ (i₂, i₃))

variable [Associative c₁ c₂ c₃ c₁₂ c₂₃ c]

/--
lemma `assoc` / 引理 `assoc`

English:
lemma assoc
  given: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
  proof: by
  apply Associative.assoc

中文:
引理 assoc
  条件: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
  证明: by
  apply Associative.assoc

Depends on / 依赖: Associative, Associative.assoc
-/
lemma assoc (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    π c₁₂ c₃ c ⟨π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃⟩ = π c₁ c₂₃ c ⟨i₁, π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩ := by
  apply Associative.assoc

/--
lemma `associative_ε₁_eq_mul` / 引理 `associative_ε₁_eq_mul`

English:
lemma associative_ε₁_eq_mul
  given: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
  proof: by
  apply Associative.ε₁_eq_mul

中文:
引理 associative_ε₁_eq_mul
  条件: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
  证明: by
  apply Associative.ε₁_eq_mul

Depends on / 依赖: Associative
-/
lemma associative_ε₁_eq_mul (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₁ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) =
      ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₁ c₁ c₂ c₁₂ (i₁, i₂) := by
  apply Associative.ε₁_eq_mul

/--
lemma `associative_ε₂_ε₁` / 引理 `associative_ε₂_ε₁`

English:
lemma associative_ε₂_ε₁
  given: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
  proof: by
  apply Associative.ε₂_ε₁

中文:
引理 associative_ε₂_ε₁
  条件: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
  证明: by
  apply Associative.ε₂_ε₁

Depends on / 依赖: Associative
-/
lemma associative_ε₂_ε₁ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₁ c₂ c₃ c₂₃ (i₂, i₃) =
      ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₂ c₁ c₂ c₁₂ (i₁, i₂) := by
  apply Associative.ε₂_ε₁

/--
lemma `associative_ε₂_eq_mul` / 引理 `associative_ε₂_eq_mul`

English:
lemma associative_ε₂_eq_mul
  given: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
  proof: by
  apply Associative.ε₂_eq_mul

中文:
引理 associative_ε₂_eq_mul
  条件: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
  证明: by
  apply Associative.ε₂_eq_mul

Depends on / 依赖: Associative
-/
lemma associative_ε₂_eq_mul (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₂ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) =
      (ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₂ c₂ c₃ c₂₃ (i₂, i₃)) := by
  apply Associative.ε₂_eq_mul

/--
Definition of `r` / `r` 的定义

English:
definition r
  signature: : I₁ × I₂ × I₃ -> J
  body: fun ⟨i₁, i₂, i₃⟩ => π c₁₂ c₃ c ⟨π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃⟩

中文:
定义 r
  签名: : I₁ × I₂ × I₃ -> J
  定义体: fun ⟨i₁, i₂, i₃⟩ => π c₁₂ c₃ c ⟨π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃⟩
-/
def r : I₁ × I₂ × I₃ -> J := fun ⟨i₁, i₂, i₃⟩ => π c₁₂ c₃ c ⟨π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃⟩

open CategoryTheory

/-- The `GradedObject.BifunctorComp₁₂IndexData` which arises from complex shapes. -/
@[reducible]
/--
Definition of `ρ₁₂` / `ρ₁₂` 的定义

English:
definition ρ₁₂
  signature: : GradedObject.BifunctorComp₁₂IndexData (r c₁ c₂ c₃ c₁₂ c) where
  body: I₁₂
  p := π c₁ c₂ c₁₂
  q := π c₁₂ c₃ c
  hpq _ := rfl

中文:
定义 ρ₁₂
  签名: : GradedObject.BifunctorComp₁₂IndexData (r c₁ c₂ c₃ c₁₂ c) where
  定义体: I₁₂
  p := π c₁ c₂ c₁₂
  q := π c₁₂ c₃ c
  hpq _ := rfl
-/
def ρ₁₂ : GradedObject.BifunctorComp₁₂IndexData (r c₁ c₂ c₃ c₁₂ c) where
  I₁₂ := I₁₂
  p := π c₁ c₂ c₁₂
  q := π c₁₂ c₃ c
  hpq _ := rfl

/-- The `GradedObject.BifunctorComp₂₃IndexData` which arises from complex shapes. -/
@[reducible]
/--
Definition of `ρ₂₃` / `ρ₂₃` 的定义

English:
definition ρ₂₃
  signature: : GradedObject.BifunctorComp₂₃IndexData (r c₁ c₂ c₃ c₁₂ c) where
  body: I₂₃
  p := π c₂ c₃ c₂₃
  q := π c₁ c₂₃ c
  hpq := fun ⟨i₁, i₂, i₃⟩ => (assoc c₁ c₂ c₃ c₁₂ c₂₃ c i₁ i₂ i₃).symm

中文:
定义 ρ₂₃
  签名: : GradedObject.BifunctorComp₂₃IndexData (r c₁ c₂ c₃ c₁₂ c) where
  定义体: I₂₃
  p := π c₂ c₃ c₂₃
  q := π c₁ c₂₃ c
  hpq := fun ⟨i₁, i₂, i₃⟩ => (assoc c₁ c₂ c₃ c₁₂ c₂₃ c i₁ i₂ i₃).symm
-/
def ρ₂₃ : GradedObject.BifunctorComp₂₃IndexData (r c₁ c₂ c₃ c₁₂ c) where
  I₂₃ := I₂₃
  p := π c₂ c₃ c₂₃
  q := π c₁ c₂₃ c
  hpq := fun ⟨i₁, i₂, i₃⟩ => (assoc c₁ c₂ c₃ c₁₂ c₂₃ c i₁ i₂ i₃).symm

end

instance {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns] :
    Associative c c c c c c where
  assoc := add_assoc
  ε₁_eq_mul _ _ _ := by dsimp; rw [one_mul]
  ε₂_ε₁ _ _ _ := by dsimp; rw [one_mul, mul_one]
  ε₂_eq_mul _ _ _ := by dsimp; rw [ε_add]

end ComplexShape

/-- The total complex shape for `c₂`, `c₁` and `c₁₂` that is deduced
from a total complex shape for `c₁`, `c₂` and `c₁₂`. -/
@[instance_reducible]
/--
Definition of `TotalComplexShape.symm` / `TotalComplexShape.symm` 的定义

English:
definition TotalComplexShape.symm
  signature: [TotalComplexShape c₁ c₂ c₁₂]
  body: fun ⟨i₂, i₁⟩ => ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  ε₁ := fun ⟨i₂, i₁⟩ => ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  ε₂ := fun ⟨i₂, i₁⟩ => ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  rel₁ h i₁ := ComplexShape.rel_π₂ c₁ c₁₂ i₁ h
  rel₂ i₂ _ _ h := ComplexShape.rel_π₁ c₂ c₁₂ h i₂
  ε₂_ε₁ h₂ h₁ := by
    rw [neg_mu

中文:
定义 TotalComplexShape.symm
  签名: [TotalComplexShape c₁ c₂ c₁₂]
  定义体: fun ⟨i₂, i₁⟩ => ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  ε₁ := fun ⟨i₂, i₁⟩ => ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  ε₂ := fun ⟨i₂, i₁⟩ => ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  rel₁ h i₁ := ComplexShape.rel_π₂ c₁ c₁₂ i₁ h
  rel₂ i₂ _ _ h := ComplexShape.rel_π₁ c₂ c₁₂ h i₂
  ε₂_ε₁ h₂ h₁ := by
    rw [neg_mu

Depends on / 依赖: ComplexShape
-/
def TotalComplexShape.symm [TotalComplexShape c₁ c₂ c₁₂] :
    TotalComplexShape c₂ c₁ c₁₂ where
  π := fun ⟨i₂, i₁⟩ => ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  ε₁ := fun ⟨i₂, i₁⟩ => ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  ε₂ := fun ⟨i₂, i₁⟩ => ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  rel₁ h i₁ := ComplexShape.rel_π₂ c₁ c₁₂ i₁ h
  rel₂ i₂ _ _ h := ComplexShape.rel_π₁ c₂ c₁₂ h i₂
  ε₂_ε₁ h₂ h₁ := by
    rw [neg_mul]; rw [ComplexShape.ε₂_ε₁ c₁₂ h₁ h₂]; rw [neg_mul]; rw [neg_neg]

/--
Definition of `TotalComplexShapeSymmetry` / `TotalComplexShapeSymmetry` 的定义

English:
class TotalComplexShapeSymmetry
  parameters: [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₁ c₁₂]
  axioms and operations (4):
    - symm((i₁ : I₁) (i₂ : I₂)) : ComplexShape.π c₂ c₁ c₁₂ ⟨i₂, i₁⟩ = ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩
    - σ((i₁ : I₁) (i₂ : I₂)) : Intˣ
    - σ_ε₁({i₁ i₁' : I₁} (h₁ : c₁.Rel i₁ i₁') (i₂ : I₂)) : σ i₁ i₂ * ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ComplexShape.ε₂ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ i₁' i₂
    - σ_ε₂((i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.Rel i₂ i₂')) : σ i₁ i₂ * ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ComplexShape.ε₁ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ i₁ i₂'

中文:
类 TotalComplexShapeSymmetry
  参数: [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₁ c₁₂]
  公理与运算 (4 个):
    - symm((i₁ : I₁) (i₂ : I₂)) : 余mplexShape.π c₂ c₁ c₁₂ ⟨i₂, i₁⟩ = 余mplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩
    - σ((i₁ : I₁) (i₂ : I₂)) : 整数ˣ
    - σ_ε₁({i₁ i₁' : I₁} (h₁ : c₁.关系 i₁ i₁') (i₂ : I₂)) : σ i₁ i₂ * 余mplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = 余mplexShape.ε₂ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ i₁' i₂
    - σ_ε₂((i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.关系 i₂ i₂')) : σ i₁ i₂ * 余mplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = 余mplexShape.ε₁ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ i₁ i₂'
-/
class TotalComplexShapeSymmetry [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₁ c₁₂] where
  symm (i₁ : I₁) (i₂ : I₂) : ComplexShape.π c₂ c₁ c₁₂ ⟨i₂, i₁⟩ = ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  /-- the signs involved in the symmetry isomorphism of the total complex -/
  σ (i₁ : I₁) (i₂ : I₂) : Intˣ
  σ_ε₁ {i₁ i₁' : I₁} (h₁ : c₁.Rel i₁ i₁') (i₂ : I₂) :
    σ i₁ i₂ * ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ComplexShape.ε₂ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ i₁' i₂
  σ_ε₂ (i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.Rel i₂ i₂') :
    σ i₁ i₂ * ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ComplexShape.ε₁ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ i₁ i₂'

/-- The symmetry between the total complex shape for `c₁`, `c₂` and `c₁₂`,
and its symmetric total complex shape. -/
@[instance_reducible]
/--
Definition of `TotalComplexShape.symmSymmetry` / `TotalComplexShape.symmSymmetry` 的定义

English:
definition TotalComplexShape.symmSymmetry
  signature: [TotalComplexShape c₁ c₂ c₁₂]
  body: TotalComplexShape.symm c₁ c₂ c₁₂
    TotalComplexShapeSymmetry c₁ c₂ c₁₂ :=
  letI := TotalComplexShape.symm c₁ c₂ c₁₂
  { symm i₁ i₂ := rfl
    σ _ _ := 1
    σ_ε₁ _ _ := by aesop
    σ_ε₂ _ _ := by aesop }

中文:
定义 TotalComplexShape.symmSymmetry
  签名: [TotalComplexShape c₁ c₂ c₁₂]
  定义体: TotalComplexShape.symm c₁ c₂ c₁₂
    TotalComplexShapeSymmetry c₁ c₂ c₁₂ :=
  letI := TotalComplexShape.symm c₁ c₂ c₁₂
  { symm i₁ i₂ := rfl
    σ _ _ := 1
    σ_ε₁ _ _ := by aesop
    σ_ε₂ _ _ := by aesop }

Depends on / 依赖: TotalComplexShape, TotalComplexShape.symm
-/
def TotalComplexShape.symmSymmetry [TotalComplexShape c₁ c₂ c₁₂] :
    letI := TotalComplexShape.symm c₁ c₂ c₁₂
    TotalComplexShapeSymmetry c₁ c₂ c₁₂ :=
  letI := TotalComplexShape.symm c₁ c₂ c₁₂
  { symm i₁ i₂ := rfl
    σ _ _ := 1
    σ_ε₁ _ _ := by aesop
    σ_ε₂ _ _ := by aesop }

namespace ComplexShape

variable [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₁ c₁₂]
  [TotalComplexShapeSymmetry c₁ c₂ c₁₂]

/--
Definition of `σ` / `σ` 的定义

English:
abbreviation σ
  signature: (i₁ : I₁) (i₂ : I₂)
  body: TotalComplexShapeSymmetry.σ c₁ c₂ c₁₂ i₁ i₂

中文:
缩写 σ
  签名: (i₁ : I₁) (i₂ : I₂)
  定义体: TotalComplexShapeSymmetry.σ c₁ c₂ c₁₂ i₁ i₂

Depends on / 依赖: TotalComplexShapeSymmetry
-/
abbrev σ (i₁ : I₁) (i₂ : I₂) : Intˣ := TotalComplexShapeSymmetry.σ c₁ c₂ c₁₂ i₁ i₂

/--
lemma `π_symm` / 引理 `π_symm`

English:
lemma π_symm
  given: (i₁ : I₁) (i₂ : I₂)
  proof: by
  apply TotalComplexShapeSymmetry.symm

中文:
引理 π_symm
  条件: (i₁ : I₁) (i₂ : I₂)
  证明: by
  apply TotalComplexShapeSymmetry.symm

Depends on / 依赖: TotalComplexShapeSymmetry, TotalComplexShapeSymmetry.symm
-/
lemma π_symm (i₁ : I₁) (i₂ : I₂) :
    π c₂ c₁ c₁₂ ⟨i₂, i₁⟩ = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ := by
  apply TotalComplexShapeSymmetry.symm

/-- The symmetry bijection `(π c₂ c₁ c₁₂ ⁻¹' {j}) ≃ (π c₁ c₂ c₁₂ ⁻¹' {j})`. -/
@[simps]
/--
Definition of `symmetryEquiv` / `symmetryEquiv` 的定义

English:
definition symmetryEquiv
  signature: (j : I₁₂)
  body: fun ⟨⟨i₂, i₁⟩, h⟩ => ⟨⟨i₁, i₂⟩, by simpa [π_symm] using h⟩
  invFun := fun ⟨⟨i₁, i₂⟩, h⟩ => ⟨⟨i₂, i₁⟩, by simpa [π_symm] using h⟩

中文:
定义 symmetryEquiv
  签名: (j : I₁₂)
  定义体: fun ⟨⟨i₂, i₁⟩, h⟩ => ⟨⟨i₁, i₂⟩, by simpa [π_symm] using h⟩
  invFun := fun ⟨⟨i₁, i₂⟩, h⟩ => ⟨⟨i₂, i₁⟩, by simpa [π_symm] using h⟩
-/
def symmetryEquiv (j : I₁₂) :
    (π c₂ c₁ c₁₂ ⁻¹' {j}) ≃ (π c₁ c₂ c₁₂ ⁻¹' {j}) where
  toFun := fun ⟨⟨i₂, i₁⟩, h⟩ => ⟨⟨i₁, i₂⟩, by simpa [π_symm] using h⟩
  invFun := fun ⟨⟨i₁, i₂⟩, h⟩ => ⟨⟨i₂, i₁⟩, by simpa [π_symm] using h⟩

variable {c₁}

/--
lemma `σ_ε₁` / 引理 `σ_ε₁`

English:
lemma σ_ε₁
  given: {i₁ i₁' : I₁} (h₁ : c₁.Rel i₁ i₁') (i₂ : I₂)
  proof: TotalComplexShapeSymmetry.σ_ε₁ h₁ i₂

中文:
引理 σ_ε₁
  条件: {i₁ i₁' : I₁} (h₁ : c₁.关系 i₁ i₁') (i₂ : I₂)
  证明: TotalComplexShapeSymmetry.σ_ε₁ h₁ i₂

Depends on / 依赖: TotalComplexShapeSymmetry
-/
lemma σ_ε₁ {i₁ i₁' : I₁} (h₁ : c₁.Rel i₁ i₁') (i₂ : I₂) :
    σ c₁ c₂ c₁₂ i₁ i₂ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ε₂ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ c₁ c₂ c₁₂ i₁' i₂ :=
  TotalComplexShapeSymmetry.σ_ε₁ h₁ i₂

variable (c₁) {c₂}

/--
lemma `σ_ε₂` / 引理 `σ_ε₂`

English:
lemma σ_ε₂
  given: (i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.Rel i₂ i₂')
  proof: TotalComplexShapeSymmetry.σ_ε₂ i₁ h₂

中文:
引理 σ_ε₂
  条件: (i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.关系 i₂ i₂')
  证明: TotalComplexShapeSymmetry.σ_ε₂ i₁ h₂

Depends on / 依赖: TotalComplexShapeSymmetry
-/
lemma σ_ε₂ (i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.Rel i₂ i₂') :
    σ c₁ c₂ c₁₂ i₁ i₂ * ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ε₁ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ c₁ c₂ c₁₂ i₁ i₂' :=
  TotalComplexShapeSymmetry.σ_ε₂ i₁ h₂

set_option backward.isDefEq.respectTransparency.types false in
@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TotalComplexShapeSymmetry (up Int) (up Int) (up Int)
  body: add_comm q p
  σ p q := (p * q).negOnePow
  σ_ε₁ := by
    rintro p _ rfl q
    dsimp
    rw [mul_one]; rw [← Int.negOnePow_add]; rw [add_comm q]; rw [add_mul]; rw [one_mul]; rw [Int.negOnePow_add]; rw [Int.negOnePow_add]; rw [mul_assoc]; rw [Int.units_mul_self]; rw [mul_one]
  σ_ε₂ := by
    rintro

中文:
实例 :
  签名: TotalComplexShapeSymmetry (up 整数) (up 整数) (up 整数)
  定义体: add_comm q p
  σ p q := (p * q).negOnePow
  σ_ε₁ := by
    rintro p _ rfl q
    dsimp
    rw [mul_one]; rw [← Int.negOnePow_add]; rw [add_comm q]; rw [add_mul]; rw [one_mul]; rw [Int.negOnePow_add]; rw [Int.negOnePow_add]; rw [mul_assoc]; rw [Int.units_mul_self]; rw [mul_one]
  σ_ε₂ := by
    rintro

Depends on / 依赖: add_comm
-/
instance : TotalComplexShapeSymmetry (up Int) (up Int) (up Int) where
  symm p q := add_comm q p
  σ p q := (p * q).negOnePow
  σ_ε₁ := by
    rintro p _ rfl q
    dsimp
    rw [mul_one]; rw [← Int.negOnePow_add]; rw [add_comm q]; rw [add_mul]; rw [one_mul]; rw [Int.negOnePow_add]; rw [Int.negOnePow_add]; rw [mul_assoc]; rw [Int.units_mul_self]; rw [mul_one]
  σ_ε₂ := by
    rintro p q _ rfl
    dsimp
    rw [one_mul]; rw [← Int.negOnePow_add]; rw [mul_add]; rw [mul_one]

end ComplexShape

/-- The obvious `TotalComplexShapeSymmetry c₂ c₁ c₁₂` deduced from a
`TotalComplexShapeSymmetry c₁ c₂ c₁₂`. -/
@[instance_reducible]
/--
Definition of `TotalComplexShapeSymmetry.symmetry` / `TotalComplexShapeSymmetry.symmetry` 的定义

English:
definition TotalComplexShapeSymmetry.symmetry
  signature: [TotalComplexShape c₁ c₂ c₁₂]
  body: (ComplexShape.π_symm c₁ c₂ c₁₂ i₁ i₂).symm
  σ i₂ i₁ := ComplexShape.σ c₁ c₂ c₁₂ i₁ i₂
  σ_ε₁ {i₂ i₂'} h₂ i₁ := by
    apply mul_right_cancel (b := ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂))
    rw [mul_assoc]
    nth_rw 2 [mul_comm]
    rw [← mul_assoc]; rw [ComplexShape.σ_ε₂ c₁ c₁₂ i₁ h₂]; rw [mul_comm];

中文:
定义 TotalComplexShapeSymmetry.symmetry
  签名: [TotalComplexShape c₁ c₂ c₁₂]
  定义体: (ComplexShape.π_symm c₁ c₂ c₁₂ i₁ i₂).symm
  σ i₂ i₁ := ComplexShape.σ c₁ c₂ c₁₂ i₁ i₂
  σ_ε₁ {i₂ i₂'} h₂ i₁ := by
    apply mul_right_cancel (b := ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂))
    rw [mul_assoc]
    nth_rw 2 [mul_comm]
    rw [← mul_assoc]; rw [ComplexShape.σ_ε₂ c₁ c₁₂ i₁ h₂]; rw [mul_comm];

Depends on / 依赖: ComplexShape
-/
def TotalComplexShapeSymmetry.symmetry [TotalComplexShape c₁ c₂ c₁₂]
    [TotalComplexShape c₂ c₁ c₁₂] [TotalComplexShapeSymmetry c₁ c₂ c₁₂] :
    TotalComplexShapeSymmetry c₂ c₁ c₁₂ where
  symm i₂ i₁ := (ComplexShape.π_symm c₁ c₂ c₁₂ i₁ i₂).symm
  σ i₂ i₁ := ComplexShape.σ c₁ c₂ c₁₂ i₁ i₂
  σ_ε₁ {i₂ i₂'} h₂ i₁ := by
    apply mul_right_cancel (b := ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂))
    rw [mul_assoc]
    nth_rw 2 [mul_comm]
    rw [← mul_assoc]; rw [ComplexShape.σ_ε₂ c₁ c₁₂ i₁ h₂]; rw [mul_comm]; rw [← mul_assoc]; rw [Int.units_mul_self]; rw [one_mul]; rw [mul_comm]; rw [← mul_assoc]; rw [Int.units_mul_self]; rw [one_mul]
  σ_ε₂ i₂ i₁ i₁' h₁ := by
    apply mul_right_cancel (b := ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂))
    rw [mul_assoc]
    nth_rw 2 [mul_comm]
    rw [← mul_assoc]; rw [ComplexShape.σ_ε₁ c₂ c₁₂ h₁ i₂]; rw [mul_comm]; rw [← mul_assoc]; rw [Int.units_mul_self]; rw [one_mul]; rw [mul_comm]; rw [← mul_assoc]; rw [Int.units_mul_self]; rw [one_mul]

/--
Definition of `TotalComplexShapeSymmetrySymmetry` / `TotalComplexShapeSymmetrySymmetry` 的定义

English:
class TotalComplexShapeSymmetrySymmetry
  parameters: [TotalComplexShape c₁ c₂ c₁₂]
  axioms and operations (1):
    - σ_symm(i₁ i₂) : ComplexShape.σ c₂ c₁ c₁₂ i₂ i₁ = ComplexShape.σ c₁ c₂ c₁₂ i₁ i₂

中文:
类 TotalComplexShapeSymmetrySymmetry
  参数: [TotalComplexShape c₁ c₂ c₁₂]
  公理与运算 (1 个):
    - σ_symm(i₁ i₂) : 余mplexShape.σ c₂ c₁ c₁₂ i₂ i₁ = 余mplexShape.σ c₁ c₂ c₁₂ i₁ i₂
-/
class TotalComplexShapeSymmetrySymmetry [TotalComplexShape c₁ c₂ c₁₂]
    [TotalComplexShape c₂ c₁ c₁₂] [TotalComplexShapeSymmetry c₁ c₂ c₁₂]
    [TotalComplexShapeSymmetry c₂ c₁ c₁₂] : Prop where
  σ_symm i₁ i₂ : ComplexShape.σ c₂ c₁ c₁₂ i₂ i₁ = ComplexShape.σ c₁ c₂ c₁₂ i₁ i₂

namespace ComplexShape

variable [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₁ c₁₂]
  [TotalComplexShapeSymmetry c₁ c₂ c₁₂] [TotalComplexShapeSymmetry c₂ c₁ c₁₂]
  [TotalComplexShapeSymmetrySymmetry c₁ c₂ c₁₂]

/--
lemma `σ_symm` / 引理 `σ_symm`

English:
lemma σ_symm
  given: (i₁ : I₁) (i₂ : I₂)
  proof: by
  apply TotalComplexShapeSymmetrySymmetry.σ_symm

中文:
引理 σ_symm
  条件: (i₁ : I₁) (i₂ : I₂)
  证明: by
  apply TotalComplexShapeSymmetrySymmetry.σ_symm

Depends on / 依赖: TotalComplexShapeSymmetrySymmetry
-/
lemma σ_symm (i₁ : I₁) (i₂ : I₂) :
    σ c₂ c₁ c₁₂ i₂ i₁ = σ c₁ c₂ c₁₂ i₁ i₂ := by
  apply TotalComplexShapeSymmetrySymmetry.σ_symm

end ComplexShape
