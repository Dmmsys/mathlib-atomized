/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Monotone.Defs

/-!

# Covariants and contravariants

This file contains general lemmas and instances to work with the interactions between a relation and
an action on a Type.

The intended application is the splitting of the ordering from the algebraic assumptions on the
operations in the `Ordered[...]` hierarchy.

The strategy is to introduce two more flexible typeclasses, `CovariantClass` and
`ContravariantClass`:

* `CovariantClass` models the implication `a ≤ b → c * a ≤ c * b` (multiplication is monotone),
* `ContravariantClass` models the implication `a * b < a * c → b < c`.

Since `Co(ntra)variantClass` takes as input the operation (typically `(+)` or `(*)`) and the order
relation (typically `(≤)` or `(<)`), these are the only two typeclasses that I have used.

The general approach is to formulate the lemma that you are interested in and prove it, with the
`IsOrdered[...]` typeclass of your liking. After that, you convert the typeclass,
say `[IsOrderedCancelMonoid M]`, into whichever typeclasses, e.g.
`[CovariantClass M M (Function.swap (*)) (≤)]`
and have a go at seeing if the proof still works!

Note that it is possible to combine several `Co(ntra)variantClass` assumptions together.
Indeed, the usual ordered typeclasses arise from assuming the pair
`[CovariantClass M M (*) (≤)] [ContravariantClass M M (*) (<)]`
on top of order/algebraic assumptions.

A formal remark is that normally `CovariantClass` uses the `(≤)`-relation, while
`ContravariantClass` uses the `(<)`-relation. This need not be the case in general, but seems to be
the most common usage. In the opposite direction, the implication
```lean
[Semigroup α] [PartialOrder α] [ContravariantClass α α (*) (≤)] → LeftCancelSemigroup α
```
holds -- note the `Co*ntra*` assumption on the `(≤)`-relation.

## Formalization notes

We stick to the convention of using `Function.swap (*)` (or `Function.swap (+)`), for the
typeclass assumptions, since `Function.swap` is slightly better behaved than `flip`.
However, sometimes as a **non-typeclass** assumption, we prefer `flip (*)` (or `flip (+)`),
as it is easier to use.

## TODO

This is unergonomic. Inline in `MulLeftMono` and friends.
-/

@[expose] public section


-- TODO: convert `ExistsMulOfLE`, `ExistsAddOfLE`?
-- TODO: relationship with `Con/AddCon`
-- TODO: include equivalence of `LeftCancelSemigroup` with
-- `Semigroup PartialOrder ContravariantClass α α (*) (≤)`?
-- TODO : use ⇒, as per Eric's suggestion? See
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/ordered.20stuff/near/236148738
-- for a discussion.
open Function

section Variants

variable {M N : Type*} (μ : M -> N -> N) (r : N -> N -> Prop)
variable (M N)

/--
Definition of `Covariant` / `Covariant` 的定义

English:
definition Covariant
  signature: : Prop
  body: forall (m) {n₁ n₂}, r n₁ n₂ -> r (μ m n₁) (μ m n₂)

中文:
定义 Covariant
  签名: : 命题
  定义体: forall (m) {n₁ n₂}, r n₁ n₂ -> r (μ m n₁) (μ m n₂)
-/
def Covariant : Prop :=
  forall (m) {n₁ n₂}, r n₁ n₂ -> r (μ m n₁) (μ m n₂)

/--
Definition of `Contravariant` / `Contravariant` 的定义

English:
definition Contravariant
  signature: : Prop
  body: forall (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) -> r n₁ n₂

中文:
定义 Contravariant
  签名: : 命题
  定义体: forall (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) -> r n₁ n₂
-/
def Contravariant : Prop :=
  forall (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) -> r n₁ n₂

/--
Definition of `CovariantClass` / `CovariantClass` 的定义

English:
class CovariantClass
  parameters: : Prop where
  axioms and operations (1):
    - elim : Covariant M N μ r

中文:
类 CovariantClass
  参数: : 命题 where
  公理与运算 (1 个):
    - elim : Covariant M N μ r
-/
class CovariantClass : Prop where
  /-- For all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
  `(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)` -/
  protected elim : Covariant M N μ r

/--
Definition of `ContravariantClass` / `ContravariantClass` 的定义

English:
class ContravariantClass
  parameters: : Prop where
  axioms and operations (1):
    - elim : Contravariant M N μ r

中文:
类 ContravariantClass
  参数: : 命题 where
  公理与运算 (1 个):
    - elim : Contravariant M N μ r
-/
class ContravariantClass : Prop where
  /-- For all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the
  pair `(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by acting upon it by `m`, then, the relation
  `r` also holds for the pair `(n₁, n₂)`. -/
  protected elim : Contravariant M N μ r

/--
Definition of `MulLeftMono` / `MulLeftMono` 的定义

English:
abbreviation MulLeftMono
  signature: [Mul M] [LE M]
  body: CovariantClass M M (· * ·) (· <= ·)

中文:
缩写 MulLeftMono
  签名: [Mul M] [LE M]
  定义体: CovariantClass M M (· * ·) (· <= ·)

Depends on / 依赖: CovariantClass
-/
abbrev MulLeftMono [Mul M] [LE M] : Prop :=
  CovariantClass M M (· * ·) (· <= ·)

/--
Definition of `MulRightMono` / `MulRightMono` 的定义

English:
abbreviation MulRightMono
  signature: [Mul M] [LE M]
  body: CovariantClass M M (swap (· * ·)) (· <= ·)

中文:
缩写 MulRightMono
  签名: [Mul M] [LE M]
  定义体: CovariantClass M M (swap (· * ·)) (· <= ·)

Depends on / 依赖: CovariantClass
-/
abbrev MulRightMono [Mul M] [LE M] : Prop :=
  CovariantClass M M (swap (· * ·)) (· <= ·)

/--
Definition of `AddLeftMono` / `AddLeftMono` 的定义

English:
abbreviation AddLeftMono
  signature: [Add M] [LE M]
  body: CovariantClass M M (· + ·) (· <= ·)

中文:
缩写 AddLeftMono
  签名: [Add M] [LE M]
  定义体: CovariantClass M M (· + ·) (· <= ·)

Depends on / 依赖: CovariantClass
-/
abbrev AddLeftMono [Add M] [LE M] : Prop :=
  CovariantClass M M (· + ·) (· <= ·)

/--
Definition of `AddRightMono` / `AddRightMono` 的定义

English:
abbreviation AddRightMono
  signature: [Add M] [LE M]
  body: CovariantClass M M (swap (· + ·)) (· <= ·)

中文:
缩写 AddRightMono
  签名: [Add M] [LE M]
  定义体: CovariantClass M M (swap (· + ·)) (· <= ·)

Depends on / 依赖: CovariantClass
-/
abbrev AddRightMono [Add M] [LE M] : Prop :=
  CovariantClass M M (swap (· + ·)) (· <= ·)

attribute [to_additive existing] MulLeftMono MulRightMono

/--
Definition of `MulLeftStrictMono` / `MulLeftStrictMono` 的定义

English:
abbreviation MulLeftStrictMono
  signature: [Mul M] [LT M]
  body: CovariantClass M M (· * ·) (· < ·)

中文:
缩写 MulLeftStrictMono
  签名: [Mul M] [LT M]
  定义体: CovariantClass M M (· * ·) (· < ·)

Depends on / 依赖: CovariantClass
-/
abbrev MulLeftStrictMono [Mul M] [LT M] : Prop :=
  CovariantClass M M (· * ·) (· < ·)

/--
Definition of `MulRightStrictMono` / `MulRightStrictMono` 的定义

English:
abbreviation MulRightStrictMono
  signature: [Mul M] [LT M]
  body: CovariantClass M M (swap (· * ·)) (· < ·)

中文:
缩写 MulRightStrictMono
  签名: [Mul M] [LT M]
  定义体: CovariantClass M M (swap (· * ·)) (· < ·)

Depends on / 依赖: CovariantClass
-/
abbrev MulRightStrictMono [Mul M] [LT M] : Prop :=
  CovariantClass M M (swap (· * ·)) (· < ·)

/--
Definition of `AddLeftStrictMono` / `AddLeftStrictMono` 的定义

English:
abbreviation AddLeftStrictMono
  signature: [Add M] [LT M]
  body: CovariantClass M M (· + ·) (· < ·)

中文:
缩写 AddLeftStrictMono
  签名: [Add M] [LT M]
  定义体: CovariantClass M M (· + ·) (· < ·)

Depends on / 依赖: CovariantClass
-/
abbrev AddLeftStrictMono [Add M] [LT M] : Prop :=
  CovariantClass M M (· + ·) (· < ·)

/--
Definition of `AddRightStrictMono` / `AddRightStrictMono` 的定义

English:
abbreviation AddRightStrictMono
  signature: [Add M] [LT M]
  body: CovariantClass M M (swap (· + ·)) (· < ·)

中文:
缩写 AddRightStrictMono
  签名: [Add M] [LT M]
  定义体: CovariantClass M M (swap (· + ·)) (· < ·)

Depends on / 依赖: CovariantClass
-/
abbrev AddRightStrictMono [Add M] [LT M] : Prop :=
  CovariantClass M M (swap (· + ·)) (· < ·)

attribute [to_additive existing] MulLeftStrictMono MulRightStrictMono

/--
Definition of `MulLeftReflectLT` / `MulLeftReflectLT` 的定义

English:
abbreviation MulLeftReflectLT
  signature: [Mul M] [LT M]
  body: ContravariantClass M M (· * ·) (· < ·)

中文:
缩写 MulLeftReflectLT
  签名: [Mul M] [LT M]
  定义体: ContravariantClass M M (· * ·) (· < ·)

Depends on / 依赖: ContravariantClass
-/
abbrev MulLeftReflectLT [Mul M] [LT M] : Prop :=
  ContravariantClass M M (· * ·) (· < ·)

/--
Definition of `MulRightReflectLT` / `MulRightReflectLT` 的定义

English:
abbreviation MulRightReflectLT
  signature: [Mul M] [LT M]
  body: ContravariantClass M M (swap (· * ·)) (· < ·)

中文:
缩写 MulRightReflectLT
  签名: [Mul M] [LT M]
  定义体: ContravariantClass M M (swap (· * ·)) (· < ·)

Depends on / 依赖: ContravariantClass
-/
abbrev MulRightReflectLT [Mul M] [LT M] : Prop :=
  ContravariantClass M M (swap (· * ·)) (· < ·)

/--
Definition of `AddLeftReflectLT` / `AddLeftReflectLT` 的定义

English:
abbreviation AddLeftReflectLT
  signature: [Add M] [LT M]
  body: ContravariantClass M M (· + ·) (· < ·)

中文:
缩写 AddLeftReflectLT
  签名: [Add M] [LT M]
  定义体: ContravariantClass M M (· + ·) (· < ·)

Depends on / 依赖: ContravariantClass
-/
abbrev AddLeftReflectLT [Add M] [LT M] : Prop :=
  ContravariantClass M M (· + ·) (· < ·)

/--
Definition of `AddRightReflectLT` / `AddRightReflectLT` 的定义

English:
abbreviation AddRightReflectLT
  signature: [Add M] [LT M]
  body: ContravariantClass M M (swap (· + ·)) (· < ·)

中文:
缩写 AddRightReflectLT
  签名: [Add M] [LT M]
  定义体: ContravariantClass M M (swap (· + ·)) (· < ·)

Depends on / 依赖: ContravariantClass
-/
abbrev AddRightReflectLT [Add M] [LT M] : Prop :=
  ContravariantClass M M (swap (· + ·)) (· < ·)

attribute [to_additive existing] MulLeftReflectLT MulRightReflectLT

/--
Definition of `MulLeftReflectLE` / `MulLeftReflectLE` 的定义

English:
class MulLeftReflectLE
  parameters: [Mul M] [LE M]
  axioms and operations (1):
    - le_of_mul_le_mul_left'({a b₁ b₂ : M}) : a * b₁ <= a * b₂ -> b₁ <= b₂

中文:
类 MulLeftReflectLE
  参数: [Mul M] [LE M]
  公理与运算 (1 个):
    - le_of_mul_le_mul_left'({a b₁ b₂ : M}) : a * b₁ <= a * b₂ -> b₁ <= b₂
-/
class MulLeftReflectLE [Mul M] [LE M] : Prop where
  /-- Do not use this. Use `le_of_mul_le_mul_left'` instead. -/
  protected le_of_mul_le_mul_left' {a b₁ b₂ : M} : a * b₁ <= a * b₂ -> b₁ <= b₂

/--
Definition of `MulRightReflectLE` / `MulRightReflectLE` 的定义

English:
class MulRightReflectLE
  parameters: [Mul M] [LE M]
  axioms and operations (1):
    - le_of_mul_le_mul_right'({b a₁ a₂ : M}) : a₁ * b <= a₂ * b -> a₁ <= a₂

中文:
类 MulRightReflectLE
  参数: [Mul M] [LE M]
  公理与运算 (1 个):
    - le_of_mul_le_mul_right'({b a₁ a₂ : M}) : a₁ * b <= a₂ * b -> a₁ <= a₂
-/
class MulRightReflectLE [Mul M] [LE M] : Prop where
  /-- Do not use this. Use `le_of_mul_le_mul_right'` instead. -/
  protected le_of_mul_le_mul_right' {b a₁ a₂ : M} : a₁ * b <= a₂ * b -> a₁ <= a₂

/--
Definition of `AddLeftReflectLE` / `AddLeftReflectLE` 的定义

English:
class AddLeftReflectLE
  parameters: [Add M] [LE M]
  axioms and operations (1):
    - le_of_add_le_add_left({a b₁ b₂ : M}) : a + b₁ <= a + b₂ -> b₁ <= b₂

中文:
类 AddLeftReflectLE
  参数: [Add M] [LE M]
  公理与运算 (1 个):
    - le_of_add_le_add_left({a b₁ b₂ : M}) : a + b₁ <= a + b₂ -> b₁ <= b₂
-/
class AddLeftReflectLE [Add M] [LE M] : Prop where
  /-- Do not use this. Use `le_of_add_le_add_left` instead. -/
  protected le_of_add_le_add_left {a b₁ b₂ : M} : a + b₁ <= a + b₂ -> b₁ <= b₂

/--
Definition of `AddRightReflectLE` / `AddRightReflectLE` 的定义

English:
class AddRightReflectLE
  parameters: [Add M] [LE M]
  axioms and operations (1):
    - le_of_add_le_add_right({b a₁ a₂ : M}) : a₁ + b <= a₂ + b -> a₁ <= a₂

中文:
类 AddRightReflectLE
  参数: [Add M] [LE M]
  公理与运算 (1 个):
    - le_of_add_le_add_right({b a₁ a₂ : M}) : a₁ + b <= a₂ + b -> a₁ <= a₂
-/
class AddRightReflectLE [Add M] [LE M] : Prop where
  /-- Do not use this. Use `le_of_add_le_add_right` instead. -/
  protected le_of_add_le_add_right {b a₁ a₂ : M} : a₁ + b <= a₂ + b -> a₁ <= a₂

attribute [to_additive existing] MulLeftReflectLE MulRightReflectLE

variable {M N μ r} in
/--
theorem `rel_iff_cov'` / 定理 `rel_iff_cov'`

English:
theorem rel_iff_cov'
  statement: (hcov : Covariant M N μ r) (hcontra : Contravariant M N μ r) {m : M}
  proof: ⟨hcontra m, hcov m⟩

中文:
定理 rel_iff_cov'
  结论: (hcov : Covariant M N μ r) (hcontra : Contravariant M N μ r) {m : M}
  证明: ⟨hcontra m, hcov m⟩

Depends on / 依赖: hcontra
-/
theorem rel_iff_cov' (hcov : Covariant M N μ r) (hcontra : Contravariant M N μ r) {m : M}
    {a b : N} : r (μ m a) (μ m b) ↔ r a b :=
  ⟨hcontra m, hcov m⟩

/--
theorem `rel_iff_cov` / 定理 `rel_iff_cov`

English:
theorem rel_iff_cov
  given: [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) {a b : N}
  proof: rel_iff_cov' CovariantClass.elim ContravariantClass.elim

中文:
定理 rel_iff_cov
  条件: [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) {a b : N}
  证明: rel_iff_cov' CovariantClass.elim ContravariantClass.elim

Depends on / 依赖: ContravariantClass, ContravariantClass.elim, CovariantClass, CovariantClass.elim, rel_iff_cov
-/
theorem rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) {a b : N} :
    r (μ m a) (μ m b) ↔ r a b :=
  rel_iff_cov' CovariantClass.elim ContravariantClass.elim

section flip

variable {M N μ r}

/--
theorem `Covariant.flip` / 定理 `Covariant.flip`

English:
theorem Covariant.flip
  given: (h : Covariant M N μ r)
  statement: Covariant M N μ (flip r)
  proof: fun a _ _ => h a

中文:
定理 Covariant.flip
  条件: (h : Covariant M N μ r)
  结论: Covariant M N μ (flip r)
  证明: fun a _ _ => h a
-/
theorem Covariant.flip (h : Covariant M N μ r) : Covariant M N μ (flip r) :=
  fun a _ _ => h a

/--
theorem `Contravariant.flip` / 定理 `Contravariant.flip`

English:
theorem Contravariant.flip
  given: (h : Contravariant M N μ r)
  statement: Contravariant M N μ (flip r)
  proof: fun a _ _ => h a

中文:
定理 Contravariant.flip
  条件: (h : Contravariant M N μ r)
  结论: Contravariant M N μ (flip r)
  证明: fun a _ _ => h a
-/
theorem Contravariant.flip (h : Contravariant M N μ r) : Contravariant M N μ (flip r) :=
  fun a _ _ => h a

end flip

section Covariant

variable {M N μ r} [CovariantClass M N μ r]

/--
theorem `act_rel_act_of_rel` / 定理 `act_rel_act_of_rel`

English:
theorem act_rel_act_of_rel
  given: (m : M) {a b : N} (ab : r a b)
  statement: r (μ m a) (μ m b)
  proof: CovariantClass.elim _ ab

@[to_additive]

中文:
定理 act_rel_act_of_rel
  条件: (m : M) {a b : N} (ab : r a b)
  结论: r (μ m a) (μ m b)
  证明: CovariantClass.elim _ ab

@[to_additive]

Depends on / 依赖: CovariantClass, CovariantClass.elim
-/
theorem act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : r (μ m a) (μ m b) :=
  CovariantClass.elim _ ab

@[to_additive]
/--
theorem `Group.covariant_iff_contravariant` / 定理 `Group.covariant_iff_contravariant`

English:
theorem Group.covariant_iff_contravariant
  given: [Group N]
  proof: by
  refine ⟨fun h a b c bc => ?_, fun h a b c bc => ?_⟩
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c]
    exact h a⁻¹ bc
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c] at bc
    exact h a⁻¹ bc

@[to_additive]

中文:
定理 Group.covariant_iff_contravariant
  条件: [Group N]
  证明: by
  refine ⟨fun h a b c bc => ?_, fun h a b c bc => ?_⟩
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c]
    exact h a⁻¹ bc
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c] at bc
    exact h a⁻¹ bc

@[to_additive]

Depends on / 依赖: inv_mul_cancel_left
-/
theorem Group.covariant_iff_contravariant [Group N] :
    Covariant N N (· * ·) r ↔ Contravariant N N (· * ·) r := by
  refine ⟨fun h a b c bc => ?_, fun h a b c bc => ?_⟩
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c]
    exact h a⁻¹ bc
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c] at bc
    exact h a⁻¹ bc

@[to_additive]
instance (priority := 100) Group.covconv [Group N] [CovariantClass N N (· * ·) r] :
    ContravariantClass N N (· * ·) r :=
  ⟨Group.covariant_iff_contravariant.mp CovariantClass.elim⟩

@[to_additive]
/--
Instance `Group.mulLeftReflectLE_of_mulLeftMono` / 实例 `Group.mulLeftReflectLE_of_mulLeftMono`

English:
instance Group.mulLeftReflectLE_of_mulLeftMono
  signature: [Group N] [LE N] [MulLeftMono N]
  body: Group.covariant_iff_contravariant.mp CovariantClass.elim _

@[to_additive]

中文:
实例 Group.mulLeftReflectLE_of_mulLeftMono
  签名: [Group N] [LE N] [MulLeftMono N]
  定义体: Group.covariant_iff_contravariant.mp CovariantClass.elim _

@[to_additive]

Depends on / 依赖: CovariantClass, CovariantClass.elim, Group.covariant_iff_contravariant.mp, covariant_iff_contravariant
-/
instance Group.mulLeftReflectLE_of_mulLeftMono [Group N] [LE N] [MulLeftMono N] :
    MulLeftReflectLE N where
  le_of_mul_le_mul_left' := Group.covariant_iff_contravariant.mp CovariantClass.elim _

@[to_additive]
/--
theorem `Group.mulLeftReflectLT_of_mulLeftStrictMono` / 定理 `Group.mulLeftReflectLT_of_mulLeftStrictMono`

English:
theorem Group.mulLeftReflectLT_of_mulLeftStrictMono
  statement: [Group N] [LT N]
  proof: inferInstance

@[to_additive]

中文:
定理 Group.mulLeftReflectLT_of_mulLeftStrictMono
  结论: [Group N] [LT N]
  证明: inferInstance

@[to_additive]
-/
theorem Group.mulLeftReflectLT_of_mulLeftStrictMono [Group N] [LT N]
    [MulLeftStrictMono N] : MulLeftReflectLT N :=
  inferInstance

@[to_additive]
/--
theorem `Group.covariant_swap_iff_contravariant_swap` / 定理 `Group.covariant_swap_iff_contravariant_swap`

English:
theorem Group.covariant_swap_iff_contravariant_swap
  given: [Group N]
  proof: by
  refine ⟨fun h a b c bc => ?_, fun h a b c bc => ?_⟩
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a]
    exact h a⁻¹ bc
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a] at bc
    exact h a⁻¹ bc


@[to_additive]

中文:
定理 Group.covariant_swap_iff_contravariant_swap
  条件: [Group N]
  证明: by
  refine ⟨fun h a b c bc => ?_, fun h a b c bc => ?_⟩
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a]
    exact h a⁻¹ bc
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a] at bc
    exact h a⁻¹ bc


@[to_additive]

Depends on / 依赖: mul_inv_cancel_right
-/
theorem Group.covariant_swap_iff_contravariant_swap [Group N] :
    Covariant N N (swap (· * ·)) r ↔ Contravariant N N (swap (· * ·)) r := by
  refine ⟨fun h a b c bc => ?_, fun h a b c bc => ?_⟩
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a]
    exact h a⁻¹ bc
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a] at bc
    exact h a⁻¹ bc


@[to_additive]
instance (priority := 100) Group.covconv_swap [Group N] [CovariantClass N N (swap (· * ·)) r] :
    ContravariantClass N N (swap (· * ·)) r :=
  ⟨Group.covariant_swap_iff_contravariant_swap.mp CovariantClass.elim⟩

@[to_additive]
/--
Instance `Group.mulRightReflectLE_of_mulRightMono` / 实例 `Group.mulRightReflectLE_of_mulRightMono`

English:
instance Group.mulRightReflectLE_of_mulRightMono
  signature: [Group N] [LE N] [MulRightMono N]
  body: Group.covariant_swap_iff_contravariant_swap.mp CovariantClass.elim _

@[to_additive]

中文:
实例 Group.mulRightReflectLE_of_mulRightMono
  签名: [Group N] [LE N] [MulRightMono N]
  定义体: Group.covariant_swap_iff_contravariant_swap.mp CovariantClass.elim _

@[to_additive]

Depends on / 依赖: CovariantClass, CovariantClass.elim, Group.covariant_swap_iff_contravariant_swap.mp, covariant_swap_iff_contravariant_swap
-/
instance Group.mulRightReflectLE_of_mulRightMono [Group N] [LE N] [MulRightMono N] :
    MulRightReflectLE N where
  le_of_mul_le_mul_right' := Group.covariant_swap_iff_contravariant_swap.mp CovariantClass.elim _

@[to_additive]
/--
theorem `Group.mulRightReflectLT_of_mulRightStrictMono` / 定理 `Group.mulRightReflectLT_of_mulRightStrictMono`

English:
theorem Group.mulRightReflectLT_of_mulRightStrictMono
  given: [Group N] [LT N] [MulRightStrictMono N]
  proof: inferInstance

中文:
定理 Group.mulRightReflectLT_of_mulRightStrictMono
  条件: [Group N] [LT N] [MulRightStrictMono N]
  证明: inferInstance
-/
theorem Group.mulRightReflectLT_of_mulRightStrictMono [Group N] [LT N] [MulRightStrictMono N] :
    MulRightReflectLT N :=
  inferInstance


section Trans

variable [IsTrans N r] (m : M) {a b c : N}

-- Lemmas with 3 elements.
/--
theorem `act_rel_of_rel_of_act_rel` / 定理 `act_rel_of_rel_of_act_rel`

English:
theorem act_rel_of_rel_of_act_rel
  given: (ab : r a b) (rl : r (μ m b) c)
  statement: r (μ m a) c
  proof: _root_.trans (act_rel_act_of_rel m ab) rl

中文:
定理 act_rel_of_rel_of_act_rel
  条件: (ab : r a b) (rl : r (μ m b) c)
  结论: r (μ m a) c
  证明: _root_.trans (act_rel_act_of_rel m ab) rl

Depends on / 依赖: _root_, _root_.trans, act_rel_act_of_rel
-/
theorem act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c :=
  _root_.trans (act_rel_act_of_rel m ab) rl

/--
theorem `rel_act_of_rel_of_rel_act` / 定理 `rel_act_of_rel_of_rel_act`

English:
theorem rel_act_of_rel_of_rel_act
  given: (ab : r a b) (rr : r c (μ m a))
  statement: r c (μ m b)
  proof: _root_.trans rr (act_rel_act_of_rel _ ab)

中文:
定理 rel_act_of_rel_of_rel_act
  条件: (ab : r a b) (rr : r c (μ m a))
  结论: r c (μ m b)
  证明: _root_.trans rr (act_rel_act_of_rel _ ab)

Depends on / 依赖: _root_, _root_.trans, act_rel_act_of_rel
-/
theorem rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) : r c (μ m b) :=
  _root_.trans rr (act_rel_act_of_rel _ ab)

end Trans

end Covariant

-- Lemma with 4 elements.
section MEqN

variable {M N μ r} {mu : N -> N -> N} [IsTrans N r] [i : CovariantClass N N mu r]
  [i' : CovariantClass N N (swap mu) r] {a b c d : N}

/--
theorem `act_rel_act_of_rel_of_rel` / 定理 `act_rel_act_of_rel_of_rel`

English:
theorem act_rel_act_of_rel_of_rel
  given: (ab : r a b) (cd : r c d)
  statement: r (mu a c) (mu b d)
  proof: _root_.trans (@act_rel_act_of_rel _ _ (swap mu) r _ c _ _ ab) (act_rel_act_of_rel b cd)

中文:
定理 act_rel_act_of_rel_of_rel
  条件: (ab : r a b) (cd : r c d)
  结论: r (mu a c) (mu b d)
  证明: _root_.trans (@act_rel_act_of_rel _ _ (swap mu) r _ c _ _ ab) (act_rel_act_of_rel b cd)

Depends on / 依赖: _root_, _root_.trans, act_rel_act_of_rel
-/
theorem act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) : r (mu a c) (mu b d) :=
  _root_.trans (@act_rel_act_of_rel _ _ (swap mu) r _ c _ _ ab) (act_rel_act_of_rel b cd)

end MEqN

section Contravariant

variable {M N μ r} [ContravariantClass M N μ r]

/--
theorem `rel_of_act_rel_act` / 定理 `rel_of_act_rel_act`

English:
theorem rel_of_act_rel_act
  given: (m : M) {a b : N} (ab : r (μ m a) (μ m b))
  statement: r a b
  proof: ContravariantClass.elim _ ab

中文:
定理 rel_of_act_rel_act
  条件: (m : M) {a b : N} (ab : r (μ m a) (μ m b))
  结论: r a b
  证明: ContravariantClass.elim _ ab

Depends on / 依赖: ContravariantClass, ContravariantClass.elim
-/
theorem rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a) (μ m b)) : r a b :=
  ContravariantClass.elim _ ab

section Trans

variable [IsTrans N r] (m : M) {a b c : N}

-- Lemmas with 3 elements.
/--
theorem `act_rel_of_act_rel_of_rel_act_rel` / 定理 `act_rel_of_act_rel_of_rel_act_rel`

English:
theorem act_rel_of_act_rel_of_rel_act_rel
  given: (ab : r (μ m a) b) (rl : r (μ m b) (μ m c))
  proof: _root_.trans ab (rel_of_act_rel_act m rl)

中文:
定理 act_rel_of_act_rel_of_rel_act_rel
  条件: (ab : r (μ m a) b) (rl : r (μ m b) (μ m c))
  证明: _root_.trans ab (rel_of_act_rel_act m rl)

Depends on / 依赖: _root_, _root_.trans, rel_of_act_rel_act
-/
theorem act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) :
    r (μ m a) c :=
  _root_.trans ab (rel_of_act_rel_act m rl)

/--
theorem `rel_act_of_act_rel_act_of_rel_act` / 定理 `rel_act_of_act_rel_act_of_rel_act`

English:
theorem rel_act_of_act_rel_act_of_rel_act
  given: (ab : r (μ m a) (μ m b)) (rr : r b (μ m c))
  proof: _root_.trans (rel_of_act_rel_act m ab) rr

中文:
定理 rel_act_of_act_rel_act_of_rel_act
  条件: (ab : r (μ m a) (μ m b)) (rr : r b (μ m c))
  证明: _root_.trans (rel_of_act_rel_act m ab) rr

Depends on / 依赖: _root_, _root_.trans, rel_of_act_rel_act
-/
theorem rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m c)) :
    r a (μ m c) :=
  _root_.trans (rel_of_act_rel_act m ab) rr

end Trans

end Contravariant

section Monotone

variable {α : Type*} {M N μ} [Preorder α] [Preorder N]
variable {f : N -> α}

/--
theorem `Covariant.monotone_of_const` / 定理 `Covariant.monotone_of_const`

English:
theorem Covariant.monotone_of_const
  given: [CovariantClass M N μ (· <= ·)] (m : M)
  statement: Monotone (μ m)
  proof: fun _ _ => CovariantClass.elim m

中文:
定理 Covariant.monotone_of_const
  条件: [CovariantClass M N μ (· <= ·)] (m : M)
  结论: Monotone (μ m)
  证明: fun _ _ => CovariantClass.elim m

Depends on / 依赖: CovariantClass, CovariantClass.elim
-/
theorem Covariant.monotone_of_const [CovariantClass M N μ (· <= ·)] (m : M) : Monotone (μ m) :=
  fun _ _ => CovariantClass.elim m

/--
theorem `Monotone.covariant_of_const` / 定理 `Monotone.covariant_of_const`

English:
theorem Monotone.covariant_of_const
  given: [CovariantClass M N μ (· <= ·)] (hf : Monotone f) (m : M)
  proof: hf.comp (Covariant.monotone_of_const m)

中文:
定理 Monotone.covariant_of_const
  条件: [CovariantClass M N μ (· <= ·)] (hf : Monotone f) (m : M)
  证明: hf.comp (Covariant.monotone_of_const m)

Depends on / 依赖: Covariant, Covariant.monotone_of_const, hf.comp, monotone_of_const
-/
theorem Monotone.covariant_of_const [CovariantClass M N μ (· <= ·)] (hf : Monotone f) (m : M) :
    Monotone (f <| μ m ·) :=
  hf.comp (Covariant.monotone_of_const m)

/--
theorem `Monotone.covariant_of_const'` / 定理 `Monotone.covariant_of_const'`

English:
theorem Monotone.covariant_of_const'
  statement: {μ : N -> N -> N} [CovariantClass N N (swap μ) (· <= ·)]
  proof: Monotone.covariant_of_const (μ := swap μ) hf m

中文:
定理 Monotone.covariant_of_const'
  结论: {μ : N -> N -> N} [CovariantClass N N (swap μ) (· <= ·)]
  证明: Monotone.covariant_of_const (μ := swap μ) hf m

Depends on / 依赖: Monotone, Monotone.covariant_of_const, covariant_of_const
-/
theorem Monotone.covariant_of_const' {μ : N -> N -> N} [CovariantClass N N (swap μ) (· <= ·)]
    (hf : Monotone f) (m : N) : Monotone (f <| μ · m) :=
  Monotone.covariant_of_const (μ := swap μ) hf m

/--
theorem `Antitone.covariant_of_const` / 定理 `Antitone.covariant_of_const`

English:
theorem Antitone.covariant_of_const
  given: [CovariantClass M N μ (· <= ·)] (hf : Antitone f) (m : M)
  proof: hf.comp_monotone Covariant.monotone_of_const m

中文:
定理 Antitone.covariant_of_const
  条件: [CovariantClass M N μ (· <= ·)] (hf : Antitone f) (m : M)
  证明: hf.comp_monotone Covariant.monotone_of_const m

Depends on / 依赖: Covariant, Covariant.monotone_of_const, comp_monotone, hf.comp_monotone, monotone_of_const
-/
theorem Antitone.covariant_of_const [CovariantClass M N μ (· <= ·)] (hf : Antitone f) (m : M) :
    Antitone (f <| μ m ·) :=
hf.comp_monotone Covariant.monotone_of_const m

/--
theorem `Antitone.covariant_of_const'` / 定理 `Antitone.covariant_of_const'`

English:
theorem Antitone.covariant_of_const'
  statement: {μ : N -> N -> N} [CovariantClass N N (swap μ) (· <= ·)]
  proof: Antitone.covariant_of_const (μ := swap μ) hf m

中文:
定理 Antitone.covariant_of_const'
  结论: {μ : N -> N -> N} [CovariantClass N N (swap μ) (· <= ·)]
  证明: Antitone.covariant_of_const (μ := swap μ) hf m

Depends on / 依赖: Antitone, Antitone.covariant_of_const, covariant_of_const
-/
theorem Antitone.covariant_of_const' {μ : N -> N -> N} [CovariantClass N N (swap μ) (· <= ·)]
    (hf : Antitone f) (m : N) : Antitone (f <| μ · m) :=
  Antitone.covariant_of_const (μ := swap μ) hf m

end Monotone

/--
theorem `covariant_le_of_covariant_lt` / 定理 `covariant_le_of_covariant_lt`

English:
theorem covariant_le_of_covariant_lt
  given: [PartialOrder N]
  proof: by
  intro h a b c bc
  rcases bc.eq_or_lt with (rfl | bc)
  · exact le_rfl
  · exact (h _ bc).le

中文:
定理 covariant_le_of_covariant_lt
  条件: [PartialOrder N]
  证明: by
  intro h a b c bc
  rcases bc.eq_or_lt with (rfl | bc)
  · exact le_rfl
  · exact (h _ bc).le

Depends on / 依赖: bc.eq_or_lt, eq_or_lt, le_rfl
-/
theorem covariant_le_of_covariant_lt [PartialOrder N] :
    Covariant M N μ (· < ·) -> Covariant M N μ (· <= ·) := by
  intro h a b c bc
  rcases bc.eq_or_lt with (rfl | bc)
  · exact le_rfl
  · exact (h _ bc).le

/--
theorem `covariantClass_le_of_lt` / 定理 `covariantClass_le_of_lt`

English:
theorem covariantClass_le_of_lt
  given: [PartialOrder N] [CovariantClass M N μ (· < ·)]
  proof: ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩

@[to_additive]

中文:
定理 covariantClass_le_of_lt
  条件: [PartialOrder N] [CovariantClass M N μ (· < ·)]
  证明: ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩

@[to_additive]

Depends on / 依赖: CovariantClass, CovariantClass.elim, covariant_le_of_covariant_lt
-/
theorem covariantClass_le_of_lt [PartialOrder N] [CovariantClass M N μ (· < ·)] :
    CovariantClass M N μ (· <= ·) := ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩

@[to_additive]
/--
theorem `mulLeftMono_of_mulLeftStrictMono` / 定理 `mulLeftMono_of_mulLeftStrictMono`

English:
theorem mulLeftMono_of_mulLeftStrictMono
  given: (M) [Mul M] [PartialOrder M] [MulLeftStrictMono M]
  proof: covariantClass_le_of_lt _ _ _

@[to_additive]

中文:
定理 mulLeftMono_of_mulLeftStrictMono
  条件: (M) [Mul M] [PartialOrder M] [MulLeftStrictMono M]
  证明: covariantClass_le_of_lt _ _ _

@[to_additive]

Depends on / 依赖: covariantClass_le_of_lt
-/
theorem mulLeftMono_of_mulLeftStrictMono (M) [Mul M] [PartialOrder M] [MulLeftStrictMono M] :
    MulLeftMono M := covariantClass_le_of_lt _ _ _

@[to_additive]
/--
theorem `mulRightMono_of_mulRightStrictMono` / 定理 `mulRightMono_of_mulRightStrictMono`

English:
theorem mulRightMono_of_mulRightStrictMono
  given: (M) [Mul M] [PartialOrder M] [MulRightStrictMono M]
  proof: covariantClass_le_of_lt _ _ _

中文:
定理 mulRightMono_of_mulRightStrictMono
  条件: (M) [Mul M] [PartialOrder M] [MulRightStrictMono M]
  证明: covariantClass_le_of_lt _ _ _

Depends on / 依赖: covariantClass_le_of_lt
-/
theorem mulRightMono_of_mulRightStrictMono (M) [Mul M] [PartialOrder M] [MulRightStrictMono M] :
    MulRightMono M := covariantClass_le_of_lt _ _ _

/--
theorem `contravariant_le_iff_contravariant_lt_and_eq` / 定理 `contravariant_le_iff_contravariant_lt_and_eq`

English:
theorem contravariant_le_iff_contravariant_lt_and_eq
  given: [PartialOrder N]
  proof: by
  refine ⟨fun h => ⟨fun a b c bc => ?_, fun a b c bc => ?_⟩, fun h => fun a b c bc => ?_⟩
  · exact (h a bc.le).lt_of_ne (by rintro rfl; exact lt_irrefl _ bc)
  · exact (h a bc.le).antisymm (h a bc.ge)
  · exact bc.lt_or_eq.elim (fun bc => (h.1 a bc).le) (fun bc => (h.2 a bc).le)

中文:
定理 contravariant_le_iff_contravariant_lt_and_eq
  条件: [PartialOrder N]
  证明: by
  refine ⟨fun h => ⟨fun a b c bc => ?_, fun a b c bc => ?_⟩, fun h => fun a b c bc => ?_⟩
  · exact (h a bc.le).lt_of_ne (by rintro rfl; exact lt_irrefl _ bc)
  · exact (h a bc.le).antisymm (h a bc.ge)
  · exact bc.lt_or_eq.elim (fun bc => (h.1 a bc).le) (fun bc => (h.2 a bc).le)

Depends on / 依赖: antisymm, bc.ge, bc.le, bc.lt_or_eq.elim, lt_irrefl, lt_of_ne, lt_or_eq
-/
theorem contravariant_le_iff_contravariant_lt_and_eq [PartialOrder N] :
    Contravariant M N μ (· <= ·) ↔ Contravariant M N μ (· < ·) ∧ Contravariant M N μ (· = ·) := by
  refine ⟨fun h => ⟨fun a b c bc => ?_, fun a b c bc => ?_⟩, fun h => fun a b c bc => ?_⟩
  · exact (h a bc.le).lt_of_ne (by rintro rfl; exact lt_irrefl _ bc)
  · exact (h a bc.le).antisymm (h a bc.ge)
  · exact bc.lt_or_eq.elim (fun bc => (h.1 a bc).le) (fun bc => (h.2 a bc).le)

/--
theorem `contravariant_lt_of_contravariant_le` / 定理 `contravariant_lt_of_contravariant_le`

English:
theorem contravariant_lt_of_contravariant_le
  given: [PartialOrder N]
  proof: And.left ∘ (contravariant_le_iff_contravariant_lt_and_eq M N μ).mp

中文:
定理 contravariant_lt_of_contravariant_le
  条件: [PartialOrder N]
  证明: And.left ∘ (contravariant_le_iff_contravariant_lt_and_eq M N μ).mp

Depends on / 依赖: And.left, contravariant_le_iff_contravariant_lt_and_eq
-/
theorem contravariant_lt_of_contravariant_le [PartialOrder N] :
    Contravariant M N μ (· <= ·) -> Contravariant M N μ (· < ·) :=
  And.left ∘ (contravariant_le_iff_contravariant_lt_and_eq M N μ).mp

/--
theorem `covariant_le_iff_contravariant_lt` / 定理 `covariant_le_iff_contravariant_lt`

English:
theorem covariant_le_iff_contravariant_lt
  given: [LinearOrder N]
  proof: ⟨fun h _ _ _ bc => not_le.mp fun k => bc.not_ge (h _ k),
   fun h _ _ _ bc => not_lt.mp fun k => bc.not_gt (h _ k)⟩

中文:
定理 covariant_le_iff_contravariant_lt
  条件: [LinearOrder N]
  证明: ⟨fun h _ _ _ bc => not_le.mp fun k => bc.not_ge (h _ k),
   fun h _ _ _ bc => not_lt.mp fun k => bc.not_gt (h _ k)⟩

Depends on / 依赖: bc.not_ge, bc.not_gt, not_ge, not_gt, not_le, not_le.mp, not_lt, not_lt.mp
-/
theorem covariant_le_iff_contravariant_lt [LinearOrder N] :
    Covariant M N μ (· <= ·) ↔ Contravariant M N μ (· < ·) :=
  ⟨fun h _ _ _ bc => not_le.mp fun k => bc.not_ge (h _ k),
   fun h _ _ _ bc => not_lt.mp fun k => bc.not_gt (h _ k)⟩

/--
theorem `covariant_lt_iff_contravariant_le` / 定理 `covariant_lt_iff_contravariant_le`

English:
theorem covariant_lt_iff_contravariant_le
  given: [LinearOrder N]
  proof: ⟨fun h _ _ _ bc => not_lt.mp fun k => bc.not_gt (h _ k),
   fun h _ _ _ bc => not_le.mp fun k => bc.not_ge (h _ k)⟩

中文:
定理 covariant_lt_iff_contravariant_le
  条件: [LinearOrder N]
  证明: ⟨fun h _ _ _ bc => not_lt.mp fun k => bc.not_gt (h _ k),
   fun h _ _ _ bc => not_le.mp fun k => bc.not_ge (h _ k)⟩

Depends on / 依赖: bc.not_ge, bc.not_gt, not_ge, not_gt, not_le, not_le.mp, not_lt, not_lt.mp
-/
theorem covariant_lt_iff_contravariant_le [LinearOrder N] :
    Covariant M N μ (· < ·) ↔ Contravariant M N μ (· <= ·) :=
  ⟨fun h _ _ _ bc => not_lt.mp fun k => bc.not_gt (h _ k),
   fun h _ _ _ bc => not_le.mp fun k => bc.not_ge (h _ k)⟩

variable (mu : N -> N -> N)

/--
theorem `covariant_flip_iff` / 定理 `covariant_flip_iff`

English:
theorem covariant_flip_iff
  given: [h : Std.Commutative mu]
  proof: by unfold flip; simp_rw [h.comm]

中文:
定理 covariant_flip_iff
  条件: [h : Std.Commutative mu]
  证明: by unfold flip; simp_rw [h.comm]

Depends on / 依赖: h.comm, simp_rw
-/
theorem covariant_flip_iff [h : Std.Commutative mu] :
    Covariant N N (flip mu) r ↔ Covariant N N mu r := by unfold flip; simp_rw [h.comm]

/--
theorem `contravariant_flip_iff` / 定理 `contravariant_flip_iff`

English:
theorem contravariant_flip_iff
  given: [h : Std.Commutative mu]
  proof: by unfold flip; simp_rw [h.comm]

中文:
定理 contravariant_flip_iff
  条件: [h : Std.Commutative mu]
  证明: by unfold flip; simp_rw [h.comm]

Depends on / 依赖: h.comm, simp_rw
-/
theorem contravariant_flip_iff [h : Std.Commutative mu] :
    Contravariant N N (flip mu) r ↔ Contravariant N N mu r := by unfold flip; simp_rw [h.comm]

/--
Instance `contravariant_lt_of_covariant_le` / 实例 `contravariant_lt_of_covariant_le`

English:
instance contravariant_lt_of_covariant_le
  signature: [LinearOrder N]
  body: (covariant_le_iff_contravariant_lt N N mu).mp CovariantClass.elim

@[to_additive]

中文:
实例 contravariant_lt_of_covariant_le
  签名: [LinearOrder N]
  定义体: (covariant_le_iff_contravariant_lt N N mu).mp CovariantClass.elim

@[to_additive]

Depends on / 依赖: CovariantClass, CovariantClass.elim, covariant_le_iff_contravariant_lt
-/
instance contravariant_lt_of_covariant_le [LinearOrder N]
    [CovariantClass N N mu (· <= ·)] : ContravariantClass N N mu (· < ·) where
  elim := (covariant_le_iff_contravariant_lt N N mu).mp CovariantClass.elim

@[to_additive]
/--
theorem `mulLeftReflectLT_of_mulLeftMono` / 定理 `mulLeftReflectLT_of_mulLeftMono`

English:
theorem mulLeftReflectLT_of_mulLeftMono
  given: [Mul N] [LinearOrder N] [MulLeftMono N]
  proof: inferInstance

@[to_additive]

中文:
定理 mulLeftReflectLT_of_mulLeftMono
  条件: [Mul N] [LinearOrder N] [MulLeftMono N]
  证明: inferInstance

@[to_additive]
-/
theorem mulLeftReflectLT_of_mulLeftMono [Mul N] [LinearOrder N] [MulLeftMono N] :
    MulLeftReflectLT N :=
  inferInstance

@[to_additive]
/--
theorem `mulRightReflectLT_of_mulRightMono` / 定理 `mulRightReflectLT_of_mulRightMono`

English:
theorem mulRightReflectLT_of_mulRightMono
  given: [Mul N] [LinearOrder N] [MulRightMono N]
  proof: inferInstance

中文:
定理 mulRightReflectLT_of_mulRightMono
  条件: [Mul N] [LinearOrder N] [MulRightMono N]
  证明: inferInstance
-/
theorem mulRightReflectLT_of_mulRightMono [Mul N] [LinearOrder N] [MulRightMono N] :
    MulRightReflectLT N :=
  inferInstance

/--
Instance `covariant_lt_of_contravariant_le` / 实例 `covariant_lt_of_contravariant_le`

English:
instance covariant_lt_of_contravariant_le
  signature: [LinearOrder N]
  body: (covariant_lt_iff_contravariant_le N N mu).mpr ContravariantClass.elim

@[to_additive]

中文:
实例 covariant_lt_of_contravariant_le
  签名: [LinearOrder N]
  定义体: (covariant_lt_iff_contravariant_le N N mu).mpr ContravariantClass.elim

@[to_additive]

Depends on / 依赖: ContravariantClass, ContravariantClass.elim, covariant_lt_iff_contravariant_le
-/
instance covariant_lt_of_contravariant_le [LinearOrder N]
    [ContravariantClass N N mu (· <= ·)] : CovariantClass N N mu (· < ·) where
  elim := (covariant_lt_iff_contravariant_le N N mu).mpr ContravariantClass.elim

@[to_additive]
/--
Instance `mulLeftStrictMono_of_mulLeftReflectLE` / 实例 `mulLeftStrictMono_of_mulLeftReflectLE`

English:
instance mulLeftStrictMono_of_mulLeftReflectLE
  signature: [Mul N] [LinearOrder N] [MulLeftReflectLE N]
  body: .mpr fun _ => MulLeftReflectLE.le_of_mul_le_mul_left' covariant_lt_iff_contravariant_le ..

@[to_additive]

中文:
实例 mulLeftStrictMono_of_mulLeftReflectLE
  签名: [Mul N] [LinearOrder N] [MulLeftReflectLE N]
  定义体: .mpr fun _ => MulLeftReflectLE.le_of_mul_le_mul_left' covariant_lt_iff_contravariant_le ..

@[to_additive]

Depends on / 依赖: MulLeftReflectLE, MulLeftReflectLE.le_of_mul_le_mul_left, covariant_lt_iff_contravariant_le, le_of_mul_le_mul_left
-/
instance mulLeftStrictMono_of_mulLeftReflectLE [Mul N] [LinearOrder N] [MulLeftReflectLE N] :
    MulLeftStrictMono N where
  elim :=
.mpr fun _ => MulLeftReflectLE.le_of_mul_le_mul_left' covariant_lt_iff_contravariant_le ..

@[to_additive]
/--
Instance `mulRightStrictMono_of_mulRightReflectLE` / 实例 `mulRightStrictMono_of_mulRightReflectLE`

English:
instance mulRightStrictMono_of_mulRightReflectLE
  signature: [Mul N] [LinearOrder N] [MulRightReflectLE N]
  body: .mpr fun _ => MulRightReflectLE.le_of_mul_le_mul_right' covariant_lt_iff_contravariant_le ..

@[to_additive]

中文:
实例 mulRightStrictMono_of_mulRightReflectLE
  签名: [Mul N] [LinearOrder N] [MulRightReflectLE N]
  定义体: .mpr fun _ => MulRightReflectLE.le_of_mul_le_mul_right' covariant_lt_iff_contravariant_le ..

@[to_additive]

Depends on / 依赖: MulRightReflectLE, MulRightReflectLE.le_of_mul_le_mul_right, covariant_lt_iff_contravariant_le, le_of_mul_le_mul_right
-/
instance mulRightStrictMono_of_mulRightReflectLE [Mul N] [LinearOrder N] [MulRightReflectLE N] :
    MulRightStrictMono N where
  elim :=
.mpr fun _ => MulRightReflectLE.le_of_mul_le_mul_right' covariant_lt_iff_contravariant_le ..

@[to_additive]
/--
Instance `covariant_swap_mul_of_covariant_mul` / 实例 `covariant_swap_mul_of_covariant_mul`

English:
instance covariant_swap_mul_of_covariant_mul
  signature: [CommSemigroup N]
  body: (covariant_flip_iff N r (· * ·)).mpr CovariantClass.elim

@[to_additive]

中文:
实例 covariant_swap_mul_of_covariant_mul
  签名: [CommSemigroup N]
  定义体: (covariant_flip_iff N r (· * ·)).mpr CovariantClass.elim

@[to_additive]

Depends on / 依赖: CovariantClass, CovariantClass.elim, covariant_flip_iff
-/
instance covariant_swap_mul_of_covariant_mul [CommSemigroup N]
    [CovariantClass N N (· * ·) r] : CovariantClass N N (swap (· * ·)) r where
  elim := (covariant_flip_iff N r (· * ·)).mpr CovariantClass.elim

@[to_additive]
/--
theorem `mulRightMono_of_mulLeftMono` / 定理 `mulRightMono_of_mulLeftMono`

English:
theorem mulRightMono_of_mulLeftMono
  given: [CommSemigroup N] [LE N] [MulLeftMono N]
  proof: inferInstance

@[to_additive]

中文:
定理 mulRightMono_of_mulLeftMono
  条件: [CommSemigroup N] [LE N] [MulLeftMono N]
  证明: inferInstance

@[to_additive]
-/
theorem mulRightMono_of_mulLeftMono [CommSemigroup N] [LE N] [MulLeftMono N] :
    MulRightMono N :=
  inferInstance

@[to_additive]
/--
theorem `mulRightStrictMono_of_mulLeftStrictMono` / 定理 `mulRightStrictMono_of_mulLeftStrictMono`

English:
theorem mulRightStrictMono_of_mulLeftStrictMono
  given: [CommSemigroup N] [LT N] [MulLeftStrictMono N]
  proof: inferInstance

@[to_additive]

中文:
定理 mulRightStrictMono_of_mulLeftStrictMono
  条件: [CommSemigroup N] [LT N] [MulLeftStrictMono N]
  证明: inferInstance

@[to_additive]
-/
theorem mulRightStrictMono_of_mulLeftStrictMono [CommSemigroup N] [LT N] [MulLeftStrictMono N] :
    MulRightStrictMono N :=
  inferInstance

@[to_additive]
/--
Instance `contravariant_swap_mul_of_contravariant_mul` / 实例 `contravariant_swap_mul_of_contravariant_mul`

English:
instance contravariant_swap_mul_of_contravariant_mul
  signature: [CommSemigroup N]
  body: (contravariant_flip_iff N r (· * ·)).mpr ContravariantClass.elim

@[to_additive]

中文:
实例 contravariant_swap_mul_of_contravariant_mul
  签名: [CommSemigroup N]
  定义体: (contravariant_flip_iff N r (· * ·)).mpr ContravariantClass.elim

@[to_additive]

Depends on / 依赖: ContravariantClass, ContravariantClass.elim, contravariant_flip_iff
-/
instance contravariant_swap_mul_of_contravariant_mul [CommSemigroup N]
    [ContravariantClass N N (· * ·) r] : ContravariantClass N N (swap (· * ·)) r where
  elim := (contravariant_flip_iff N r (· * ·)).mpr ContravariantClass.elim

@[to_additive]
/--
Instance `mulRightReflectLE_of_mulLeftReflectLE` / 实例 `mulRightReflectLE_of_mulLeftReflectLE`

English:
instance mulRightReflectLE_of_mulLeftReflectLE
  signature: [CommSemigroup N] [LE N] [MulLeftReflectLE N]
  body: contravariant_flip_iff ..
    (fun _ => MulLeftReflectLE.le_of_mul_le_mul_left' : Contravariant N N (· * ·) _) _

@[to_additive]

中文:
实例 mulRightReflectLE_of_mulLeftReflectLE
  签名: [CommSemigroup N] [LE N] [MulLeftReflectLE N]
  定义体: contravariant_flip_iff ..
    (fun _ => MulLeftReflectLE.le_of_mul_le_mul_left' : Contravariant N N (· * ·) _) _

@[to_additive]

Depends on / 依赖: contravariant_flip_iff
-/
instance mulRightReflectLE_of_mulLeftReflectLE [CommSemigroup N] [LE N] [MulLeftReflectLE N] :
    MulRightReflectLE N where
.mpr le_of_mul_le_mul_right' := contravariant_flip_iff ..
    (fun _ => MulLeftReflectLE.le_of_mul_le_mul_left' : Contravariant N N (· * ·) _) _

@[to_additive]
/--
theorem `mulRightReflectLT_of_mulLeftReflectLT` / 定理 `mulRightReflectLT_of_mulLeftReflectLT`

English:
theorem mulRightReflectLT_of_mulLeftReflectLT
  given: [CommSemigroup N] [LT N] [MulLeftReflectLT N]
  proof: inferInstance

中文:
定理 mulRightReflectLT_of_mulLeftReflectLT
  条件: [CommSemigroup N] [LT N] [MulLeftReflectLT N]
  证明: inferInstance
-/
theorem mulRightReflectLT_of_mulLeftReflectLT [CommSemigroup N] [LT N] [MulLeftReflectLT N] :
    MulRightReflectLT N :=
  inferInstance

/--
theorem `covariant_lt_of_covariant_le_of_contravariant_eq` / 定理 `covariant_lt_of_covariant_le_of_contravariant_eq`

English:
theorem covariant_lt_of_covariant_le_of_contravariant_eq
  statement: [ContravariantClass M N μ (· = ·)]
  proof: (CovariantClass.elim a bc.le).lt_of_ne (bc.ne ∘ ContravariantClass.elim _)

中文:
定理 covariant_lt_of_covariant_le_of_contravariant_eq
  结论: [ContravariantClass M N μ (· = ·)]
  证明: (CovariantClass.elim a bc.le).lt_of_ne (bc.ne ∘ ContravariantClass.elim _)

Depends on / 依赖: ContravariantClass, ContravariantClass.elim, CovariantClass, CovariantClass.elim, bc.le, bc.ne, lt_of_ne
-/
theorem covariant_lt_of_covariant_le_of_contravariant_eq [ContravariantClass M N μ (· = ·)]
    [PartialOrder N] [CovariantClass M N μ (· <= ·)] : CovariantClass M N μ (· < ·) where
  elim a _ _ bc := (CovariantClass.elim a bc.le).lt_of_ne (bc.ne ∘ ContravariantClass.elim _)

/--
theorem `contravariant_le_of_contravariant_eq_and_lt` / 定理 `contravariant_le_of_contravariant_eq_and_lt`

English:
theorem contravariant_le_of_contravariant_eq_and_lt
  statement: [PartialOrder N]
  proof: (contravariant_le_iff_contravariant_lt_and_eq M N μ).mpr
    ⟨ContravariantClass.elim, ContravariantClass.elim⟩

中文:
定理 contravariant_le_of_contravariant_eq_and_lt
  结论: [PartialOrder N]
  证明: (contravariant_le_iff_contravariant_lt_and_eq M N μ).mpr
    ⟨ContravariantClass.elim, ContravariantClass.elim⟩

Depends on / 依赖: contravariant_le_iff_contravariant_lt_and_eq
-/
theorem contravariant_le_of_contravariant_eq_and_lt [PartialOrder N]
    [ContravariantClass M N μ (· = ·)] [ContravariantClass M N μ (· < ·)] :
    ContravariantClass M N μ (· <= ·) where
  elim := (contravariant_le_iff_contravariant_lt_and_eq M N μ).mpr
    ⟨ContravariantClass.elim, ContravariantClass.elim⟩

/- TODO:
  redefine `IsLeftCancel N mu` as abbrev of `ContravariantClass N N mu (· = ·)`,
  redefine `IsRightCancel N mu` as abbrev of `ContravariantClass N N (flip mu) (· = ·)`,
  redefine `IsLeftCancelMul` as abbrev of `IsLeftCancel`,
  then the following four instances (actually eight) can be removed in favor of the above two. -/

@[to_additive]
/--
Instance `IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono` / 实例 `IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono`

English:
instance IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono
  signature: [Mul N] [IsLeftCancelMul N]
  body: (CovariantClass.elim a bc.le).lt_of_ne ((mul_ne_mul_right a).mpr bc.ne)

@[to_additive]

中文:
实例 IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono
  签名: [Mul N] [IsLeftCancelMul N]
  定义体: (CovariantClass.elim a bc.le).lt_of_ne ((mul_ne_mul_right a).mpr bc.ne)

@[to_additive]

Depends on / 依赖: CovariantClass, CovariantClass.elim, bc.le, bc.ne, lt_of_ne, mul_ne_mul_right
-/
instance IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono [Mul N] [IsLeftCancelMul N]
    [PartialOrder N] [MulLeftMono N] :
    MulLeftStrictMono N where
  elim a _ _ bc := (CovariantClass.elim a bc.le).lt_of_ne ((mul_ne_mul_right a).mpr bc.ne)

@[to_additive]
/--
Instance `IsRightCancelMul.mulRightStrictMono_of_mulRightMono` / 实例 `IsRightCancelMul.mulRightStrictMono_of_mulRightMono`

English:
instance IsRightCancelMul.mulRightStrictMono_of_mulRightMono
  body: (CovariantClass.elim a bc.le).lt_of_ne ((mul_ne_mul_left a).mpr bc.ne)

@[to_additive]

中文:
实例 IsRightCancelMul.mulRightStrictMono_of_mulRightMono
  定义体: (CovariantClass.elim a bc.le).lt_of_ne ((mul_ne_mul_left a).mpr bc.ne)

@[to_additive]

Depends on / 依赖: CovariantClass, CovariantClass.elim, bc.le, bc.ne, lt_of_ne, mul_ne_mul_left
-/
instance IsRightCancelMul.mulRightStrictMono_of_mulRightMono
    [Mul N] [IsRightCancelMul N] [PartialOrder N] [MulRightMono N] :
    MulRightStrictMono N where
  elim a _ _ bc := (CovariantClass.elim a bc.le).lt_of_ne ((mul_ne_mul_left a).mpr bc.ne)

@[to_additive]
/--
Instance `IsLeftCancelMul.mulLeftReflectLE_of_mulLeftReflectLT` / 实例 `IsLeftCancelMul.mulLeftReflectLE_of_mulLeftReflectLT`

English:
instance IsLeftCancelMul.mulLeftReflectLE_of_mulLeftReflectLT
  signature: [Mul N] [IsLeftCancelMul N]
  body: contravariant_le_iff_contravariant_lt_and_eq N N _
    ⟨‹MulLeftReflectLT N›.elim, fun _ => mul_left_cancel⟩ _

@[to_additive]

中文:
实例 IsLeftCancelMul.mulLeftReflectLE_of_mulLeftReflectLT
  签名: [Mul N] [IsLeftCancelMul N]
  定义体: contravariant_le_iff_contravariant_lt_and_eq N N _
    ⟨‹MulLeftReflectLT N›.elim, fun _ => mul_left_cancel⟩ _

@[to_additive]

Depends on / 依赖: contravariant_le_iff_contravariant_lt_and_eq
-/
instance IsLeftCancelMul.mulLeftReflectLE_of_mulLeftReflectLT [Mul N] [IsLeftCancelMul N]
    [PartialOrder N] [MulLeftReflectLT N] :
    MulLeftReflectLE N where
.mpr le_of_mul_le_mul_left' := contravariant_le_iff_contravariant_lt_and_eq N N _
    ⟨‹MulLeftReflectLT N›.elim, fun _ => mul_left_cancel⟩ _

@[to_additive]
/--
Instance `IsRightCancelMul.mulRightReflectLE_of_mulRightReflectLT` / 实例 `IsRightCancelMul.mulRightReflectLE_of_mulRightReflectLT`

English:
instance IsRightCancelMul.mulRightReflectLE_of_mulRightReflectLT
  body: contravariant_le_iff_contravariant_lt_and_eq N N _
    ⟨‹MulRightReflectLT N›.elim, fun _ => mul_right_cancel⟩ _

中文:
实例 IsRightCancelMul.mulRightReflectLE_of_mulRightReflectLT
  定义体: contravariant_le_iff_contravariant_lt_and_eq N N _
    ⟨‹MulRightReflectLT N›.elim, fun _ => mul_right_cancel⟩ _

Depends on / 依赖: contravariant_le_iff_contravariant_lt_and_eq
-/
instance IsRightCancelMul.mulRightReflectLE_of_mulRightReflectLT
    [Mul N] [IsRightCancelMul N] [PartialOrder N] [MulRightReflectLT N] :
    MulRightReflectLE N where
.mpr le_of_mul_le_mul_right' := contravariant_le_iff_contravariant_lt_and_eq N N _
    ⟨‹MulRightReflectLT N›.elim, fun _ => mul_right_cancel⟩ _

end Variants
