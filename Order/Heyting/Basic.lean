/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.PropInstances
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Heyting algebras

This file defines Heyting, co-Heyting and bi-Heyting algebras.

A Heyting algebra is a bounded distributive lattice with an implication operation `⇨` such that
`a ≤ b ⇨ c ↔ a ⊓ b ≤ c`. It also comes with a pseudo-complement `ᶜ`, such that `aᶜ = a ⇨ ⊥`.

Co-Heyting algebras are dual to Heyting algebras. They have a difference `\` and a negation `￢`
such that `a \ b ≤ c ↔ a ≤ b ⊔ c` and `￢a = ⊤ \ a`.

Bi-Heyting algebras are Heyting algebras that are also co-Heyting algebras.

From a logic standpoint, Heyting algebras precisely model intuitionistic logic, whereas Boolean
algebras model classical logic.

Heyting algebras are the order-theoretic equivalent of Cartesian closed categories.

## Main declarations

* `GeneralizedHeytingAlgebra`: Heyting algebra without a top element (nor negation).
* `GeneralizedCoheytingAlgebra`: Co-Heyting algebra without a bottom element (nor complement).
* `HeytingAlgebra`: Heyting algebra.
* `CoheytingAlgebra`: Co-Heyting algebra.
* `BiheytingAlgebra`: Bi-Heyting algebra.

## Implementation notes

Aligning the `Heyting` and `Coheyting` API with `to_dual` is kind of awkward, because they are
unfortunately quite different. One reason is that the arguments of sup/inf are often swapped
in the dual version, which is not compatible with `to_dual`. We work around this with extensive
use of `to_dual none`.

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]

## Tags

Heyting, Brouwer, algebra, implication, negation, intuitionistic
-/

@[expose] public section

assert_not_exists RelIso

open Function OrderDual

to_dual_name_hint Compl HNot
to_dual_name_hint SDiff HImp

universe u

variable {ι α β : Type*}

/-! ### Notation -/

@[to_dual]
/--
Instance `Prod.instHImp` / 实例 `Prod.instHImp`

English:
instance Prod.instHImp
  signature: [HImp α] [HImp β]
  body: ⟨fun a b => (a.1 ⇨ b.1, a.2 ⇨ b.2)⟩

@[to_dual]

中文:
实例 积类型.instHImp
  签名: [HImp α] [HImp β]
  定义体: ⟨fun a b => (a.1 ⇨ b.1, a.2 ⇨ b.2)⟩

@[to_dual]
-/
instance Prod.instHImp [HImp α] [HImp β] : HImp (α × β) :=
  ⟨fun a b => (a.1 ⇨ b.1, a.2 ⇨ b.2)⟩

@[to_dual]
/--
Instance `Prod.instHNot` / 实例 `Prod.instHNot`

English:
instance Prod.instHNot
  signature: [HNot α] [HNot β]
  body: ⟨fun a => (￢a.1, ￢a.2)⟩

@[to_dual (attr := simp)]

中文:
实例 积类型.instHNot
  签名: [HNot α] [HNot β]
  定义体: ⟨fun a => (￢a.1, ￢a.2)⟩

@[to_dual (attr := simp)]
-/
instance Prod.instHNot [HNot α] [HNot β] : HNot (α × β) :=
  ⟨fun a => (￢a.1, ￢a.2)⟩

@[to_dual (attr := simp)]
/--
theorem `fst_himp` / 定理 `fst_himp`

English:
theorem fst_himp
  given: [HImp α] [HImp β] (a b : α × β)
  statement: (a ⇨ b).1 = a.1 ⇨ b.1
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 fst_himp
  条件: [HImp α] [HImp β] (a b : α × β)
  结论: (a ⇨ b).1 = a.1 ⇨ b.1
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem fst_himp [HImp α] [HImp β] (a b : α × β) : (a ⇨ b).1 = a.1 ⇨ b.1 :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `snd_himp` / 定理 `snd_himp`

English:
theorem snd_himp
  given: [HImp α] [HImp β] (a b : α × β)
  statement: (a ⇨ b).2 = a.2 ⇨ b.2
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 snd_himp
  条件: [HImp α] [HImp β] (a b : α × β)
  结论: (a ⇨ b).2 = a.2 ⇨ b.2
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem snd_himp [HImp α] [HImp β] (a b : α × β) : (a ⇨ b).2 = a.2 ⇨ b.2 :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `fst_hnot` / 定理 `fst_hnot`

English:
theorem fst_hnot
  given: [HNot α] [HNot β] (a : α × β)
  statement: (￢a).1 = ￢a.1
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 fst_hnot
  条件: [HNot α] [HNot β] (a : α × β)
  结论: (￢a).1 = ￢a.1
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem fst_hnot [HNot α] [HNot β] (a : α × β) : (￢a).1 = ￢a.1 :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `snd_hnot` / 定理 `snd_hnot`

English:
theorem snd_hnot
  given: [HNot α] [HNot β] (a : α × β)
  statement: (￢a).2 = ￢a.2
  proof: rfl

中文:
定理 snd_hnot
  条件: [HNot α] [HNot β] (a : α × β)
  结论: (￢a).2 = ￢a.2
  证明: rfl
-/
theorem snd_hnot [HNot α] [HNot β] (a : α × β) : (￢a).2 = ￢a.2 :=
  rfl

/--
Definition of `GeneralizedHeytingAlgebra` / `GeneralizedHeytingAlgebra` 的定义

English:
class GeneralizedHeytingAlgebra
  parameters: (α : Type*)
  extends: Lattice α, OrderTop α, HImp α
  axioms and operations (1):
    - le_himp_iff((a b c : α)) : a <= b ⇨ c ↔ a ⊓ b <= c

中文:
类 GeneralizedHeyting代数
  参数: (α : 类型)
  继承: 格 α, 有顶序 α, HImp α
  公理与运算 (1 个):
    - le_himp_iff((a b c : α)) : a <= b ⇨ c ↔ a ⊓ b <= c
-/
class GeneralizedHeytingAlgebra (α : Type*) extends Lattice α, OrderTop α, HImp α where
  /-- `(a ⇨ ·)` is right adjoint to `(a ⊓ ·)` -/
  le_himp_iff (a b c : α) : a <= b ⇨ c ↔ a ⊓ b <= c

set_option linter.translate.warnInvalid false in
/-- A generalized co-Heyting algebra is a lattice with an additional binary
difference operation `\` such that `(· \ a)` is left adjoint to `(· ⊔ a)`.

This generalizes `CoheytingAlgebra` by not requiring a top element. -/
@[to_dual]
/--
Definition of `GeneralizedCoheytingAlgebra` / `GeneralizedCoheytingAlgebra` 的定义

English:
class GeneralizedCoheytingAlgebra
  parameters: (α : Type*)
  extends: Lattice α, OrderBot α, SDiff α
  axioms and operations (1):
    - sdiff_le_iff((a b c : α)) : a \ b <= c ↔ a <= b ⊔ c

中文:
类 GeneralizedCoheyting代数
  参数: (α : 类型)
  继承: 格 α, 有底序 α, 对称差 α
  公理与运算 (1 个):
    - sdiff_le_iff((a b c : α)) : a \ b <= c ↔ a <= b ⊔ c
-/
class GeneralizedCoheytingAlgebra (α : Type*) extends Lattice α, OrderBot α, SDiff α where
  /-- `(· \ a)` is left adjoint to `(· ⊔ a)` -/
  sdiff_le_iff (a b c : α) : a \ b <= c ↔ a <= b ⊔ c

/--
Definition of `HeytingAlgebra` / `HeytingAlgebra` 的定义

English:
class HeytingAlgebra
  parameters: (α : Type*)
  extends: GeneralizedHeytingAlgebra α, OrderBot α, Compl α
  axioms and operations (1):
    - himp_bot((a : α)) : a ⇨ ⊥ = aᶜ

中文:
类 Heyting代数
  参数: (α : 类型)
  继承: GeneralizedHeyting代数 α, 有底序 α, 补集 α
  公理与运算 (1 个):
    - himp_bot((a : α)) : a ⇨ ⊥ = aᶜ
-/
class HeytingAlgebra (α : Type*) extends GeneralizedHeytingAlgebra α, OrderBot α, Compl α where
  /-- `aᶜ` is defined as `a ⇨ ⊥` -/
  himp_bot (a : α) : a ⇨ ⊥ = aᶜ

set_option linter.translate.warnInvalid false in
/-- A co-Heyting algebra is a bounded lattice with an additional binary difference operation `\`
such that `(· \ a)` is left adjoint to `(· ⊔ a)`. -/
@[to_dual]
/--
Definition of `CoheytingAlgebra` / `CoheytingAlgebra` 的定义

English:
class CoheytingAlgebra
  parameters: (α : Type*)
  extends: GeneralizedCoheytingAlgebra α, OrderTop α, HNot α
  axioms and operations (1):
    - top_sdiff((a : α)) : ⊤ \ a = ￢a

中文:
类 余heyting代数
  参数: (α : 类型)
  继承: GeneralizedCoheyting代数 α, 有顶序 α, HNot α
  公理与运算 (1 个):
    - top_sdiff((a : α)) : ⊤ \ a = ￢a
-/
class CoheytingAlgebra (α : Type*) extends GeneralizedCoheytingAlgebra α, OrderTop α, HNot α where
  /-- `⊤ \ a` is `￢a` -/
  top_sdiff (a : α) : ⊤ \ a = ￢a

/--
Definition of `BiheytingAlgebra` / `BiheytingAlgebra` 的定义

English:
class BiheytingAlgebra
  parameters: (α : Type*)
  extends: HeytingAlgebra α, CoheytingAlgebra α
  (no additional axioms)

中文:
类 Biheyting代数
  参数: (α : 类型)
  继承: Heyting代数 α, 余heyting代数 α
  (无附加公理)
-/
class BiheytingAlgebra (α : Type*) extends HeytingAlgebra α, CoheytingAlgebra α where

attribute [to_dual existing] BiheytingAlgebra.toHeytingAlgebra

-- See note [lower instance priority]
attribute [instance 100] GeneralizedHeytingAlgebra.toOrderTop
attribute [instance 100] GeneralizedCoheytingAlgebra.toOrderBot

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) HeytingAlgebra.toBoundedOrder [HeytingAlgebra α] : BoundedOrder α where

-- See note [reducible non-instances]
/--
Definition of `HeytingAlgebra.ofHImp` / `HeytingAlgebra.ofHImp` 的定义

English:
abbreviation HeytingAlgebra.ofHImp
  signature: [DistribLattice α] [BoundedOrder α] (himp : α -> α -> α)
  body: { ‹DistribLattice α›, ‹BoundedOrder α› with
    himp,
    compl := fun a => himp a ⊥,
    le_himp_iff,
    himp_bot := fun _ => rfl }

中文:
缩写 Heyting代数.ofHImp
  签名: [Distrib格 α] [有界序 α] (himp : α -> α -> α)
  定义体: { ‹DistribLattice α›, ‹BoundedOrder α› with
    himp,
    compl := fun a => himp a ⊥,
    le_himp_iff,
    himp_bot := fun _ => rfl }

Depends on / 依赖: BoundedOrder, DistribLattice, himp_bot, le_himp_iff
-/
abbrev HeytingAlgebra.ofHImp [DistribLattice α] [BoundedOrder α] (himp : α -> α -> α)
    (le_himp_iff : forall a b c, a <= himp b c ↔ a ⊓ b <= c) : HeytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with
    himp,
    compl := fun a => himp a ⊥,
    le_himp_iff,
    himp_bot := fun _ => rfl }

-- See note [reducible non-instances]
/--
Definition of `HeytingAlgebra.ofCompl` / `HeytingAlgebra.ofCompl` 的定义

English:
abbreviation HeytingAlgebra.ofCompl
  signature: [DistribLattice α] [BoundedOrder α] (compl : α -> α)
  body: (compl · ⊔ ·)
  compl := compl
  le_himp_iff := le_himp_iff
  himp_bot _ := sup_bot_eq _

中文:
缩写 Heyting代数.ofCompl
  签名: [Distrib格 α] [有界序 α] (compl : α -> α)
  定义体: (compl · ⊔ ·)
  compl := compl
  le_himp_iff := le_himp_iff
  himp_bot _ := sup_bot_eq _
-/
abbrev HeytingAlgebra.ofCompl [DistribLattice α] [BoundedOrder α] (compl : α -> α)
    (le_himp_iff : forall a b c, a <= compl b ⊔ c ↔ a ⊓ b <= c) : HeytingAlgebra α where
  himp := (compl · ⊔ ·)
  compl := compl
  le_himp_iff := le_himp_iff
  himp_bot _ := sup_bot_eq _

-- See note [reducible non-instances]
/--
Definition of `CoheytingAlgebra.ofSDiff` / `CoheytingAlgebra.ofSDiff` 的定义

English:
abbreviation CoheytingAlgebra.ofSDiff
  signature: [DistribLattice α] [BoundedOrder α] (sdiff : α -> α -> α)
  body: { ‹DistribLattice α›, ‹BoundedOrder α› with
    sdiff,
    hnot := fun a => sdiff ⊤ a,
    sdiff_le_iff,
    top_sdiff := fun _ => rfl }

中文:
缩写 余heyting代数.ofSDiff
  签名: [Distrib格 α] [有界序 α] (sdiff : α -> α -> α)
  定义体: { ‹DistribLattice α›, ‹BoundedOrder α› with
    sdiff,
    hnot := fun a => sdiff ⊤ a,
    sdiff_le_iff,
    top_sdiff := fun _ => rfl }

Depends on / 依赖: BoundedOrder, DistribLattice, sdiff_le_iff, top_sdiff
-/
abbrev CoheytingAlgebra.ofSDiff [DistribLattice α] [BoundedOrder α] (sdiff : α -> α -> α)
    (sdiff_le_iff : forall a b c, sdiff a b <= c ↔ a <= b ⊔ c) : CoheytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with
    sdiff,
    hnot := fun a => sdiff ⊤ a,
    sdiff_le_iff,
    top_sdiff := fun _ => rfl }

-- See note [reducible non-instances]
/--
Definition of `CoheytingAlgebra.ofHNot` / `CoheytingAlgebra.ofHNot` 的定义

English:
abbreviation CoheytingAlgebra.ofHNot
  signature: [DistribLattice α] [BoundedOrder α] (hnot : α -> α)
  body: a ⊓ hnot b
  hnot := hnot
  sdiff_le_iff := sdiff_le_iff
  top_sdiff _ := top_inf_eq _

中文:
缩写 余heyting代数.ofHNot
  签名: [Distrib格 α] [有界序 α] (hnot : α -> α)
  定义体: a ⊓ hnot b
  hnot := hnot
  sdiff_le_iff := sdiff_le_iff
  top_sdiff _ := top_inf_eq _
-/
abbrev CoheytingAlgebra.ofHNot [DistribLattice α] [BoundedOrder α] (hnot : α -> α)
    (sdiff_le_iff : forall a b c, a ⊓ hnot b <= c ↔ a <= b ⊔ c) : CoheytingAlgebra α where
  sdiff a b := a ⊓ hnot b
  hnot := hnot
  sdiff_le_iff := sdiff_le_iff
  top_sdiff _ := top_inf_eq _

/-! In this section, we'll give interpretations of these results in the Heyting algebra model of
intuitionistic logic,- where `≤` can be interpreted as "validates", `⇨` as "implies", `⊓` as "and",
`⊔` as "or", `⊥` as "false" and `⊤` as "true". Note that we confuse `→` and `⊢` because those are
the same in this logic.

See also `Prop.heytingAlgebra`. -/
section GeneralizedHeytingAlgebra

@[simp low] -- low priority so that it doesn't overwrite user-provided simp lemmas
/--
theorem `sdiff_le_iff` / 定理 `sdiff_le_iff`

English:
theorem sdiff_le_iff
  given: [GeneralizedCoheytingAlgebra α] {a b c : α}
  statement: a \ b <= c ↔ a <= b ⊔ c
  proof: GeneralizedCoheytingAlgebra.sdiff_le_iff _ _ _

中文:
定理 sdiff_le_iff
  条件: [GeneralizedCoheyting代数 α] {a b c : α}
  结论: a \ b <= c ↔ a <= b ⊔ c
  证明: GeneralizedCoheytingAlgebra.sdiff_le_iff _ _ _

Depends on / 依赖: GeneralizedCoheytingAlgebra, GeneralizedCoheytingAlgebra.sdiff_le_iff, sdiff_le_iff
-/
theorem sdiff_le_iff [GeneralizedCoheytingAlgebra α] {a b c : α} : a \ b <= c ↔ a <= b ⊔ c :=
  GeneralizedCoheytingAlgebra.sdiff_le_iff _ _ _

/--
theorem `sdiff_le_iff'` / 定理 `sdiff_le_iff'`

English:
theorem sdiff_le_iff'
  given: [GeneralizedCoheytingAlgebra α] {a b c : α}
  statement: a \ b <= c ↔ a <= c ⊔ b
  proof: by
  rw [sdiff_le_iff]; rw [sup_comm]

中文:
定理 sdiff_le_iff'
  条件: [GeneralizedCoheyting代数 α] {a b c : α}
  结论: a \ b <= c ↔ a <= c ⊔ b
  证明: by
  rw [sdiff_le_iff]; rw [sup_comm]

Depends on / 依赖: sdiff_le_iff, sup_comm
-/
theorem sdiff_le_iff' [GeneralizedCoheytingAlgebra α] {a b c : α} : a \ b <= c ↔ a <= c ⊔ b := by
  rw [sdiff_le_iff]; rw [sup_comm]

variable [GeneralizedHeytingAlgebra α] {a b c d : α}

/-- `p → q → r ↔ p ∧ q → r` -/
@[to_dual existing sdiff_le_iff', simp]
/--
theorem `le_himp_iff` / 定理 `le_himp_iff`

English:
theorem le_himp_iff
  statement: a <= b ⇨ c ↔ a ⊓ b <= c
  proof: GeneralizedHeytingAlgebra.le_himp_iff _ _ _

中文:
定理 le_himp_iff
  结论: a <= b ⇨ c ↔ a ⊓ b <= c
  证明: GeneralizedHeytingAlgebra.le_himp_iff _ _ _

Depends on / 依赖: GeneralizedHeytingAlgebra, GeneralizedHeytingAlgebra.le_himp_iff, le_himp_iff
-/
theorem le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c :=
  GeneralizedHeytingAlgebra.le_himp_iff _ _ _

/-- `p → q → r ↔ q ∧ p → r` -/
@[to_dual existing sdiff_le_iff]
/--
theorem `le_himp_iff'` / 定理 `le_himp_iff'`

English:
theorem le_himp_iff'
  statement: a <= b ⇨ c ↔ b ⊓ a <= c
  proof: by rw [le_himp_iff, inf_comm]

中文:
定理 le_himp_iff'
  结论: a <= b ⇨ c ↔ b ⊓ a <= c
  证明: by rw [le_himp_iff, inf_comm]

Depends on / 依赖: inf_comm, le_himp_iff
-/
theorem le_himp_iff' : a <= b ⇨ c ↔ b ⊓ a <= c := by rw [le_himp_iff, inf_comm]

/-- `p → q → r ↔ q → p → r` -/
@[to_dual sdiff_le_comm]
/--
theorem `le_himp_comm` / 定理 `le_himp_comm`

English:
theorem le_himp_comm
  statement: a <= b ⇨ c ↔ b <= a ⇨ c
  proof: by rw [le_himp_iff, le_himp_iff']

中文:
定理 le_himp_comm
  结论: a <= b ⇨ c ↔ b <= a ⇨ c
  证明: by rw [le_himp_iff, le_himp_iff']

Depends on / 依赖: le_himp_iff
-/
theorem le_himp_comm : a <= b ⇨ c ↔ b <= a ⇨ c := by rw [le_himp_iff, le_himp_iff']

/-- `p → q → p` -/
@[to_dual sdiff_le]
/--
theorem `le_himp` / 定理 `le_himp`

English:
theorem le_himp
  statement: a <= b ⇨ a
  proof: le_himp_iff.2 inf_le_left

中文:
定理 le_himp
  结论: a <= b ⇨ a
  证明: le_himp_iff.2 inf_le_left

Depends on / 依赖: inf_le_left, le_himp_iff
-/
theorem le_himp : a <= b ⇨ a :=
  le_himp_iff.2 inf_le_left

/-- `p → p → q ↔ p → q` -/
@[to_dual sdiff_le_iff_left]
/--
theorem `le_himp_iff_left` / 定理 `le_himp_iff_left`

English:
theorem le_himp_iff_left
  statement: a <= a ⇨ b ↔ a <= b
  proof: by rw [le_himp_iff, inf_idem]

中文:
定理 le_himp_iff_left
  结论: a <= a ⇨ b ↔ a <= b
  证明: by rw [le_himp_iff, inf_idem]

Depends on / 依赖: inf_idem, le_himp_iff
-/
theorem le_himp_iff_left : a <= a ⇨ b ↔ a <= b := by rw [le_himp_iff, inf_idem]

/-- `p → p` -/
@[to_dual (attr := simp)]
/--
theorem `himp_self` / 定理 `himp_self`

English:
theorem himp_self
  statement: a ⇨ a = ⊤
  proof: top_le_iff.1 le_himp_iff.2 inf_le_right

中文:
定理 himp_self
  结论: a ⇨ a = ⊤
  证明: top_le_iff.1 le_himp_iff.2 inf_le_right

Depends on / 依赖: inf_le_right, le_himp_iff, top_le_iff
-/
theorem himp_self : a ⇨ a = ⊤ :=
top_le_iff.1 le_himp_iff.2 inf_le_right

/-- `(p → q) ∧ p → q` -/
@[to_dual le_sdiff_sup]
/--
theorem `himp_inf_le` / 定理 `himp_inf_le`

English:
theorem himp_inf_le
  statement: (a ⇨ b) ⊓ a <= b
  proof: le_himp_iff.1 le_rfl

中文:
定理 himp_inf_le
  结论: (a ⇨ b) ⊓ a <= b
  证明: le_himp_iff.1 le_rfl

Depends on / 依赖: le_himp_iff, le_rfl
-/
theorem himp_inf_le : (a ⇨ b) ⊓ a <= b :=
  le_himp_iff.1 le_rfl

/-- `p ∧ (p → q) → q` -/
@[to_dual le_sup_sdiff]
/--
theorem `inf_himp_le` / 定理 `inf_himp_le`

English:
theorem inf_himp_le
  statement: a ⊓ (a ⇨ b) <= b
  proof: by rw [inf_comm, ← le_himp_iff]

中文:
定理 inf_himp_le
  结论: a ⊓ (a ⇨ b) <= b
  证明: by rw [inf_comm, ← le_himp_iff]

Depends on / 依赖: inf_comm, le_himp_iff
-/
theorem inf_himp_le : a ⊓ (a ⇨ b) <= b := by rw [inf_comm, ← le_himp_iff]

/-- `p ∧ (p → q) ↔ p ∧ q` -/
@[to_dual (attr := simp) sup_sdiff_self]
-- TODO: Should this be renamed to `inf_himp_self`?
/--
theorem `inf_himp` / 定理 `inf_himp`

English:
theorem inf_himp
  given: (a b : α)
  statement: a ⊓ (a ⇨ b) = a ⊓ b
  proof: le_antisymm (le_inf inf_le_left <| by rw [inf_comm, ← le_himp_iff]) inf_le_inf_left _ le_himp

中文:
定理 inf_himp
  条件: (a b : α)
  结论: a ⊓ (a ⇨ b) = a ⊓ b
  证明: le_antisymm (le_inf inf_le_left <| by rw [inf_comm, ← le_himp_iff]) inf_le_inf_left _ le_himp

Depends on / 依赖: inf_comm, inf_le_inf_left, inf_le_left, le_antisymm, le_himp, le_himp_iff, le_inf
-/
theorem inf_himp (a b : α) : a ⊓ (a ⇨ b) = a ⊓ b :=
le_antisymm (le_inf inf_le_left <| by rw [inf_comm, ← le_himp_iff]) inf_le_inf_left _ le_himp

/-- `(p → q) ∧ p ↔ q ∧ p` -/
@[to_dual (attr := simp)]
/--
theorem `himp_inf_self` / 定理 `himp_inf_self`

English:
theorem himp_inf_self
  given: (a b : α)
  statement: (a ⇨ b) ⊓ a = b ⊓ a
  proof: by rw [inf_comm, inf_himp, inf_comm]

中文:
定理 himp_inf_self
  条件: (a b : α)
  结论: (a ⇨ b) ⊓ a = b ⊓ a
  证明: by rw [inf_comm, inf_himp, inf_comm]

Depends on / 依赖: inf_comm, inf_himp
-/
theorem himp_inf_self (a b : α) : (a ⇨ b) ⊓ a = b ⊓ a := by rw [inf_comm, inf_himp, inf_comm]

/-- The **deduction theorem** in the Heyting algebra model of intuitionistic logic:
an implication holds iff the conclusion follows from the hypothesis. -/
@[to_dual (attr := simp)]
/--
theorem `himp_eq_top_iff` / 定理 `himp_eq_top_iff`

English:
theorem himp_eq_top_iff
  statement: a ⇨ b = ⊤ ↔ a <= b
  proof: by rw [← top_le_iff, le_himp_iff, top_inf_eq]

中文:
定理 himp_eq_top_iff
  结论: a ⇨ b = ⊤ ↔ a <= b
  证明: by rw [← top_le_iff, le_himp_iff, top_inf_eq]

Depends on / 依赖: le_himp_iff, top_inf_eq, top_le_iff
-/
theorem himp_eq_top_iff : a ⇨ b = ⊤ ↔ a <= b := by rw [← top_le_iff, le_himp_iff, top_inf_eq]

/-- `p → true` -/
@[to_dual (attr := simp) bot_sdiff]
/--
theorem `himp_top` / 定理 `himp_top`

English:
theorem himp_top
  statement: a ⇨ ⊤ = ⊤
  proof: himp_eq_top_iff.2 le_top

中文:
定理 himp_top
  结论: a ⇨ ⊤ = ⊤
  证明: himp_eq_top_iff.2 le_top

Depends on / 依赖: himp_eq_top_iff, le_top
-/
theorem himp_top : a ⇨ ⊤ = ⊤ :=
  himp_eq_top_iff.2 le_top

/-- `true → p ↔ p` -/
@[to_dual (attr := simp) sdiff_bot]
/--
theorem `top_himp` / 定理 `top_himp`

English:
theorem top_himp
  statement: ⊤ ⇨ a = a
  proof: eq_of_forall_le_iff fun b => by rw [le_himp_iff, inf_top_eq]

中文:
定理 top_himp
  结论: ⊤ ⇨ a = a
  证明: eq_of_forall_le_iff fun b => by rw [le_himp_iff, inf_top_eq]

Depends on / 依赖: eq_of_forall_le_iff, inf_top_eq, le_himp_iff
-/
theorem top_himp : ⊤ ⇨ a = a :=
  eq_of_forall_le_iff fun b => by rw [le_himp_iff, inf_top_eq]

/-- `p → q → r ↔ p ∧ q → r` -/
@[to_dual none]
/--
theorem `himp_himp` / 定理 `himp_himp`

English:
theorem himp_himp
  given: (a b c : α)
  statement: a ⇨ b ⇨ c = a ⊓ b ⇨ c
  proof: eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, inf_assoc]

中文:
定理 himp_himp
  条件: (a b c : α)
  结论: a ⇨ b ⇨ c = a ⊓ b ⇨ c
  证明: eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, inf_assoc]

Depends on / 依赖: eq_of_forall_le_iff, inf_assoc, le_himp_iff, simp_rw
-/
theorem himp_himp (a b c : α) : a ⇨ b ⇨ c = a ⊓ b ⇨ c :=
  eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, inf_assoc]

/-- `(q → r) → (p → q) → q → r` -/
@[to_dual none]
/--
theorem `himp_le_himp_himp_himp` / 定理 `himp_le_himp_himp_himp`

English:
theorem himp_le_himp_himp_himp
  statement: b ⇨ c <= (a ⇨ b) ⇨ a ⇨ c
  proof: by
  rw [le_himp_iff]; rw [le_himp_iff]; rw [inf_assoc]; rw [himp_inf_self]; rw [← inf_assoc]; rw [himp_inf_self]; rw [inf_assoc]
  exact inf_le_left

@[simp, to_dual none]

中文:
定理 himp_le_himp_himp_himp
  结论: b ⇨ c <= (a ⇨ b) ⇨ a ⇨ c
  证明: by
  rw [le_himp_iff]; rw [le_himp_iff]; rw [inf_assoc]; rw [himp_inf_self]; rw [← inf_assoc]; rw [himp_inf_self]; rw [inf_assoc]
  exact inf_le_left

@[simp, to_dual none]

Depends on / 依赖: himp_inf_self, inf_assoc, inf_le_left, le_himp_iff
-/
theorem himp_le_himp_himp_himp : b ⇨ c <= (a ⇨ b) ⇨ a ⇨ c := by
  rw [le_himp_iff]; rw [le_himp_iff]; rw [inf_assoc]; rw [himp_inf_self]; rw [← inf_assoc]; rw [himp_inf_self]; rw [inf_assoc]
  exact inf_le_left

@[simp, to_dual none]
/--
theorem `himp_inf_himp_inf_le` / 定理 `himp_inf_himp_inf_le`

English:
theorem himp_inf_himp_inf_le
  statement: (b ⇨ c) ⊓ (a ⇨ b) ⊓ a <= c
  proof: by
  simpa using @himp_le_himp_himp_himp

中文:
定理 himp_inf_himp_inf_le
  结论: (b ⇨ c) ⊓ (a ⇨ b) ⊓ a <= c
  证明: by
  simpa using @himp_le_himp_himp_himp

Depends on / 依赖: himp_le_himp_himp_himp
-/
theorem himp_inf_himp_inf_le : (b ⇨ c) ⊓ (a ⇨ b) ⊓ a <= c := by
  simpa using @himp_le_himp_himp_himp

/-- `p → q → r ↔ q → p → r` -/
@[to_dual (reorder := a c) sdiff_right_comm]
/--
theorem `himp_left_comm` / 定理 `himp_left_comm`

English:
theorem himp_left_comm
  given: (a b c : α)
  statement: a ⇨ b ⇨ c = b ⇨ a ⇨ c
  proof: by simp_rw [himp_himp, inf_comm]

@[to_dual (attr := simp)]

中文:
定理 himp_left_comm
  条件: (a b c : α)
  结论: a ⇨ b ⇨ c = b ⇨ a ⇨ c
  证明: by simp_rw [himp_himp, inf_comm]

@[to_dual (attr := simp)]

Depends on / 依赖: himp_himp, inf_comm, simp_rw
-/
theorem himp_left_comm (a b c : α) : a ⇨ b ⇨ c = b ⇨ a ⇨ c := by simp_rw [himp_himp, inf_comm]

@[to_dual (attr := simp)]
/--
theorem `himp_idem` / 定理 `himp_idem`

English:
theorem himp_idem
  statement: b ⇨ b ⇨ a = b ⇨ a
  proof: by rw [himp_himp, inf_idem]

@[to_dual (reorder := a c b) sup_sdiff_distrib]

中文:
定理 himp_idem
  结论: b ⇨ b ⇨ a = b ⇨ a
  证明: by rw [himp_himp, inf_idem]

@[to_dual (reorder := a c b) sup_sdiff_distrib]

Depends on / 依赖: himp_himp, inf_idem
-/
theorem himp_idem : b ⇨ b ⇨ a = b ⇨ a := by rw [himp_himp, inf_idem]

@[to_dual (reorder := a c b) sup_sdiff_distrib]
/--
theorem `himp_inf_distrib` / 定理 `himp_inf_distrib`

English:
theorem himp_inf_distrib
  given: (a b c : α)
  statement: a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c)
  proof: eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, le_inf_iff, le_himp_iff]

@[to_dual (reorder := a c b) sdiff_inf_distrib]

中文:
定理 himp_inf_distrib
  条件: (a b c : α)
  结论: a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c)
  证明: eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, le_inf_iff, le_himp_iff]

@[to_dual (reorder := a c b) sdiff_inf_distrib]

Depends on / 依赖: eq_of_forall_le_iff, le_himp_iff, le_inf_iff, simp_rw
-/
theorem himp_inf_distrib (a b c : α) : a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c) :=
  eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, le_inf_iff, le_himp_iff]

@[to_dual (reorder := a c b) sdiff_inf_distrib]
/--
theorem `sup_himp_distrib` / 定理 `sup_himp_distrib`

English:
theorem sup_himp_distrib
  given: (a b c : α)
  statement: a ⊔ b ⇨ c = (a ⇨ c) ⊓ (b ⇨ c)
  proof: eq_of_forall_le_iff fun d => by
    rw [le_inf_iff]; rw [le_himp_comm]; rw [sup_le_iff]
    simp_rw [le_himp_comm]

@[to_dual sdiff_le_sdiff_right]

中文:
定理 sup_himp_distrib
  条件: (a b c : α)
  结论: a ⊔ b ⇨ c = (a ⇨ c) ⊓ (b ⇨ c)
  证明: eq_of_forall_le_iff fun d => by
    rw [le_inf_iff]; rw [le_himp_comm]; rw [sup_le_iff]
    simp_rw [le_himp_comm]

@[to_dual sdiff_le_sdiff_right]

Depends on / 依赖: eq_of_forall_le_iff, le_himp_comm, le_inf_iff, simp_rw, sup_le_iff
-/
theorem sup_himp_distrib (a b c : α) : a ⊔ b ⇨ c = (a ⇨ c) ⊓ (b ⇨ c) :=
  eq_of_forall_le_iff fun d => by
    rw [le_inf_iff]; rw [le_himp_comm]; rw [sup_le_iff]
    simp_rw [le_himp_comm]

@[to_dual sdiff_le_sdiff_right]
/--
theorem `himp_le_himp_left` / 定理 `himp_le_himp_left`

English:
theorem himp_le_himp_left
  given: (h : a <= b)
  statement: c ⇨ a <= c ⇨ b
  proof: le_himp_iff.2 himp_inf_le.trans h

@[to_dual sdiff_le_sdiff_left]

中文:
定理 himp_le_himp_left
  条件: (h : a <= b)
  结论: c ⇨ a <= c ⇨ b
  证明: le_himp_iff.2 himp_inf_le.trans h

@[to_dual sdiff_le_sdiff_left]

Depends on / 依赖: himp_inf_le, himp_inf_le.trans, le_himp_iff
-/
theorem himp_le_himp_left (h : a <= b) : c ⇨ a <= c ⇨ b :=
le_himp_iff.2 himp_inf_le.trans h

@[to_dual sdiff_le_sdiff_left]
/--
theorem `himp_le_himp_right` / 定理 `himp_le_himp_right`

English:
theorem himp_le_himp_right
  given: (h : a <= b)
  statement: b ⇨ c <= a ⇨ c
  proof: le_himp_iff.2 (inf_le_inf_left _ h).trans himp_inf_le

@[to_dual (reorder := hab hcd) (attr := gcongr)]

中文:
定理 himp_le_himp_right
  条件: (h : a <= b)
  结论: b ⇨ c <= a ⇨ c
  证明: le_himp_iff.2 (inf_le_inf_left _ h).trans himp_inf_le

@[to_dual (reorder := hab hcd) (attr := gcongr)]

Depends on / 依赖: himp_inf_le, inf_le_inf_left, le_himp_iff
-/
theorem himp_le_himp_right (h : a <= b) : b ⇨ c <= a ⇨ c :=
le_himp_iff.2 (inf_le_inf_left _ h).trans himp_inf_le

@[to_dual (reorder := hab hcd) (attr := gcongr)]
/--
theorem `himp_le_himp` / 定理 `himp_le_himp`

English:
theorem himp_le_himp
  given: (hab : a <= b) (hcd : c <= d)
  statement: b ⇨ c <= a ⇨ d
  proof: (himp_le_himp_right hab).trans himp_le_himp_left hcd

@[to_dual (attr := simp) sdiff_inf_self_left]

中文:
定理 himp_le_himp
  条件: (hab : a <= b) (hcd : c <= d)
  结论: b ⇨ c <= a ⇨ d
  证明: (himp_le_himp_right hab).trans himp_le_himp_left hcd

@[to_dual (attr := simp) sdiff_inf_self_left]

Depends on / 依赖: himp_le_himp_left, himp_le_himp_right
-/
theorem himp_le_himp (hab : a <= b) (hcd : c <= d) : b ⇨ c <= a ⇨ d :=
(himp_le_himp_right hab).trans himp_le_himp_left hcd

@[to_dual (attr := simp) sdiff_inf_self_left]
/--
theorem `sup_himp_self_left` / 定理 `sup_himp_self_left`

English:
theorem sup_himp_self_left
  given: (a b : α)
  statement: a ⊔ b ⇨ a = b ⇨ a
  proof: by
  rw [sup_himp_distrib]; rw [himp_self]; rw [top_inf_eq]

@[to_dual (attr := simp) sdiff_inf_self_right]

中文:
定理 sup_himp_self_left
  条件: (a b : α)
  结论: a ⊔ b ⇨ a = b ⇨ a
  证明: by
  rw [sup_himp_distrib]; rw [himp_self]; rw [top_inf_eq]

@[to_dual (attr := simp) sdiff_inf_self_right]

Depends on / 依赖: himp_self, sup_himp_distrib, top_inf_eq
-/
theorem sup_himp_self_left (a b : α) : a ⊔ b ⇨ a = b ⇨ a := by
  rw [sup_himp_distrib]; rw [himp_self]; rw [top_inf_eq]

@[to_dual (attr := simp) sdiff_inf_self_right]
/--
theorem `sup_himp_self_right` / 定理 `sup_himp_self_right`

English:
theorem sup_himp_self_right
  given: (a b : α)
  statement: a ⊔ b ⇨ b = a ⇨ b
  proof: by
  rw [sup_himp_distrib]; rw [himp_self]; rw [inf_top_eq]

@[to_dual sdiff_eq_left]

中文:
定理 sup_himp_self_right
  条件: (a b : α)
  结论: a ⊔ b ⇨ b = a ⇨ b
  证明: by
  rw [sup_himp_distrib]; rw [himp_self]; rw [inf_top_eq]

@[to_dual sdiff_eq_left]

Depends on / 依赖: himp_self, inf_top_eq, sup_himp_distrib
-/
theorem sup_himp_self_right (a b : α) : a ⊔ b ⇨ b = a ⇨ b := by
  rw [sup_himp_distrib]; rw [himp_self]; rw [inf_top_eq]

@[to_dual sdiff_eq_left]
/--
theorem `Codisjoint.himp_eq_right` / 定理 `Codisjoint.himp_eq_right`

English:
theorem Codisjoint.himp_eq_right
  given: (h : Codisjoint a b)
  statement: b ⇨ a = a
  proof: by
  conv_rhs => rw [← @top_himp _ _ a]
  rw [← h.eq_top]; rw [sup_himp_self_left]

@[to_dual sdiff_eq_right]

中文:
定理 Codisjoint.himp_eq_right
  条件: (h : Codisjoint a b)
  结论: b ⇨ a = a
  证明: by
  conv_rhs => rw [← @top_himp _ _ a]
  rw [← h.eq_top]; rw [sup_himp_self_left]

@[to_dual sdiff_eq_right]

Depends on / 依赖: conv_rhs, eq_top, h.eq_top, sup_himp_self_left, top_himp
-/
theorem Codisjoint.himp_eq_right (h : Codisjoint a b) : b ⇨ a = a := by
  conv_rhs => rw [← @top_himp _ _ a]
  rw [← h.eq_top]; rw [sup_himp_self_left]

@[to_dual sdiff_eq_right]
/--
theorem `Codisjoint.himp_eq_left` / 定理 `Codisjoint.himp_eq_left`

English:
theorem Codisjoint.himp_eq_left
  given: (h : Codisjoint a b)
  statement: a ⇨ b = b
  proof: h.symm.himp_eq_right

@[to_dual sup_sdiff_cancel_left]

中文:
定理 Codisjoint.himp_eq_left
  条件: (h : Codisjoint a b)
  结论: a ⇨ b = b
  证明: h.symm.himp_eq_right

@[to_dual sup_sdiff_cancel_left]

Depends on / 依赖: h.symm.himp_eq_right, himp_eq_right
-/
theorem Codisjoint.himp_eq_left (h : Codisjoint a b) : a ⇨ b = b :=
  h.symm.himp_eq_right

@[to_dual sup_sdiff_cancel_left]
/--
theorem `Codisjoint.himp_inf_cancel_left` / 定理 `Codisjoint.himp_inf_cancel_left`

English:
theorem Codisjoint.himp_inf_cancel_left
  given: (h : Codisjoint a b)
  statement: a ⇨ a ⊓ b = b
  proof: by
  rw [himp_inf_distrib]; rw [himp_self]; rw [top_inf_eq]; rw [h.himp_eq_left]

@[to_dual sup_sdiff_cancel_right]

中文:
定理 Codisjoint.himp_inf_cancel_left
  条件: (h : Codisjoint a b)
  结论: a ⇨ a ⊓ b = b
  证明: by
  rw [himp_inf_distrib]; rw [himp_self]; rw [top_inf_eq]; rw [h.himp_eq_left]

@[to_dual sup_sdiff_cancel_right]

Depends on / 依赖: h.himp_eq_left, himp_eq_left, himp_inf_distrib, himp_self, top_inf_eq
-/
theorem Codisjoint.himp_inf_cancel_left (h : Codisjoint a b) : a ⇨ a ⊓ b = b := by
  rw [himp_inf_distrib]; rw [himp_self]; rw [top_inf_eq]; rw [h.himp_eq_left]

@[to_dual sup_sdiff_cancel_right]
/--
theorem `Codisjoint.himp_inf_cancel_right` / 定理 `Codisjoint.himp_inf_cancel_right`

English:
theorem Codisjoint.himp_inf_cancel_right
  given: (h : Codisjoint a b)
  statement: b ⇨ a ⊓ b = a
  proof: by
  rw [himp_inf_distrib]; rw [himp_self]; rw [inf_top_eq]; rw [h.himp_eq_right]

中文:
定理 Codisjoint.himp_inf_cancel_right
  条件: (h : Codisjoint a b)
  结论: b ⇨ a ⊓ b = a
  证明: by
  rw [himp_inf_distrib]; rw [himp_self]; rw [inf_top_eq]; rw [h.himp_eq_right]

Depends on / 依赖: h.himp_eq_right, himp_eq_right, himp_inf_distrib, himp_self, inf_top_eq
-/
theorem Codisjoint.himp_inf_cancel_right (h : Codisjoint a b) : b ⇨ a ⊓ b = a := by
  rw [himp_inf_distrib]; rw [himp_self]; rw [inf_top_eq]; rw [h.himp_eq_right]

/-- See `himp_le` for a stronger version in Boolean algebras. -/
@[to_dual le_sdiff_of_le_left
/-- See `le_sdiff` for a stronger version in generalised Boolean algebras. -/]
/--
theorem `Codisjoint.himp_le_of_right_le` / 定理 `Codisjoint.himp_le_of_right_le`

English:
theorem Codisjoint.himp_le_of_right_le
  given: (hac : Codisjoint a c) (hba : b <= a)
  statement: c ⇨ b <= a
  proof: (himp_le_himp_left hba).trans_eq hac.himp_eq_right

@[to_dual sdiff_sdiff_le]

中文:
定理 Codisjoint.himp_le_of_right_le
  条件: (hac : Codisjoint a c) (hba : b <= a)
  结论: c ⇨ b <= a
  证明: (himp_le_himp_left hba).trans_eq hac.himp_eq_right

@[to_dual sdiff_sdiff_le]

Depends on / 依赖: hac.himp_eq_right, himp_eq_right, himp_le_himp_left, trans_eq
-/
theorem Codisjoint.himp_le_of_right_le (hac : Codisjoint a c) (hba : b <= a) : c ⇨ b <= a :=
  (himp_le_himp_left hba).trans_eq hac.himp_eq_right

@[to_dual sdiff_sdiff_le]
/--
theorem `le_himp_himp` / 定理 `le_himp_himp`

English:
theorem le_himp_himp
  statement: a <= (a ⇨ b) ⇨ b
  proof: le_himp_iff.2 inf_himp_le

@[to_dual (attr := simp)]

中文:
定理 le_himp_himp
  结论: a <= (a ⇨ b) ⇨ b
  证明: le_himp_iff.2 inf_himp_le

@[to_dual (attr := simp)]

Depends on / 依赖: inf_himp_le, le_himp_iff
-/
theorem le_himp_himp : a <= (a ⇨ b) ⇨ b :=
  le_himp_iff.2 inf_himp_le

@[to_dual (attr := simp)]
/--
lemma `himp_eq_himp_iff` / 引理 `himp_eq_himp_iff`

English:
lemma himp_eq_himp_iff
  statement: b ⇨ a = a ⇨ b ↔ a = b
  proof: by simp [le_antisymm_iff]

@[to_dual]

中文:
引理 himp_eq_himp_iff
  结论: b ⇨ a = a ⇨ b ↔ a = b
  证明: by simp [le_antisymm_iff]

@[to_dual]

Depends on / 依赖: le_antisymm_iff
-/
lemma himp_eq_himp_iff : b ⇨ a = a ⇨ b ↔ a = b := by simp [le_antisymm_iff]

@[to_dual]
/--
lemma `himp_ne_himp_iff` / 引理 `himp_ne_himp_iff`

English:
lemma himp_ne_himp_iff
  statement: b ⇨ a != a ⇨ b ↔ a != b
  proof: himp_eq_himp_iff.not

@[to_dual none]

中文:
引理 himp_ne_himp_iff
  结论: b ⇨ a != a ⇨ b ↔ a != b
  证明: himp_eq_himp_iff.not

@[to_dual none]

Depends on / 依赖: himp_eq_himp_iff, himp_eq_himp_iff.not
-/
lemma himp_ne_himp_iff : b ⇨ a != a ⇨ b ↔ a != b := himp_eq_himp_iff.not

@[to_dual none]
/--
theorem `himp_triangle` / 定理 `himp_triangle`

English:
theorem himp_triangle
  given: (a b c : α)
  statement: (a ⇨ b) ⊓ (b ⇨ c) <= a ⇨ c
  proof: by
  rw [le_himp_iff]; rw [inf_right_comm]; rw [← le_himp_iff]
  exact himp_inf_le.trans le_himp_himp

@[to_dual none]

中文:
定理 himp_triangle
  条件: (a b c : α)
  结论: (a ⇨ b) ⊓ (b ⇨ c) <= a ⇨ c
  证明: by
  rw [le_himp_iff]; rw [inf_right_comm]; rw [← le_himp_iff]
  exact himp_inf_le.trans le_himp_himp

@[to_dual none]

Depends on / 依赖: himp_inf_le, himp_inf_le.trans, inf_right_comm, le_himp_himp, le_himp_iff
-/
theorem himp_triangle (a b c : α) : (a ⇨ b) ⊓ (b ⇨ c) <= a ⇨ c := by
  rw [le_himp_iff]; rw [inf_right_comm]; rw [← le_himp_iff]
  exact himp_inf_le.trans le_himp_himp

@[to_dual none]
/--
theorem `himp_inf_himp_cancel` / 定理 `himp_inf_himp_cancel`

English:
theorem himp_inf_himp_cancel
  given: (hba : b <= a) (hcb : c <= b)
  statement: (a ⇨ b) ⊓ (b ⇨ c) = a ⇨ c
  proof: (himp_triangle _ _ _).antisymm le_inf (himp_le_himp_left hcb) (himp_le_himp_right hba)

@[to_dual gc_sdiff_sup]

中文:
定理 himp_inf_himp_cancel
  条件: (hba : b <= a) (hcb : c <= b)
  结论: (a ⇨ b) ⊓ (b ⇨ c) = a ⇨ c
  证明: (himp_triangle _ _ _).antisymm le_inf (himp_le_himp_left hcb) (himp_le_himp_right hba)

@[to_dual gc_sdiff_sup]

Depends on / 依赖: antisymm, himp_le_himp_left, himp_le_himp_right, himp_triangle, le_inf
-/
theorem himp_inf_himp_cancel (hba : b <= a) (hcb : c <= b) : (a ⇨ b) ⊓ (b ⇨ c) = a ⇨ c :=
(himp_triangle _ _ _).antisymm le_inf (himp_le_himp_left hcb) (himp_le_himp_right hba)

@[to_dual gc_sdiff_sup]
/--
theorem `gc_inf_himp` / 定理 `gc_inf_himp`

English:
theorem gc_inf_himp
  statement: GaloisConnection (a ⊓ ·) (a ⇨ ·)
  proof: fun _ _ => Iff.symm le_himp_iff'

中文:
定理 gc_inf_himp
  结论: GaloisConnection (a ⊓ ·) (a ⇨ ·)
  证明: fun _ _ => Iff.symm le_himp_iff'

Depends on / 依赖: Iff.symm, le_himp_iff
-/
theorem gc_inf_himp : GaloisConnection (a ⊓ ·) (a ⇨ ·) :=
  fun _ _ => Iff.symm le_himp_iff'

-- See note [lower instance priority]
instance (priority := 100) GeneralizedHeytingAlgebra.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    simp_rw [inf_comm a, ← le_himp_iff, sup_le_iff, le_himp_iff, ← sup_le_iff]; rfl

/--
Instance `OrderDual.instGeneralizedCoheytingAlgebra` / 实例 `OrderDual.instGeneralizedCoheytingAlgebra`

English:
instance OrderDual.instGeneralizedCoheytingAlgebra
  signature: : GeneralizedCoheytingAlgebra αᵒᵈ where
  body: toDual (ofDual b ⇨ ofDual a)
  sdiff_le_iff a b c := by rw [sup_comm]; exact le_himp_iff

中文:
实例 OrderDual.instGeneralizedCoheytingAlgebra
  签名: : GeneralizedCoheyting代数 αᵒᵈ where
  定义体: toDual (ofDual b ⇨ ofDual a)
  sdiff_le_iff a b c := by rw [sup_comm]; exact le_himp_iff

Depends on / 依赖: ofDual, toDual
-/
instance OrderDual.instGeneralizedCoheytingAlgebra : GeneralizedCoheytingAlgebra αᵒᵈ where
  sdiff a b := toDual (ofDual b ⇨ ofDual a)
  sdiff_le_iff a b c := by rw [sup_comm]; exact le_himp_iff

/--
Instance `Prod.instGeneralizedHeytingAlgebra` / 实例 `Prod.instGeneralizedHeytingAlgebra`

English:
instance Prod.instGeneralizedHeytingAlgebra
  signature: [GeneralizedHeytingAlgebra β]
  body: and_congr le_himp_iff le_himp_iff

中文:
实例 积类型.instGeneralizedHeytingAlgebra
  签名: [GeneralizedHeyting代数 β]
  定义体: and_congr le_himp_iff le_himp_iff

Depends on / 依赖: and_congr, le_himp_iff
-/
instance Prod.instGeneralizedHeytingAlgebra [GeneralizedHeytingAlgebra β] :
    GeneralizedHeytingAlgebra (α × β) where
  le_himp_iff _ _ _ := and_congr le_himp_iff le_himp_iff

/--
Instance `Pi.instGeneralizedHeytingAlgebra` / 实例 `Pi.instGeneralizedHeytingAlgebra`

English:
instance Pi.instGeneralizedHeytingAlgebra
  signature: {α : ι -> Type*} [forall i, GeneralizedHeytingAlgebra (α i)]
  body: by simp [le_def]

中文:
实例 依赖函数类型.instGeneralizedHeytingAlgebra
  签名: {α : ι -> 类型} [对任意 i, GeneralizedHeyting代数 (α i)]
  定义体: by simp [le_def]

Depends on / 依赖: le_def
-/
instance Pi.instGeneralizedHeytingAlgebra {α : ι -> Type*} [forall i, GeneralizedHeytingAlgebra (α i)] :
    GeneralizedHeytingAlgebra (forall i, α i) where
  le_himp_iff i := by simp [le_def]

end GeneralizedHeytingAlgebra

section GeneralizedCoheytingAlgebra

variable [GeneralizedCoheytingAlgebra α] {a b c d : α}

@[to_dual none]
/--
theorem `Disjoint.disjoint_sdiff_left` / 定理 `Disjoint.disjoint_sdiff_left`

English:
theorem Disjoint.disjoint_sdiff_left
  given: (h : Disjoint a b)
  statement: Disjoint (a \ c) b
  proof: h.mono_left sdiff_le

@[to_dual none]

中文:
定理 Disjoint.disjoint_sdiff_left
  条件: (h : Disjoint a b)
  结论: Disjoint (a \ c) b
  证明: h.mono_left sdiff_le

@[to_dual none]

Depends on / 依赖: h.mono_left, mono_left, sdiff_le
-/
theorem Disjoint.disjoint_sdiff_left (h : Disjoint a b) : Disjoint (a \ c) b :=
  h.mono_left sdiff_le

@[to_dual none]
/--
theorem `Disjoint.disjoint_sdiff_right` / 定理 `Disjoint.disjoint_sdiff_right`

English:
theorem Disjoint.disjoint_sdiff_right
  given: (h : Disjoint a b)
  statement: Disjoint a (b \ c)
  proof: h.mono_right sdiff_le

@[to_dual none]

中文:
定理 Disjoint.disjoint_sdiff_right
  条件: (h : Disjoint a b)
  结论: Disjoint a (b \ c)
  证明: h.mono_right sdiff_le

@[to_dual none]

Depends on / 依赖: h.mono_right, mono_right, sdiff_le
-/
theorem Disjoint.disjoint_sdiff_right (h : Disjoint a b) : Disjoint a (b \ c) :=
  h.mono_right sdiff_le

@[to_dual none]
/--
theorem `sup_sdiff_left` / 定理 `sup_sdiff_left`

English:
theorem sup_sdiff_left
  statement: a ⊔ a \ b = a
  proof: sup_of_le_left sdiff_le

@[to_dual none]

中文:
定理 sup_sdiff_left
  结论: a ⊔ a \ b = a
  证明: sup_of_le_left sdiff_le

@[to_dual none]

Depends on / 依赖: sdiff_le, sup_of_le_left
-/
theorem sup_sdiff_left : a ⊔ a \ b = a :=
  sup_of_le_left sdiff_le

@[to_dual none]
/--
theorem `sup_sdiff_right` / 定理 `sup_sdiff_right`

English:
theorem sup_sdiff_right
  statement: a \ b ⊔ a = a
  proof: sup_of_le_right sdiff_le

@[to_dual none]

中文:
定理 sup_sdiff_right
  结论: a \ b ⊔ a = a
  证明: sup_of_le_right sdiff_le

@[to_dual none]

Depends on / 依赖: sdiff_le, sup_of_le_right
-/
theorem sup_sdiff_right : a \ b ⊔ a = a :=
  sup_of_le_right sdiff_le

@[to_dual none]
/--
theorem `inf_sdiff_left` / 定理 `inf_sdiff_left`

English:
theorem inf_sdiff_left
  statement: a \ b ⊓ a = a \ b
  proof: inf_of_le_left sdiff_le

@[to_dual none]

中文:
定理 inf_sdiff_left
  结论: a \ b ⊓ a = a \ b
  证明: inf_of_le_left sdiff_le

@[to_dual none]

Depends on / 依赖: inf_of_le_left, sdiff_le
-/
theorem inf_sdiff_left : a \ b ⊓ a = a \ b :=
  inf_of_le_left sdiff_le

@[to_dual none]
/--
theorem `inf_sdiff_right` / 定理 `inf_sdiff_right`

English:
theorem inf_sdiff_right
  statement: a ⊓ a \ b = a \ b
  proof: inf_of_le_right sdiff_le

@[to_dual none]
alias sup_sdiff_self_left := sdiff_sup_self

@[to_dual none]
alias sup_sdiff_self_right := sup_sdiff_self

@[to_dual none]

中文:
定理 inf_sdiff_right
  结论: a ⊓ a \ b = a \ b
  证明: inf_of_le_right sdiff_le

@[to_dual none]
alias sup_sdiff_self_left := sdiff_sup_self

@[to_dual none]
alias sup_sdiff_self_right := sup_sdiff_self

@[to_dual none]

Depends on / 依赖: inf_of_le_right, sdiff_le
-/
theorem inf_sdiff_right : a ⊓ a \ b = a \ b :=
  inf_of_le_right sdiff_le

@[to_dual none]
alias sup_sdiff_self_left := sdiff_sup_self

@[to_dual none]
alias sup_sdiff_self_right := sup_sdiff_self

@[to_dual none]
/--
theorem `sup_sdiff_eq_sup` / 定理 `sup_sdiff_eq_sup`

English:
theorem sup_sdiff_eq_sup
  given: (h : c <= a)
  statement: a ⊔ b \ c = a ⊔ b
  proof: sup_congr_left (sdiff_le.trans le_sup_right) le_sup_sdiff.trans sup_le_sup_right h _

中文:
定理 sup_sdiff_eq_sup
  条件: (h : c <= a)
  结论: a ⊔ b \ c = a ⊔ b
  证明: sup_congr_left (sdiff_le.trans le_sup_right) le_sup_sdiff.trans sup_le_sup_right h _

Depends on / 依赖: le_sup_right, le_sup_sdiff, le_sup_sdiff.trans, sdiff_le, sdiff_le.trans, sup_congr_left, sup_le_sup_right
-/
theorem sup_sdiff_eq_sup (h : c <= a) : a ⊔ b \ c = a ⊔ b :=
sup_congr_left (sdiff_le.trans le_sup_right) le_sup_sdiff.trans sup_le_sup_right h _

-- cf. `Set.union_sdiff_cancel'`
@[to_dual none]
/--
theorem `sup_sdiff_cancel'` / 定理 `sup_sdiff_cancel'`

English:
theorem sup_sdiff_cancel'
  given: (hab : a <= b) (hbc : b <= c)
  statement: b ⊔ c \ a = c
  proof: by
  rw [sup_sdiff_eq_sup hab]; rw [sup_of_le_right hbc]

@[to_dual none]

中文:
定理 sup_sdiff_cancel'
  条件: (hab : a <= b) (hbc : b <= c)
  结论: b ⊔ c \ a = c
  证明: by
  rw [sup_sdiff_eq_sup hab]; rw [sup_of_le_right hbc]

@[to_dual none]

Depends on / 依赖: sup_of_le_right, sup_sdiff_eq_sup
-/
theorem sup_sdiff_cancel' (hab : a <= b) (hbc : b <= c) : b ⊔ c \ a = c := by
  rw [sup_sdiff_eq_sup hab]; rw [sup_of_le_right hbc]

@[to_dual none]
/--
theorem `sup_sdiff_cancel_right` / 定理 `sup_sdiff_cancel_right`

English:
theorem sup_sdiff_cancel_right
  given: (h : a <= b)
  statement: a ⊔ b \ a = b
  proof: sup_sdiff_cancel' le_rfl h

@[to_dual none]

中文:
定理 sup_sdiff_cancel_right
  条件: (h : a <= b)
  结论: a ⊔ b \ a = b
  证明: sup_sdiff_cancel' le_rfl h

@[to_dual none]

Depends on / 依赖: le_rfl, sup_sdiff_cancel
-/
theorem sup_sdiff_cancel_right (h : a <= b) : a ⊔ b \ a = b :=
  sup_sdiff_cancel' le_rfl h

@[to_dual none]
/--
theorem `sdiff_sup_cancel` / 定理 `sdiff_sup_cancel`

English:
theorem sdiff_sup_cancel
  given: (h : b <= a)
  statement: a \ b ⊔ b = a
  proof: by rw [sup_comm, sup_sdiff_cancel_right h]

@[to_dual none]

中文:
定理 sdiff_sup_cancel
  条件: (h : b <= a)
  结论: a \ b ⊔ b = a
  证明: by rw [sup_comm, sup_sdiff_cancel_right h]

@[to_dual none]

Depends on / 依赖: sup_comm, sup_sdiff_cancel_right
-/
theorem sdiff_sup_cancel (h : b <= a) : a \ b ⊔ b = a := by rw [sup_comm, sup_sdiff_cancel_right h]

@[to_dual none]
/--
theorem `sdiff_left_inj` / 定理 `sdiff_left_inj`

English:
theorem sdiff_left_inj
  given: (hac : c <= a) (hbc : c <= b)
  statement: a \ c = b \ c ↔ a = b
  proof: ⟨fun h => by rw [← sdiff_sup_cancel hac, h, sdiff_sup_cancel hbc], congrArg (· \ c)⟩

@[to_dual none]

中文:
定理 sdiff_left_inj
  条件: (hac : c <= a) (hbc : c <= b)
  结论: a \ c = b \ c ↔ a = b
  证明: ⟨fun h => by rw [← sdiff_sup_cancel hac, h, sdiff_sup_cancel hbc], congrArg (· \ c)⟩

@[to_dual none]

Depends on / 依赖: sdiff_sup_cancel
-/
theorem sdiff_left_inj (hac : c <= a) (hbc : c <= b) : a \ c = b \ c ↔ a = b :=
  ⟨fun h => by rw [← sdiff_sup_cancel hac, h, sdiff_sup_cancel hbc], congrArg (· \ c)⟩

@[to_dual none]
/--
theorem `sup_le_of_le_sdiff_left` / 定理 `sup_le_of_le_sdiff_left`

English:
theorem sup_le_of_le_sdiff_left
  given: (h : b <= c \ a) (hac : a <= c)
  statement: a ⊔ b <= c
  proof: sup_le hac h.trans sdiff_le

@[to_dual none]

中文:
定理 sup_le_of_le_sdiff_left
  条件: (h : b <= c \ a) (hac : a <= c)
  结论: a ⊔ b <= c
  证明: sup_le hac h.trans sdiff_le

@[to_dual none]

Depends on / 依赖: h.trans, sdiff_le, sup_le
-/
theorem sup_le_of_le_sdiff_left (h : b <= c \ a) (hac : a <= c) : a ⊔ b <= c :=
sup_le hac h.trans sdiff_le

@[to_dual none]
/--
theorem `sup_le_of_le_sdiff_right` / 定理 `sup_le_of_le_sdiff_right`

English:
theorem sup_le_of_le_sdiff_right
  given: (h : a <= c \ b) (hbc : b <= c)
  statement: a ⊔ b <= c
  proof: sup_le (h.trans sdiff_le) hbc

@[to_dual none]

中文:
定理 sup_le_of_le_sdiff_right
  条件: (h : a <= c \ b) (hbc : b <= c)
  结论: a ⊔ b <= c
  证明: sup_le (h.trans sdiff_le) hbc

@[to_dual none]

Depends on / 依赖: h.trans, sdiff_le, sup_le
-/
theorem sup_le_of_le_sdiff_right (h : a <= c \ b) (hbc : b <= c) : a ⊔ b <= c :=
  sup_le (h.trans sdiff_le) hbc

@[to_dual none]
/--
theorem `sdiff_sdiff_sdiff_le_sdiff` / 定理 `sdiff_sdiff_sdiff_le_sdiff`

English:
theorem sdiff_sdiff_sdiff_le_sdiff
  statement: (a \ b) \ (a \ c) <= c \ b
  proof: by
  rw [sdiff_le_iff]; rw [sdiff_le_iff]; rw [sup_left_comm]; rw [sup_sdiff_self]; rw [sup_left_comm]; rw [sdiff_sup_self]; rw [sup_left_comm]
  exact le_sup_left

@[simp, to_dual none]

中文:
定理 sdiff_sdiff_sdiff_le_sdiff
  结论: (a \ b) \ (a \ c) <= c \ b
  证明: by
  rw [sdiff_le_iff]; rw [sdiff_le_iff]; rw [sup_left_comm]; rw [sup_sdiff_self]; rw [sup_left_comm]; rw [sdiff_sup_self]; rw [sup_left_comm]
  exact le_sup_left

@[simp, to_dual none]

Depends on / 依赖: le_sup_left, sdiff_le_iff, sdiff_sup_self, sup_left_comm, sup_sdiff_self
-/
theorem sdiff_sdiff_sdiff_le_sdiff : (a \ b) \ (a \ c) <= c \ b := by
  rw [sdiff_le_iff]; rw [sdiff_le_iff]; rw [sup_left_comm]; rw [sup_sdiff_self]; rw [sup_left_comm]; rw [sdiff_sup_self]; rw [sup_left_comm]
  exact le_sup_left

@[simp, to_dual none]
/--
theorem `le_sup_sdiff_sup_sdiff` / 定理 `le_sup_sdiff_sup_sdiff`

English:
theorem le_sup_sdiff_sup_sdiff
  statement: a <= b ⊔ (a \ c ⊔ c \ b)
  proof: by
  simpa using @sdiff_sdiff_sdiff_le_sdiff

@[to_dual none]

中文:
定理 le_sup_sdiff_sup_sdiff
  结论: a <= b ⊔ (a \ c ⊔ c \ b)
  证明: by
  simpa using @sdiff_sdiff_sdiff_le_sdiff

@[to_dual none]

Depends on / 依赖: sdiff_sdiff_sdiff_le_sdiff
-/
theorem le_sup_sdiff_sup_sdiff : a <= b ⊔ (a \ c ⊔ c \ b) := by
  simpa using @sdiff_sdiff_sdiff_le_sdiff

@[to_dual none]
/--
theorem `sdiff_sdiff` / 定理 `sdiff_sdiff`

English:
theorem sdiff_sdiff
  given: (a b c : α)
  statement: (a \ b) \ c = a \ (b ⊔ c)
  proof: eq_of_forall_ge_iff fun d => by simp_rw [sdiff_le_iff, sup_assoc]

@[to_dual none]

中文:
定理 sdiff_sdiff
  条件: (a b c : α)
  结论: (a \ b) \ c = a \ (b ⊔ c)
  证明: eq_of_forall_ge_iff fun d => by simp_rw [sdiff_le_iff, sup_assoc]

@[to_dual none]

Depends on / 依赖: eq_of_forall_ge_iff, sdiff_le_iff, simp_rw, sup_assoc
-/
theorem sdiff_sdiff (a b c : α) : (a \ b) \ c = a \ (b ⊔ c) :=
  eq_of_forall_ge_iff fun d => by simp_rw [sdiff_le_iff, sup_assoc]

@[to_dual none]
/--
theorem `sdiff_sdiff_left` / 定理 `sdiff_sdiff_left`

English:
theorem sdiff_sdiff_left
  statement: (a \ b) \ c = a \ (b ⊔ c)
  proof: sdiff_sdiff _ _ _

@[to_dual none]

中文:
定理 sdiff_sdiff_left
  结论: (a \ b) \ c = a \ (b ⊔ c)
  证明: sdiff_sdiff _ _ _

@[to_dual none]

Depends on / 依赖: sdiff_sdiff
-/
theorem sdiff_sdiff_left : (a \ b) \ c = a \ (b ⊔ c) :=
  sdiff_sdiff _ _ _

@[to_dual none]
/--
theorem `sdiff_sdiff_comm` / 定理 `sdiff_sdiff_comm`

English:
theorem sdiff_sdiff_comm
  statement: (a \ b) \ c = (a \ c) \ b
  proof: sdiff_right_comm _ _ _

@[simp, to_dual none]

中文:
定理 sdiff_sdiff_comm
  结论: (a \ b) \ c = (a \ c) \ b
  证明: sdiff_right_comm _ _ _

@[simp, to_dual none]

Depends on / 依赖: sdiff_right_comm
-/
theorem sdiff_sdiff_comm : (a \ b) \ c = (a \ c) \ b :=
  sdiff_right_comm _ _ _

@[simp, to_dual none]
/--
theorem `sdiff_sdiff_self` / 定理 `sdiff_sdiff_self`

English:
theorem sdiff_sdiff_self
  statement: (a \ b) \ a = ⊥
  proof: by rw [sdiff_sdiff_comm, sdiff_self, bot_sdiff]

@[to_dual none]

中文:
定理 sdiff_sdiff_self
  结论: (a \ b) \ a = ⊥
  证明: by rw [sdiff_sdiff_comm, sdiff_self, bot_sdiff]

@[to_dual none]

Depends on / 依赖: bot_sdiff, sdiff_sdiff_comm, sdiff_self
-/
theorem sdiff_sdiff_self : (a \ b) \ a = ⊥ := by rw [sdiff_sdiff_comm, sdiff_self, bot_sdiff]

@[to_dual none]
/--
theorem `sup_sdiff` / 定理 `sup_sdiff`

English:
theorem sup_sdiff
  statement: (a ⊔ b) \ c = a \ c ⊔ b \ c
  proof: sup_sdiff_distrib _ _ _

@[simp, to_dual none]

中文:
定理 sup_sdiff
  结论: (a ⊔ b) \ c = a \ c ⊔ b \ c
  证明: sup_sdiff_distrib _ _ _

@[simp, to_dual none]

Depends on / 依赖: sup_sdiff_distrib
-/
theorem sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c :=
  sup_sdiff_distrib _ _ _

@[simp, to_dual none]
/--
theorem `sup_sdiff_right_self` / 定理 `sup_sdiff_right_self`

English:
theorem sup_sdiff_right_self
  statement: (a ⊔ b) \ b = a \ b
  proof: by rw [sup_sdiff, sdiff_self, sup_bot_eq]

@[simp, to_dual none]

中文:
定理 sup_sdiff_right_self
  结论: (a ⊔ b) \ b = a \ b
  证明: by rw [sup_sdiff, sdiff_self, sup_bot_eq]

@[simp, to_dual none]

Depends on / 依赖: sdiff_self, sup_bot_eq, sup_sdiff
-/
theorem sup_sdiff_right_self : (a ⊔ b) \ b = a \ b := by rw [sup_sdiff, sdiff_self, sup_bot_eq]

@[simp, to_dual none]
/--
theorem `sup_sdiff_left_self` / 定理 `sup_sdiff_left_self`

English:
theorem sup_sdiff_left_self
  statement: (a ⊔ b) \ a = b \ a
  proof: by rw [sup_comm, sup_sdiff_right_self]

中文:
定理 sup_sdiff_left_self
  结论: (a ⊔ b) \ a = b \ a
  证明: by rw [sup_comm, sup_sdiff_right_self]

Depends on / 依赖: sup_comm, sup_sdiff_right_self
-/
theorem sup_sdiff_left_self : (a ⊔ b) \ a = b \ a := by rw [sup_comm, sup_sdiff_right_self]

-- cf. `IsCompl.inf_sup`
@[to_dual none]
/--
theorem `sdiff_inf` / 定理 `sdiff_inf`

English:
theorem sdiff_inf
  statement: a \ (b ⊓ c) = a \ b ⊔ a \ c
  proof: sdiff_inf_distrib _ _ _

@[to_dual none]

中文:
定理 sdiff_inf
  结论: a \ (b ⊓ c) = a \ b ⊔ a \ c
  证明: sdiff_inf_distrib _ _ _

@[to_dual none]

Depends on / 依赖: sdiff_inf_distrib
-/
theorem sdiff_inf : a \ (b ⊓ c) = a \ b ⊔ a \ c :=
  sdiff_inf_distrib _ _ _

@[to_dual none]
/--
theorem `sdiff_triangle` / 定理 `sdiff_triangle`

English:
theorem sdiff_triangle
  given: (a b c : α)
  statement: a \ c <= a \ b ⊔ b \ c
  proof: by
  rw [sdiff_le_iff]; rw [sup_left_comm]; rw [← sdiff_le_iff]
  exact sdiff_sdiff_le.trans le_sup_sdiff

@[to_dual none]

中文:
定理 sdiff_triangle
  条件: (a b c : α)
  结论: a \ c <= a \ b ⊔ b \ c
  证明: by
  rw [sdiff_le_iff]; rw [sup_left_comm]; rw [← sdiff_le_iff]
  exact sdiff_sdiff_le.trans le_sup_sdiff

@[to_dual none]

Depends on / 依赖: le_sup_sdiff, sdiff_le_iff, sdiff_sdiff_le, sdiff_sdiff_le.trans, sup_left_comm
-/
theorem sdiff_triangle (a b c : α) : a \ c <= a \ b ⊔ b \ c := by
  rw [sdiff_le_iff]; rw [sup_left_comm]; rw [← sdiff_le_iff]
  exact sdiff_sdiff_le.trans le_sup_sdiff

@[to_dual none]
/--
theorem `sdiff_sup_sdiff_cancel` / 定理 `sdiff_sup_sdiff_cancel`

English:
theorem sdiff_sup_sdiff_cancel
  given: (hba : b <= a) (hcb : c <= b)
  statement: a \ b ⊔ b \ c = a \ c
  proof: (sdiff_triangle _ _ _).antisymm' sup_le (sdiff_le_sdiff_left hcb) (sdiff_le_sdiff_right hba)

中文:
定理 sdiff_sup_sdiff_cancel
  条件: (hba : b <= a) (hcb : c <= b)
  结论: a \ b ⊔ b \ c = a \ c
  证明: (sdiff_triangle _ _ _).antisymm' sup_le (sdiff_le_sdiff_left hcb) (sdiff_le_sdiff_right hba)

Depends on / 依赖: antisymm, sdiff_le_sdiff_left, sdiff_le_sdiff_right, sdiff_triangle, sup_le
-/
theorem sdiff_sup_sdiff_cancel (hba : b <= a) (hcb : c <= b) : a \ b ⊔ b \ c = a \ c :=
(sdiff_triangle _ _ _).antisymm' sup_le (sdiff_le_sdiff_left hcb) (sdiff_le_sdiff_right hba)

/-- a version of `sdiff_sup_sdiff_cancel` with more general hypotheses. -/
@[to_dual none]
/--
theorem `sdiff_sup_sdiff_cancel'` / 定理 `sdiff_sup_sdiff_cancel'`

English:
theorem sdiff_sup_sdiff_cancel'
  given: (hinf : a ⊓ c <= b) (hsup : b <= a ⊔ c)
  proof: by
refine (sdiff_triangle ..).antisymm' sup_le ?_ by simpa [sup_comm]
  rw [← sdiff_inf_self_left (b := c)]
  exact sdiff_le_sdiff_left hinf

@[to_dual none]

中文:
定理 sdiff_sup_sdiff_cancel'
  条件: (hinf : a ⊓ c <= b) (hsup : b <= a ⊔ c)
  证明: by
refine (sdiff_triangle ..).antisymm' sup_le ?_ by simpa [sup_comm]
  rw [← sdiff_inf_self_left (b := c)]
  exact sdiff_le_sdiff_left hinf

@[to_dual none]

Depends on / 依赖: antisymm, sdiff_inf_self_left, sdiff_le_sdiff_left, sdiff_triangle, sup_comm, sup_le
-/
theorem sdiff_sup_sdiff_cancel' (hinf : a ⊓ c <= b) (hsup : b <= a ⊔ c) :
    a \ b ⊔ b \ c = a \ c := by
refine (sdiff_triangle ..).antisymm' sup_le ?_ by simpa [sup_comm]
  rw [← sdiff_inf_self_left (b := c)]
  exact sdiff_le_sdiff_left hinf

@[to_dual none]
/--
theorem `sdiff_le_sdiff_of_sup_le_sup_left` / 定理 `sdiff_le_sdiff_of_sup_le_sup_left`

English:
theorem sdiff_le_sdiff_of_sup_le_sup_left
  given: (h : c ⊔ a <= c ⊔ b)
  statement: a \ c <= b \ c
  proof: by
  rw [← sup_sdiff_left_self]; rw [← @sup_sdiff_left_self _ _ _ b]
  exact sdiff_le_sdiff_right h

@[to_dual none]

中文:
定理 sdiff_le_sdiff_of_sup_le_sup_left
  条件: (h : c ⊔ a <= c ⊔ b)
  结论: a \ c <= b \ c
  证明: by
  rw [← sup_sdiff_left_self]; rw [← @sup_sdiff_left_self _ _ _ b]
  exact sdiff_le_sdiff_right h

@[to_dual none]

Depends on / 依赖: sdiff_le_sdiff_right, sup_sdiff_left_self
-/
theorem sdiff_le_sdiff_of_sup_le_sup_left (h : c ⊔ a <= c ⊔ b) : a \ c <= b \ c := by
  rw [← sup_sdiff_left_self]; rw [← @sup_sdiff_left_self _ _ _ b]
  exact sdiff_le_sdiff_right h

@[to_dual none]
/--
theorem `sdiff_le_sdiff_of_sup_le_sup_right` / 定理 `sdiff_le_sdiff_of_sup_le_sup_right`

English:
theorem sdiff_le_sdiff_of_sup_le_sup_right
  given: (h : a ⊔ c <= b ⊔ c)
  statement: a \ c <= b \ c
  proof: by
  rw [← sup_sdiff_right_self]; rw [← @sup_sdiff_right_self _ _ b]
  exact sdiff_le_sdiff_right h

@[simp, to_dual none]

中文:
定理 sdiff_le_sdiff_of_sup_le_sup_right
  条件: (h : a ⊔ c <= b ⊔ c)
  结论: a \ c <= b \ c
  证明: by
  rw [← sup_sdiff_right_self]; rw [← @sup_sdiff_right_self _ _ b]
  exact sdiff_le_sdiff_right h

@[simp, to_dual none]

Depends on / 依赖: sdiff_le_sdiff_right, sup_sdiff_right_self
-/
theorem sdiff_le_sdiff_of_sup_le_sup_right (h : a ⊔ c <= b ⊔ c) : a \ c <= b \ c := by
  rw [← sup_sdiff_right_self]; rw [← @sup_sdiff_right_self _ _ b]
  exact sdiff_le_sdiff_right h

@[simp, to_dual none]
/--
theorem `inf_sdiff_sup_left` / 定理 `inf_sdiff_sup_left`

English:
theorem inf_sdiff_sup_left
  statement: a \ c ⊓ (a ⊔ b) = a \ c
  proof: inf_of_le_left sdiff_le.trans le_sup_left

@[simp, to_dual none]

中文:
定理 inf_sdiff_sup_left
  结论: a \ c ⊓ (a ⊔ b) = a \ c
  证明: inf_of_le_left sdiff_le.trans le_sup_left

@[simp, to_dual none]

Depends on / 依赖: inf_of_le_left, le_sup_left, sdiff_le, sdiff_le.trans
-/
theorem inf_sdiff_sup_left : a \ c ⊓ (a ⊔ b) = a \ c :=
inf_of_le_left sdiff_le.trans le_sup_left

@[simp, to_dual none]
/--
theorem `inf_sdiff_sup_right` / 定理 `inf_sdiff_sup_right`

English:
theorem inf_sdiff_sup_right
  statement: a \ c ⊓ (b ⊔ a) = a \ c
  proof: inf_of_le_left sdiff_le.trans le_sup_right

中文:
定理 inf_sdiff_sup_right
  结论: a \ c ⊓ (b ⊔ a) = a \ c
  证明: inf_of_le_left sdiff_le.trans le_sup_right

Depends on / 依赖: inf_of_le_left, le_sup_right, sdiff_le, sdiff_le.trans
-/
theorem inf_sdiff_sup_right : a \ c ⊓ (b ⊔ a) = a \ c :=
inf_of_le_left sdiff_le.trans le_sup_right

-- See note [lower instance priority]
@[to_dual existing]
instance (priority := 100) GeneralizedCoheytingAlgebra.toDistribLattice : DistribLattice α :=
  { ‹GeneralizedCoheytingAlgebra α› with
    le_sup_inf :=
      fun a b c => by simp_rw [← sdiff_le_iff, le_inf_iff, sdiff_le_iff, ← le_inf_iff]; rfl }

@[to_dual existing]
/--
Instance `OrderDual.instGeneralizedHeytingAlgebra` / 实例 `OrderDual.instGeneralizedHeytingAlgebra`

English:
instance OrderDual.instGeneralizedHeytingAlgebra
  signature: : GeneralizedHeytingAlgebra αᵒᵈ where
  body: fun a b => toDual (ofDual b \ ofDual a)
  le_himp_iff := fun a b c => by rw [inf_comm]; exact sdiff_le_iff

@[to_dual existing]

中文:
实例 OrderDual.instGeneralizedHeytingAlgebra
  签名: : GeneralizedHeyting代数 αᵒᵈ where
  定义体: fun a b => toDual (ofDual b \ ofDual a)
  le_himp_iff := fun a b c => by rw [inf_comm]; exact sdiff_le_iff

@[to_dual existing]

Depends on / 依赖: ofDual, toDual
-/
instance OrderDual.instGeneralizedHeytingAlgebra : GeneralizedHeytingAlgebra αᵒᵈ where
  himp := fun a b => toDual (ofDual b \ ofDual a)
  le_himp_iff := fun a b c => by rw [inf_comm]; exact sdiff_le_iff

@[to_dual existing]
/--
Instance `Prod.instGeneralizedCoheytingAlgebra` / 实例 `Prod.instGeneralizedCoheytingAlgebra`

English:
instance Prod.instGeneralizedCoheytingAlgebra
  signature: [GeneralizedCoheytingAlgebra β]
  body: and_congr sdiff_le_iff sdiff_le_iff

@[to_dual existing]

中文:
实例 积类型.instGeneralizedCoheytingAlgebra
  签名: [GeneralizedCoheyting代数 β]
  定义体: and_congr sdiff_le_iff sdiff_le_iff

@[to_dual existing]

Depends on / 依赖: and_congr, sdiff_le_iff
-/
instance Prod.instGeneralizedCoheytingAlgebra [GeneralizedCoheytingAlgebra β] :
    GeneralizedCoheytingAlgebra (α × β) where
  sdiff_le_iff _ _ _ := and_congr sdiff_le_iff sdiff_le_iff

@[to_dual existing]
/--
Instance `Pi.instGeneralizedCoheytingAlgebra` / 实例 `Pi.instGeneralizedCoheytingAlgebra`

English:
instance Pi.instGeneralizedCoheytingAlgebra
  signature: {α : ι -> Type*}
  body: by simp [le_def]

中文:
实例 依赖函数类型.instGeneralizedCoheytingAlgebra
  签名: {α : ι -> 类型}
  定义体: by simp [le_def]

Depends on / 依赖: le_def
-/
instance Pi.instGeneralizedCoheytingAlgebra {α : ι -> Type*}
    [forall i, GeneralizedCoheytingAlgebra (α i)] : GeneralizedCoheytingAlgebra (forall i, α i) where
  sdiff_le_iff i := by simp [le_def]

end GeneralizedCoheytingAlgebra

section HeytingAlgebra

variable [HeytingAlgebra α] {a b : α}

@[to_dual (attr := simp) top_sdiff']
/--
theorem `himp_bot` / 定理 `himp_bot`

English:
theorem himp_bot
  given: (a : α)
  statement: a ⇨ ⊥ = aᶜ
  proof: HeytingAlgebra.himp_bot _

@[to_dual (attr := simp) sdiff_top]

中文:
定理 himp_bot
  条件: (a : α)
  结论: a ⇨ ⊥ = aᶜ
  证明: HeytingAlgebra.himp_bot _

@[to_dual (attr := simp) sdiff_top]

Depends on / 依赖: HeytingAlgebra, HeytingAlgebra.himp_bot, himp_bot
-/
theorem himp_bot (a : α) : a ⇨ ⊥ = aᶜ :=
  HeytingAlgebra.himp_bot _

@[to_dual (attr := simp) sdiff_top]
/--
theorem `bot_himp` / 定理 `bot_himp`

English:
theorem bot_himp
  given: (a : α)
  statement: ⊥ ⇨ a = ⊤
  proof: himp_eq_top_iff.2 bot_le

@[to_dual]

中文:
定理 bot_himp
  条件: (a : α)
  结论: ⊥ ⇨ a = ⊤
  证明: himp_eq_top_iff.2 bot_le

@[to_dual]

Depends on / 依赖: bot_le, himp_eq_top_iff
-/
theorem bot_himp (a : α) : ⊥ ⇨ a = ⊤ :=
  himp_eq_top_iff.2 bot_le

@[to_dual]
/--
theorem `compl_sup_distrib` / 定理 `compl_sup_distrib`

English:
theorem compl_sup_distrib
  given: (a b : α)
  statement: (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
  proof: by
  simp_rw [← himp_bot, sup_himp_distrib]

@[to_dual (attr := simp)]

中文:
定理 compl_sup_distrib
  条件: (a b : α)
  结论: (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
  证明: by
  simp_rw [← himp_bot, sup_himp_distrib]

@[to_dual (attr := simp)]

Depends on / 依赖: himp_bot, simp_rw, sup_himp_distrib
-/
theorem compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by
  simp_rw [← himp_bot, sup_himp_distrib]

@[to_dual (attr := simp)]
/--
theorem `compl_sup` / 定理 `compl_sup`

English:
theorem compl_sup
  statement: (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
  proof: compl_sup_distrib _ _

@[to_dual sdiff_le_hnot]

中文:
定理 compl_sup
  结论: (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
  证明: compl_sup_distrib _ _

@[to_dual sdiff_le_hnot]

Depends on / 依赖: compl_sup_distrib
-/
theorem compl_sup : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ :=
  compl_sup_distrib _ _

@[to_dual sdiff_le_hnot]
/--
theorem `compl_le_himp` / 定理 `compl_le_himp`

English:
theorem compl_le_himp
  statement: aᶜ <= a ⇨ b
  proof: (himp_bot _).ge.trans himp_le_himp_left bot_le

@[to_dual none]

中文:
定理 compl_le_himp
  结论: aᶜ <= a ⇨ b
  证明: (himp_bot _).ge.trans himp_le_himp_left bot_le

@[to_dual none]

Depends on / 依赖: bot_le, ge.trans, himp_bot, himp_le_himp_left
-/
theorem compl_le_himp : aᶜ <= a ⇨ b :=
(himp_bot _).ge.trans himp_le_himp_left bot_le

@[to_dual none]
/--
theorem `compl_sup_le_himp` / 定理 `compl_sup_le_himp`

English:
theorem compl_sup_le_himp
  statement: aᶜ ⊔ b <= a ⇨ b
  proof: sup_le compl_le_himp le_himp

@[to_dual sdiff_le_inf_hnot]

中文:
定理 compl_sup_le_himp
  结论: aᶜ ⊔ b <= a ⇨ b
  证明: sup_le compl_le_himp le_himp

@[to_dual sdiff_le_inf_hnot]

Depends on / 依赖: compl_le_himp, le_himp, sup_le
-/
theorem compl_sup_le_himp : aᶜ ⊔ b <= a ⇨ b :=
  sup_le compl_le_himp le_himp

@[to_dual sdiff_le_inf_hnot]
/--
theorem `sup_compl_le_himp` / 定理 `sup_compl_le_himp`

English:
theorem sup_compl_le_himp
  statement: b ⊔ aᶜ <= a ⇨ b
  proof: sup_le le_himp compl_le_himp

中文:
定理 sup_compl_le_himp
  结论: b ⊔ aᶜ <= a ⇨ b
  证明: sup_le le_himp compl_le_himp

Depends on / 依赖: compl_le_himp, le_himp, sup_le
-/
theorem sup_compl_le_himp : b ⊔ aᶜ <= a ⇨ b :=
  sup_le le_himp compl_le_himp

-- `p → ¬ p ↔ ¬ p`
@[to_dual (attr := simp) hnot_sdiff]
/--
theorem `himp_compl` / 定理 `himp_compl`

English:
theorem himp_compl
  given: (a : α)
  statement: a ⇨ aᶜ = aᶜ
  proof: by rw [← himp_bot, himp_himp, inf_idem]

中文:
定理 himp_compl
  条件: (a : α)
  结论: a ⇨ aᶜ = aᶜ
  证明: by rw [← himp_bot, himp_himp, inf_idem]

Depends on / 依赖: himp_bot, himp_himp, inf_idem
-/
theorem himp_compl (a : α) : a ⇨ aᶜ = aᶜ := by rw [← himp_bot, himp_himp, inf_idem]

-- `p → ¬ q ↔ q → ¬ p`
@[to_dual (reorder := a b) hnot_sdiff_comm]
/--
theorem `himp_compl_comm` / 定理 `himp_compl_comm`

English:
theorem himp_compl_comm
  given: (a b : α)
  statement: a ⇨ bᶜ = b ⇨ aᶜ
  proof: by simp_rw [← himp_bot, himp_left_comm]

@[to_dual hnot_le_iff_codisjoint_left]

中文:
定理 himp_compl_comm
  条件: (a b : α)
  结论: a ⇨ bᶜ = b ⇨ aᶜ
  证明: by simp_rw [← himp_bot, himp_left_comm]

@[to_dual hnot_le_iff_codisjoint_left]

Depends on / 依赖: himp_bot, himp_left_comm, simp_rw
-/
theorem himp_compl_comm (a b : α) : a ⇨ bᶜ = b ⇨ aᶜ := by simp_rw [← himp_bot, himp_left_comm]

@[to_dual hnot_le_iff_codisjoint_left]
/--
theorem `le_compl_iff_disjoint_right` / 定理 `le_compl_iff_disjoint_right`

English:
theorem le_compl_iff_disjoint_right
  statement: a <= bᶜ ↔ Disjoint a b
  proof: by
  rw [← himp_bot]; rw [le_himp_iff]; rw [disjoint_iff_inf_le]

@[to_dual hnot_le_iff_codisjoint_right]

中文:
定理 le_compl_iff_disjoint_right
  结论: a <= bᶜ ↔ Disjoint a b
  证明: by
  rw [← himp_bot]; rw [le_himp_iff]; rw [disjoint_iff_inf_le]

@[to_dual hnot_le_iff_codisjoint_right]

Depends on / 依赖: disjoint_iff_inf_le, himp_bot, le_himp_iff
-/
theorem le_compl_iff_disjoint_right : a <= bᶜ ↔ Disjoint a b := by
  rw [← himp_bot]; rw [le_himp_iff]; rw [disjoint_iff_inf_le]

@[to_dual hnot_le_iff_codisjoint_right]
/--
theorem `le_compl_iff_disjoint_left` / 定理 `le_compl_iff_disjoint_left`

English:
theorem le_compl_iff_disjoint_left
  statement: a <= bᶜ ↔ Disjoint b a
  proof: le_compl_iff_disjoint_right.trans disjoint_comm

@[to_dual hnot_le_comm]

中文:
定理 le_compl_iff_disjoint_left
  结论: a <= bᶜ ↔ Disjoint b a
  证明: le_compl_iff_disjoint_right.trans disjoint_comm

@[to_dual hnot_le_comm]

Depends on / 依赖: disjoint_comm, le_compl_iff_disjoint_right, le_compl_iff_disjoint_right.trans
-/
theorem le_compl_iff_disjoint_left : a <= bᶜ ↔ Disjoint b a :=
  le_compl_iff_disjoint_right.trans disjoint_comm

@[to_dual hnot_le_comm]
/--
theorem `le_compl_comm` / 定理 `le_compl_comm`

English:
theorem le_compl_comm
  statement: a <= bᶜ ↔ b <= aᶜ
  proof: by
  rw [le_compl_iff_disjoint_right]; rw [le_compl_iff_disjoint_left]

@[to_dual hnot_le_left]
alias ⟨_, Disjoint.le_compl_right⟩ := le_compl_iff_disjoint_right

@[to_dual hnot_le_right]
alias ⟨_, Disjoint.le_compl_left⟩ := le_compl_iff_disjoint_left

@[to_dual hnot_le_iff_hnot_le]
alias le_compl_iff_le_compl := le_compl_comm

@[to_dual hnot_le_of_hnot_le]
alias ⟨le_compl_of_le_compl, _⟩ := le_compl_comm

@[to_dual]

中文:
定理 le_compl_comm
  结论: a <= bᶜ ↔ b <= aᶜ
  证明: by
  rw [le_compl_iff_disjoint_right]; rw [le_compl_iff_disjoint_left]

@[to_dual hnot_le_left]
alias ⟨_, Disjoint.le_compl_right⟩ := le_compl_iff_disjoint_right

@[to_dual hnot_le_right]
alias ⟨_, Disjoint.le_compl_left⟩ := le_compl_iff_disjoint_left

@[to_dual hnot_le_iff_hnot_le]
alias le_compl_iff_le_compl := le_compl_comm

@[to_dual hnot_le_of_hnot_le]
alias ⟨le_compl_of_le_compl, _⟩ := le_compl_comm

@[to_dual]

Depends on / 依赖: le_compl_iff_disjoint_left, le_compl_iff_disjoint_right
-/
theorem le_compl_comm : a <= bᶜ ↔ b <= aᶜ := by
  rw [le_compl_iff_disjoint_right]; rw [le_compl_iff_disjoint_left]

@[to_dual hnot_le_left]
alias ⟨_, Disjoint.le_compl_right⟩ := le_compl_iff_disjoint_right

@[to_dual hnot_le_right]
alias ⟨_, Disjoint.le_compl_left⟩ := le_compl_iff_disjoint_left

@[to_dual hnot_le_iff_hnot_le]
alias le_compl_iff_le_compl := le_compl_comm

@[to_dual hnot_le_of_hnot_le]
alias ⟨le_compl_of_le_compl, _⟩ := le_compl_comm

@[to_dual]
/--
theorem `disjoint_compl_left` / 定理 `disjoint_compl_left`

English:
theorem disjoint_compl_left
  statement: Disjoint aᶜ a
  proof: disjoint_iff_inf_le.mpr le_himp_iff.1 (himp_bot _).ge

@[to_dual]

中文:
定理 disjoint_compl_left
  结论: Disjoint aᶜ a
  证明: disjoint_iff_inf_le.mpr le_himp_iff.1 (himp_bot _).ge

@[to_dual]

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, himp_bot, le_himp_iff
-/
theorem disjoint_compl_left : Disjoint aᶜ a :=
disjoint_iff_inf_le.mpr le_himp_iff.1 (himp_bot _).ge

@[to_dual]
/--
theorem `disjoint_compl_right` / 定理 `disjoint_compl_right`

English:
theorem disjoint_compl_right
  statement: Disjoint a aᶜ
  proof: disjoint_compl_left.symm

@[to_dual]

中文:
定理 disjoint_compl_right
  结论: Disjoint a aᶜ
  证明: disjoint_compl_left.symm

@[to_dual]

Depends on / 依赖: disjoint_compl_left, disjoint_compl_left.symm
-/
theorem disjoint_compl_right : Disjoint a aᶜ :=
  disjoint_compl_left.symm

@[to_dual]
/--
theorem `LE.le.disjoint_compl_left` / 定理 `LE.le.disjoint_compl_left`

English:
theorem LE.le.disjoint_compl_left
  given: (h : b <= a)
  statement: Disjoint aᶜ b
  proof: _root_.disjoint_compl_left.mono_right h

@[to_dual]

中文:
定理 LE.le.disjoint_compl_left
  条件: (h : b <= a)
  结论: Disjoint aᶜ b
  证明: _root_.disjoint_compl_left.mono_right h

@[to_dual]

Depends on / 依赖: _root_, _root_.disjoint_compl_left.mono_right, disjoint_compl_left, mono_right
-/
theorem LE.le.disjoint_compl_left (h : b <= a) : Disjoint aᶜ b :=
  _root_.disjoint_compl_left.mono_right h

@[to_dual]
/--
theorem `LE.le.disjoint_compl_right` / 定理 `LE.le.disjoint_compl_right`

English:
theorem LE.le.disjoint_compl_right
  given: (h : a <= b)
  statement: Disjoint a bᶜ
  proof: _root_.disjoint_compl_right.mono_left h

@[to_dual]

中文:
定理 LE.le.disjoint_compl_right
  条件: (h : a <= b)
  结论: Disjoint a bᶜ
  证明: _root_.disjoint_compl_right.mono_left h

@[to_dual]

Depends on / 依赖: _root_, _root_.disjoint_compl_right.mono_left, disjoint_compl_right, mono_left
-/
theorem LE.le.disjoint_compl_right (h : a <= b) : Disjoint a bᶜ :=
  _root_.disjoint_compl_right.mono_left h

@[to_dual]
/--
theorem `IsCompl.compl_eq` / 定理 `IsCompl.compl_eq`

English:
theorem IsCompl.compl_eq
  given: (h : IsCompl a b)
  statement: aᶜ = b
  proof: h.1.le_compl_left.antisymm' Disjoint.le_of_codisjoint disjoint_compl_left h.2

@[to_dual]

中文:
定理 是补集.compl_eq
  条件: (h : 是补集 a b)
  结论: aᶜ = b
  证明: h.1.le_compl_left.antisymm' Disjoint.le_of_codisjoint disjoint_compl_left h.2

@[to_dual]

Depends on / 依赖: Disjoint, Disjoint.le_of_codisjoint, antisymm, disjoint_compl_left, le_compl_left, le_compl_left.antisymm, le_of_codisjoint
-/
theorem IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b :=
h.1.le_compl_left.antisymm' Disjoint.le_of_codisjoint disjoint_compl_left h.2

@[to_dual]
/--
theorem `IsCompl.eq_compl` / 定理 `IsCompl.eq_compl`

English:
theorem IsCompl.eq_compl
  given: (h : IsCompl a b)
  statement: a = bᶜ
  proof: h.1.le_compl_right.antisymm Disjoint.le_of_codisjoint disjoint_compl_left h.2.symm

@[to_dual none]

中文:
定理 是补集.eq_compl
  条件: (h : 是补集 a b)
  结论: a = bᶜ
  证明: h.1.le_compl_right.antisymm Disjoint.le_of_codisjoint disjoint_compl_left h.2.symm

@[to_dual none]

Depends on / 依赖: Disjoint, Disjoint.le_of_codisjoint, antisymm, disjoint_compl_left, le_compl_right, le_compl_right.antisymm, le_of_codisjoint
-/
theorem IsCompl.eq_compl (h : IsCompl a b) : a = bᶜ :=
h.1.le_compl_right.antisymm Disjoint.le_of_codisjoint disjoint_compl_left h.2.symm

@[to_dual none]
/--
theorem `compl_unique` / 定理 `compl_unique`

English:
theorem compl_unique
  given: (h₀ : a ⊓ b = ⊥) (h₁ : a ⊔ b = ⊤)
  statement: aᶜ = b
  proof: (IsCompl.of_eq h₀ h₁).compl_eq

@[to_dual (attr := simp)]

中文:
定理 compl_unique
  条件: (h₀ : a ⊓ b = ⊥) (h₁ : a ⊔ b = ⊤)
  结论: aᶜ = b
  证明: (IsCompl.of_eq h₀ h₁).compl_eq

@[to_dual (attr := simp)]

Depends on / 依赖: IsCompl, IsCompl.of_eq, compl_eq, of_eq
-/
theorem compl_unique (h₀ : a ⊓ b = ⊥) (h₁ : a ⊔ b = ⊤) : aᶜ = b :=
  (IsCompl.of_eq h₀ h₁).compl_eq

@[to_dual (attr := simp)]
/--
theorem `inf_compl_self` / 定理 `inf_compl_self`

English:
theorem inf_compl_self
  given: (a : α)
  statement: a ⊓ aᶜ = ⊥
  proof: disjoint_compl_right.eq_bot

@[to_dual (attr := simp)]

中文:
定理 inf_compl_self
  条件: (a : α)
  结论: a ⊓ aᶜ = ⊥
  证明: disjoint_compl_right.eq_bot

@[to_dual (attr := simp)]

Depends on / 依赖: disjoint_compl_right, disjoint_compl_right.eq_bot, eq_bot
-/
theorem inf_compl_self (a : α) : a ⊓ aᶜ = ⊥ :=
  disjoint_compl_right.eq_bot

@[to_dual (attr := simp)]
/--
theorem `compl_inf_self` / 定理 `compl_inf_self`

English:
theorem compl_inf_self
  given: (a : α)
  statement: aᶜ ⊓ a = ⊥
  proof: disjoint_compl_left.eq_bot

@[to_dual]

中文:
定理 compl_inf_self
  条件: (a : α)
  结论: aᶜ ⊓ a = ⊥
  证明: disjoint_compl_left.eq_bot

@[to_dual]

Depends on / 依赖: disjoint_compl_left, disjoint_compl_left.eq_bot, eq_bot
-/
theorem compl_inf_self (a : α) : aᶜ ⊓ a = ⊥ :=
  disjoint_compl_left.eq_bot

@[to_dual]
/--
theorem `inf_compl_eq_bot` / 定理 `inf_compl_eq_bot`

English:
theorem inf_compl_eq_bot
  statement: a ⊓ aᶜ = ⊥
  proof: inf_compl_self _

@[to_dual]

中文:
定理 inf_compl_eq_bot
  结论: a ⊓ aᶜ = ⊥
  证明: inf_compl_self _

@[to_dual]

Depends on / 依赖: inf_compl_self
-/
theorem inf_compl_eq_bot : a ⊓ aᶜ = ⊥ :=
  inf_compl_self _

@[to_dual]
/--
theorem `compl_inf_eq_bot` / 定理 `compl_inf_eq_bot`

English:
theorem compl_inf_eq_bot
  statement: aᶜ ⊓ a = ⊥
  proof: compl_inf_self _

@[to_dual (attr := simp)]

中文:
定理 compl_inf_eq_bot
  结论: aᶜ ⊓ a = ⊥
  证明: compl_inf_self _

@[to_dual (attr := simp)]

Depends on / 依赖: compl_inf_self
-/
theorem compl_inf_eq_bot : aᶜ ⊓ a = ⊥ :=
  compl_inf_self _

@[to_dual (attr := simp)]
/--
theorem `compl_top` / 定理 `compl_top`

English:
theorem compl_top
  statement: (⊤ : α)ᶜ = ⊥
  proof: eq_of_forall_le_iff fun a => by rw [le_compl_iff_disjoint_right, disjoint_top, le_bot_iff]

@[to_dual (attr := simp)]

中文:
定理 compl_top
  结论: (⊤ : α)ᶜ = ⊥
  证明: eq_of_forall_le_iff fun a => by rw [le_compl_iff_disjoint_right, disjoint_top, le_bot_iff]

@[to_dual (attr := simp)]

Depends on / 依赖: disjoint_top, eq_of_forall_le_iff, le_bot_iff, le_compl_iff_disjoint_right
-/
theorem compl_top : (⊤ : α)ᶜ = ⊥ :=
  eq_of_forall_le_iff fun a => by rw [le_compl_iff_disjoint_right, disjoint_top, le_bot_iff]

@[to_dual (attr := simp)]
/--
theorem `compl_bot` / 定理 `compl_bot`

English:
theorem compl_bot
  statement: (⊥ : α)ᶜ = ⊤
  proof: by rw [← himp_bot, himp_self]

@[to_dual (attr := simp)]

中文:
定理 compl_bot
  结论: (⊥ : α)ᶜ = ⊤
  证明: by rw [← himp_bot, himp_self]

@[to_dual (attr := simp)]

Depends on / 依赖: himp_bot, himp_self
-/
theorem compl_bot : (⊥ : α)ᶜ = ⊤ := by rw [← himp_bot, himp_self]

@[to_dual (attr := simp)]
/--
theorem `le_compl_self` / 定理 `le_compl_self`

English:
theorem le_compl_self
  statement: a <= aᶜ ↔ a = ⊥
  proof: by
  rw [le_compl_iff_disjoint_left]; rw [disjoint_self]

@[to_dual (attr := simp)]

中文:
定理 le_compl_self
  结论: a <= aᶜ ↔ a = ⊥
  证明: by
  rw [le_compl_iff_disjoint_left]; rw [disjoint_self]

@[to_dual (attr := simp)]

Depends on / 依赖: disjoint_self, le_compl_iff_disjoint_left
-/
theorem le_compl_self : a <= aᶜ ↔ a = ⊥ := by
  rw [le_compl_iff_disjoint_left]; rw [disjoint_self]

@[to_dual (attr := simp)]
/--
theorem `ne_compl_self` / 定理 `ne_compl_self`

English:
theorem ne_compl_self
  given: [Nontrivial α]
  statement: a != aᶜ
  proof: by
  intro h
  cases le_compl_self.1 (le_of_eq h)
  simp at h

@[to_dual (attr := simp)]

中文:
定理 ne_compl_self
  条件: [非平凡 α]
  结论: a != aᶜ
  证明: by
  intro h
  cases le_compl_self.1 (le_of_eq h)
  simp at h

@[to_dual (attr := simp)]

Depends on / 依赖: le_compl_self, le_of_eq
-/
theorem ne_compl_self [Nontrivial α] : a != aᶜ := by
  intro h
  cases le_compl_self.1 (le_of_eq h)
  simp at h

@[to_dual (attr := simp)]
/--
theorem `compl_ne_self` / 定理 `compl_ne_self`

English:
theorem compl_ne_self
  given: [Nontrivial α]
  statement: aᶜ != a
  proof: ne_comm.1 ne_compl_self

@[to_dual (attr := simp)]

中文:
定理 compl_ne_self
  条件: [非平凡 α]
  结论: aᶜ != a
  证明: ne_comm.1 ne_compl_self

@[to_dual (attr := simp)]

Depends on / 依赖: ne_comm, ne_compl_self
-/
theorem compl_ne_self [Nontrivial α] : aᶜ != a :=
  ne_comm.1 ne_compl_self

@[to_dual (attr := simp)]
/--
theorem `lt_compl_self` / 定理 `lt_compl_self`

English:
theorem lt_compl_self
  given: [Nontrivial α]
  statement: a < aᶜ ↔ a = ⊥
  proof: by
  rw [lt_iff_le_and_ne]; simp

@[to_dual hnot_hnot_le]

中文:
定理 lt_compl_self
  条件: [非平凡 α]
  结论: a < aᶜ ↔ a = ⊥
  证明: by
  rw [lt_iff_le_and_ne]; simp

@[to_dual hnot_hnot_le]

Depends on / 依赖: lt_iff_le_and_ne
-/
theorem lt_compl_self [Nontrivial α] : a < aᶜ ↔ a = ⊥ := by
  rw [lt_iff_le_and_ne]; simp

@[to_dual hnot_hnot_le]
/--
theorem `le_compl_compl` / 定理 `le_compl_compl`

English:
theorem le_compl_compl
  statement: a <= aᶜᶜ
  proof: disjoint_compl_right.le_compl_right

@[to_dual]

中文:
定理 le_compl_compl
  结论: a <= aᶜᶜ
  证明: disjoint_compl_right.le_compl_right

@[to_dual]

Depends on / 依赖: disjoint_compl_right, disjoint_compl_right.le_compl_right, le_compl_right
-/
theorem le_compl_compl : a <= aᶜᶜ :=
  disjoint_compl_right.le_compl_right

@[to_dual]
/--
theorem `compl_anti` / 定理 `compl_anti`

English:
theorem compl_anti
  statement: Antitone (compl : α -> α)
  proof: fun _ _ h =>
le_compl_comm.1 h.trans le_compl_compl

@[to_dual (attr := gcongr)]

中文:
定理 compl_anti
  结论: 递减 (compl : α -> α)
  证明: fun _ _ h =>
le_compl_comm.1 h.trans le_compl_compl

@[to_dual (attr := gcongr)]
-/
theorem compl_anti : Antitone (compl : α -> α) := fun _ _ h =>
le_compl_comm.1 h.trans le_compl_compl

@[to_dual (attr := gcongr)]
/--
theorem `compl_le_compl` / 定理 `compl_le_compl`

English:
theorem compl_le_compl
  given: (h : a <= b)
  statement: bᶜ <= aᶜ
  proof: compl_anti h

@[to_dual (attr := simp)]

中文:
定理 compl_le_compl
  条件: (h : a <= b)
  结论: bᶜ <= aᶜ
  证明: compl_anti h

@[to_dual (attr := simp)]

Depends on / 依赖: compl_anti
-/
theorem compl_le_compl (h : a <= b) : bᶜ <= aᶜ :=
  compl_anti h

@[to_dual (attr := simp)]
/--
theorem `compl_compl_compl` / 定理 `compl_compl_compl`

English:
theorem compl_compl_compl
  given: (a : α)
  statement: aᶜᶜᶜ = aᶜ
  proof: (compl_anti le_compl_compl).antisymm le_compl_compl

@[to_dual (attr := simp)]

中文:
定理 compl_compl_compl
  条件: (a : α)
  结论: aᶜᶜᶜ = aᶜ
  证明: (compl_anti le_compl_compl).antisymm le_compl_compl

@[to_dual (attr := simp)]

Depends on / 依赖: antisymm, compl_anti, le_compl_compl
-/
theorem compl_compl_compl (a : α) : aᶜᶜᶜ = aᶜ :=
  (compl_anti le_compl_compl).antisymm le_compl_compl

@[to_dual (attr := simp)]
/--
theorem `disjoint_compl_compl_left_iff` / 定理 `disjoint_compl_compl_left_iff`

English:
theorem disjoint_compl_compl_left_iff
  statement: Disjoint aᶜᶜ b ↔ Disjoint a b
  proof: by
  simp_rw [← le_compl_iff_disjoint_left, compl_compl_compl]

@[to_dual (attr := simp)]

中文:
定理 disjoint_compl_compl_left_iff
  结论: Disjoint aᶜᶜ b ↔ Disjoint a b
  证明: by
  simp_rw [← le_compl_iff_disjoint_left, compl_compl_compl]

@[to_dual (attr := simp)]

Depends on / 依赖: compl_compl_compl, le_compl_iff_disjoint_left, simp_rw
-/
theorem disjoint_compl_compl_left_iff : Disjoint aᶜᶜ b ↔ Disjoint a b := by
  simp_rw [← le_compl_iff_disjoint_left, compl_compl_compl]

@[to_dual (attr := simp)]
/--
theorem `disjoint_compl_compl_right_iff` / 定理 `disjoint_compl_compl_right_iff`

English:
theorem disjoint_compl_compl_right_iff
  statement: Disjoint a bᶜᶜ ↔ Disjoint a b
  proof: by
  simp_rw [← le_compl_iff_disjoint_right, compl_compl_compl]

@[to_dual le_hnot_inf_hnot]

中文:
定理 disjoint_compl_compl_right_iff
  结论: Disjoint a bᶜᶜ ↔ Disjoint a b
  证明: by
  simp_rw [← le_compl_iff_disjoint_right, compl_compl_compl]

@[to_dual le_hnot_inf_hnot]

Depends on / 依赖: compl_compl_compl, le_compl_iff_disjoint_right, simp_rw
-/
theorem disjoint_compl_compl_right_iff : Disjoint a bᶜᶜ ↔ Disjoint a b := by
  simp_rw [← le_compl_iff_disjoint_right, compl_compl_compl]

@[to_dual le_hnot_inf_hnot]
/--
theorem `compl_sup_compl_le` / 定理 `compl_sup_compl_le`

English:
theorem compl_sup_compl_le
  statement: aᶜ ⊔ bᶜ <= (a ⊓ b)ᶜ
  proof: sup_le (compl_anti inf_le_left) compl_anti inf_le_right

@[to_dual]

中文:
定理 compl_sup_compl_le
  结论: aᶜ ⊔ bᶜ <= (a ⊓ b)ᶜ
  证明: sup_le (compl_anti inf_le_left) compl_anti inf_le_right

@[to_dual]

Depends on / 依赖: compl_anti, inf_le_left, inf_le_right, sup_le
-/
theorem compl_sup_compl_le : aᶜ ⊔ bᶜ <= (a ⊓ b)ᶜ :=
sup_le (compl_anti inf_le_left) compl_anti inf_le_right

@[to_dual]
/--
theorem `compl_compl_inf_distrib` / 定理 `compl_compl_inf_distrib`

English:
theorem compl_compl_inf_distrib
  given: (a b : α)
  statement: (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ
  proof: by
  refine ((compl_anti compl_sup_compl_le).trans (compl_sup_distrib _ _).le).antisymm ?_
  rw [le_compl_iff_disjoint_right]; rw [disjoint_assoc]; rw [disjoint_compl_compl_left_iff]; rw [disjoint_left_comm]; rw [disjoint_compl_compl_left_iff]; rw [← disjoint_assoc]; rw [inf_comm]
  exact disjoint_compl_right

@[to_dual]

中文:
定理 compl_compl_inf_distrib
  条件: (a b : α)
  结论: (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ
  证明: by
  refine ((compl_anti compl_sup_compl_le).trans (compl_sup_distrib _ _).le).antisymm ?_
  rw [le_compl_iff_disjoint_right]; rw [disjoint_assoc]; rw [disjoint_compl_compl_left_iff]; rw [disjoint_left_comm]; rw [disjoint_compl_compl_left_iff]; rw [← disjoint_assoc]; rw [inf_comm]
  exact disjoint_compl_right

@[to_dual]

Depends on / 依赖: antisymm, compl_anti, compl_sup_compl_le, compl_sup_distrib, disjoint_assoc, disjoint_compl_compl_left_iff, disjoint_compl_right, disjoint_left_comm, inf_comm, le_compl_iff_disjoint_right
-/
theorem compl_compl_inf_distrib (a b : α) : (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ := by
  refine ((compl_anti compl_sup_compl_le).trans (compl_sup_distrib _ _).le).antisymm ?_
  rw [le_compl_iff_disjoint_right]; rw [disjoint_assoc]; rw [disjoint_compl_compl_left_iff]; rw [disjoint_left_comm]; rw [disjoint_compl_compl_left_iff]; rw [← disjoint_assoc]; rw [inf_comm]
  exact disjoint_compl_right

@[to_dual]
/--
theorem `compl_compl_himp_distrib` / 定理 `compl_compl_himp_distrib`

English:
theorem compl_compl_himp_distrib
  given: (a b : α)
  statement: (a ⇨ b)ᶜᶜ = aᶜᶜ ⇨ bᶜᶜ
  proof: by
  apply le_antisymm
  · rw [le_himp_iff, ← compl_compl_inf_distrib]
    exact compl_anti (compl_anti himp_inf_le)
  · refine le_compl_comm.1 ((compl_anti compl_sup_le_himp).trans ?_)
    rw [compl_sup_distrib]; rw [le_compl_iff_disjoint_right]; rw [disjoint_right_comm]; rw [←
      le_compl_iff_disjoint_right]
    exact inf_himp_le

中文:
定理 compl_compl_himp_distrib
  条件: (a b : α)
  结论: (a ⇨ b)ᶜᶜ = aᶜᶜ ⇨ bᶜᶜ
  证明: by
  apply le_antisymm
  · rw [le_himp_iff, ← compl_compl_inf_distrib]
    exact compl_anti (compl_anti himp_inf_le)
  · refine le_compl_comm.1 ((compl_anti compl_sup_le_himp).trans ?_)
    rw [compl_sup_distrib]; rw [le_compl_iff_disjoint_right]; rw [disjoint_right_comm]; rw [←
      le_compl_iff_disjoint_right]
    exact inf_himp_le

Depends on / 依赖: compl_anti, compl_compl_inf_distrib, compl_sup_distrib, compl_sup_le_himp, disjoint_right_comm, himp_inf_le, inf_himp_le, le_antisymm, le_compl_comm, le_compl_iff_disjoint_right, le_himp_iff
-/
theorem compl_compl_himp_distrib (a b : α) : (a ⇨ b)ᶜᶜ = aᶜᶜ ⇨ bᶜᶜ := by
  apply le_antisymm
  · rw [le_himp_iff, ← compl_compl_inf_distrib]
    exact compl_anti (compl_anti himp_inf_le)
  · refine le_compl_comm.1 ((compl_anti compl_sup_le_himp).trans ?_)
    rw [compl_sup_distrib]; rw [le_compl_iff_disjoint_right]; rw [disjoint_right_comm]; rw [←
      le_compl_iff_disjoint_right]
    exact inf_himp_le

/--
Instance `OrderDual.instCoheytingAlgebra` / 实例 `OrderDual.instCoheytingAlgebra`

English:
instance OrderDual.instCoheytingAlgebra
  signature: : CoheytingAlgebra αᵒᵈ where
  body: toDual ∘ compl ∘ ofDual
  sdiff a b := toDual (ofDual b ⇨ ofDual a)
  sdiff_le_iff a b c := by rw [sup_comm]; exact le_himp_iff
  top_sdiff := @himp_bot α _

@[to_dual existing]

中文:
实例 OrderDual.instCoheytingAlgebra
  签名: : 余heyting代数 αᵒᵈ where
  定义体: toDual ∘ compl ∘ ofDual
  sdiff a b := toDual (ofDual b ⇨ ofDual a)
  sdiff_le_iff a b c := by rw [sup_comm]; exact le_himp_iff
  top_sdiff := @himp_bot α _

@[to_dual existing]

Depends on / 依赖: ofDual, toDual
-/
instance OrderDual.instCoheytingAlgebra : CoheytingAlgebra αᵒᵈ where
  hnot := toDual ∘ compl ∘ ofDual
  sdiff a b := toDual (ofDual b ⇨ ofDual a)
  sdiff_le_iff a b c := by rw [sup_comm]; exact le_himp_iff
  top_sdiff := @himp_bot α _

@[to_dual existing]
/--
Instance `OrderDual.instHeytingAlgebra` / 实例 `OrderDual.instHeytingAlgebra`

English:
instance OrderDual.instHeytingAlgebra
  signature: {α : Type u_2} [CoheytingAlgebra α]
  body: toDual ∘ hnot ∘ ofDual
  himp a b := toDual (ofDual b \ ofDual a)
  le_himp_iff a b c := by rw [inf_comm]; exact sdiff_le_iff
  himp_bot := @top_sdiff' α _

@[to_dual (attr := simp)]

中文:
实例 OrderDual.instHeytingAlgebra
  签名: {α : 类型u_2} [余heyting代数 α]
  定义体: toDual ∘ hnot ∘ ofDual
  himp a b := toDual (ofDual b \ ofDual a)
  le_himp_iff a b c := by rw [inf_comm]; exact sdiff_le_iff
  himp_bot := @top_sdiff' α _

@[to_dual (attr := simp)]

Depends on / 依赖: ofDual, toDual
-/
instance OrderDual.instHeytingAlgebra {α : Type u_2} [CoheytingAlgebra α] : HeytingAlgebra αᵒᵈ where
  compl := toDual ∘ hnot ∘ ofDual
  himp a b := toDual (ofDual b \ ofDual a)
  le_himp_iff a b c := by rw [inf_comm]; exact sdiff_le_iff
  himp_bot := @top_sdiff' α _

@[to_dual (attr := simp)]
/--
theorem `ofDual_hnot` / 定理 `ofDual_hnot`

English:
theorem ofDual_hnot
  given: (a : αᵒᵈ)
  statement: ofDual (￢a) = (ofDual a)ᶜ
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 ofDual_hnot
  条件: (a : αᵒᵈ)
  结论: ofDual (￢a) = (ofDual a)ᶜ
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem ofDual_hnot (a : αᵒᵈ) : ofDual (￢a) = (ofDual a)ᶜ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `ofDual_sdiff` / 定理 `ofDual_sdiff`

English:
theorem ofDual_sdiff
  given: (a b : αᵒᵈ)
  statement: ofDual (a \ b) = ofDual b ⇨ ofDual a
  proof: rfl
@[to_dual (attr := simp)]

中文:
定理 ofDual_sdiff
  条件: (a b : αᵒᵈ)
  结论: ofDual (a \ b) = ofDual b ⇨ ofDual a
  证明: rfl
@[to_dual (attr := simp)]

Depends on / 依赖: to_dual
-/
theorem ofDual_sdiff (a b : αᵒᵈ) : ofDual (a \ b) = ofDual b ⇨ ofDual a :=
  rfl
@[to_dual (attr := simp)]
/--
theorem `toDual_compl` / 定理 `toDual_compl`

English:
theorem toDual_compl
  given: (a : α)
  statement: toDual aᶜ = ￢toDual a
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toDual_compl
  条件: (a : α)
  结论: toDual aᶜ = ￢toDual a
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toDual_compl (a : α) : toDual aᶜ = ￢toDual a :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `toDual_himp` / 定理 `toDual_himp`

English:
theorem toDual_himp
  given: (a b : α)
  statement: toDual (a ⇨ b) = toDual b \ toDual a
  proof: rfl

中文:
定理 toDual_himp
  条件: (a b : α)
  结论: toDual (a ⇨ b) = toDual b \ toDual a
  证明: rfl
-/
theorem toDual_himp (a b : α) : toDual (a ⇨ b) = toDual b \ toDual a :=
  rfl

/--
Instance `Prod.instHeytingAlgebra` / 实例 `Prod.instHeytingAlgebra`

English:
instance Prod.instHeytingAlgebra
  signature: [HeytingAlgebra β]
  body: Prod.ext_iff.2 ⟨himp_bot a.1, himp_bot a.2⟩

中文:
实例 积类型.instHeytingAlgebra
  签名: [Heyting代数 β]
  定义体: Prod.ext_iff.2 ⟨himp_bot a.1, himp_bot a.2⟩

Depends on / 依赖: Prod.ext_iff, ext_iff, himp_bot
-/
instance Prod.instHeytingAlgebra [HeytingAlgebra β] : HeytingAlgebra (α × β) where
    himp_bot a := Prod.ext_iff.2 ⟨himp_bot a.1, himp_bot a.2⟩

/--
Instance `Pi.instHeytingAlgebra` / 实例 `Pi.instHeytingAlgebra`

English:
instance Pi.instHeytingAlgebra
  signature: {α : ι -> Type*} [forall i, HeytingAlgebra (α i)]
  body: funext fun i => himp_bot (f i)

中文:
实例 依赖函数类型.instHeytingAlgebra
  签名: {α : ι -> 类型} [对任意 i, Heyting代数 (α i)]
  定义体: funext fun i => himp_bot (f i)

Depends on / 依赖: himp_bot
-/
instance Pi.instHeytingAlgebra {α : ι -> Type*} [forall i, HeytingAlgebra (α i)] :
    HeytingAlgebra (forall i, α i) where
  himp_bot f := funext fun i => himp_bot (f i)

end HeytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] {a b : α}

@[to_dual existing]
/--
Instance `Prod.instCoheytingAlgebra` / 实例 `Prod.instCoheytingAlgebra`

English:
instance Prod.instCoheytingAlgebra
  signature: [CoheytingAlgebra β]
  body: and_congr sdiff_le_iff sdiff_le_iff
  top_sdiff a := Prod.ext_iff.2 ⟨top_sdiff' a.1, top_sdiff' a.2⟩

@[to_dual existing]

中文:
实例 积类型.instCoheytingAlgebra
  签名: [余heyting代数 β]
  定义体: and_congr sdiff_le_iff sdiff_le_iff
  top_sdiff a := Prod.ext_iff.2 ⟨top_sdiff' a.1, top_sdiff' a.2⟩

@[to_dual existing]

Depends on / 依赖: and_congr, sdiff_le_iff
-/
instance Prod.instCoheytingAlgebra [CoheytingAlgebra β] : CoheytingAlgebra (α × β) where
  sdiff_le_iff _ _ _ := and_congr sdiff_le_iff sdiff_le_iff
  top_sdiff a := Prod.ext_iff.2 ⟨top_sdiff' a.1, top_sdiff' a.2⟩

@[to_dual existing]
/--
Instance `Pi.instCoheytingAlgebra` / 实例 `Pi.instCoheytingAlgebra`

English:
instance Pi.instCoheytingAlgebra
  signature: {α : ι -> Type*} [forall i, CoheytingAlgebra (α i)]
  body: funext fun i => top_sdiff' (f i)

中文:
实例 依赖函数类型.instCoheytingAlgebra
  签名: {α : ι -> 类型} [对任意 i, 余heyting代数 (α i)]
  定义体: funext fun i => top_sdiff' (f i)

Depends on / 依赖: top_sdiff
-/
instance Pi.instCoheytingAlgebra {α : ι -> Type*} [forall i, CoheytingAlgebra (α i)] :
    CoheytingAlgebra (forall i, α i) where
  top_sdiff f := funext fun i => top_sdiff' (f i)

end CoheytingAlgebra

section BiheytingAlgebra

variable [BiheytingAlgebra α] {a : α}

/--
theorem `compl_le_hnot` / 定理 `compl_le_hnot`

English:
theorem compl_le_hnot
  statement: aᶜ <= ￢a
  proof: (disjoint_compl_left : Disjoint _ a).le_of_codisjoint codisjoint_hnot_right

中文:
定理 compl_le_hnot
  结论: aᶜ <= ￢a
  证明: (disjoint_compl_left : Disjoint _ a).le_of_codisjoint codisjoint_hnot_right

Depends on / 依赖: Disjoint, codisjoint_hnot_right, disjoint_compl_left, le_of_codisjoint
-/
theorem compl_le_hnot : aᶜ <= ￢a :=
  (disjoint_compl_left : Disjoint _ a).le_of_codisjoint codisjoint_hnot_right

end BiheytingAlgebra

/--
Instance `Prop.instHeytingAlgebra` / 实例 `Prop.instHeytingAlgebra`

English:
instance Prop.instHeytingAlgebra
  signature: : HeytingAlgebra Prop
  body: { Prop.instDistribLattice, Prop.instBoundedOrder with
    himp := (· -> ·),
    le_himp_iff := fun _ _ _ => and_imp.symm, himp_bot := fun _ => rfl }

@[simp]

中文:
实例 命题.instHeytingAlgebra
  签名: : Heyting代数 命题
  定义体: { Prop.instDistribLattice, Prop.instBoundedOrder with
    himp := (· -> ·),
    le_himp_iff := fun _ _ _ => and_imp.symm, himp_bot := fun _ => rfl }

@[simp]

Depends on / 依赖: Prop.instBoundedOrder, Prop.instDistribLattice, and_imp, and_imp.symm, himp_bot, instBoundedOrder, instDistribLattice, le_himp_iff
-/
instance Prop.instHeytingAlgebra : HeytingAlgebra Prop :=
  { Prop.instDistribLattice, Prop.instBoundedOrder with
    himp := (· -> ·),
    le_himp_iff := fun _ _ _ => and_imp.symm, himp_bot := fun _ => rfl }

@[simp]
/--
theorem `himp_iff_imp` / 定理 `himp_iff_imp`

English:
theorem himp_iff_imp
  given: (p q : Prop)
  statement: p ⇨ q ↔ p -> q
  proof: Iff.rfl

@[simp]

中文:
定理 himp_iff_imp
  条件: (p q : 命题)
  结论: p ⇨ q ↔ p -> q
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem himp_iff_imp (p q : Prop) : p ⇨ q ↔ p -> q :=
  Iff.rfl

@[simp]
/--
theorem `compl_iff_not` / 定理 `compl_iff_not`

English:
theorem compl_iff_not
  given: (p : Prop)
  statement: pᶜ ↔ ¬p
  proof: Iff.rfl

中文:
定理 compl_iff_not
  条件: (p : 命题)
  结论: pᶜ ↔ ¬p
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem compl_iff_not (p : Prop) : pᶜ ↔ ¬p :=
  Iff.rfl

variable (α) in
-- See note [reducible non-instances]
/--
Definition of `LinearOrder.toBiheytingAlgebra` / `LinearOrder.toBiheytingAlgebra` 的定义

English:
abbreviation LinearOrder.toBiheytingAlgebra
  signature: [LinearOrder α] [BoundedOrder α]
  body: { LinearOrder.toLattice, ‹BoundedOrder α› with
    himp := fun a b => if a <= b then ⊤ else b,
    compl := fun a => if a = ⊥ then ⊤ else ⊥,
    le_himp_iff := fun a b c => by
      split_ifs with h
      · exact iff_of_true le_top (inf_le_of_right_le h)
      · rw [inf_le_iff, or_iff_left h],
    himp_bot := fun _ => if_congr le_bot_iff rfl rfl, sdiff := fun a b => if a <= b then ⊥ else a,
    hnot := fun a => if a = ⊤ then ⊥ else ⊤,
    sdiff_le_iff := fun a b c => by
      split_ifs with h
      · exact iff_of_true bot_le (le_sup_of_le_left h)
      · rw [le_sup_iff, or_iff_right h],
    top_sdiff := fun _ => if_congr top_le_iff rfl rfl }

中文:
缩写 线性序.toBiheytingAlgebra
  签名: [线性序 α] [有界序 α]
  定义体: { LinearOrder.toLattice, ‹BoundedOrder α› with
    himp := fun a b => if a <= b then ⊤ else b,
    compl := fun a => if a = ⊥ then ⊤ else ⊥,
    le_himp_iff := fun a b c => by
      split_ifs with h
      · exact iff_of_true le_top (inf_le_of_right_le h)
      · rw [inf_le_iff, or_iff_left h],
    himp_bot := fun _ => if_congr le_bot_iff rfl rfl, sdiff := fun a b => if a <= b then ⊥ else a,
    hnot := fun a => if a = ⊤ then ⊥ else ⊤,
    sdiff_le_iff := fun a b c => by
      split_ifs with h
      · exact iff_of_true bot_le (le_sup_of_le_left h)
      · rw [le_sup_iff, or_iff_right h],
    top_sdiff := fun _ => if_congr top_le_iff rfl rfl }

Depends on / 依赖: BoundedOrder, LinearOrder, LinearOrder.toLattice, bot_le, himp_bot, if_congr, iff_of_true, inf_le_iff, inf_le_of_right_le, le_bot_iff, le_himp_iff, le_sup_of_le_left, le_top, or_iff_left, sdiff_le_iff, split_ifs, toLattice
-/
abbrev LinearOrder.toBiheytingAlgebra [LinearOrder α] [BoundedOrder α] : BiheytingAlgebra α :=
  { LinearOrder.toLattice, ‹BoundedOrder α› with
    himp := fun a b => if a <= b then ⊤ else b,
    compl := fun a => if a = ⊥ then ⊤ else ⊥,
    le_himp_iff := fun a b c => by
      split_ifs with h
      · exact iff_of_true le_top (inf_le_of_right_le h)
      · rw [inf_le_iff, or_iff_left h],
    himp_bot := fun _ => if_congr le_bot_iff rfl rfl, sdiff := fun a b => if a <= b then ⊥ else a,
    hnot := fun a => if a = ⊤ then ⊥ else ⊤,
    sdiff_le_iff := fun a b c => by
      split_ifs with h
      · exact iff_of_true bot_le (le_sup_of_le_left h)
      · rw [le_sup_iff, or_iff_right h],
    top_sdiff := fun _ => if_congr top_le_iff rfl rfl }

/--
Instance `OrderDual.instBiheytingAlgebra` / 实例 `OrderDual.instBiheytingAlgebra`

English:
instance OrderDual.instBiheytingAlgebra
  signature: [BiheytingAlgebra α]
  body: instHeytingAlgebra
  __ := instCoheytingAlgebra

中文:
实例 OrderDual.instBiheytingAlgebra
  签名: [Biheyting代数 α]
  定义体: instHeytingAlgebra
  __ := instCoheytingAlgebra

Depends on / 依赖: instHeytingAlgebra
-/
instance OrderDual.instBiheytingAlgebra [BiheytingAlgebra α] : BiheytingAlgebra αᵒᵈ where
  __ := instHeytingAlgebra
  __ := instCoheytingAlgebra

/--
Instance `Prod.instBiheytingAlgebra` / 实例 `Prod.instBiheytingAlgebra`

English:
instance Prod.instBiheytingAlgebra
  signature: [BiheytingAlgebra α] [BiheytingAlgebra β]
  body: instHeytingAlgebra
  __ := instCoheytingAlgebra

中文:
实例 积类型.instBiheytingAlgebra
  签名: [Biheyting代数 α] [Biheyting代数 β]
  定义体: instHeytingAlgebra
  __ := instCoheytingAlgebra

Depends on / 依赖: instHeytingAlgebra
-/
instance Prod.instBiheytingAlgebra [BiheytingAlgebra α] [BiheytingAlgebra β] :
    BiheytingAlgebra (α × β) where
  __ := instHeytingAlgebra
  __ := instCoheytingAlgebra

/--
Instance `Pi.instBiheytingAlgebra` / 实例 `Pi.instBiheytingAlgebra`

English:
instance Pi.instBiheytingAlgebra
  signature: {α : ι -> Type*} [forall i, BiheytingAlgebra (α i)]
  body: instHeytingAlgebra
  __ := instCoheytingAlgebra

中文:
实例 依赖函数类型.instBiheytingAlgebra
  签名: {α : ι -> 类型} [对任意 i, Biheyting代数 (α i)]
  定义体: instHeytingAlgebra
  __ := instCoheytingAlgebra

Depends on / 依赖: instHeytingAlgebra
-/
instance Pi.instBiheytingAlgebra {α : ι -> Type*} [forall i, BiheytingAlgebra (α i)] :
    BiheytingAlgebra (forall i, α i) where
  __ := instHeytingAlgebra
  __ := instCoheytingAlgebra

section lift

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.generalizedHeytingAlgebra` / `Function.Injective.generalizedHeytingAlgebra` 的定义

English:
abbreviation Function.Injective.generalizedHeytingAlgebra
  signature: [Max α] [Min α]
  body: hf.lattice f le lt map_sup map_inf
  le_top a := by
    rw [← le]; rw [map_top]
    exact le_top
  le_himp_iff a b c := by
    rw [← le]; rw [← le]; rw [map_himp]; rw [map_inf]; rw [le_himp_iff]

中文:
缩写 函数.单射.generalizedHeytingAlgebra
  签名: [最大值 α] [最小值 α]
  定义体: hf.lattice f le lt map_sup map_inf
  le_top a := by
    rw [← le]; rw [map_top]
    exact le_top
  le_himp_iff a b c := by
    rw [← le]; rw [← le]; rw [map_himp]; rw [map_inf]; rw [le_himp_iff]
-/
protected abbrev Function.Injective.generalizedHeytingAlgebra [Max α] [Min α]
    [LE α] [LT α] [Top α] [HImp α] [GeneralizedHeytingAlgebra β] (f : α -> β) (hf : Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_himp : forall a b, f (a ⇨ b) = f a ⇨ f b) :
    GeneralizedHeytingAlgebra α where
  __ := hf.lattice f le lt map_sup map_inf
  le_top a := by
    rw [← le]; rw [map_top]
    exact le_top
  le_himp_iff a b c := by
    rw [← le]; rw [← le]; rw [map_himp]; rw [map_inf]; rw [le_himp_iff]

-- See note [reducible non-instances]
/-- Pullback a `GeneralizedCoheytingAlgebra` along an injection. -/
@[to_dual existing (reorder := 3 4, le (x y), lt (x y), map_sup map_inf, map_sdiff (a b))]
/--
Definition of `Function.Injective.generalizedCoheytingAlgebra` / `Function.Injective.generalizedCoheytingAlgebra` 的定义

English:
abbreviation Function.Injective.generalizedCoheytingAlgebra
  signature: [Max α] [Min α]
  body: hf.lattice f le lt map_sup map_inf
  bot_le a := by
    rw [← le]; rw [map_bot]
    exact bot_le
  sdiff_le_iff a b c := by
    rw [← le]; rw [← le]; rw [map_sdiff]; rw [map_sup]; rw [sdiff_le_iff]

中文:
缩写 函数.单射.generalizedCoheytingAlgebra
  签名: [最大值 α] [最小值 α]
  定义体: hf.lattice f le lt map_sup map_inf
  bot_le a := by
    rw [← le]; rw [map_bot]
    exact bot_le
  sdiff_le_iff a b c := by
    rw [← le]; rw [← le]; rw [map_sdiff]; rw [map_sup]; rw [sdiff_le_iff]
-/
protected abbrev Function.Injective.generalizedCoheytingAlgebra [Max α] [Min α]
    [LE α] [LT α] [Bot α] [SDiff α] [GeneralizedCoheytingAlgebra β] (f : α -> β) (hf : Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_bot : f ⊥ = ⊥) (map_sdiff : forall a b, f (a \ b) = f a \ f b) :
    GeneralizedCoheytingAlgebra α where
  __ := hf.lattice f le lt map_sup map_inf
  bot_le a := by
    rw [← le]; rw [map_bot]
    exact bot_le
  sdiff_le_iff a b c := by
    rw [← le]; rw [← le]; rw [map_sdiff]; rw [map_sup]; rw [sdiff_le_iff]

-- See note [reducible non-instances]
/-- Pullback a `HeytingAlgebra` along an injection. -/
@[to_dual (reorder := le (x y), lt (x y), map_sup map_inf, map_top map_bot, map_himp (a b))
/-- Pullback a `CoheytingAlgebra` along an injection. -/]
/--
Definition of `Function.Injective.heytingAlgebra` / `Function.Injective.heytingAlgebra` 的定义

English:
abbreviation Function.Injective.heytingAlgebra
  signature: [Max α] [Min α] [LE α] [LT α] [Top α] [Bot α]
  body: hf.generalizedHeytingAlgebra f le lt map_sup map_inf map_top map_himp
  bot_le a := by
    rw [← le]; rw [map_bot]
    exact bot_le
himp_bot a := hf by rw [map_himp, map_compl, map_bot, himp_bot]

中文:
缩写 函数.单射.heytingAlgebra
  签名: [最大值 α] [最小值 α] [LE α] [LT α] [顶元素 α] [底元素 α]
  定义体: hf.generalizedHeytingAlgebra f le lt map_sup map_inf map_top map_himp
  bot_le a := by
    rw [← le]; rw [map_bot]
    exact bot_le
himp_bot a := hf by rw [map_himp, map_compl, map_bot, himp_bot]
-/
protected abbrev Function.Injective.heytingAlgebra [Max α] [Min α] [LE α] [LT α] [Top α] [Bot α]
    [Compl α] [HImp α] [HeytingAlgebra β] (f : α -> β) (hf : Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : forall a, f aᶜ = (f a)ᶜ)
    (map_himp : forall a b, f (a ⇨ b) = f a ⇨ f b) : HeytingAlgebra α where
  __ := hf.generalizedHeytingAlgebra f le lt map_sup map_inf map_top map_himp
  bot_le a := by
    rw [← le]; rw [map_bot]
    exact bot_le
himp_bot a := hf by rw [map_himp, map_compl, map_bot, himp_bot]

-- See note [reducible non-instances]
/-- Pullback a `BiheytingAlgebra` along an injection. -/
@[to_dual self (reorder := 3 4, 7 8, 9 10, 11 12, le (x y), lt (x y),
  map_sup map_inf, map_top map_bot, map_compl map_hnot, map_himp map_sdiff (a b))]
/--
Definition of `Function.Injective.biheytingAlgebra` / `Function.Injective.biheytingAlgebra` 的定义

English:
abbreviation Function.Injective.biheytingAlgebra
  signature: [Max α] [Min α] [LE α] [LT α] [Top α] [Bot α]
  body: hf.heytingAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_himp
  __ := hf.coheytingAlgebra f le lt map_sup map_inf map_top map_bot map_hnot map_sdiff

中文:
缩写 函数.单射.biheytingAlgebra
  签名: [最大值 α] [最小值 α] [LE α] [LT α] [顶元素 α] [底元素 α]
  定义体: hf.heytingAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_himp
  __ := hf.coheytingAlgebra f le lt map_sup map_inf map_top map_bot map_hnot map_sdiff
-/
protected abbrev Function.Injective.biheytingAlgebra [Max α] [Min α] [LE α] [LT α] [Top α] [Bot α]
    [Compl α] [HNot α] [HImp α] [SDiff α] [BiheytingAlgebra β] (f : α -> β) (hf : Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : forall a, f aᶜ = (f a)ᶜ) (map_hnot : forall a, f (￢a) = ￢f a)
    (map_himp : forall a b, f (a ⇨ b) = f a ⇨ f b) (map_sdiff : forall a b, f (a \ b) = f a \ f b) :
    BiheytingAlgebra α where
  __ := hf.heytingAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_himp
  __ := hf.coheytingAlgebra f le lt map_sup map_inf map_top map_bot map_hnot map_sdiff

namespace Equiv

variable (e : α ≃ β)

/--
Definition of `generalizedHeytingAlgebra` / `generalizedHeytingAlgebra` 的定义

English:
abbreviation generalizedHeytingAlgebra
  signature: [GeneralizedHeytingAlgebra β]
  body: by
  let lattice := e.lattice
  let top := e.top
  let himp := e.himp
  apply e.injective.generalizedHeytingAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _

中文:
缩写 generalizedHeytingAlgebra
  签名: [GeneralizedHeyting代数 β]
  定义体: by
  let lattice := e.lattice
  let top := e.top
  let himp := e.himp
  apply e.injective.generalizedHeytingAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _
-/
protected abbrev generalizedHeytingAlgebra [GeneralizedHeytingAlgebra β] :
    GeneralizedHeytingAlgebra α := by
  let lattice := e.lattice
  let top := e.top
  let himp := e.himp
  apply e.injective.generalizedHeytingAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _

/--
Definition of `generalizedCoheytingAlgebra` / `generalizedCoheytingAlgebra` 的定义

English:
abbreviation generalizedCoheytingAlgebra
  signature: [GeneralizedCoheytingAlgebra β]
  body: by
  let lattice := e.lattice
  let bot := e.bot
  let sdiff := e.sdiff
  apply e.injective.generalizedCoheytingAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _

中文:
缩写 generalizedCoheytingAlgebra
  签名: [GeneralizedCoheyting代数 β]
  定义体: by
  let lattice := e.lattice
  let bot := e.bot
  let sdiff := e.sdiff
  apply e.injective.generalizedCoheytingAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _
-/
protected abbrev generalizedCoheytingAlgebra [GeneralizedCoheytingAlgebra β] :
    GeneralizedCoheytingAlgebra α := by
  let lattice := e.lattice
  let bot := e.bot
  let sdiff := e.sdiff
  apply e.injective.generalizedCoheytingAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _

/--
Definition of `heytingAlgebra` / `heytingAlgebra` 的定义

English:
abbreviation heytingAlgebra
  signature: [HeytingAlgebra β]
  body: by
  let generalizedHeytingAlgebra := e.generalizedHeytingAlgebra
  let bot := e.bot
  let compl := e.compl
  apply e.injective.heytingAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 heytingAlgebra
  签名: [Heyting代数 β]
  定义体: by
  let generalizedHeytingAlgebra := e.generalizedHeytingAlgebra
  let bot := e.bot
  let compl := e.compl
  apply e.injective.heytingAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev heytingAlgebra [HeytingAlgebra β] : HeytingAlgebra α := by
  let generalizedHeytingAlgebra := e.generalizedHeytingAlgebra
  let bot := e.bot
  let compl := e.compl
  apply e.injective.heytingAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

/--
Definition of `coheytingAlgebra` / `coheytingAlgebra` 的定义

English:
abbreviation coheytingAlgebra
  signature: [CoheytingAlgebra β]
  body: by
  let generalizedCoheytingAlgebra := e.generalizedCoheytingAlgebra
  let top := e.top
  let hnot := e.hnot
  apply e.injective.coheytingAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 coheytingAlgebra
  签名: [余heyting代数 β]
  定义体: by
  let generalizedCoheytingAlgebra := e.generalizedCoheytingAlgebra
  let top := e.top
  let hnot := e.hnot
  apply e.injective.coheytingAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev coheytingAlgebra [CoheytingAlgebra β] : CoheytingAlgebra α := by
  let generalizedCoheytingAlgebra := e.generalizedCoheytingAlgebra
  let top := e.top
  let hnot := e.hnot
  apply e.injective.coheytingAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

/--
Definition of `biheytingAlgebra` / `biheytingAlgebra` 的定义

English:
abbreviation biheytingAlgebra
  signature: [BiheytingAlgebra β]
  body: by
  let heytingAlgebra := e.heytingAlgebra
  let coheytingAlgebra := e.coheytingAlgebra
  apply e.injective.biheytingAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 biheytingAlgebra
  签名: [Biheyting代数 β]
  定义体: by
  let heytingAlgebra := e.heytingAlgebra
  let coheytingAlgebra := e.coheytingAlgebra
  apply e.injective.biheytingAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev biheytingAlgebra [BiheytingAlgebra β] : BiheytingAlgebra α := by
  let heytingAlgebra := e.heytingAlgebra
  let coheytingAlgebra := e.coheytingAlgebra
  apply e.injective.biheytingAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

end Equiv

end lift

namespace PUnit

variable (a b : PUnit.{u + 1})

/--
Instance `instBiheytingAlgebra` / 实例 `instBiheytingAlgebra`

English:
instance instBiheytingAlgebra
  signature: : BiheytingAlgebra PUnit.{u + 1}
  body: { PUnit.instLinearOrder.{u} with
    top := unit,
    bot := unit,
    sup := fun _ _ => unit,
    inf := fun _ _ => unit,
    compl := fun _ => unit,
    sdiff := fun _ _ => unit,
    hnot := fun _ => unit,
    himp := fun _ _ => unit,
    le_top := fun _ => trivial,
    le_sup_left := fun _ _ => trivial,
    le_sup_right := fun _ _ => trivial,
    sup_le := fun _ _ _ _ _ => trivial,
    inf_le_left := fun _ _ => trivial,
    inf_le_right := fun _ _ => trivial,
    le_inf := fun _ _ _ _ _ => trivial,
    bot_le := fun _ => trivial,
    le_himp_iff := fun _ _ _ => Iff.rfl,
    himp_bot := fun _ => rfl,
    top_sdiff := fun _ => rfl,
    sdiff_le_iff := fun _ _ _ => Iff.rfl }

@[to_dual (attr := simp)]

中文:
实例 instBiheytingAlgebra
  签名: : Biheyting代数 命题单元.{u + 1}
  定义体: { PUnit.instLinearOrder.{u} with
    top := unit,
    bot := unit,
    sup := fun _ _ => unit,
    inf := fun _ _ => unit,
    compl := fun _ => unit,
    sdiff := fun _ _ => unit,
    hnot := fun _ => unit,
    himp := fun _ _ => unit,
    le_top := fun _ => trivial,
    le_sup_left := fun _ _ => trivial,
    le_sup_right := fun _ _ => trivial,
    sup_le := fun _ _ _ _ _ => trivial,
    inf_le_left := fun _ _ => trivial,
    inf_le_right := fun _ _ => trivial,
    le_inf := fun _ _ _ _ _ => trivial,
    bot_le := fun _ => trivial,
    le_himp_iff := fun _ _ _ => Iff.rfl,
    himp_bot := fun _ => rfl,
    top_sdiff := fun _ => rfl,
    sdiff_le_iff := fun _ _ _ => Iff.rfl }

@[to_dual (attr := simp)]

Depends on / 依赖: PUnit.instLinearOrder, bot_le, inf_le_left, inf_le_right, instLinearOrder, le_himp_iff, le_inf, le_sup_left, le_sup_right, le_top, sup_le
-/
instance instBiheytingAlgebra : BiheytingAlgebra PUnit.{u + 1} :=
  { PUnit.instLinearOrder.{u} with
    top := unit,
    bot := unit,
    sup := fun _ _ => unit,
    inf := fun _ _ => unit,
    compl := fun _ => unit,
    sdiff := fun _ _ => unit,
    hnot := fun _ => unit,
    himp := fun _ _ => unit,
    le_top := fun _ => trivial,
    le_sup_left := fun _ _ => trivial,
    le_sup_right := fun _ _ => trivial,
    sup_le := fun _ _ _ _ _ => trivial,
    inf_le_left := fun _ _ => trivial,
    inf_le_right := fun _ _ => trivial,
    le_inf := fun _ _ _ _ _ => trivial,
    bot_le := fun _ => trivial,
    le_himp_iff := fun _ _ _ => Iff.rfl,
    himp_bot := fun _ => rfl,
    top_sdiff := fun _ => rfl,
    sdiff_le_iff := fun _ _ _ => Iff.rfl }

@[to_dual (attr := simp)]
/--
theorem `top_eq` / 定理 `top_eq`

English:
theorem top_eq
  statement: (⊤ : PUnit) = unit
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 top_eq
  结论: (⊤ : 命题单元) = unit
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem top_eq : (⊤ : PUnit) = unit :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `sup_eq` / 定理 `sup_eq`

English:
theorem sup_eq
  statement: a ⊔ b = unit
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 sup_eq
  结论: a ⊔ b = unit
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem sup_eq : a ⊔ b = unit :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `hnot_eq` / 定理 `hnot_eq`

English:
theorem hnot_eq
  statement: ￢a = unit
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 hnot_eq
  结论: ￢a = unit
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem hnot_eq : ￢a = unit :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `himp_eq` / 定理 `himp_eq`

English:
theorem himp_eq
  statement: a ⇨ b = unit
  proof: rfl

中文:
定理 himp_eq
  结论: a ⇨ b = unit
  证明: rfl
-/
theorem himp_eq : a ⇨ b = unit :=
  rfl

end PUnit
