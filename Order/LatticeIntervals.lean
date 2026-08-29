/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Order.Bounds.Basic

/-!
# Intervals in Lattices

In this file, we provide instances of lattice structures on intervals within lattices.
Some of them depend on the order of the endpoints of the interval, and thus are not made
global instances. These are probably not all of the lattice instances that could be placed on these
intervals, but more can be added easily along the same lines when needed.

## Main definitions

In the following, `*` can represent either `c`, `o`, or `i`.
  * `Set.Ic*.orderBot`
  * `Set.Ii*.semilatticeInf`
  * `Set.I*c.orderTop`
  * `Set.I*c.semilatticeInf`
  * `Set.I**.lattice`
  * `Set.Iic.boundedOrder`, within an `OrderBot`
  * `Set.Ici.boundedOrder`, within an `OrderTop`
-/

public section


variable {α : Type*}

namespace Set

namespace Ico

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: [SemilatticeInf α] {a b : α}
  body: Subtype.semilatticeInf fun _ _ hx hy => ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩

@[simp, norm_cast]

中文:
实例 semilatticeInf
  签名: [SemilatticeInf α] {a b : α}
  定义体: Subtype.semilatticeInf fun _ _ hx hy => ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩

@[simp, norm_cast]

Depends on / 依赖: Ideal.IsPrime.ne_top, IsPrime, IsSimpleOrder, IsSimpleOrder.eq_bot_or_eq_top, Subtype, Subtype.semilatticeInf, eq_bot_or_eq_top, inf_le_left, le_inf, lt_of_le_of_lt, ne_top, resolve_right, semilatticeInf
-/
instance semilatticeInf [SemilatticeInf α] {a b : α} : SemilatticeInf (Ico a b) :=
  Subtype.semilatticeInf fun _ _ hx hy => ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩

@[simp, norm_cast]
/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: [SemilatticeInf α] {a b : α} {x y : Ico a b}
  proof: rfl

中文:
引理 coe_inf
  条件: [SemilatticeInf α] {a b : α} {x y : 左闭右开区间 a b}
  证明: rfl
-/
protected lemma coe_inf [SemilatticeInf α] {a b : α} {x y : Ico a b} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: [PartialOrder α] {a b : α} [Fact (a < b)]
  body: (isLeast_Ico Fact.out).orderBot

@[simp, norm_cast]

中文:
实例 orderBot
  签名: [偏序 α] {a b : α} [Fact (a < b)]
  定义体: (isLeast_Ico Fact.out).orderBot

@[simp, norm_cast]

Depends on / 依赖: Fact.out, isLeast_Ico, orderBot
-/
instance orderBot [PartialOrder α] {a b : α} [Fact (a < b)] : OrderBot (Ico a b) :=
  (isLeast_Ico Fact.out).orderBot

@[simp, norm_cast]
/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  given: [PartialOrder α] (a b : α) [Fact (a < b)]
  statement: ↑(⊥ : Ico a b) = a
  proof: rfl

中文:
引理 coe_bot
  条件: [偏序 α] (a b : α) [Fact (a < b)]
  结论: ↑(⊥ : 左闭右开区间 a b) = a
  证明: rfl
-/
protected lemma coe_bot [PartialOrder α] (a b : α) [Fact (a < b)] : ↑(⊥ : Ico a b) = a := rfl

/--
lemma `disjoint_iff` / 引理 `disjoint_iff`

English:
lemma disjoint_iff
  given: [SemilatticeInf α] {a b : α} [Fact (a < b)] {x y : Ico a b}
  proof: by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

中文:
引理 disjoint_iff
  条件: [SemilatticeInf α] {a b : α} [Fact (a < b)] {x y : 左闭右开区间 a b}
  证明: by
  simp [_root_.disjoint_iff, Subtype.ext_iff]
-/
protected lemma disjoint_iff [SemilatticeInf α] {a b : α} [Fact (a < b)] {x y : Ico a b} :
    Disjoint x y ↔ ↑x ⊓ ↑y = a := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

end Ico

namespace Iio

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: [SemilatticeInf α] {a : α}
  body: Subtype.semilatticeInf fun _ _ hx _ => lt_of_le_of_lt inf_le_left hx

@[simp, norm_cast]

中文:
实例 semilatticeInf
  签名: [SemilatticeInf α] {a : α}
  定义体: Subtype.semilatticeInf fun _ _ hx _ => lt_of_le_of_lt inf_le_left hx

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.semilatticeInf, inf_le_left, lt_of_le_of_lt, semilatticeInf
-/
instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf (Iio a) :=
  Subtype.semilatticeInf fun _ _ hx _ => lt_of_le_of_lt inf_le_left hx

@[simp, norm_cast]
/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: [SemilatticeInf α] {a : α} {x y : Iio a}
  proof: rfl

中文:
引理 coe_inf
  条件: [SemilatticeInf α] {a : α} {x y : 左无界右开区间 a}
  证明: rfl
-/
protected lemma coe_inf [SemilatticeInf α] {a : α} {x y : Iio a} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

end Iio

namespace Ioc

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: [SemilatticeSup α] {a b : α}
  body: Subtype.semilatticeSup fun _ _ hx hy => ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩

@[simp, norm_cast]

中文:
实例 semilatticeSup
  签名: [SemilatticeSup α] {a b : α}
  定义体: Subtype.semilatticeSup fun _ _ hx hy => ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.semilatticeSup, le_sup_left, lt_of_lt_of_le, semilatticeSup, sup_le
-/
instance semilatticeSup [SemilatticeSup α] {a b : α} : SemilatticeSup (Ioc a b) :=
  Subtype.semilatticeSup fun _ _ hx hy => ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩

@[simp, norm_cast]
/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: [SemilatticeSup α] {a b : α} {x y : Ioc a b}
  proof: rfl

中文:
引理 coe_sup
  条件: [SemilatticeSup α] {a b : α} {x y : 左开右闭区间 a b}
  证明: rfl
-/
protected lemma coe_sup [SemilatticeSup α] {a b : α} {x y : Ioc a b} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

/--
Instance `orderTop` / 实例 `orderTop`

English:
instance orderTop
  signature: [PartialOrder α] {a b : α} [Fact (a < b)]
  body: (isGreatest_Ioc Fact.out).orderTop

@[simp, norm_cast]

中文:
实例 orderTop
  签名: [偏序 α] {a b : α} [Fact (a < b)]
  定义体: (isGreatest_Ioc Fact.out).orderTop

@[simp, norm_cast]

Depends on / 依赖: Fact.out, isGreatest_Ioc, orderTop
-/
instance orderTop [PartialOrder α] {a b : α} [Fact (a < b)] : OrderTop (Ioc a b) :=
  (isGreatest_Ioc Fact.out).orderTop

@[simp, norm_cast]
/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  given: [PartialOrder α] (a b : α) [Fact (a < b)]
  statement: ↑(⊤ : Ioc a b) = b
  proof: rfl

中文:
引理 coe_top
  条件: [偏序 α] (a b : α) [Fact (a < b)]
  结论: ↑(⊤ : 左开右闭区间 a b) = b
  证明: rfl
-/
protected lemma coe_top [PartialOrder α] (a b : α) [Fact (a < b)] : ↑(⊤ : Ioc a b) = b := rfl

/--
lemma `codisjoint_iff` / 引理 `codisjoint_iff`

English:
lemma codisjoint_iff
  given: [SemilatticeSup α] {a b : α} [Fact (a < b)] {x y : Ioc a b}
  proof: by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]

中文:
引理 codisjoint_iff
  条件: [SemilatticeSup α] {a b : α} [Fact (a < b)] {x y : 左开右闭区间 a b}
  证明: by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]
-/
protected lemma codisjoint_iff [SemilatticeSup α] {a b : α} [Fact (a < b)] {x y : Ioc a b} :
    Codisjoint x y ↔ ↑x ⊔ ↑y = b := by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]

end Ioc

namespace Ioi

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: [SemilatticeSup α] {a : α}
  body: Subtype.semilatticeSup fun _ _ hx _ => lt_of_lt_of_le hx le_sup_left

@[simp, norm_cast]

中文:
实例 semilatticeSup
  签名: [SemilatticeSup α] {a : α}
  定义体: Subtype.semilatticeSup fun _ _ hx _ => lt_of_lt_of_le hx le_sup_left

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.semilatticeSup, le_sup_left, lt_of_lt_of_le, semilatticeSup
-/
instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup (Ioi a) :=
  Subtype.semilatticeSup fun _ _ hx _ => lt_of_lt_of_le hx le_sup_left

@[simp, norm_cast]
/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: [SemilatticeSup α] {a : α} {x y : Ioi a}
  proof: rfl

中文:
引理 coe_sup
  条件: [SemilatticeSup α] {a : α} {x y : 左开右无界区间 a}
  证明: rfl
-/
protected lemma coe_sup [SemilatticeSup α] {a : α} {x y : Ioi a} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

end Ioi

namespace Iic

variable {a : α}

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: [SemilatticeInf α]
  body: Subtype.semilatticeInf fun _ _ hx _ => le_trans inf_le_left hx

@[simp, norm_cast]

中文:
实例 semilatticeInf
  签名: [SemilatticeInf α]
  定义体: Subtype.semilatticeInf fun _ _ hx _ => le_trans inf_le_left hx

@[simp, norm_cast]

Depends on / 依赖: Ideal.LiesOver.over, Ideal.isPrime_map_quotientMk_of_isPrime, Ideal.map_le_iff_le_comap, LiesOver, Subtype, Subtype.semilatticeInf, inf_le_left, isPrime_map_quotientMk_of_isPrime, le_trans, map_le_iff_le_comap, semilatticeInf
-/
instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (Iic a) :=
  Subtype.semilatticeInf fun _ _ hx _ => le_trans inf_le_left hx

@[simp, norm_cast]
/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: [SemilatticeInf α] {x y : Iic a}
  proof: rfl

中文:
引理 coe_inf
  条件: [SemilatticeInf α] {x y : 左无界右闭区间 a}
  证明: rfl
-/
protected lemma coe_inf [SemilatticeInf α] {x y : Iic a} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: [SemilatticeSup α]
  body: Subtype.semilatticeSup fun _ _ hx hy => sup_le hx hy

@[simp, norm_cast]

中文:
实例 semilatticeSup
  签名: [SemilatticeSup α]
  定义体: Subtype.semilatticeSup fun _ _ hx hy => sup_le hx hy

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.semilatticeSup, semilatticeSup, sup_le
-/
instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (Iic a) :=
  Subtype.semilatticeSup fun _ _ hx hy => sup_le hx hy

@[simp, norm_cast]
/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: [SemilatticeSup α] {x y : Iic a}
  proof: rfl

中文:
引理 coe_sup
  条件: [SemilatticeSup α] {x y : 左无界右闭区间 a}
  证明: rfl
-/
protected lemma coe_sup [SemilatticeSup α] {x y : Iic a} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Lattice
  signature: α] : Lattice (Iic a)
  body: { Iic.semilatticeInf, Iic.semilatticeSup with }

中文:
实例 [格
  签名: α] : 格 (左无界右闭区间 a)
  定义体: { Iic.semilatticeInf, Iic.semilatticeSup with }

Depends on / 依赖: Iic.semilatticeInf, Iic.semilatticeSup, semilatticeInf, semilatticeSup
-/
instance [Lattice α] : Lattice (Iic a) :=
  { Iic.semilatticeInf, Iic.semilatticeSup with }

/--
Instance `orderTop` / 实例 `orderTop`

English:
instance orderTop
  signature: [Preorder α]
  body: ⟨a, le_refl a⟩
  le_top x := x.prop

@[simp, norm_cast]

中文:
实例 orderTop
  签名: [预序 α]
  定义体: ⟨a, le_refl a⟩
  le_top x := x.prop

@[simp, norm_cast]

Depends on / 依赖: le_refl
-/
instance orderTop [Preorder α] :
    OrderTop (Iic a) where
  top := ⟨a, le_refl a⟩
  le_top x := x.prop

@[simp, norm_cast]
/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  given: [Preorder α] (a : α)
  statement: (⊤ : Iic a) = a
  proof: rfl

中文:
引理 coe_top
  条件: [预序 α] (a : α)
  结论: (⊤ : 左无界右闭区间 a) = a
  证明: rfl
-/
protected lemma coe_top [Preorder α] (a : α) : (⊤ : Iic a) = a := rfl

/--
lemma `eq_top_iff` / 引理 `eq_top_iff`

English:
lemma eq_top_iff
  given: [Preorder α] {x : Iic a}
  proof: by
  simp [Subtype.ext_iff]

中文:
引理 eq_top_iff
  条件: [预序 α] {x : 左无界右闭区间 a}
  证明: by
  simp [Subtype.ext_iff]
-/
protected lemma eq_top_iff [Preorder α] {x : Iic a} :
    x = ⊤ ↔ (x : α) = a := by
  simp [Subtype.ext_iff]

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: [Preorder α] [OrderBot α]
  body: ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

@[simp, norm_cast]

中文:
实例 orderBot
  签名: [预序 α] [有底序 α]
  定义体: ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

@[simp, norm_cast]

Depends on / 依赖: bot_le
-/
instance orderBot [Preorder α] [OrderBot α] :
    OrderBot (Iic a) where
  bot := ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

@[simp, norm_cast]
/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  given: [Preorder α] [OrderBot α] (a : α)
  statement: (⊥ : Iic a) = (⊥ : α)
  proof: rfl

中文:
引理 coe_bot
  条件: [预序 α] [有底序 α] (a : α)
  结论: (⊥ : 左无界右闭区间 a) = (⊥ : α)
  证明: rfl
-/
protected lemma coe_bot [Preorder α] [OrderBot α] (a : α) : (⊥ : Iic a) = (⊥ : α) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [OrderBot α] : BoundedOrder (Iic a)
  body: { Iic.orderTop, Iic.orderBot with }

中文:
实例 [预序
  签名: α] [有底序 α] : 有界序 (左无界右闭区间 a)
  定义体: { Iic.orderTop, Iic.orderBot with }

Depends on / 依赖: Iic.orderBot, Iic.orderTop, orderBot, orderTop
-/
instance [Preorder α] [OrderBot α] : BoundedOrder (Iic a) :=
  { Iic.orderTop, Iic.orderBot with }

/--
lemma `disjoint_iff` / 引理 `disjoint_iff`

English:
lemma disjoint_iff
  given: [SemilatticeInf α] [OrderBot α] {x y : Iic a}
  proof: by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

中文:
引理 disjoint_iff
  条件: [SemilatticeInf α] [有底序 α] {x y : 左无界右闭区间 a}
  证明: by
  simp [_root_.disjoint_iff, Subtype.ext_iff]
-/
protected lemma disjoint_iff [SemilatticeInf α] [OrderBot α] {x y : Iic a} :
    Disjoint x y ↔ Disjoint (x : α) (y : α) := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

/--
lemma `codisjoint_iff` / 引理 `codisjoint_iff`

English:
lemma codisjoint_iff
  given: [SemilatticeSup α] {x y : Iic a}
  proof: by
  simpa only [_root_.codisjoint_iff] using! Iic.eq_top_iff

中文:
引理 codisjoint_iff
  条件: [SemilatticeSup α] {x y : 左无界右闭区间 a}
  证明: by
  simpa only [_root_.codisjoint_iff] using! Iic.eq_top_iff
-/
protected lemma codisjoint_iff [SemilatticeSup α] {x y : Iic a} :
    Codisjoint x y ↔ ↑x ⊔ ↑y = a := by
  simpa only [_root_.codisjoint_iff] using! Iic.eq_top_iff

/--
lemma `isCompl_iff` / 引理 `isCompl_iff`

English:
lemma isCompl_iff
  given: [Lattice α] [OrderBot α] {x y : Iic a}
  proof: by
  rw [_root_.isCompl_iff]; rw [Iic.disjoint_iff]; rw [Iic.codisjoint_iff]

中文:
引理 isCompl_iff
  条件: [格 α] [有底序 α] {x y : 左无界右闭区间 a}
  证明: by
  rw [_root_.isCompl_iff]; rw [Iic.disjoint_iff]; rw [Iic.codisjoint_iff]
-/
protected lemma isCompl_iff [Lattice α] [OrderBot α] {x y : Iic a} :
    IsCompl x y ↔ Disjoint (x : α) (y : α) ∧ ↑x ⊔ ↑y = a := by
  rw [_root_.isCompl_iff]; rw [Iic.disjoint_iff]; rw [Iic.codisjoint_iff]

/--
lemma `complementedLattice_iff` / 引理 `complementedLattice_iff`

English:
lemma complementedLattice_iff
  given: [Lattice α] [OrderBot α]
  proof: by
  simp_rw [complementedLattice_iff, Iic.isCompl_iff, Subtype.forall, Subtype.exists, disjoint_iff,
    exists_prop, Set.mem_Iic]

中文:
引理 complementedLattice_iff
  条件: [格 α] [有底序 α]
  证明: by
  simp_rw [complementedLattice_iff, Iic.isCompl_iff, Subtype.forall, Subtype.exists, disjoint_iff,
    exists_prop, Set.mem_Iic]
-/
protected lemma complementedLattice_iff [Lattice α] [OrderBot α] :
    ComplementedLattice (Iic a) ↔ forall b, b <= a -> exists c <= a, b ⊓ c = ⊥ ∧ b ⊔ c = a := by
  simp_rw [complementedLattice_iff, Iic.isCompl_iff, Subtype.forall, Subtype.exists, disjoint_iff,
    exists_prop, Set.mem_Iic]

end Iic

namespace Ici

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: [SemilatticeInf α] {a : α}
  body: Subtype.semilatticeInf fun _ _ hx hy => le_inf hx hy

@[simp, norm_cast]

中文:
实例 semilatticeInf
  签名: [SemilatticeInf α] {a : α}
  定义体: Subtype.semilatticeInf fun _ _ hx hy => le_inf hx hy

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.semilatticeInf, le_inf, semilatticeInf
-/
instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf (Ici a) :=
  Subtype.semilatticeInf fun _ _ hx hy => le_inf hx hy

@[simp, norm_cast]
/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: [SemilatticeInf α] {a : α} {x y : Ici a}
  proof: rfl

中文:
引理 coe_inf
  条件: [SemilatticeInf α] {a : α} {x y : 左闭右无界区间 a}
  证明: rfl
-/
protected lemma coe_inf [SemilatticeInf α] {a : α} {x y : Ici a} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: [SemilatticeSup α] {a : α}
  body: Subtype.semilatticeSup fun _ _ hx _ => le_trans hx le_sup_left

@[simp, norm_cast]

中文:
实例 semilatticeSup
  签名: [SemilatticeSup α] {a : α}
  定义体: Subtype.semilatticeSup fun _ _ hx _ => le_trans hx le_sup_left

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.semilatticeSup, le_sup_left, le_trans, semilatticeSup
-/
instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup (Ici a) :=
  Subtype.semilatticeSup fun _ _ hx _ => le_trans hx le_sup_left

@[simp, norm_cast]
/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: [SemilatticeSup α] {a : α} {x y : Ici a}
  proof: rfl

中文:
引理 coe_sup
  条件: [SemilatticeSup α] {a : α} {x y : 左闭右无界区间 a}
  证明: rfl
-/
protected lemma coe_sup [SemilatticeSup α] {a : α} {x y : Ici a} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

/--
Instance `lattice` / 实例 `lattice`

English:
instance lattice
  signature: [Lattice α] {a : α}
  body: { Ici.semilatticeInf, Ici.semilatticeSup with }

中文:
实例 lattice
  签名: [格 α] {a : α}
  定义体: { Ici.semilatticeInf, Ici.semilatticeSup with }

Depends on / 依赖: Ici.semilatticeInf, Ici.semilatticeSup, semilatticeInf, semilatticeSup
-/
instance lattice [Lattice α] {a : α} : Lattice (Ici a) :=
  { Ici.semilatticeInf, Ici.semilatticeSup with }

/--
Instance `distribLattice` / 实例 `distribLattice`

English:
instance distribLattice
  signature: [DistribLattice α] {a : α}
  body: { Ici.lattice with le_sup_inf := fun _ _ _ => le_sup_inf }

中文:
实例 distribLattice
  签名: [Distrib格 α] {a : α}
  定义体: { Ici.lattice with le_sup_inf := fun _ _ _ => le_sup_inf }

Depends on / 依赖: Ici.lattice, lattice, le_sup_inf
-/
instance distribLattice [DistribLattice α] {a : α} : DistribLattice (Ici a) :=
  { Ici.lattice with le_sup_inf := fun _ _ _ => le_sup_inf }

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: [Preorder α] {a : α}
  body: ⟨a, le_refl a⟩
  bot_le x := x.prop

@[simp, norm_cast]

中文:
实例 orderBot
  签名: [预序 α] {a : α}
  定义体: ⟨a, le_refl a⟩
  bot_le x := x.prop

@[simp, norm_cast]

Depends on / 依赖: le_refl
-/
instance orderBot [Preorder α] {a : α} :
    OrderBot (Ici a) where
  bot := ⟨a, le_refl a⟩
  bot_le x := x.prop

@[simp, norm_cast]
/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  given: [Preorder α] (a : α)
  statement: ↑(⊥ : Ici a) = a
  proof: rfl

中文:
引理 coe_bot
  条件: [预序 α] (a : α)
  结论: ↑(⊥ : 左闭右无界区间 a) = a
  证明: rfl
-/
protected lemma coe_bot [Preorder α] (a : α) : ↑(⊥ : Ici a) = a := rfl

/--
Instance `orderTop` / 实例 `orderTop`

English:
instance orderTop
  signature: [Preorder α] [OrderTop α] {a : α}
  body: ⟨⊤, le_top⟩
  le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top

@[simp, norm_cast]

中文:
实例 orderTop
  签名: [预序 α] [有顶序 α] {a : α}
  定义体: ⟨⊤, le_top⟩
  le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top

@[simp, norm_cast]

Depends on / 依赖: le_top
-/
instance orderTop [Preorder α] [OrderTop α] {a : α} :
    OrderTop (Ici a) where
  top := ⟨⊤, le_top⟩
  le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top

@[simp, norm_cast]
/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  given: [Preorder α] [OrderTop α] (a : α)
  statement: ↑(⊤ : Ici a) = (⊤ : α)
  proof: rfl

中文:
引理 coe_top
  条件: [预序 α] [有顶序 α] (a : α)
  结论: ↑(⊤ : 左闭右无界区间 a) = (⊤ : α)
  证明: rfl
-/
protected lemma coe_top [Preorder α] [OrderTop α] (a : α) : ↑(⊤ : Ici a) = (⊤ : α) := rfl

/--
Instance `boundedOrder` / 实例 `boundedOrder`

English:
instance boundedOrder
  signature: [Preorder α] [OrderTop α] {a : α}
  body: { Ici.orderTop, Ici.orderBot with }

中文:
实例 boundedOrder
  签名: [预序 α] [有顶序 α] {a : α}
  定义体: { Ici.orderTop, Ici.orderBot with }

Depends on / 依赖: Ici.orderBot, Ici.orderTop, orderBot, orderTop
-/
instance boundedOrder [Preorder α] [OrderTop α] {a : α} : BoundedOrder (Ici a) :=
  { Ici.orderTop, Ici.orderBot with }

/--
lemma `disjoint_iff` / 引理 `disjoint_iff`

English:
lemma disjoint_iff
  given: [SemilatticeInf α] {a : α} {x y : Ici a}
  proof: by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

中文:
引理 disjoint_iff
  条件: [SemilatticeInf α] {a : α} {x y : 左闭右无界区间 a}
  证明: by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

Depends on / 依赖: Ideal.smul_mem_pointwise_smul_iff, Subgroup, Subgroup.inv_mem, Subgroup.normal_subgroupOf_iff, Submodule, Submodule.mem_toAddSubgroup, inertia_le_stabilizer, inv_mem, inv_mul_cancel_left, mem_toAddSubgroup, mul_assoc, mul_smul, normal_subgroupOf_iff, smul_mem_pointwise_smul_iff, smul_smul, smul_sub
-/
protected lemma disjoint_iff [SemilatticeInf α] {a : α} {x y : Ici a} :
    Disjoint x y ↔ ↑x ⊓ ↑y = a := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

/--
lemma `codisjoint_iff` / 引理 `codisjoint_iff`

English:
lemma codisjoint_iff
  given: [SemilatticeSup α] [OrderTop α] {a : α} {x y : Ici a}
  proof: by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]

中文:
引理 codisjoint_iff
  条件: [SemilatticeSup α] [有顶序 α] {a : α} {x y : 左闭右无界区间 a}
  证明: by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]
-/
protected lemma codisjoint_iff [SemilatticeSup α] [OrderTop α] {a : α} {x y : Ici a} :
    Codisjoint x y ↔ Codisjoint (x : α) (y : α) := by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]

/--
lemma `isCompl_iff` / 引理 `isCompl_iff`

English:
lemma isCompl_iff
  given: [Lattice α] [OrderTop α] {a : α} {x y : Ici a}
  proof: by
  rw [_root_.isCompl_iff]; rw [Ici.disjoint_iff]; rw [Ici.codisjoint_iff]

中文:
引理 isCompl_iff
  条件: [格 α] [有顶序 α] {a : α} {x y : 左闭右无界区间 a}
  证明: by
  rw [_root_.isCompl_iff]; rw [Ici.disjoint_iff]; rw [Ici.codisjoint_iff]
-/
protected lemma isCompl_iff [Lattice α] [OrderTop α] {a : α} {x y : Ici a} :
    IsCompl x y ↔ ↑x ⊓ ↑y = a ∧ Codisjoint (x : α) (y : α) := by
  rw [_root_.isCompl_iff]; rw [Ici.disjoint_iff]; rw [Ici.codisjoint_iff]

end Ici

namespace Icc

variable {a b : α}

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: [SemilatticeInf α]
  body: Subtype.semilatticeInf fun _ _ hx hy => ⟨le_inf hx.1 hy.1, le_trans inf_le_left hx.2⟩

@[simp, norm_cast]

中文:
实例 semilatticeInf
  签名: [SemilatticeInf α]
  定义体: Subtype.semilatticeInf fun _ _ hx hy => ⟨le_inf hx.1 hy.1, le_trans inf_le_left hx.2⟩

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.semilatticeInf, inf_le_left, le_inf, le_trans, semilatticeInf
-/
instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (Icc a b) :=
  Subtype.semilatticeInf fun _ _ hx hy => ⟨le_inf hx.1 hy.1, le_trans inf_le_left hx.2⟩

@[simp, norm_cast]
/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: [SemilatticeInf α] {x y : Icc a b}
  proof: rfl

中文:
引理 coe_inf
  条件: [SemilatticeInf α] {x y : 闭区间 a b}
  证明: rfl
-/
protected lemma coe_inf [SemilatticeInf α] {x y : Icc a b} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: [SemilatticeSup α]
  body: Subtype.semilatticeSup fun _ _ hx hy => ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩

@[simp, norm_cast]

中文:
实例 semilatticeSup
  签名: [SemilatticeSup α]
  定义体: Subtype.semilatticeSup fun _ _ hx hy => ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.semilatticeSup, le_sup_left, le_trans, semilatticeSup, sup_le
-/
instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (Icc a b) :=
  Subtype.semilatticeSup fun _ _ hx hy => ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩

@[simp, norm_cast]
/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: [SemilatticeSup α] {x y : Icc a b}
  proof: rfl

中文:
引理 coe_sup
  条件: [SemilatticeSup α] {x y : 闭区间 a b}
  证明: rfl
-/
protected lemma coe_sup [SemilatticeSup α] {x y : Icc a b} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

/--
Instance `lattice` / 实例 `lattice`

English:
instance lattice
  signature: [Lattice α]
  body: { Icc.semilatticeInf, Icc.semilatticeSup with }

中文:
实例 lattice
  签名: [格 α]
  定义体: { Icc.semilatticeInf, Icc.semilatticeSup with }

Depends on / 依赖: Icc.semilatticeInf, Icc.semilatticeSup, semilatticeInf, semilatticeSup
-/
instance lattice [Lattice α] : Lattice (Icc a b) :=
  { Icc.semilatticeInf, Icc.semilatticeSup with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [Fact (a <= b)] : OrderBot (Icc a b)
  body: (isLeast_Icc Fact.out).orderBot

@[simp, norm_cast]

中文:
实例 [预序
  签名: α] [Fact (a <= b)] : 有底序 (闭区间 a b)
  定义体: (isLeast_Icc Fact.out).orderBot

@[simp, norm_cast]

Depends on / 依赖: Fact.out, isLeast_Icc, orderBot
-/
instance [Preorder α] [Fact (a <= b)] : OrderBot (Icc a b) :=
  (isLeast_Icc Fact.out).orderBot

@[simp, norm_cast]
/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  given: [Preorder α] (a b : α) [Fact (a <= b)]
  statement: ↑(⊥ : Icc a b) = a
  proof: rfl

中文:
引理 coe_bot
  条件: [预序 α] (a b : α) [Fact (a <= b)]
  结论: ↑(⊥ : 闭区间 a b) = a
  证明: rfl
-/
protected lemma coe_bot [Preorder α] (a b : α) [Fact (a <= b)] : ↑(⊥ : Icc a b) = a := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [Fact (a <= b)] : OrderTop (Icc a b)
  body: (isGreatest_Icc Fact.out).orderTop

@[simp, norm_cast]

中文:
实例 [预序
  签名: α] [Fact (a <= b)] : 有顶序 (闭区间 a b)
  定义体: (isGreatest_Icc Fact.out).orderTop

@[simp, norm_cast]

Depends on / 依赖: Fact.out, isGreatest_Icc, orderTop
-/
instance [Preorder α] [Fact (a <= b)] : OrderTop (Icc a b) :=
  (isGreatest_Icc Fact.out).orderTop

@[simp, norm_cast]
/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  given: [Preorder α] (a b : α) [Fact (a <= b)]
  statement: ↑(⊤ : Icc a b) = b
  proof: rfl

中文:
引理 coe_top
  条件: [预序 α] (a b : α) [Fact (a <= b)]
  结论: ↑(⊤ : 闭区间 a b) = b
  证明: rfl
-/
protected lemma coe_top [Preorder α] (a b : α) [Fact (a <= b)] : ↑(⊤ : Icc a b) = b := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [Fact (a <= b)] : BoundedOrder (Icc a b) where

中文:
实例 [预序
  签名: α] [Fact (a <= b)] : 有界序 (闭区间 a b) where

Depends on / 依赖: Subtype, Subtype.ext_iff, _root_, _root_.disjoint_iff, disjoint_iff, ext_iff
-/
instance [Preorder α] [Fact (a <= b)] : BoundedOrder (Icc a b) where

/--
lemma `disjoint_iff` / 引理 `disjoint_iff`

English:
lemma disjoint_iff
  given: [SemilatticeInf α] [Fact (a <= b)] {x y : Icc a b}
  proof: by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

中文:
引理 disjoint_iff
  条件: [SemilatticeInf α] [Fact (a <= b)] {x y : 闭区间 a b}
  证明: by
  simp [_root_.disjoint_iff, Subtype.ext_iff]
-/
protected lemma disjoint_iff [SemilatticeInf α] [Fact (a <= b)] {x y : Icc a b} :
    Disjoint x y ↔ ↑x ⊓ ↑y = a := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

/--
lemma `codisjoint_iff` / 引理 `codisjoint_iff`

English:
lemma codisjoint_iff
  given: [SemilatticeSup α] [Fact (a <= b)] {x y : Icc a b}
  proof: by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]

中文:
引理 codisjoint_iff
  条件: [SemilatticeSup α] [Fact (a <= b)] {x y : 闭区间 a b}
  证明: by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]
-/
protected lemma codisjoint_iff [SemilatticeSup α] [Fact (a <= b)] {x y : Icc a b} :
    Codisjoint x y ↔ ↑x ⊔ (y : α) = b := by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]

/--
lemma `isCompl_iff` / 引理 `isCompl_iff`

English:
lemma isCompl_iff
  given: [Lattice α] [Fact (a <= b)] {x y : Icc a b}
  proof: by
  rw [_root_.isCompl_iff]; rw [Icc.disjoint_iff]; rw [Icc.codisjoint_iff]

中文:
引理 isCompl_iff
  条件: [格 α] [Fact (a <= b)] {x y : 闭区间 a b}
  证明: by
  rw [_root_.isCompl_iff]; rw [Icc.disjoint_iff]; rw [Icc.codisjoint_iff]
-/
protected lemma isCompl_iff [Lattice α] [Fact (a <= b)] {x y : Icc a b} :
    IsCompl x y ↔ ↑x ⊓ ↑y = a ∧ ↑x ⊔ ↑y = b := by
  rw [_root_.isCompl_iff]; rw [Icc.disjoint_iff]; rw [Icc.codisjoint_iff]

end Icc

end Set
