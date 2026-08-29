/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Sigma.Lex
public import Mathlib.Util.Notation3
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Lex

/-!
# Orders on a sigma type

This file defines two orders on a sigma type:
* The disjoint sum of orders. `a` is less `b` iff `a` and `b` are in the same summand and `a` is
  less than `b` there.
* The lexicographical order. `a` is less than `b` if its summand is strictly less than the summand
  of `b` or they are in the same summand and `a` is less than `b` there.

We make the disjoint sum of orders the default set of instances. The lexicographic order goes on a
type synonym.

## Notation

* `_root_.Lex (Sigma α)`: Sigma type equipped with the lexicographic order.
  Type synonym of `Σ i, α i`.

## See also

Related files are:
* `Data.Finset.CoLex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σₗ' i, α i`. Basically a twin of this file.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.

## TODO

Upgrade `Equiv.sigma_congr_left`, `Equiv.sigma_congr`, `Equiv.sigma_assoc`,
`Equiv.sigma_prod_of_equiv`, `Equiv.sigma_equiv_prod`, ... to order isomorphisms.
-/

@[expose] public section


namespace Sigma

variable {ι : Type*} {α : ι -> Type*}

/-! ### Disjoint sum of orders on `Sigma` -/

/--
Inductive type `LE` / 归纳类型 `LE`

English:
inductive LE
  parameters: [forall i, LE (α i)]
  constructors (1):
    - fiber: (i : ι) (a b : α i) : a <= b -> Sigma.LE ⟨i, a⟩ ⟨i, b⟩

中文:
归纳类型 LE
  参数: [对任意 i, LE (α i)]
  构造子 (1 个):
    - fiber: (i : ι) (a b : α i) : a <= b -> Sigma.LE ⟨i, a⟩ ⟨i, b⟩
-/
protected inductive LE [forall i, LE (α i)] : forall _a _b : Σ i, α i, Prop
  | fiber (i : ι) (a b : α i) : a <= b -> Sigma.LE ⟨i, a⟩ ⟨i, b⟩

/--
Inductive type `LT` / 归纳类型 `LT`

English:
inductive LT
  parameters: [forall i, LT (α i)]
  constructors (1):
    - fiber: (i : ι) (a b : α i) : a < b -> Sigma.LT ⟨i, a⟩ ⟨i, b⟩

中文:
归纳类型 LT
  参数: [对任意 i, LT (α i)]
  构造子 (1 个):
    - fiber: (i : ι) (a b : α i) : a < b -> Sigma.LT ⟨i, a⟩ ⟨i, b⟩
-/
protected inductive LT [forall i, LT (α i)] : forall _a _b : Σ i, α i, Prop
  | fiber (i : ι) (a b : α i) : a < b -> Sigma.LT ⟨i, a⟩ ⟨i, b⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, LE (α i)] : LE (Σ i, α i) where
  body: Sigma.LE

中文:
实例 [forall
  签名: i, LE (α i)] : LE (Σ i, α i) where
  定义体: Sigma.LE
-/
protected instance [forall i, LE (α i)] : LE (Σ i, α i) where
  le := Sigma.LE

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, LT (α i)] : LT (Σ i, α i) where
  body: Sigma.LT

@[simp]

中文:
实例 [forall
  签名: i, LT (α i)] : LT (Σ i, α i) where
  定义体: Sigma.LT

@[simp]
-/
protected instance [forall i, LT (α i)] : LT (Σ i, α i) where
  lt := Sigma.LT

@[simp]
/--
theorem `mk_le_mk_iff` / 定理 `mk_le_mk_iff`

English:
theorem mk_le_mk_iff
  given: [forall i, LE (α i)] {i : ι} {a b : α i}
  statement: (⟨i, a⟩ : Sigma α) <= ⟨i, b⟩ ↔ a <= b
  proof: ⟨fun ⟨_, _, _, h⟩ => h, Sigma.LE.fiber _ _ _⟩

@[simp]

中文:
定理 mk_le_mk_iff
  条件: [对任意 i, LE (α i)] {i : ι} {a b : α i}
  结论: (⟨i, a⟩ : Sigma α) <= ⟨i, b⟩ ↔ a <= b
  证明: ⟨fun ⟨_, _, _, h⟩ => h, Sigma.LE.fiber _ _ _⟩

@[simp]

Depends on / 依赖: Sigma.LE.fiber
-/
theorem mk_le_mk_iff [forall i, LE (α i)] {i : ι} {a b : α i} : (⟨i, a⟩ : Sigma α) <= ⟨i, b⟩ ↔ a <= b :=
  ⟨fun ⟨_, _, _, h⟩ => h, Sigma.LE.fiber _ _ _⟩

@[simp]
/--
theorem `mk_lt_mk_iff` / 定理 `mk_lt_mk_iff`

English:
theorem mk_lt_mk_iff
  given: [forall i, LT (α i)] {i : ι} {a b : α i}
  statement: (⟨i, a⟩ : Sigma α) < ⟨i, b⟩ ↔ a < b
  proof: ⟨fun ⟨_, _, _, h⟩ => h, Sigma.LT.fiber _ _ _⟩

中文:
定理 mk_lt_mk_iff
  条件: [对任意 i, LT (α i)] {i : ι} {a b : α i}
  结论: (⟨i, a⟩ : Sigma α) < ⟨i, b⟩ ↔ a < b
  证明: ⟨fun ⟨_, _, _, h⟩ => h, Sigma.LT.fiber _ _ _⟩

Depends on / 依赖: Sigma.LT.fiber
-/
theorem mk_lt_mk_iff [forall i, LT (α i)] {i : ι} {a b : α i} : (⟨i, a⟩ : Sigma α) < ⟨i, b⟩ ↔ a < b :=
  ⟨fun ⟨_, _, _, h⟩ => h, Sigma.LT.fiber _ _ _⟩

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: [forall i, LE (α i)] {a b : Σ i, α i}
  statement: a <= b ↔ exists h : a.1 = b.1, h.rec a.2 <= b.2
  proof: by
  constructor
  · rintro ⟨i, a, b, h⟩
    exact ⟨rfl, h⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    rintro ⟨rfl : i = j, h⟩
    exact LE.fiber _ _ _ h

中文:
定理 le_def
  条件: [对任意 i, LE (α i)] {a b : Σ i, α i}
  结论: a <= b ↔ 存在 h : a.1 = b.1, h.rec a.2 <= b.2
  证明: by
  constructor
  · rintro ⟨i, a, b, h⟩
    exact ⟨rfl, h⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    rintro ⟨rfl : i = j, h⟩
    exact LE.fiber _ _ _ h

Depends on / 依赖: LE.fiber
-/
theorem le_def [forall i, LE (α i)] {a b : Σ i, α i} : a <= b ↔ exists h : a.1 = b.1, h.rec a.2 <= b.2 := by
  constructor
  · rintro ⟨i, a, b, h⟩
    exact ⟨rfl, h⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    rintro ⟨rfl : i = j, h⟩
    exact LE.fiber _ _ _ h

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: [forall i, LT (α i)] {a b : Σ i, α i}
  statement: a < b ↔ exists h : a.1 = b.1, h.rec a.2 < b.2
  proof: by
  constructor
  · rintro ⟨i, a, b, h⟩
    exact ⟨rfl, h⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    rintro ⟨rfl : i = j, h⟩
    exact LT.fiber _ _ _ h

中文:
定理 lt_def
  条件: [对任意 i, LT (α i)] {a b : Σ i, α i}
  结论: a < b ↔ 存在 h : a.1 = b.1, h.rec a.2 < b.2
  证明: by
  constructor
  · rintro ⟨i, a, b, h⟩
    exact ⟨rfl, h⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    rintro ⟨rfl : i = j, h⟩
    exact LT.fiber _ _ _ h

Depends on / 依赖: LT.fiber
-/
theorem lt_def [forall i, LT (α i)] {a b : Σ i, α i} : a < b ↔ exists h : a.1 = b.1, h.rec a.2 < b.2 := by
  constructor
  · rintro ⟨i, a, b, h⟩
    exact ⟨rfl, h⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    rintro ⟨rfl : i = j, h⟩
    exact LT.fiber _ _ _ h

/--
Instance `preorder` / 实例 `preorder`

English:
instance preorder
  signature: [forall i, Preorder (α i)]
  body: { le_refl := fun ⟨i, a⟩ => Sigma.LE.fiber i a a le_rfl,
    le_trans := by
      rintro _ _ _ ⟨i, a, b, hab⟩ ⟨_, _, c, hbc⟩
      exact LE.fiber i a c (hab.trans hbc),
    lt_iff_le_not_ge := fun _ _ => by
      constructor
      · rintro ⟨i, a, b, hab⟩
        rwa [mk_le_mk_iff, mk_le_mk_iff, ← lt_

中文:
实例 preorder
  签名: [对任意 i, Preorder (α i)]
  定义体: { le_refl := fun ⟨i, a⟩ => Sigma.LE.fiber i a a le_rfl,
    le_trans := by
      rintro _ _ _ ⟨i, a, b, hab⟩ ⟨_, _, c, hbc⟩
      exact LE.fiber i a c (hab.trans hbc),
    lt_iff_le_not_ge := fun _ _ => by
      constructor
      · rintro ⟨i, a, b, hab⟩
        rwa [mk_le_mk_iff, mk_le_mk_iff, ← lt_
-/
protected instance preorder [forall i, Preorder (α i)] : Preorder (Σ i, α i) :=
  { le_refl := fun ⟨i, a⟩ => Sigma.LE.fiber i a a le_rfl,
    le_trans := by
      rintro _ _ _ ⟨i, a, b, hab⟩ ⟨_, _, c, hbc⟩
      exact LE.fiber i a c (hab.trans hbc),
    lt_iff_le_not_ge := fun _ _ => by
      constructor
      · rintro ⟨i, a, b, hab⟩
        rwa [mk_le_mk_iff, mk_le_mk_iff, ← lt_iff_le_not_ge]
      · rintro ⟨⟨i, a, b, hab⟩, h⟩
        rw [mk_le_mk_iff] at h
        exact mk_lt_mk_iff.2 (hab.lt_of_not_ge h) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, PartialOrder (α i)] : PartialOrder (Σ i, α i)
  body: { Sigma.preorder with
    le_antisymm := by
      rintro _ _ ⟨i, a, b, hab⟩ ⟨_, _, _, hba⟩
exact congr_arg (Sigma.mk _ ·) hab.antisymm hba }

中文:
实例 [forall
  签名: i, PartialOrder (α i)] : PartialOrder (Σ i, α i)
  定义体: { Sigma.preorder with
    le_antisymm := by
      rintro _ _ ⟨i, a, b, hab⟩ ⟨_, _, _, hba⟩
exact congr_arg (Sigma.mk _ ·) hab.antisymm hba }

Depends on / 依赖: Sigma.mk, Sigma.preorder, antisymm, congr_arg, hab.antisymm, le_antisymm, preorder
-/
instance [forall i, PartialOrder (α i)] : PartialOrder (Σ i, α i) :=
  { Sigma.preorder with
    le_antisymm := by
      rintro _ _ ⟨i, a, b, hab⟩ ⟨_, _, _, hba⟩
exact congr_arg (Sigma.mk _ ·) hab.antisymm hba }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Preorder (α i)] [forall i, DenselyOrdered (α i)] : DenselyOrdered (Σ i, α i) where
  body: by
    rintro ⟨i, a⟩ ⟨_, _⟩ ⟨_, _, b, h⟩
    obtain ⟨c, ha, hb⟩ := exists_between h
    exact ⟨⟨i, c⟩, LT.fiber i a c ha, LT.fiber i c b hb⟩

中文:
实例 [forall
  签名: i, Preorder (α i)] [对任意 i, DenselyOrdered (α i)] : DenselyOrdered (Σ i, α i) where
  定义体: by
    rintro ⟨i, a⟩ ⟨_, _⟩ ⟨_, _, b, h⟩
    obtain ⟨c, ha, hb⟩ := exists_between h
    exact ⟨⟨i, c⟩, LT.fiber i a c ha, LT.fiber i c b hb⟩

Depends on / 依赖: LT.fiber, exists_between
-/
instance [forall i, Preorder (α i)] [forall i, DenselyOrdered (α i)] : DenselyOrdered (Σ i, α i) where
  dense := by
    rintro ⟨i, a⟩ ⟨_, _⟩ ⟨_, _, b, h⟩
    obtain ⟨c, ha, hb⟩ := exists_between h
    exact ⟨⟨i, c⟩, LT.fiber i a c ha, LT.fiber i c b hb⟩

/-! ### Lexicographical order on `Sigma` -/


namespace Lex
/-- The notation `Σₗ i, α i` refers to a sigma type equipped with the lexicographic order. -/
notation3 "Σₗ " (...) ", " r:(scoped p => _root_.Lex (Sigma p)) => r

/--
Instance `LE` / 实例 `LE`

English:
instance LE
  signature: [LT ι] [forall i, LE (α i)]
  body: Lex (· < ·) fun _ => (· <= ·)

中文:
实例 LE
  签名: [LT ι] [对任意 i, LE (α i)]
  定义体: Lex (· < ·) fun _ => (· <= ·)
-/
protected instance LE [LT ι] [forall i, LE (α i)] : LE (Σₗ i, α i) where
  le := Lex (· < ·) fun _ => (· <= ·)

/--
Instance `LT` / 实例 `LT`

English:
instance LT
  signature: [LT ι] [forall i, LT (α i)]
  body: Lex (· < ·) fun _ => (· < ·)

中文:
实例 LT
  签名: [LT ι] [对任意 i, LT (α i)]
  定义体: Lex (· < ·) fun _ => (· < ·)
-/
protected instance LT [LT ι] [forall i, LT (α i)] : LT (Σₗ i, α i) where
  lt := Lex (· < ·) fun _ => (· < ·)

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: [LT ι] [forall i, LE (α i)] {a b : Σₗ i, α i}
  proof: Sigma.lex_iff

中文:
定理 le_def
  条件: [LT ι] [对任意 i, LE (α i)] {a b : Σₗ i, α i}
  证明: Sigma.lex_iff

Depends on / 依赖: Sigma.lex_iff, lex_iff
-/
theorem le_def [LT ι] [forall i, LE (α i)] {a b : Σₗ i, α i} :
    a <= b ↔ a.1 < b.1 ∨ exists h : a.1 = b.1, h.rec a.2 <= b.2 :=
  Sigma.lex_iff

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: [LT ι] [forall i, LT (α i)] {a b : Σₗ i, α i}
  proof: Sigma.lex_iff

中文:
定理 lt_def
  条件: [LT ι] [对任意 i, LT (α i)] {a b : Σₗ i, α i}
  证明: Sigma.lex_iff

Depends on / 依赖: Sigma.lex_iff, lex_iff
-/
theorem lt_def [LT ι] [forall i, LT (α i)] {a b : Σₗ i, α i} :
    a < b ↔ a.1 < b.1 ∨ exists h : a.1 = b.1, h.rec a.2 < b.2 :=
  Sigma.lex_iff

/--
Instance `preorder` / 实例 `preorder`

English:
instance preorder
  signature: [Preorder ι] [forall i, Preorder (α i)]
  body: { Sigma.Lex.LE, Sigma.Lex.LT with
    le_refl := fun ⟨_, a⟩ => Lex.right a a le_rfl,
    le_trans := fun _ _ _ => trans_of ((Lex (· < ·)) fun _ => (· <= ·)),
    lt_iff_le_not_ge := by
      refine fun a b => ⟨fun hab => ⟨hab.mono_right fun i a b => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨b, a, hji⟩ | ⟨

中文:
实例 preorder
  签名: [Preorder ι] [对任意 i, Preorder (α i)]
  定义体: { Sigma.Lex.LE, Sigma.Lex.LT with
    le_refl := fun ⟨_, a⟩ => Lex.right a a le_rfl,
    le_trans := fun _ _ _ => trans_of ((Lex (· < ·)) fun _ => (· <= ·)),
    lt_iff_le_not_ge := by
      refine fun a b => ⟨fun hab => ⟨hab.mono_right fun i a b => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨b, a, hji⟩ | ⟨

Depends on / 依赖: Lex.right, Sigma.Lex.LE, Sigma.Lex.LT, Sigma.Lex.left, hab.mono_right, hab.not_ge, hij.not_gt, le_of_lt, le_refl, le_rfl, le_trans, lt_iff_le_not_ge, lt_irrefl, mono_right, not_ge, not_gt, trans_of
-/
instance preorder [Preorder ι] [forall i, Preorder (α i)] : Preorder (Σₗ i, α i) :=
  { Sigma.Lex.LE, Sigma.Lex.LT with
    le_refl := fun ⟨_, a⟩ => Lex.right a a le_rfl,
    le_trans := fun _ _ _ => trans_of ((Lex (· < ·)) fun _ => (· <= ·)),
    lt_iff_le_not_ge := by
      refine fun a b => ⟨fun hab => ⟨hab.mono_right fun i a b => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨b, a, hji⟩ | ⟨b, a, hba⟩) <;> obtain ⟨_, _, hij⟩ | ⟨_, _, hab⟩ := hab
        · exact hij.not_gt hji
        · exact lt_irrefl _ hji
        · exact lt_irrefl _ hij
        · exact hab.not_ge hba
      · rintro ⟨⟨a, b, hij⟩ | ⟨a, b, hab⟩, hba⟩
        · exact Sigma.Lex.left _ _ hij
        · exact Sigma.Lex.right _ _ (hab.lt_of_not_ge fun h => hba <| Sigma.Lex.right _ _ h) }

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: [Preorder ι] [forall i, PartialOrder (α i)]
  body: { Lex.preorder with
    le_antisymm := fun _ _ => antisymm_of ((Lex (· < ·)) fun _ => (· <= ·)) }

中文:
实例 partialOrder
  签名: [Preorder ι] [对任意 i, PartialOrder (α i)]
  定义体: { Lex.preorder with
    le_antisymm := fun _ _ => antisymm_of ((Lex (· < ·)) fun _ => (· <= ·)) }

Depends on / 依赖: Lex.preorder, antisymm_of, le_antisymm, preorder
-/
instance partialOrder [Preorder ι] [forall i, PartialOrder (α i)] :
    PartialOrder (Σₗ i, α i) :=
  { Lex.preorder with
    le_antisymm := fun _ _ => antisymm_of ((Lex (· < ·)) fun _ => (· <= ·)) }



/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: [LinearOrder ι] [forall i, LinearOrder (α i)]
  body: { Lex.partialOrder with
    le_total := total_of ((Lex (· < ·)) fun _ => (· <= ·)),
    toDecidableEq := Sigma.instDecidableEqSigma
    toDecidableLE := Lex.decidable _ _
    toDecidableLT := Lex.decidable _ _ }

中文:
实例 linearOrder
  签名: [LinearOrder ι] [对任意 i, LinearOrder (α i)]
  定义体: { Lex.partialOrder with
    le_total := total_of ((Lex (· < ·)) fun _ => (· <= ·)),
    toDecidableEq := Sigma.instDecidableEqSigma
    toDecidableLE := Lex.decidable _ _
    toDecidableLT := Lex.decidable _ _ }

Depends on / 依赖: Lex.decidable, Lex.partialOrder, Sigma.instDecidableEqSigma, decidable, instDecidableEqSigma, le_total, partialOrder, toDecidableEq, toDecidableLE, toDecidableLT, total_of
-/
instance linearOrder [LinearOrder ι] [forall i, LinearOrder (α i)] :
    LinearOrder (Σₗ i, α i) :=
  { Lex.partialOrder with
    le_total := total_of ((Lex (· < ·)) fun _ => (· <= ·)),
    toDecidableEq := Sigma.instDecidableEqSigma
    toDecidableLE := Lex.decidable _ _
    toDecidableLT := Lex.decidable _ _ }

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: [PartialOrder ι] [OrderBot ι] [forall i, Preorder (α i)] [OrderBot (α ⊥)]
  body: ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_bot_or_bot_lt a
    · exact Lex.right _ _ bot_le
    · exact Lex.left _ _ ha

中文:
实例 orderBot
  签名: [PartialOrder ι] [OrderBot ι] [对任意 i, Preorder (α i)] [OrderBot (α ⊥)]
  定义体: ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_bot_or_bot_lt a
    · exact Lex.right _ _ bot_le
    · exact Lex.left _ _ ha
-/
instance orderBot [PartialOrder ι] [OrderBot ι] [forall i, Preorder (α i)] [OrderBot (α ⊥)] :
    OrderBot (Σₗ i, α i) where
  bot := ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_bot_or_bot_lt a
    · exact Lex.right _ _ bot_le
    · exact Lex.left _ _ ha

/--
Instance `orderTop` / 实例 `orderTop`

English:
instance orderTop
  signature: [PartialOrder ι] [OrderTop ι] [forall i, Preorder (α i)] [OrderTop (α ⊤)]
  body: ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_top_or_lt_top a
    · exact Lex.right _ _ le_top
    · exact Lex.left _ _ ha

中文:
实例 orderTop
  签名: [PartialOrder ι] [OrderTop ι] [对任意 i, Preorder (α i)] [OrderTop (α ⊤)]
  定义体: ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_top_or_lt_top a
    · exact Lex.right _ _ le_top
    · exact Lex.left _ _ ha
-/
instance orderTop [PartialOrder ι] [OrderTop ι] [forall i, Preorder (α i)] [OrderTop (α ⊤)] :
    OrderTop (Σₗ i, α i) where
  top := ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_top_or_lt_top a
    · exact Lex.right _ _ le_top
    · exact Lex.left _ _ ha

/--
Instance `boundedOrder` / 实例 `boundedOrder`

English:
instance boundedOrder
  signature: [PartialOrder ι] [BoundedOrder ι] [forall i, Preorder (α i)] [OrderBot (α ⊥)]
  body: { Lex.orderBot, Lex.orderTop with }

中文:
实例 boundedOrder
  签名: [PartialOrder ι] [BoundedOrder ι] [对任意 i, Preorder (α i)] [OrderBot (α ⊥)]
  定义体: { Lex.orderBot, Lex.orderTop with }

Depends on / 依赖: Lex.orderBot, Lex.orderTop, orderBot, orderTop
-/
instance boundedOrder [PartialOrder ι] [BoundedOrder ι] [forall i, Preorder (α i)] [OrderBot (α ⊥)]
    [OrderTop (α ⊤)] : BoundedOrder (Σₗ i, α i) :=
  { Lex.orderBot, Lex.orderTop with }

/--
Instance `denselyOrdered` / 实例 `denselyOrdered`

English:
instance denselyOrdered
  signature: [Preorder ι] [DenselyOrdered ι] [forall i, Nonempty (α i)] [forall i, Preorder (α i)]
  body: by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨k, hi, hj⟩ := exists_between h
      obtain ⟨c⟩ : Nonempty (α k) := inferInstance
      exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩

中文:
实例 denselyOrdered
  签名: [Preorder ι] [DenselyOrdered ι] [对任意 i, Nonempty (α i)] [对任意 i, Preorder (α i)]
  定义体: by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨k, hi, hj⟩ := exists_between h
      obtain ⟨c⟩ : Nonempty (α k) := inferInstance
      exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩

Depends on / 依赖: Nonempty, exists_between
-/
instance denselyOrdered [Preorder ι] [DenselyOrdered ι] [forall i, Nonempty (α i)] [forall i, Preorder (α i)]
    [forall i, DenselyOrdered (α i)] : DenselyOrdered (Σₗ i, α i) where
  dense := by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨k, hi, hj⟩ := exists_between h
      obtain ⟨c⟩ : Nonempty (α k) := inferInstance
      exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩

/--
Instance `denselyOrdered_of_noMaxOrder` / 实例 `denselyOrdered_of_noMaxOrder`

English:
instance denselyOrdered_of_noMaxOrder
  signature: [Preorder ι] [forall i, Preorder (α i)]
  body: by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨c, ha⟩ := exists_gt a
      exact ⟨⟨i, c⟩, right _ _ ha, left _ _ h⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩

中文:
实例 denselyOrdered_of_noMaxOrder
  签名: [Preorder ι] [对任意 i, Preorder (α i)]
  定义体: by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨c, ha⟩ := exists_gt a
      exact ⟨⟨i, c⟩, right _ _ ha, left _ _ h⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩

Depends on / 依赖: exists_between, exists_gt
-/
instance denselyOrdered_of_noMaxOrder [Preorder ι] [forall i, Preorder (α i)]
    [forall i, DenselyOrdered (α i)] [forall i, NoMaxOrder (α i)] :
    DenselyOrdered (Σₗ i, α i) where
  dense := by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨c, ha⟩ := exists_gt a
      exact ⟨⟨i, c⟩, right _ _ ha, left _ _ h⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩

/--
Instance `denselyOrdered_of_noMinOrder` / 实例 `denselyOrdered_of_noMinOrder`

English:
instance denselyOrdered_of_noMinOrder
  signature: [Preorder ι] [forall i, Preorder (α i)]
  body: by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨c, hb⟩ := exists_lt b
      exact ⟨⟨j, c⟩, left _ _ h, right _ _ hb⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩

中文:
实例 denselyOrdered_of_noMinOrder
  签名: [Preorder ι] [对任意 i, Preorder (α i)]
  定义体: by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨c, hb⟩ := exists_lt b
      exact ⟨⟨j, c⟩, left _ _ h, right _ _ hb⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩

Depends on / 依赖: exists_between, exists_lt
-/
instance denselyOrdered_of_noMinOrder [Preorder ι] [forall i, Preorder (α i)]
    [forall i, DenselyOrdered (α i)] [forall i, NoMinOrder (α i)] :
    DenselyOrdered (Σₗ i, α i) where
  dense := by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨c, hb⟩ := exists_lt b
      exact ⟨⟨j, c⟩, left _ _ h, right _ _ hb⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩

/--
Instance `noMaxOrder_of_nonempty` / 实例 `noMaxOrder_of_nonempty`

English:
instance noMaxOrder_of_nonempty
  signature: [Preorder ι] [forall i, Preorder (α i)] [NoMaxOrder ι]
  body: by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_gt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩

中文:
实例 noMaxOrder_of_nonempty
  签名: [Preorder ι] [对任意 i, Preorder (α i)] [NoMaxOrder ι]
  定义体: by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_gt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩

Depends on / 依赖: Nonempty, exists_gt
-/
instance noMaxOrder_of_nonempty [Preorder ι] [forall i, Preorder (α i)] [NoMaxOrder ι]
    [forall i, Nonempty (α i)] : NoMaxOrder (Σₗ i, α i) where
  exists_gt := by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_gt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩

/--
Instance `noMinOrder_of_nonempty` / 实例 `noMinOrder_of_nonempty`

English:
instance noMinOrder_of_nonempty
  signature: [Preorder ι] [forall i, Preorder (α i)] [NoMinOrder ι]
  body: by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_lt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩

中文:
实例 noMinOrder_of_nonempty
  签名: [Preorder ι] [对任意 i, Preorder (α i)] [NoMinOrder ι]
  定义体: by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_lt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩

Depends on / 依赖: Nonempty, exists_lt
-/
instance noMinOrder_of_nonempty [Preorder ι] [forall i, Preorder (α i)] [NoMinOrder ι]
    [forall i, Nonempty (α i)] : NoMinOrder (Σₗ i, α i) where
  exists_lt := by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_lt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩

/--
Instance `noMaxOrder` / 实例 `noMaxOrder`

English:
instance noMaxOrder
  signature: [Preorder ι] [forall i, Preorder (α i)] [forall i, NoMaxOrder (α i)]
  body: by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_gt a
    exact ⟨⟨i, b⟩, right _ _ h⟩

中文:
实例 noMaxOrder
  签名: [Preorder ι] [对任意 i, Preorder (α i)] [对任意 i, NoMaxOrder (α i)]
  定义体: by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_gt a
    exact ⟨⟨i, b⟩, right _ _ h⟩

Depends on / 依赖: exists_gt
-/
instance noMaxOrder [Preorder ι] [forall i, Preorder (α i)] [forall i, NoMaxOrder (α i)] :
    NoMaxOrder (Σₗ i, α i) where
  exists_gt := by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_gt a
    exact ⟨⟨i, b⟩, right _ _ h⟩

/--
Instance `noMinOrder` / 实例 `noMinOrder`

English:
instance noMinOrder
  signature: [Preorder ι] [forall i, Preorder (α i)] [forall i, NoMinOrder (α i)]
  body: by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_lt a
    exact ⟨⟨i, b⟩, right _ _ h⟩

中文:
实例 noMinOrder
  签名: [Preorder ι] [对任意 i, Preorder (α i)] [对任意 i, NoMinOrder (α i)]
  定义体: by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_lt a
    exact ⟨⟨i, b⟩, right _ _ h⟩

Depends on / 依赖: exists_lt
-/
instance noMinOrder [Preorder ι] [forall i, Preorder (α i)] [forall i, NoMinOrder (α i)] :
    NoMinOrder (Σₗ i, α i) where
  exists_lt := by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_lt a
    exact ⟨⟨i, b⟩, right _ _ h⟩

end Lex

end Sigma
