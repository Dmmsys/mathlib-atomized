/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.DFinsupp.Lex
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Lexicographic order on finitely supported functions

This file defines the lexicographic order on `Finsupp`.
-/

@[expose] public section


variable {α N : Type*}

namespace Finsupp

section NHasZero

variable [Zero N]

/--
Definition of `Lex` / `Lex` 的定义

English:
definition Lex
  signature: (r : α -> α -> Prop) (s : N -> N -> Prop) (x y : α ->₀ N)
  body: Pi.Lex r s x y

中文:
定义 Lex
  签名: (r : α -> α -> 命题) (s : N -> N -> 命题) (x y : α ->₀ N)
  定义体: Pi.Lex r s x y
-/
protected def Lex (r : α -> α -> Prop) (s : N -> N -> Prop) (x y : α ->₀ N) : Prop :=
  Pi.Lex r s x y

/--
theorem `_root_.Pi.lex_eq_finsupp_lex` / 定理 `_root_.Pi.lex_eq_finsupp_lex`

English:
theorem _root_.Pi.lex_eq_finsupp_lex
  given: {r : α -> α -> Prop} {s : N -> N -> Prop} (a b : α ->₀ N)
  proof: rfl

中文:
定理 _root_.依赖函数类型.lex_eq_finsupp_lex
  条件: {r : α -> α -> 命题} {s : N -> N -> 命题} (a b : α ->₀ N)
  证明: rfl
-/
theorem _root_.Pi.lex_eq_finsupp_lex {r : α -> α -> Prop} {s : N -> N -> Prop} (a b : α ->₀ N) :
    Pi.Lex r s a b = Finsupp.Lex r s a b :=
  rfl

/--
theorem `lex_def` / 定理 `lex_def`

English:
theorem lex_def
  given: {r : α -> α -> Prop} {s : N -> N -> Prop} {a b : α ->₀ N}
  proof: .rfl

中文:
定理 lex_def
  条件: {r : α -> α -> 命题} {s : N -> N -> 命题} {a b : α ->₀ N}
  证明: .rfl
-/
theorem lex_def {r : α -> α -> Prop} {s : N -> N -> Prop} {a b : α ->₀ N} :
    Finsupp.Lex r s a b ↔ exists j, (forall d, r d j -> a d = b d) ∧ s (a j) (b j) :=
  .rfl

/--
theorem `lex_eq_invImage_dfinsupp_lex` / 定理 `lex_eq_invImage_dfinsupp_lex`

English:
theorem lex_eq_invImage_dfinsupp_lex
  given: (r : α -> α -> Prop) (s : N -> N -> Prop)
  proof: rfl

中文:
定理 lex_eq_invImage_dfinsupp_lex
  条件: (r : α -> α -> 命题) (s : N -> N -> 命题)
  证明: rfl
-/
theorem lex_eq_invImage_dfinsupp_lex (r : α -> α -> Prop) (s : N -> N -> Prop) :
    Finsupp.Lex r s = InvImage (DFinsupp.Lex r fun _ => s) toDFinsupp :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] [LT N] : LT (Lex (α ->₀ N))
  body: ⟨fun f g => Finsupp.Lex (· < ·) (· < ·) (ofLex f) (ofLex g)⟩

中文:
实例 [LT
  签名: α] [LT N] : LT (Lex (α ->₀ N))
  定义体: ⟨fun f g => Finsupp.Lex (· < ·) (· < ·) (ofLex f) (ofLex g)⟩

Depends on / 依赖: Finsupp, Finsupp.Lex
-/
instance [LT α] [LT N] : LT (Lex (α ->₀ N)) :=
  ⟨fun f g => Finsupp.Lex (· < ·) (· < ·) (ofLex f) (ofLex g)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] [LT N] : LT (Colex (α ->₀ N))
  body: ⟨fun f g => Finsupp.Lex (· > ·) (· < ·) (ofColex f) (ofColex g)⟩

中文:
实例 [LT
  签名: α] [LT N] : LT (Colex (α ->₀ N))
  定义体: ⟨fun f g => Finsupp.Lex (· > ·) (· < ·) (ofColex f) (ofColex g)⟩

Depends on / 依赖: Finsupp, Finsupp.Lex, ofColex
-/
instance [LT α] [LT N] : LT (Colex (α ->₀ N)) :=
  ⟨fun f g => Finsupp.Lex (· > ·) (· < ·) (ofColex f) (ofColex g)⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Lex.lt_iff` / 定理 `Lex.lt_iff`

English:
theorem Lex.lt_iff
  given: [LT α] [LT N] {a b : Lex (α ->₀ N)}
  proof: .rfl

中文:
定理 Lex.lt_iff
  条件: [LT α] [LT N] {a b : Lex (α ->₀ N)}
  证明: .rfl
-/
theorem Lex.lt_iff [LT α] [LT N] {a b : Lex (α ->₀ N)} :
    a < b ↔ exists i, (forall j, j < i -> a j = b j) ∧ a i < b i :=
  .rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Colex.lt_iff` / 定理 `Colex.lt_iff`

English:
theorem Colex.lt_iff
  given: [LT α] [LT N] {a b : Colex (α ->₀ N)}
  proof: .rfl

中文:
定理 Colex.lt_iff
  条件: [LT α] [LT N] {a b : Colex (α ->₀ N)}
  证明: .rfl
-/
theorem Colex.lt_iff [LT α] [LT N] {a b : Colex (α ->₀ N)} :
    a < b ↔ exists i, (forall j, i < j -> a j = b j) ∧ a i < b i :=
  .rfl

/--
theorem `lex_lt_of_lt_of_preorder` / 定理 `lex_lt_of_lt_of_preorder`

English:
theorem lex_lt_of_lt_of_preorder
  given: [Preorder N] (r) [IsStrictOrder α r] {x y : α ->₀ N} (hlt : x < y)
  proof: DFinsupp.lex_lt_of_lt_of_preorder r (id hlt : x.toDFinsupp < y.toDFinsupp)

中文:
定理 lex_lt_of_lt_of_preorder
  条件: [预序 N] (r) [是Strict序 α r] {x y : α ->₀ N} (hlt : x < y)
  证明: DFinsupp.lex_lt_of_lt_of_preorder r (id hlt : x.toDFinsupp < y.toDFinsupp)

Depends on / 依赖: DFinsupp, DFinsupp.lex_lt_of_lt_of_preorder, lex_lt_of_lt_of_preorder, toDFinsupp, x.toDFinsupp, y.toDFinsupp
-/
theorem lex_lt_of_lt_of_preorder [Preorder N] (r) [IsStrictOrder α r] {x y : α ->₀ N} (hlt : x < y) :
    exists i, (forall j, r j i -> x j <= y j ∧ y j <= x j) ∧ x i < y i :=
  DFinsupp.lex_lt_of_lt_of_preorder r (id hlt : x.toDFinsupp < y.toDFinsupp)

/--
theorem `lex_lt_of_lt` / 定理 `lex_lt_of_lt`

English:
theorem lex_lt_of_lt
  given: [PartialOrder N] (r) [IsStrictOrder α r] {x y : α ->₀ N} (hlt : x < y)
  proof: DFinsupp.lex_lt_of_lt r (id hlt : x.toDFinsupp < y.toDFinsupp)

中文:
定理 lex_lt_of_lt
  条件: [偏序 N] (r) [是Strict序 α r] {x y : α ->₀ N} (hlt : x < y)
  证明: DFinsupp.lex_lt_of_lt r (id hlt : x.toDFinsupp < y.toDFinsupp)

Depends on / 依赖: DFinsupp, DFinsupp.lex_lt_of_lt, lex_lt_of_lt, toDFinsupp, x.toDFinsupp, y.toDFinsupp
-/
theorem lex_lt_of_lt [PartialOrder N] (r) [IsStrictOrder α r] {x y : α ->₀ N} (hlt : x < y) :
    Pi.Lex r (· < ·) x y :=
  DFinsupp.lex_lt_of_lt r (id hlt : x.toDFinsupp < y.toDFinsupp)

/--
theorem `lex_iff_of_unique` / 定理 `lex_iff_of_unique`

English:
theorem lex_iff_of_unique
  given: [Unique α] [LT N] {r} [Std.Irrefl r] {x y : α ->₀ N}
  proof: Pi.lex_iff_of_unique

中文:
定理 lex_iff_of_unique
  条件: [唯一 α] [LT N] {r} [Std.Irrefl r] {x y : α ->₀ N}
  证明: Pi.lex_iff_of_unique

Depends on / 依赖: Pi.lex_iff_of_unique, lex_iff_of_unique
-/
theorem lex_iff_of_unique [Unique α] [LT N] {r} [Std.Irrefl r] {x y : α ->₀ N} :
    Finsupp.Lex r (· < ·) x y ↔ x default < y default :=
  Pi.lex_iff_of_unique

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Lex.lt_iff_of_unique` / 定理 `Lex.lt_iff_of_unique`

English:
theorem Lex.lt_iff_of_unique
  given: [Unique α] [LT N] [Preorder α] {x y : Lex (α ->₀ N)}
  proof: lex_iff_of_unique

中文:
定理 Lex.lt_iff_of_unique
  条件: [唯一 α] [LT N] [预序 α] {x y : Lex (α ->₀ N)}
  证明: lex_iff_of_unique
-/
theorem Lex.lt_iff_of_unique [Unique α] [LT N] [Preorder α] {x y : Lex (α ->₀ N)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Colex.lt_iff_of_unique` / 定理 `Colex.lt_iff_of_unique`

English:
theorem Colex.lt_iff_of_unique
  given: [Unique α] [LT N] [Preorder α] {x y : Colex (α ->₀ N)}
  proof: Lex.lt_iff_of_unique (α := αᵒᵈ)

中文:
定理 Colex.lt_iff_of_unique
  条件: [唯一 α] [LT N] [预序 α] {x y : Colex (α ->₀ N)}
  证明: Lex.lt_iff_of_unique (α := αᵒᵈ)

Depends on / 依赖: Lex.lt_iff_of_unique, lt_iff_of_unique
-/
theorem Colex.lt_iff_of_unique [Unique α] [LT N] [Preorder α] {x y : Colex (α ->₀ N)} :
    x < y ↔ x default < y default :=
  Lex.lt_iff_of_unique (α := αᵒᵈ)

variable [LinearOrder α]

/--
Instance `Lex.isStrictOrder` / 实例 `Lex.isStrictOrder`

English:
instance Lex.isStrictOrder
  signature: [PartialOrder N]
  body: lt_irrefl (α := Lex (α -> N)) _
  trans _ _ _ := lt_trans (α := Lex (α -> N))

中文:
实例 Lex.isStrictOrder
  签名: [偏序 N]
  定义体: lt_irrefl (α := Lex (α -> N)) _
  trans _ _ _ := lt_trans (α := Lex (α -> N))
-/
instance Lex.isStrictOrder [PartialOrder N] : IsStrictOrder (Lex (α ->₀ N)) (· < ·) where
  irrefl _ := lt_irrefl (α := Lex (α -> N)) _
  trans _ _ _ := lt_trans (α := Lex (α -> N))

/--
Instance `Colex.isStrictOrder` / 实例 `Colex.isStrictOrder`

English:
instance Colex.isStrictOrder
  signature: [PartialOrder N]
  body: Lex.isStrictOrder (α := αᵒᵈ)

中文:
实例 Colex.isStrictOrder
  签名: [偏序 N]
  定义体: Lex.isStrictOrder (α := αᵒᵈ)
-/
instance Colex.isStrictOrder [PartialOrder N] : IsStrictOrder (Colex (α ->₀ N)) (· < ·) :=
  Lex.isStrictOrder (α := αᵒᵈ)

/--
Instance `Lex.partialOrder` / 实例 `Lex.partialOrder`

English:
instance Lex.partialOrder
  signature: [PartialOrder N]
  body: (· < ·)
  le x y := ⇑(ofLex x) = ⇑(ofLex y) ∨ x < y
  __ := PartialOrder.lift (fun x : Lex (α ->₀ N) => toLex (⇑(ofLex x)))
    (DFunLike.coe_injective (F := Finsupp α N))

中文:
实例 Lex.partialOrder
  签名: [偏序 N]
  定义体: (· < ·)
  le x y := ⇑(ofLex x) = ⇑(ofLex y) ∨ x < y
  __ := PartialOrder.lift (fun x : Lex (α ->₀ N) => toLex (⇑(ofLex x)))
    (DFunLike.coe_injective (F := Finsupp α N))
-/
instance Lex.partialOrder [PartialOrder N] : PartialOrder (Lex (α ->₀ N)) where
  lt := (· < ·)
  le x y := ⇑(ofLex x) = ⇑(ofLex y) ∨ x < y
  __ := PartialOrder.lift (fun x : Lex (α ->₀ N) => toLex (⇑(ofLex x)))
    (DFunLike.coe_injective (F := Finsupp α N))

/--
Instance `Colex.partialOrder` / 实例 `Colex.partialOrder`

English:
instance Colex.partialOrder
  signature: [PartialOrder N]
  body: (· < ·)
  le x y := ⇑(ofColex x) = ⇑(ofColex y) ∨ x < y
  __ := PartialOrder.lift (fun x : Colex (α ->₀ N) => toColex (⇑(ofColex x)))
    (DFunLike.coe_injective (F := Finsupp α N))

中文:
实例 Colex.partialOrder
  签名: [偏序 N]
  定义体: (· < ·)
  le x y := ⇑(ofColex x) = ⇑(ofColex y) ∨ x < y
  __ := PartialOrder.lift (fun x : Colex (α ->₀ N) => toColex (⇑(ofColex x)))
    (DFunLike.coe_injective (F := Finsupp α N))
-/
instance Colex.partialOrder [PartialOrder N] : PartialOrder (Colex (α ->₀ N)) where
  lt := (· < ·)
  le x y := ⇑(ofColex x) = ⇑(ofColex y) ∨ x < y
  __ := PartialOrder.lift (fun x : Colex (α ->₀ N) => toColex (⇑(ofColex x)))
    (DFunLike.coe_injective (F := Finsupp α N))

/--
Instance `Lex.linearOrder` / 实例 `Lex.linearOrder`

English:
instance Lex.linearOrder
  signature: [LinearOrder N]
  body: Lex.partialOrder
  __ := LinearOrder.lift' (toLex ∘ toDFinsupp ∘ ofLex) finsuppEquivDFinsupp.injective

中文:
实例 Lex.linearOrder
  签名: [线性序 N]
  定义体: Lex.partialOrder
  __ := LinearOrder.lift' (toLex ∘ toDFinsupp ∘ ofLex) finsuppEquivDFinsupp.injective
-/
instance Lex.linearOrder [LinearOrder N] : LinearOrder (Lex (α ->₀ N)) where
  __ := Lex.partialOrder
  __ := LinearOrder.lift' (toLex ∘ toDFinsupp ∘ ofLex) finsuppEquivDFinsupp.injective

/--
Instance `Colex.linearOrder` / 实例 `Colex.linearOrder`

English:
instance Colex.linearOrder
  signature: [LinearOrder N]
  body: (· < ·)
  le := (· <= ·)
  __ := LinearOrder.lift' (toColex ∘ toDFinsupp ∘ ofColex) finsuppEquivDFinsupp.injective

中文:
实例 Colex.linearOrder
  签名: [线性序 N]
  定义体: (· < ·)
  le := (· <= ·)
  __ := LinearOrder.lift' (toColex ∘ toDFinsupp ∘ ofColex) finsuppEquivDFinsupp.injective
-/
instance Colex.linearOrder [LinearOrder N] : LinearOrder (Colex (α ->₀ N)) where
  lt := (· < ·)
  le := (· <= ·)
  __ := LinearOrder.lift' (toColex ∘ toDFinsupp ∘ ofColex) finsuppEquivDFinsupp.injective

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Lex.le_iff_of_unique` / 定理 `Lex.le_iff_of_unique`

English:
theorem Lex.le_iff_of_unique
  given: [Unique α] [PartialOrder N] {x y : Lex (α ->₀ N)}
  proof: Pi.lex_le_iff_of_unique

中文:
定理 Lex.le_iff_of_unique
  条件: [唯一 α] [偏序 N] {x y : Lex (α ->₀ N)}
  证明: Pi.lex_le_iff_of_unique
-/
theorem Lex.le_iff_of_unique [Unique α] [PartialOrder N] {x y : Lex (α ->₀ N)} :
    x <= y ↔ x default <= y default :=
  Pi.lex_le_iff_of_unique

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Colex.le_iff_of_unique` / 定理 `Colex.le_iff_of_unique`

English:
theorem Colex.le_iff_of_unique
  given: [Unique α] [PartialOrder N] {x y : Colex (α ->₀ N)}
  proof: Lex.le_iff_of_unique (α := αᵒᵈ)

中文:
定理 Colex.le_iff_of_unique
  条件: [唯一 α] [偏序 N] {x y : Colex (α ->₀ N)}
  证明: Lex.le_iff_of_unique (α := αᵒᵈ)
-/
theorem Colex.le_iff_of_unique [Unique α] [PartialOrder N] {x y : Colex (α ->₀ N)} :
    x <= y ↔ x default <= y default :=
  Lex.le_iff_of_unique (α := αᵒᵈ)

/--
theorem `Lex.single_strictAnti` / 定理 `Lex.single_strictAnti`

English:
theorem Lex.single_strictAnti
  statement: StrictAnti fun (a : α) => toLex (single a 1)
  proof: by
  intro a b h
  simp only [LT.lt, Finsupp.lex_def]
  simp only [ofLex_toLex, Nat.lt_eq]
  use a
  constructor
  · intro d hd
    simp only [Finsupp.single_eq_of_ne hd.ne, Finsupp.single_eq_of_ne (hd.trans h).ne]
  · simp [h.ne']

中文:
定理 Lex.single_strictAnti
  结论: 严格递减 fun (a : α) => toLex (single a 1)
  证明: by
  intro a b h
  simp only [LT.lt, Finsupp.lex_def]
  simp only [ofLex_toLex, Nat.lt_eq]
  use a
  constructor
  · intro d hd
    simp only [Finsupp.single_eq_of_ne hd.ne, Finsupp.single_eq_of_ne (hd.trans h).ne]
  · simp [h.ne']

Depends on / 依赖: Finsupp, Finsupp.lex_def, Finsupp.single_eq_of_ne, LT.lt, Nat.lt_eq, h.ne, hd.ne, hd.trans, lex_def, lt_eq, ofLex_toLex, single_eq_of_ne
-/
theorem Lex.single_strictAnti : StrictAnti fun (a : α) => toLex (single a 1) := by
  intro a b h
  simp only [LT.lt, Finsupp.lex_def]
  simp only [ofLex_toLex, Nat.lt_eq]
  use a
  constructor
  · intro d hd
    simp only [Finsupp.single_eq_of_ne hd.ne, Finsupp.single_eq_of_ne (hd.trans h).ne]
  · simp [h.ne']

/--
theorem `Colex.single_strictMono` / 定理 `Colex.single_strictMono`

English:
theorem Colex.single_strictMono
  statement: StrictMono fun (a : α) => toColex (single a 1)
  proof: fun _ _ h => Lex.single_strictAnti (α := αᵒᵈ) h

中文:
定理 Colex.single_strictMono
  结论: 严格递增 fun (a : α) => toColex (single a 1)
  证明: fun _ _ h => Lex.single_strictAnti (α := αᵒᵈ) h

Depends on / 依赖: Lex.refl_left, Lex.single_strictAnti, refl_left, single_strictAnti
-/
theorem Colex.single_strictMono : StrictMono fun (a : α) => toColex (single a 1) :=
  fun _ _ h => Lex.single_strictAnti (α := αᵒᵈ) h

/--
theorem `Lex.single_lt_iff` / 定理 `Lex.single_lt_iff`

English:
theorem Lex.single_lt_iff
  given: {a b : α}
  statement: toLex (single b 1) < toLex (single a 1) ↔ a < b
  proof: Lex.single_strictAnti.lt_iff_gt

中文:
定理 Lex.single_lt_iff
  条件: {a b : α}
  结论: toLex (single b 1) < toLex (single a 1) ↔ a < b
  证明: Lex.single_strictAnti.lt_iff_gt

Depends on / 依赖: Lex.refl_right, Lex.single_strictAnti.lt_iff_gt, lt_iff_gt, refl_right, single_strictAnti
-/
theorem Lex.single_lt_iff {a b : α} : toLex (single b 1) < toLex (single a 1) ↔ a < b :=
  Lex.single_strictAnti.lt_iff_gt

/--
theorem `Colex.single_lt_iff` / 定理 `Colex.single_lt_iff`

English:
theorem Colex.single_lt_iff
  given: {a b : α}
  statement: toColex (single a 1) < toColex (single b 1) ↔ a < b
  proof: Colex.single_strictMono.lt_iff_lt

中文:
定理 Colex.single_lt_iff
  条件: {a b : α}
  结论: toColex (single a 1) < toColex (single b 1) ↔ a < b
  证明: Colex.single_strictMono.lt_iff_lt

Depends on / 依赖: Colex.single_strictMono.lt_iff_lt, lt_iff_lt, single_strictMono
-/
theorem Colex.single_lt_iff {a b : α} : toColex (single a 1) < toColex (single b 1) ↔ a < b :=
  Colex.single_strictMono.lt_iff_lt

/--
theorem `Lex.single_le_iff` / 定理 `Lex.single_le_iff`

English:
theorem Lex.single_le_iff
  given: {a b : α}
  statement: toLex (single b 1) <= toLex (single a 1) ↔ a <= b
  proof: Lex.single_strictAnti.le_iff_ge

中文:
定理 Lex.single_le_iff
  条件: {a b : α}
  结论: toLex (single b 1) <= toLex (single a 1) ↔ a <= b
  证明: Lex.single_strictAnti.le_iff_ge

Depends on / 依赖: Lex.single_strictAnti.le_iff_ge, Lex.trans, le_iff_ge, single_strictAnti
-/
theorem Lex.single_le_iff {a b : α} : toLex (single b 1) <= toLex (single a 1) ↔ a <= b :=
  Lex.single_strictAnti.le_iff_ge

/--
theorem `Colex.single_le_iff` / 定理 `Colex.single_le_iff`

English:
theorem Colex.single_le_iff
  given: {a b : α}
  statement: toColex (single a 1) <= toColex (single b 1) ↔ a <= b
  proof: Colex.single_strictMono.le_iff_le

中文:
定理 Colex.single_le_iff
  条件: {a b : α}
  结论: toColex (single a 1) <= toColex (single b 1) ↔ a <= b
  证明: Colex.single_strictMono.le_iff_le

Depends on / 依赖: Colex.single_strictMono.le_iff_le, _root_, _root_.trans, antisymm, irrefl, le_iff_le, single_strictMono
-/
theorem Colex.single_le_iff {a b : α} : toColex (single a 1) <= toColex (single b 1) ↔ a <= b :=
  Colex.single_strictMono.le_iff_le

variable [PartialOrder N]

/--
theorem `toLex_monotone` / 定理 `toLex_monotone`

English:
theorem toLex_monotone
  statement: Monotone (@toLex (α ->₀ N))
  proof: fun a b h => DFinsupp.toLex_monotone (id h : forall i, (toDFinsupp a) i <= (toDFinsupp b) i)

中文:
定理 toLex_monotone
  结论: 递增 (@toLex (α ->₀ N))
  证明: fun a b h => DFinsupp.toLex_monotone (id h : forall i, (toDFinsupp a) i <= (toDFinsupp b) i)

Depends on / 依赖: DFinsupp, DFinsupp.toLex_monotone, toDFinsupp, toLex_monotone
-/
theorem toLex_monotone : Monotone (@toLex (α ->₀ N)) :=
  fun a b h => DFinsupp.toLex_monotone (id h : forall i, (toDFinsupp a) i <= (toDFinsupp b) i)

/--
theorem `toColex_monotone` / 定理 `toColex_monotone`

English:
theorem toColex_monotone
  statement: Monotone (@toColex (α ->₀ N))
  proof: toLex_monotone (α := αᵒᵈ)

中文:
定理 toColex_monotone
  结论: 递增 (@toColex (α ->₀ N))
  证明: toLex_monotone (α := αᵒᵈ)

Depends on / 依赖: toLex_monotone
-/
theorem toColex_monotone : Monotone (@toColex (α ->₀ N)) :=
  toLex_monotone (α := αᵒᵈ)

end NHasZero

section Covariants

variable [LinearOrder α] [AddMonoid N] [LinearOrder N]

/-! We are about to sneak in a hypothesis that might appear to be too strong.
We assume `AddLeftStrictMono` (covariant with *strict* inequality `<`) also when proving the one
with the *weak* inequality `≤`. This is actually necessary: addition on `Lex (α →₀ N)` may fail to
be monotone, when it is "just" monotone on `N`.

See `Counterexamples/ZeroDivisorsInAddMonoidAlgebras.lean` for a counterexample. -/


section Left

variable [AddLeftStrictMono N]

/--
Instance `Lex.addLeftStrictMono` / 实例 `Lex.addLeftStrictMono`

English:
instance Lex.addLeftStrictMono
  signature: : AddLeftStrictMono (Lex (α ->₀ N))
  body: ⟨fun _ _ _ ⟨a, lta, ha⟩ => ⟨a, fun j ja => congr_arg _ (lta j ja), add_lt_add_right ha _⟩⟩

中文:
实例 Lex.addLeftStrictMono
  签名: : AddLeftStrictMono (Lex (α ->₀ N))
  定义体: ⟨fun _ _ _ ⟨a, lta, ha⟩ => ⟨a, fun j ja => congr_arg _ (lta j ja), add_lt_add_right ha _⟩⟩
-/
instance Lex.addLeftStrictMono : AddLeftStrictMono (Lex (α ->₀ N)) :=
  ⟨fun _ _ _ ⟨a, lta, ha⟩ => ⟨a, fun j ja => congr_arg _ (lta j ja), add_lt_add_right ha _⟩⟩

/--
Instance `Colex.addLeftStrictMono` / 实例 `Colex.addLeftStrictMono`

English:
instance Colex.addLeftStrictMono
  signature: : AddLeftStrictMono (Colex (α ->₀ N))
  body: Lex.addLeftStrictMono (α := αᵒᵈ)

中文:
实例 Colex.addLeftStrictMono
  签名: : AddLeftStrictMono (Colex (α ->₀ N))
  定义体: Lex.addLeftStrictMono (α := αᵒᵈ)
-/
instance Colex.addLeftStrictMono : AddLeftStrictMono (Colex (α ->₀ N)) :=
  Lex.addLeftStrictMono (α := αᵒᵈ)

/--
Instance `Lex.addLeftMono` / 实例 `Lex.addLeftMono`

English:
instance Lex.addLeftMono
  signature: : AddLeftMono (Lex (α ->₀ N))
  body: addLeftMono_of_addLeftStrictMono _

中文:
实例 Lex.addLeftMono
  签名: : AddLeftMono (Lex (α ->₀ N))
  定义体: addLeftMono_of_addLeftStrictMono _
-/
instance Lex.addLeftMono : AddLeftMono (Lex (α ->₀ N)) :=
  addLeftMono_of_addLeftStrictMono _

/--
Instance `Colex.addLeftMono` / 实例 `Colex.addLeftMono`

English:
instance Colex.addLeftMono
  signature: : AddLeftMono (Colex (α ->₀ N))
  body: addLeftMono_of_addLeftStrictMono _

中文:
实例 Colex.addLeftMono
  签名: : AddLeftMono (Colex (α ->₀ N))
  定义体: addLeftMono_of_addLeftStrictMono _
-/
instance Colex.addLeftMono : AddLeftMono (Colex (α ->₀ N)) :=
  addLeftMono_of_addLeftStrictMono _

end Left

section Right

variable [AddRightStrictMono N]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Lex.addRightStrictMono` / 实例 `Lex.addRightStrictMono`

English:
instance Lex.addRightStrictMono
  signature: : AddRightStrictMono (Lex (α ->₀ N))
  body: ⟨fun f _ _ ⟨a, lta, ha⟩ => ⟨a, fun j ja => congr($(lta j ja) + f j), add_lt_add_left ha _⟩⟩

中文:
实例 Lex.addRightStrictMono
  签名: : AddRightStrictMono (Lex (α ->₀ N))
  定义体: ⟨fun f _ _ ⟨a, lta, ha⟩ => ⟨a, fun j ja => congr($(lta j ja) + f j), add_lt_add_left ha _⟩⟩
-/
instance Lex.addRightStrictMono : AddRightStrictMono (Lex (α ->₀ N)) :=
  ⟨fun f _ _ ⟨a, lta, ha⟩ => ⟨a, fun j ja => congr($(lta j ja) + f j), add_lt_add_left ha _⟩⟩

/--
Instance `Colex.addRightStrictMono` / 实例 `Colex.addRightStrictMono`

English:
instance Colex.addRightStrictMono
  signature: : AddRightStrictMono (Colex (α ->₀ N))
  body: Lex.addRightStrictMono (α := αᵒᵈ)

中文:
实例 Colex.addRightStrictMono
  签名: : AddRightStrictMono (Colex (α ->₀ N))
  定义体: Lex.addRightStrictMono (α := αᵒᵈ)
-/
instance Colex.addRightStrictMono : AddRightStrictMono (Colex (α ->₀ N)) :=
  Lex.addRightStrictMono (α := αᵒᵈ)

/--
Instance `Lex.addRightMono` / 实例 `Lex.addRightMono`

English:
instance Lex.addRightMono
  signature: : AddRightMono (Lex (α ->₀ N))
  body: addRightMono_of_addRightStrictMono _

中文:
实例 Lex.addRightMono
  签名: : AddRightMono (Lex (α ->₀ N))
  定义体: addRightMono_of_addRightStrictMono _
-/
instance Lex.addRightMono : AddRightMono (Lex (α ->₀ N)) :=
  addRightMono_of_addRightStrictMono _

/--
Instance `Colex.addRightMono` / 实例 `Colex.addRightMono`

English:
instance Colex.addRightMono
  signature: : AddRightMono (Colex (α ->₀ N))
  body: addRightMono_of_addRightStrictMono _

中文:
实例 Colex.addRightMono
  签名: : AddRightMono (Colex (α ->₀ N))
  定义体: addRightMono_of_addRightStrictMono _
-/
instance Colex.addRightMono : AddRightMono (Colex (α ->₀ N)) :=
  addRightMono_of_addRightStrictMono _

end Right

end Covariants

section OrderedAddMonoid

variable [LinearOrder α]

/--
Instance `Lex.orderBot` / 实例 `Lex.orderBot`

English:
instance Lex.orderBot
  signature: [AddCommMonoid N] [PartialOrder N] [IsBotZeroClass N]
  body: 0
  bot_le _ := Finsupp.toLex_monotone bot_le

中文:
实例 Lex.orderBot
  签名: [加法交换幺半群 N] [偏序 N] [是BotZero类 N]
  定义体: 0
  bot_le _ := Finsupp.toLex_monotone bot_le
-/
instance Lex.orderBot [AddCommMonoid N] [PartialOrder N] [IsBotZeroClass N] :
    OrderBot (Lex (α ->₀ N)) where
  bot := 0
  bot_le _ := Finsupp.toLex_monotone bot_le

/--
Instance `Lex.isBotZeroClass` / 实例 `Lex.isBotZeroClass`

English:
instance Lex.isBotZeroClass
  signature: [AddCommMonoid N] [PartialOrder N] [IsBotZeroClass N]
  body: isBot_bot

中文:
实例 Lex.isBotZeroClass
  签名: [加法交换幺半群 N] [偏序 N] [是BotZero类 N]
  定义体: isBot_bot
-/
instance Lex.isBotZeroClass [AddCommMonoid N] [PartialOrder N] [IsBotZeroClass N] :
    IsBotZeroClass (Lex (α ->₀ N)) where
  isBot_zero := isBot_bot

/--
Instance `Colex.orderBot` / 实例 `Colex.orderBot`

English:
instance Colex.orderBot
  signature: [AddCommMonoid N] [PartialOrder N] [IsBotZeroClass N]
  body: 0
  bot_le _ := Finsupp.toColex_monotone bot_le

中文:
实例 Colex.orderBot
  签名: [加法交换幺半群 N] [偏序 N] [是BotZero类 N]
  定义体: 0
  bot_le _ := Finsupp.toColex_monotone bot_le
-/
instance Colex.orderBot [AddCommMonoid N] [PartialOrder N] [IsBotZeroClass N] :
    OrderBot (Colex (α ->₀ N)) where
  bot := 0
  bot_le _ := Finsupp.toColex_monotone bot_le

/--
Instance `Colex.isBotZeroClass` / 实例 `Colex.isBotZeroClass`

English:
instance Colex.isBotZeroClass
  signature: [AddCommMonoid N] [PartialOrder N] [IsBotZeroClass N]
  body: isBot_bot

中文:
实例 Colex.isBotZeroClass
  签名: [加法交换幺半群 N] [偏序 N] [是BotZero类 N]
  定义体: isBot_bot
-/
instance Colex.isBotZeroClass [AddCommMonoid N] [PartialOrder N] [IsBotZeroClass N] :
    IsBotZeroClass (Colex (α ->₀ N)) where
  isBot_zero := isBot_bot

/--
Instance `Lex.isOrderedCancelAddMonoid` / 实例 `Lex.isOrderedCancelAddMonoid`

English:
instance Lex.isOrderedCancelAddMonoid
  body: add_le_add_left (α := Lex (α -> N)) h _
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left (α := Lex (α -> N))

中文:
实例 Lex.isOrderedCancelAddMonoid
  定义体: add_le_add_left (α := Lex (α -> N)) h _
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left (α := Lex (α -> N))
-/
instance Lex.isOrderedCancelAddMonoid
    [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N] :
    IsOrderedCancelAddMonoid (Lex (α ->₀ N)) where
  add_le_add_left _ _ h _ := add_le_add_left (α := Lex (α -> N)) h _
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left (α := Lex (α -> N))

/--
Instance `Colex.isOrderedCancelAddMonoid` / 实例 `Colex.isOrderedCancelAddMonoid`

English:
instance Colex.isOrderedCancelAddMonoid
  body: Lex.isOrderedCancelAddMonoid (α := αᵒᵈ)

中文:
实例 Colex.isOrderedCancelAddMonoid
  定义体: Lex.isOrderedCancelAddMonoid (α := αᵒᵈ)
-/
instance Colex.isOrderedCancelAddMonoid
    [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N] :
    IsOrderedCancelAddMonoid (Colex (α ->₀ N)) :=
  Lex.isOrderedCancelAddMonoid (α := αᵒᵈ)

end OrderedAddMonoid

end Finsupp
