/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyan Xu
-/
module

public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Data.DFinsupp.Order
public import Mathlib.Data.DFinsupp.NeLocus
public import Mathlib.Order.WellFoundedSet

/-!
# Lexicographic order on finitely supported dependent functions

This file defines the lexicographic order on `DFinsupp`.
-/

@[expose] public section


variable {ι : Type*} {α : ι -> Type*}

namespace DFinsupp

section Zero

variable [forall i, Zero (α i)]

/--
Definition of `Lex` / `Lex` 的定义

English:
definition Lex
  signature: (r : ι -> ι -> Prop) (s : forall i, α i -> α i -> Prop) (x y : Π₀ i, α i)
  body: Pi.Lex r (s _) x y

中文:
定义 Lex
  签名: (r : ι -> ι -> 命题) (s : 对任意 i, α i -> α i -> 命题) (x y : Π₀ i, α i)
  定义体: Pi.Lex r (s _) x y
-/
protected def Lex (r : ι -> ι -> Prop) (s : forall i, α i -> α i -> Prop) (x y : Π₀ i, α i) : Prop :=
  Pi.Lex r (s _) x y

/--
theorem `_root_.Pi.lex_eq_dfinsupp_lex` / 定理 `_root_.Pi.lex_eq_dfinsupp_lex`

English:
theorem _root_.Pi.lex_eq_dfinsupp_lex
  statement: {r : ι -> ι -> Prop} {s : forall i, α i -> α i -> Prop}
  proof: rfl

中文:
定理 _root_.依赖函数类型.lex_eq_dfinsupp_lex
  结论: {r : ι -> ι -> 命题} {s : 对任意 i, α i -> α i -> 命题}
  证明: rfl
-/
theorem _root_.Pi.lex_eq_dfinsupp_lex {r : ι -> ι -> Prop} {s : forall i, α i -> α i -> Prop}
    (a b : Π₀ i, α i) : Pi.Lex r (s _) (a : forall i, α i) b = DFinsupp.Lex r s a b :=
  rfl

/--
theorem `lex_def` / 定理 `lex_def`

English:
theorem lex_def
  given: {r : ι -> ι -> Prop} {s : forall i, α i -> α i -> Prop} {a b : Π₀ i, α i}
  proof: .rfl

中文:
定理 lex_def
  条件: {r : ι -> ι -> 命题} {s : 对任意 i, α i -> α i -> 命题} {a b : Π₀ i, α i}
  证明: .rfl
-/
theorem lex_def {r : ι -> ι -> Prop} {s : forall i, α i -> α i -> Prop} {a b : Π₀ i, α i} :
    DFinsupp.Lex r s a b ↔ exists j, (forall d, r d j -> a d = b d) ∧ s j (a j) (b j) :=
  .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: ι] [forall i, LT (α i)] : LT (Lex (Π₀ i, α i))
  body: ⟨fun f g => DFinsupp.Lex (· < ·) (fun _ => (· < ·)) (ofLex f) (ofLex g)⟩

中文:
实例 [LT
  签名: ι] [对任意 i, LT (α i)] : LT (Lex (Π₀ i, α i))
  定义体: ⟨fun f g => DFinsupp.Lex (· < ·) (fun _ => (· < ·)) (ofLex f) (ofLex g)⟩

Depends on / 依赖: DFinsupp, DFinsupp.Lex
-/
instance [LT ι] [forall i, LT (α i)] : LT (Lex (Π₀ i, α i)) :=
  ⟨fun f g => DFinsupp.Lex (· < ·) (fun _ => (· < ·)) (ofLex f) (ofLex g)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: ι] [forall i, LT (α i)] : LT (Colex (Π₀ i, α i))
  body: ⟨fun f g => DFinsupp.Lex (· > ·) (fun _ => (· < ·)) (ofColex f) (ofColex g)⟩

中文:
实例 [LT
  签名: ι] [对任意 i, LT (α i)] : LT (Colex (Π₀ i, α i))
  定义体: ⟨fun f g => DFinsupp.Lex (· > ·) (fun _ => (· < ·)) (ofColex f) (ofColex g)⟩

Depends on / 依赖: DFinsupp, DFinsupp.Lex, ofColex
-/
instance [LT ι] [forall i, LT (α i)] : LT (Colex (Π₀ i, α i)) :=
  ⟨fun f g => DFinsupp.Lex (· > ·) (fun _ => (· < ·)) (ofColex f) (ofColex g)⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Lex.lt_iff` / 定理 `Lex.lt_iff`

English:
theorem Lex.lt_iff
  given: [LT ι] [forall i, LT (α i)] {a b : Lex (Π₀ i, α i)}
  proof: .rfl

中文:
定理 Lex.lt_iff
  条件: [LT ι] [对任意 i, LT (α i)] {a b : Lex (Π₀ i, α i)}
  证明: .rfl
-/
theorem Lex.lt_iff [LT ι] [forall i, LT (α i)] {a b : Lex (Π₀ i, α i)} :
    a < b ↔ exists i, (forall j, j < i -> a j = b j) ∧ a i < b i :=
  .rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Colex.lt_iff` / 定理 `Colex.lt_iff`

English:
theorem Colex.lt_iff
  given: [LT ι] [forall i, LT (α i)] {a b : Colex (Π₀ i, α i)}
  proof: .rfl

中文:
定理 Colex.lt_iff
  条件: [LT ι] [对任意 i, LT (α i)] {a b : Colex (Π₀ i, α i)}
  证明: .rfl
-/
theorem Colex.lt_iff [LT ι] [forall i, LT (α i)] {a b : Colex (Π₀ i, α i)} :
    a < b ↔ exists i, (forall j, i < j -> a j = b j) ∧ a i < b i :=
  .rfl

/--
theorem `lex_lt_of_lt_of_preorder` / 定理 `lex_lt_of_lt_of_preorder`

English:
theorem lex_lt_of_lt_of_preorder
  statement: [forall i, Preorder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i}
  proof: by
  obtain ⟨hle, j, hlt⟩ := Pi.lt_def.1 hlt
  classical
  have : (x.neLocus y : Set ι).WellFoundedOn r := (x.neLocus y).finite_toSet.wellFoundedOn
  obtain ⟨i, hi, hl⟩ := this.has_min { i | x i < y i } ⟨⟨j, mem_neLocus.2 hlt.ne⟩, hlt⟩
  refine ⟨i, fun k hk => ⟨hle k, ?_⟩, hi⟩
  exact of_not_not fun

中文:
定理 lex_lt_of_lt_of_preorder
  结论: [对任意 i, 预序 (α i)] (r) [是Strict序 ι r] {x y : Π₀ i, α i}
  证明: by
  obtain ⟨hle, j, hlt⟩ := Pi.lt_def.1 hlt
  classical
  have : (x.neLocus y : Set ι).WellFoundedOn r := (x.neLocus y).finite_toSet.wellFoundedOn
  obtain ⟨i, hi, hl⟩ := this.has_min { i | x i < y i } ⟨⟨j, mem_neLocus.2 hlt.ne⟩, hlt⟩
  refine ⟨i, fun k hk => ⟨hle k, ?_⟩, hi⟩
  exact of_not_not fun

Depends on / 依赖: Pi.lt_def, WellFoundedOn, classical, finite_toSet, finite_toSet.wellFoundedOn, has_min, hlt.ne, lt_def, lt_of_not_ge, mem_neLocus, neLocus, ne_of_not_le, of_not_not, this.has_min, wellFoundedOn, x.neLocus
-/
theorem lex_lt_of_lt_of_preorder [forall i, Preorder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i}
    (hlt : x < y) : exists i, (forall j, r j i -> x j <= y j ∧ y j <= x j) ∧ x i < y i := by
  obtain ⟨hle, j, hlt⟩ := Pi.lt_def.1 hlt
  classical
  have : (x.neLocus y : Set ι).WellFoundedOn r := (x.neLocus y).finite_toSet.wellFoundedOn
  obtain ⟨i, hi, hl⟩ := this.has_min { i | x i < y i } ⟨⟨j, mem_neLocus.2 hlt.ne⟩, hlt⟩
  refine ⟨i, fun k hk => ⟨hle k, ?_⟩, hi⟩
  exact of_not_not fun h => hl ⟨k, mem_neLocus.2 (ne_of_not_le h).symm⟩ ((hle k).lt_of_not_ge h) hk

/--
theorem `lex_lt_of_lt` / 定理 `lex_lt_of_lt`

English:
theorem lex_lt_of_lt
  statement: [forall i, PartialOrder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i}
  proof: by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder r hlt

中文:
定理 lex_lt_of_lt
  结论: [对任意 i, 偏序 (α i)] (r) [是Strict序 ι r] {x y : Π₀ i, α i}
  证明: by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder r hlt

Depends on / 依赖: Pi.Lex, le_antisymm_iff, lex_lt_of_lt_of_preorder, simp_rw
-/
theorem lex_lt_of_lt [forall i, PartialOrder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i}
    (hlt : x < y) : Pi.Lex r (· < ·) x y := by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder r hlt

/--
theorem `lex_iff_of_unique` / 定理 `lex_iff_of_unique`

English:
theorem lex_iff_of_unique
  given: [Unique ι] [forall i, LT (α i)] {r} [Std.Irrefl r] {x y : Π₀ i, α i}
  proof: Pi.lex_iff_of_unique

中文:
定理 lex_iff_of_unique
  条件: [唯一 ι] [对任意 i, LT (α i)] {r} [Std.Irrefl r] {x y : Π₀ i, α i}
  证明: Pi.lex_iff_of_unique

Depends on / 依赖: Pi.lex_iff_of_unique, lex_iff_of_unique
-/
theorem lex_iff_of_unique [Unique ι] [forall i, LT (α i)] {r} [Std.Irrefl r] {x y : Π₀ i, α i} :
    DFinsupp.Lex r (fun _ => (· < ·)) x y ↔ x default < y default :=
  Pi.lex_iff_of_unique

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Lex.lt_iff_of_unique` / 定理 `Lex.lt_iff_of_unique`

English:
theorem Lex.lt_iff_of_unique
  given: [Unique ι] [forall i, LT (α i)] [Preorder ι] {x y : Lex (Π₀ i, α i)}
  proof: lex_iff_of_unique

中文:
定理 Lex.lt_iff_of_unique
  条件: [唯一 ι] [对任意 i, LT (α i)] [预序 ι] {x y : Lex (Π₀ i, α i)}
  证明: lex_iff_of_unique

Depends on / 依赖: lex_iff_of_unique
-/
theorem Lex.lt_iff_of_unique [Unique ι] [forall i, LT (α i)] [Preorder ι] {x y : Lex (Π₀ i, α i)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique

set_option backward.isDefEq.respectTransparency false in
/--
theorem `colex_lt_iff_of_unique` / 定理 `colex_lt_iff_of_unique`

English:
theorem colex_lt_iff_of_unique
  given: [Unique ι] [forall i, LT (α i)] [Preorder ι] {x y : Colex (Π₀ i, α i)}
  proof: lex_iff_of_unique

中文:
定理 colex_lt_iff_of_unique
  条件: [唯一 ι] [对任意 i, LT (α i)] [预序 ι] {x y : Colex (Π₀ i, α i)}
  证明: lex_iff_of_unique

Depends on / 依赖: lex_iff_of_unique
-/
theorem colex_lt_iff_of_unique [Unique ι] [forall i, LT (α i)] [Preorder ι] {x y : Colex (Π₀ i, α i)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique

variable [LinearOrder ι]

/--
Instance `Lex.isStrictOrder` / 实例 `Lex.isStrictOrder`

English:
instance Lex.isStrictOrder
  signature: [forall i, PartialOrder (α i)]
  body: lt_irrefl (α := Lex (forall i, α i)) _
  trans _ _ _ := lt_trans (α := Lex (forall i, α i))

中文:
实例 Lex.isStrictOrder
  签名: [对任意 i, 偏序 (α i)]
  定义体: lt_irrefl (α := Lex (forall i, α i)) _
  trans _ _ _ := lt_trans (α := Lex (forall i, α i))

Depends on / 依赖: lt_irrefl
-/
instance Lex.isStrictOrder [forall i, PartialOrder (α i)] :
    IsStrictOrder (Lex (Π₀ i, α i)) (· < ·) where
  irrefl _ := lt_irrefl (α := Lex (forall i, α i)) _
  trans _ _ _ := lt_trans (α := Lex (forall i, α i))

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Colex.isStrictOrder` / 实例 `Colex.isStrictOrder`

English:
instance Colex.isStrictOrder
  signature: [forall i, PartialOrder (α i)]
  body: Lex.isStrictOrder (ι := ιᵒᵈ)

中文:
实例 Colex.isStrictOrder
  签名: [对任意 i, 偏序 (α i)]
  定义体: Lex.isStrictOrder (ι := ιᵒᵈ)

Depends on / 依赖: Lex.isStrictOrder, isStrictOrder
-/
instance Colex.isStrictOrder [forall i, PartialOrder (α i)] :
    IsStrictOrder (Colex (Π₀ i, α i)) (· < ·) :=
  Lex.isStrictOrder (ι := ιᵒᵈ)

/--
Instance `Lex.partialOrder` / 实例 `Lex.partialOrder`

English:
instance Lex.partialOrder
  signature: [forall i, PartialOrder (α i)]
  body: ⇑(ofLex x) = ⇑(ofLex y) ∨ x < y
  toLT := instLTLex
  __ := PartialOrder.lift (fun x : Lex (Π₀ i, α i) => toLex (⇑(ofLex x)))
    (DFunLike.coe_injective (F := DFinsupp α))

中文:
实例 Lex.partialOrder
  签名: [对任意 i, 偏序 (α i)]
  定义体: ⇑(ofLex x) = ⇑(ofLex y) ∨ x < y
  toLT := instLTLex
  __ := PartialOrder.lift (fun x : Lex (Π₀ i, α i) => toLex (⇑(ofLex x)))
    (DFunLike.coe_injective (F := DFinsupp α))
-/
instance Lex.partialOrder [forall i, PartialOrder (α i)] : PartialOrder (Lex (Π₀ i, α i)) where
  le x y := ⇑(ofLex x) = ⇑(ofLex y) ∨ x < y
  toLT := instLTLex
  __ := PartialOrder.lift (fun x : Lex (Π₀ i, α i) => toLex (⇑(ofLex x)))
    (DFunLike.coe_injective (F := DFinsupp α))

/--
Instance `Colex.partialOrder` / 实例 `Colex.partialOrder`

English:
instance Colex.partialOrder
  signature: [forall i, PartialOrder (α i)]
  body: ⇑(ofColex x) = ⇑(ofColex y) ∨ x < y
  toLT := instLTColex
  __ := PartialOrder.lift (fun x : Colex (Π₀ i, α i) => toColex (⇑(ofColex x)))
    (DFunLike.coe_injective (F := DFinsupp α))

中文:
实例 Colex.partialOrder
  签名: [对任意 i, 偏序 (α i)]
  定义体: ⇑(ofColex x) = ⇑(ofColex y) ∨ x < y
  toLT := instLTColex
  __ := PartialOrder.lift (fun x : Colex (Π₀ i, α i) => toColex (⇑(ofColex x)))
    (DFunLike.coe_injective (F := DFinsupp α))

Depends on / 依赖: ofColex
-/
instance Colex.partialOrder [forall i, PartialOrder (α i)] : PartialOrder (Colex (Π₀ i, α i)) where
  le x y := ⇑(ofColex x) = ⇑(ofColex y) ∨ x < y
  toLT := instLTColex
  __ := PartialOrder.lift (fun x : Colex (Π₀ i, α i) => toColex (⇑(ofColex x)))
    (DFunLike.coe_injective (F := DFinsupp α))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Lex.le_iff_of_unique` / 定理 `Lex.le_iff_of_unique`

English:
theorem Lex.le_iff_of_unique
  given: [Unique ι] [forall i, PartialOrder (α i)] {x y : Lex (Π₀ i, α i)}
  proof: Pi.lex_le_iff_of_unique

中文:
定理 Lex.le_iff_of_unique
  条件: [唯一 ι] [对任意 i, 偏序 (α i)] {x y : Lex (Π₀ i, α i)}
  证明: Pi.lex_le_iff_of_unique

Depends on / 依赖: Pi.lex_le_iff_of_unique, lex_le_iff_of_unique
-/
theorem Lex.le_iff_of_unique [Unique ι] [forall i, PartialOrder (α i)] {x y : Lex (Π₀ i, α i)} :
    x <= y ↔ x default <= y default :=
  Pi.lex_le_iff_of_unique

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Colex.le_iff_of_unique` / 定理 `Colex.le_iff_of_unique`

English:
theorem Colex.le_iff_of_unique
  given: [Unique ι] [forall i, PartialOrder (α i)] {x y : Colex (Π₀ i, α i)}
  proof: Lex.le_iff_of_unique (ι := ιᵒᵈ)

中文:
定理 Colex.le_iff_of_unique
  条件: [唯一 ι] [对任意 i, 偏序 (α i)] {x y : Colex (Π₀ i, α i)}
  证明: Lex.le_iff_of_unique (ι := ιᵒᵈ)

Depends on / 依赖: Lex.le_iff_of_unique, le_iff_of_unique
-/
theorem Colex.le_iff_of_unique [Unique ι] [forall i, PartialOrder (α i)] {x y : Colex (Π₀ i, α i)} :
    x <= y ↔ x default <= y default :=
  Lex.le_iff_of_unique (ι := ιᵒᵈ)

section LinearOrder

variable [forall i, LinearOrder (α i)]

set_option backward.privateInPublic true in
/--
Definition of `lt_trichotomy_rec` / `lt_trichotomy_rec` 的定义

English:
definition lt_trichotomy_rec
  signature: {P : Lex (Π₀ i, α i) -> Lex (Π₀ i, α i) -> Sort*}
  body: Lex.rec fun f => Lex.rec fun g => match (motive := forall y, (f.neLocus g).min = y -> _) _, rfl with
  | ⊤, h => h_eq (neLocus_eq_empty.mp <| Finset.min_eq_top.mp h)
  | (wit : ι), h => by
    apply (mem_neLocus.mp <| Finset.mem_of_min h).lt_or_gt.by_cases <;> intro hwit
    · exact h_lt ⟨wit, fun j

中文:
定义 lt_trichotomy_rec
  签名: {P : Lex (Π₀ i, α i) -> Lex (Π₀ i, α i) -> 类型层*}
  定义体: Lex.rec fun f => Lex.rec fun g => match (motive := forall y, (f.neLocus g).min = y -> _) _, rfl with
  | ⊤, h => h_eq (neLocus_eq_empty.mp <| Finset.min_eq_top.mp h)
  | (wit : ι), h => by
    apply (mem_neLocus.mp <| Finset.mem_of_min h).lt_or_gt.by_cases <;> intro hwit
    · exact h_lt ⟨wit, fun j
-/
private def lt_trichotomy_rec {P : Lex (Π₀ i, α i) -> Lex (Π₀ i, α i) -> Sort*}
    (h_lt : forall {f g}, toLex f < toLex g -> P (toLex f) (toLex g))
    (h_eq : forall {f g}, toLex f = toLex g -> P (toLex f) (toLex g))
    (h_gt : forall {f g}, toLex g < toLex f -> P (toLex f) (toLex g)) : forall f g, P f g :=
  Lex.rec fun f => Lex.rec fun g => match (motive := forall y, (f.neLocus g).min = y -> _) _, rfl with
  | ⊤, h => h_eq (neLocus_eq_empty.mp <| Finset.min_eq_top.mp h)
  | (wit : ι), h => by
    apply (mem_neLocus.mp <| Finset.mem_of_min h).lt_or_gt.by_cases <;> intro hwit
    · exact h_lt ⟨wit, fun j hj => notMem_neLocus.mp (Finset.notMem_of_lt_min hj h), hwit⟩
    · exact h_gt ⟨wit, fun j hj =>
        notMem_neLocus.mp (Finset.notMem_of_lt_min hj <| by rwa [neLocus_comm]), hwit⟩

/--
Instance `Lex.total_le` / 实例 `Lex.total_le`

English:
instance Lex.total_le
  signature: : @Std.Total (Lex (Π₀ i, α i)) (· <= ·) where
  body: lt_trichotomy_rec (fun h => Or.inl h.le) (fun h => Or.inl h.le) fun h => Or.inr h.le

中文:
实例 Lex.total_le
  签名: : @Std.全 (Lex (Π₀ i, α i)) (· <= ·) where
  定义体: lt_trichotomy_rec (fun h => Or.inl h.le) (fun h => Or.inl h.le) fun h => Or.inr h.le

Depends on / 依赖: Or.inl, Or.inr, h.le, lt_trichotomy_rec
-/
instance Lex.total_le : @Std.Total (Lex (Π₀ i, α i)) (· <= ·) where
  total := lt_trichotomy_rec (fun h => Or.inl h.le) (fun h => Or.inl h.le) fun h => Or.inr h.le

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Colex.total_le` / 实例 `Colex.total_le`

English:
instance Colex.total_le
  signature: : @Std.Total (Colex (Π₀ i, α i)) (· <= ·)
  body: Lex.total_le (ι := ιᵒᵈ)

中文:
实例 Colex.total_le
  签名: : @Std.全 (Colex (Π₀ i, α i)) (· <= ·)
  定义体: Lex.total_le (ι := ιᵒᵈ)

Depends on / 依赖: Lex.total_le, total_le
-/
instance Colex.total_le : @Std.Total (Colex (Π₀ i, α i)) (· <= ·) :=
  Lex.total_le (ι := ιᵒᵈ)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `Lex.decidableLE` / 实例 `Lex.decidableLE`

English:
instance Lex.decidableLE
  signature: : DecidableLE (Lex (Π₀ i, α i))
  body: lt_trichotomy_rec (fun h => isTrue <| Or.inr h)
    (fun h => isTrue <| Or.inl <| congr_arg _ h)
    fun h => isFalse fun h' => lt_irrefl _ (h.trans_le h')

中文:
实例 Lex.decidableLE
  签名: : DecidableLE (Lex (Π₀ i, α i))
  定义体: lt_trichotomy_rec (fun h => isTrue <| Or.inr h)
    (fun h => isTrue <| Or.inl <| congr_arg _ h)
    fun h => isFalse fun h' => lt_irrefl _ (h.trans_le h')

Depends on / 依赖: Or.inl, Or.inr, congr_arg, h.trans_le, isFalse, isTrue, lt_irrefl, lt_trichotomy_rec, trans_le
-/
instance Lex.decidableLE : DecidableLE (Lex (Π₀ i, α i)) :=
  lt_trichotomy_rec (fun h => isTrue <| Or.inr h)
    (fun h => isTrue <| Or.inl <| congr_arg _ h)
    fun h => isFalse fun h' => lt_irrefl _ (h.trans_le h')

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Colex.decidableLE` / 实例 `Colex.decidableLE`

English:
instance Colex.decidableLE
  signature: : DecidableLE (Colex (Π₀ i, α i))
  body: Lex.decidableLE (ι := ιᵒᵈ)

中文:
实例 Colex.decidableLE
  签名: : DecidableLE (Colex (Π₀ i, α i))
  定义体: Lex.decidableLE (ι := ιᵒᵈ)

Depends on / 依赖: Lex.decidableLE, decidableLE
-/
instance Colex.decidableLE : DecidableLE (Colex (Π₀ i, α i)) :=
  Lex.decidableLE (ι := ιᵒᵈ)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `Lex.decidableLT` / 实例 `Lex.decidableLT`

English:
instance Lex.decidableLT
  signature: : DecidableLT (Lex (Π₀ i, α i))
  body: lt_trichotomy_rec (fun h => isTrue h) (fun h => isFalse h.not_lt) fun h => isFalse h.asymm

中文:
实例 Lex.decidableLT
  签名: : DecidableLT (Lex (Π₀ i, α i))
  定义体: lt_trichotomy_rec (fun h => isTrue h) (fun h => isFalse h.not_lt) fun h => isFalse h.asymm

Depends on / 依赖: h.asymm, h.not_lt, isFalse, isTrue, lt_trichotomy_rec, not_lt
-/
instance Lex.decidableLT : DecidableLT (Lex (Π₀ i, α i)) :=
  lt_trichotomy_rec (fun h => isTrue h) (fun h => isFalse h.not_lt) fun h => isFalse h.asymm

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Colex.decidableLT` / 实例 `Colex.decidableLT`

English:
instance Colex.decidableLT
  signature: : DecidableLT (Colex (Π₀ i, α i))
  body: Lex.decidableLT (ι := ιᵒᵈ)

中文:
实例 Colex.decidableLT
  签名: : DecidableLT (Colex (Π₀ i, α i))
  定义体: Lex.decidableLT (ι := ιᵒᵈ)

Depends on / 依赖: Lex.decidableLT, decidableLT
-/
instance Colex.decidableLT : DecidableLT (Colex (Π₀ i, α i)) :=
  Lex.decidableLT (ι := ιᵒᵈ)

/--
Instance `Lex.linearOrder` / 实例 `Lex.linearOrder`

English:
instance Lex.linearOrder
  signature: : LinearOrder (Lex (Π₀ i, α i)) where
  body: total_of _
  toDecidableLT := decidableLT
  toDecidableLE := decidableLE

中文:
实例 Lex.linearOrder
  签名: : 线性序 (Lex (Π₀ i, α i)) where
  定义体: total_of _
  toDecidableLT := decidableLT
  toDecidableLE := decidableLE

Depends on / 依赖: total_of
-/
instance Lex.linearOrder : LinearOrder (Lex (Π₀ i, α i)) where
  le_total := total_of _
  toDecidableLT := decidableLT
  toDecidableLE := decidableLE

/--
Instance `Colex.linearOrder` / 实例 `Colex.linearOrder`

English:
instance Colex.linearOrder
  signature: : LinearOrder (Colex (Π₀ i, α i)) where
  body: total_of _
  toDecidableLT := decidableLT
  toDecidableLE := decidableLE

中文:
实例 Colex.linearOrder
  签名: : 线性序 (Colex (Π₀ i, α i)) where
  定义体: total_of _
  toDecidableLT := decidableLT
  toDecidableLE := decidableLE

Depends on / 依赖: total_of
-/
instance Colex.linearOrder : LinearOrder (Colex (Π₀ i, α i)) where
  le_total := total_of _
  toDecidableLT := decidableLT
  toDecidableLE := decidableLE

end LinearOrder

variable [forall i, PartialOrder (α i)]

/--
theorem `toLex_monotone` / 定理 `toLex_monotone`

English:
theorem toLex_monotone
  statement: Monotone (@toLex (Π₀ i, α i))
  proof: by
  intro a b h
  refine le_of_lt_or_eq (or_iff_not_imp_right.2 fun hne => ?_)
  classical
  exact ⟨Finset.min' _ (nonempty_neLocus_iff.2 hne),
    fun j hj => notMem_neLocus.1 fun h => (Finset.min'_le _ _ h).not_gt hj,
    (h _).lt_of_ne (mem_neLocus.1 <| Finset.min'_mem _ _)⟩

中文:
定理 toLex_monotone
  结论: 递增 (@toLex (Π₀ i, α i))
  证明: by
  intro a b h
  refine le_of_lt_or_eq (or_iff_not_imp_right.2 fun hne => ?_)
  classical
  exact ⟨Finset.min' _ (nonempty_neLocus_iff.2 hne),
    fun j hj => notMem_neLocus.1 fun h => (Finset.min'_le _ _ h).not_gt hj,
    (h _).lt_of_ne (mem_neLocus.1 <| Finset.min'_mem _ _)⟩

Depends on / 依赖: Finset, Finset.min, _mem, classical, le_of_lt_or_eq, lt_of_ne, mem_neLocus, nonempty_neLocus_iff, notMem_neLocus, not_gt, or_iff_not_imp_right
-/
theorem toLex_monotone : Monotone (@toLex (Π₀ i, α i)) := by
  intro a b h
  refine le_of_lt_or_eq (or_iff_not_imp_right.2 fun hne => ?_)
  classical
  exact ⟨Finset.min' _ (nonempty_neLocus_iff.2 hne),
    fun j hj => notMem_neLocus.1 fun h => (Finset.min'_le _ _ h).not_gt hj,
    (h _).lt_of_ne (mem_neLocus.1 <| Finset.min'_mem _ _)⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toColex_monotone` / 定理 `toColex_monotone`

English:
theorem toColex_monotone
  statement: Monotone (@toColex (Π₀ i, α i))
  proof: toLex_monotone (ι := ιᵒᵈ)

中文:
定理 toColex_monotone
  结论: 递增 (@toColex (Π₀ i, α i))
  证明: toLex_monotone (ι := ιᵒᵈ)

Depends on / 依赖: toLex_monotone
-/
theorem toColex_monotone : Monotone (@toColex (Π₀ i, α i)) :=
  toLex_monotone (ι := ιᵒᵈ)

end Zero

section Covariants

variable [LinearOrder ι] [forall i, AddMonoid (α i)] [forall i, LinearOrder (α i)]

/-! We are about to sneak in a hypothesis that might appear to be too strong.
We assume `AddLeftStrictMono` (covariant with *strict* inequality `<`) also when proving the one
with the *weak* inequality `≤`. This is actually necessary: addition on `Lex (Π₀ i, α i)` may fail
to be monotone, when it is "just" monotone on `α i`. -/

section Left

variable [forall i, AddLeftStrictMono (α i)]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `Lex.addLeftStrictMono` / 实例 `Lex.addLeftStrictMono`

English:
instance Lex.addLeftStrictMono
  signature: : AddLeftStrictMono (Lex (Π₀ i, α i))
  body: ⟨fun _ _ _ ⟨a, lta, ha⟩ => ⟨a, fun j ja => congr_arg _ (lta j ja), by dsimp; gcongr⟩⟩

中文:
实例 Lex.addLeftStrictMono
  签名: : AddLeftStrictMono (Lex (Π₀ i, α i))
  定义体: ⟨fun _ _ _ ⟨a, lta, ha⟩ => ⟨a, fun j ja => congr_arg _ (lta j ja), by dsimp; gcongr⟩⟩

Depends on / 依赖: congr_arg
-/
instance Lex.addLeftStrictMono : AddLeftStrictMono (Lex (Π₀ i, α i)) :=
  ⟨fun _ _ _ ⟨a, lta, ha⟩ => ⟨a, fun j ja => congr_arg _ (lta j ja), by dsimp; gcongr⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Colex.addLeftStrictMono` / 实例 `Colex.addLeftStrictMono`

English:
instance Colex.addLeftStrictMono
  signature: : AddLeftStrictMono (Colex (Π₀ i, α i))
  body: Lex.addLeftStrictMono (ι := ιᵒᵈ)

中文:
实例 Colex.addLeftStrictMono
  签名: : AddLeftStrictMono (Colex (Π₀ i, α i))
  定义体: Lex.addLeftStrictMono (ι := ιᵒᵈ)

Depends on / 依赖: Lex.addLeftStrictMono, addLeftStrictMono
-/
instance Colex.addLeftStrictMono : AddLeftStrictMono (Colex (Π₀ i, α i)) :=
  Lex.addLeftStrictMono (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Lex.addLeftMono` / 实例 `Lex.addLeftMono`

English:
instance Lex.addLeftMono
  signature: : AddLeftMono (Lex (Π₀ i, α i))
  body: addLeftMono_of_addLeftStrictMono _

中文:
实例 Lex.addLeftMono
  签名: : AddLeftMono (Lex (Π₀ i, α i))
  定义体: addLeftMono_of_addLeftStrictMono _

Depends on / 依赖: addLeftMono_of_addLeftStrictMono
-/
instance Lex.addLeftMono : AddLeftMono (Lex (Π₀ i, α i)) :=
  addLeftMono_of_addLeftStrictMono _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Colex.addLeftMono` / 实例 `Colex.addLeftMono`

English:
instance Colex.addLeftMono
  signature: : AddLeftMono (Colex (Π₀ i, α i))
  body: Lex.addLeftMono (ι := ιᵒᵈ)

中文:
实例 Colex.addLeftMono
  签名: : AddLeftMono (Colex (Π₀ i, α i))
  定义体: Lex.addLeftMono (ι := ιᵒᵈ)

Depends on / 依赖: Lex.addLeftMono, addLeftMono
-/
instance Colex.addLeftMono : AddLeftMono (Colex (Π₀ i, α i)) :=
  Lex.addLeftMono (ι := ιᵒᵈ)

end Left

section Right

variable [forall i, AddRightStrictMono (α i)]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `Lex.addRightStrictMono` / 实例 `Lex.addRightStrictMono`

English:
instance Lex.addRightStrictMono
  signature: : AddRightStrictMono (Lex (Π₀ i, α i))
  body: ⟨fun f _ _ ⟨a, lta, ha⟩ =>
    ⟨a, fun j ja => congr_arg (· + ofLex f j) (lta j ja), by dsimp; gcongr⟩⟩

中文:
实例 Lex.addRightStrictMono
  签名: : AddRightStrictMono (Lex (Π₀ i, α i))
  定义体: ⟨fun f _ _ ⟨a, lta, ha⟩ =>
    ⟨a, fun j ja => congr_arg (· + ofLex f j) (lta j ja), by dsimp; gcongr⟩⟩

Depends on / 依赖: congr_arg
-/
instance Lex.addRightStrictMono : AddRightStrictMono (Lex (Π₀ i, α i)) :=
  ⟨fun f _ _ ⟨a, lta, ha⟩ =>
    ⟨a, fun j ja => congr_arg (· + ofLex f j) (lta j ja), by dsimp; gcongr⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Colex.addRightStrictMono` / 实例 `Colex.addRightStrictMono`

English:
instance Colex.addRightStrictMono
  signature: : AddRightStrictMono (Colex (Π₀ i, α i))
  body: Lex.addRightStrictMono (ι := ιᵒᵈ)

中文:
实例 Colex.addRightStrictMono
  签名: : AddRightStrictMono (Colex (Π₀ i, α i))
  定义体: Lex.addRightStrictMono (ι := ιᵒᵈ)

Depends on / 依赖: Lex.addRightStrictMono, addRightStrictMono
-/
instance Colex.addRightStrictMono : AddRightStrictMono (Colex (Π₀ i, α i)) :=
  Lex.addRightStrictMono (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Lex.addRightMono` / 实例 `Lex.addRightMono`

English:
instance Lex.addRightMono
  signature: : AddRightMono (Lex (Π₀ i, α i))
  body: addRightMono_of_addRightStrictMono _

中文:
实例 Lex.addRightMono
  签名: : AddRightMono (Lex (Π₀ i, α i))
  定义体: addRightMono_of_addRightStrictMono _

Depends on / 依赖: addRightMono_of_addRightStrictMono
-/
instance Lex.addRightMono : AddRightMono (Lex (Π₀ i, α i)) :=
  addRightMono_of_addRightStrictMono _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Colex.addRightMono` / 实例 `Colex.addRightMono`

English:
instance Colex.addRightMono
  signature: : AddRightMono (Colex (Π₀ i, α i))
  body: Lex.addRightMono (ι := ιᵒᵈ)

中文:
实例 Colex.addRightMono
  签名: : AddRightMono (Colex (Π₀ i, α i))
  定义体: Lex.addRightMono (ι := ιᵒᵈ)

Depends on / 依赖: Lex.addRightMono, addRightMono
-/
instance Colex.addRightMono : AddRightMono (Colex (Π₀ i, α i)) :=
  Lex.addRightMono (ι := ιᵒᵈ)

end Right

end Covariants

section OrderedAddMonoid

variable [LinearOrder ι]

/--
Instance `Lex.orderBot` / 实例 `Lex.orderBot`

English:
instance Lex.orderBot
  signature: [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
  body: 0
  bot_le _ := DFinsupp.toLex_monotone bot_le

中文:
实例 Lex.orderBot
  签名: [对任意 i, 加法交换幺半群 (α i)] [对任意 i, 偏序 (α i)]
  定义体: 0
  bot_le _ := DFinsupp.toLex_monotone bot_le
-/
instance Lex.orderBot [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
    [forall i, IsBotZeroClass (α i)] :
    OrderBot (Lex (Π₀ i, α i)) where
  bot := 0
  bot_le _ := DFinsupp.toLex_monotone bot_le

/--
Instance `Lex.isBotZeroClass` / 实例 `Lex.isBotZeroClass`

English:
instance Lex.isBotZeroClass
  signature: [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
  body: isBot_bot

中文:
实例 Lex.isBotZeroClass
  签名: [对任意 i, 加法交换幺半群 (α i)] [对任意 i, 偏序 (α i)]
  定义体: isBot_bot

Depends on / 依赖: isBot_bot
-/
instance Lex.isBotZeroClass [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
    [forall i, IsBotZeroClass (α i)] :
    IsBotZeroClass (Lex (Π₀ i, α i)) where
  isBot_zero := isBot_bot

/--
Instance `Colex.orderBot` / 实例 `Colex.orderBot`

English:
instance Colex.orderBot
  signature: [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
  body: 0
  bot_le _ := DFinsupp.toColex_monotone bot_le

中文:
实例 Colex.orderBot
  签名: [对任意 i, 加法交换幺半群 (α i)] [对任意 i, 偏序 (α i)]
  定义体: 0
  bot_le _ := DFinsupp.toColex_monotone bot_le
-/
instance Colex.orderBot [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
    [forall i, IsBotZeroClass (α i)] :
    OrderBot (Colex (Π₀ i, α i)) where
  bot := 0
  bot_le _ := DFinsupp.toColex_monotone bot_le

/--
Instance `Colex.isBotZeroClass` / 实例 `Colex.isBotZeroClass`

English:
instance Colex.isBotZeroClass
  signature: [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
  body: isBot_bot

中文:
实例 Colex.isBotZeroClass
  签名: [对任意 i, 加法交换幺半群 (α i)] [对任意 i, 偏序 (α i)]
  定义体: isBot_bot

Depends on / 依赖: isBot_bot
-/
instance Colex.isBotZeroClass [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
    [forall i, IsBotZeroClass (α i)] :
    IsBotZeroClass (Colex (Π₀ i, α i)) where
  isBot_zero := isBot_bot

/--
Instance `Lex.isOrderedCancelAddMonoid` / 实例 `Lex.isOrderedCancelAddMonoid`

English:
instance Lex.isOrderedCancelAddMonoid
  signature: [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
  body: add_le_add_left (α := Lex (forall i, α i)) h _
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left (α := Lex (forall i, α i))

中文:
实例 Lex.isOrderedCancelAddMonoid
  签名: [对任意 i, 加法交换幺半群 (α i)] [对任意 i, 偏序 (α i)]
  定义体: add_le_add_left (α := Lex (forall i, α i)) h _
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left (α := Lex (forall i, α i))

Depends on / 依赖: add_le_add_left
-/
instance Lex.isOrderedCancelAddMonoid [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
    [forall i, IsOrderedCancelAddMonoid (α i)] :
    IsOrderedCancelAddMonoid (Lex (Π₀ i, α i)) where
  add_le_add_left _ _ h _ := add_le_add_left (α := Lex (forall i, α i)) h _
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left (α := Lex (forall i, α i))

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Colex.isOrderedCancelAddMonoid` / 实例 `Colex.isOrderedCancelAddMonoid`

English:
instance Colex.isOrderedCancelAddMonoid
  signature: [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
  body: Lex.isOrderedCancelAddMonoid (ι := ιᵒᵈ)

中文:
实例 Colex.isOrderedCancelAddMonoid
  签名: [对任意 i, 加法交换幺半群 (α i)] [对任意 i, 偏序 (α i)]
  定义体: Lex.isOrderedCancelAddMonoid (ι := ιᵒᵈ)

Depends on / 依赖: Lex.isOrderedCancelAddMonoid, isOrderedCancelAddMonoid
-/
instance Colex.isOrderedCancelAddMonoid [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
    [forall i, IsOrderedCancelAddMonoid (α i)] :
    IsOrderedCancelAddMonoid (Colex (Π₀ i, α i)) :=
  Lex.isOrderedCancelAddMonoid (ι := ιᵒᵈ)

/--
Instance `Lex.isOrderedAddMonoid` / 实例 `Lex.isOrderedAddMonoid`

English:
instance Lex.isOrderedAddMonoid
  signature: [forall i, AddCommGroup (α i)] [forall i, PartialOrder (α i)]
  body: add_le_add_left

中文:
实例 Lex.isOrderedAddMonoid
  签名: [对任意 i, 加法交换群 (α i)] [对任意 i, 偏序 (α i)]
  定义体: add_le_add_left

Depends on / 依赖: add_le_add_left
-/
instance Lex.isOrderedAddMonoid [forall i, AddCommGroup (α i)] [forall i, PartialOrder (α i)]
    [forall i, IsOrderedAddMonoid (α i)] :
    IsOrderedAddMonoid (Lex (Π₀ i, α i)) where
  add_le_add_left _ _ := add_le_add_left

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Colex.isOrderedAddMonoid` / 实例 `Colex.isOrderedAddMonoid`

English:
instance Colex.isOrderedAddMonoid
  signature: [forall i, AddCommGroup (α i)] [forall i, PartialOrder (α i)]
  body: Lex.isOrderedAddMonoid (ι := ιᵒᵈ)

中文:
实例 Colex.isOrderedAddMonoid
  签名: [对任意 i, 加法交换群 (α i)] [对任意 i, 偏序 (α i)]
  定义体: Lex.isOrderedAddMonoid (ι := ιᵒᵈ)

Depends on / 依赖: Lex.isOrderedAddMonoid, isOrderedAddMonoid
-/
instance Colex.isOrderedAddMonoid [forall i, AddCommGroup (α i)] [forall i, PartialOrder (α i)]
    [forall i, IsOrderedAddMonoid (α i)] :
    IsOrderedAddMonoid (Colex (Π₀ i, α i)) :=
  Lex.isOrderedAddMonoid (ι := ιᵒᵈ)

end OrderedAddMonoid

end DFinsupp
