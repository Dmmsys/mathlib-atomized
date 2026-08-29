/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Order.Lex
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.Common

/-!
# Lexicographic order on Pi types

This file defines the lexicographic and colexicographic orders for Pi types.

* In the lexicographic order, `a` is less than `b` if `a i = b i` for all `i` up to some point
  `k`, and `a k < b k`.
* In the colexicographic order, `a` is less than `b` if `a i = b i` for all `i` above some point
  `k`, and `a k < b k`.

## Notation

* `Πₗ i, α i`: Pi type equipped with the lexicographic order. Type synonym of `Π i, α i`.

## See also

Related files are:
* `Data.Finset.Colex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Sigma.Order`: Lexicographic order on `Σₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σₗ' i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.
-/

@[expose] public section

assert_not_exists Monoid

variable {ι : Type*} {β : ι -> Type*} (r : ι -> ι -> Prop) (s : forall {i}, β i -> β i -> Prop)

namespace Pi

/--
Definition of `Lex` / `Lex` 的定义

English:
definition Lex
  signature: (x y : forall i, β i)
  body: exists i, (forall j, r j i -> x j = y j) ∧ s (x i) (y i)

中文:
定义 Lex
  签名: (x y : 对任意 i, β i)
  定义体: exists i, (forall j, r j i -> x j = y j) ∧ s (x i) (y i)
-/
protected def Lex (x y : forall i, β i) : Prop :=
  exists i, (forall j, r j i -> x j = y j) ∧ s (x i) (y i)

/- This unfortunately results in a type that isn't delta-reduced, so we keep the notation out of the
basic API, just in case -/
/-- The notation `Πₗ i, α i` refers to a pi type equipped with the lexicographic order. -/
notation3 (prettyPrint := false) "Πₗ " (...) ", " r:(scoped p => Lex (forall i, p i)) => r

/--
theorem `lex_lt_of_lt_of_preorder` / 定理 `lex_lt_of_lt_of_preorder`

English:
theorem lex_lt_of_lt_of_preorder
  statement: [forall i, Preorder (β i)] {r} (hwf : WellFounded r) {x y : forall i, β i}
  proof: let h' := Pi.lt_def.1 hlt
  let ⟨i, hi, hl⟩ := hwf.has_min {i | x i < y i} h'.2
  ⟨i, fun j hj => ⟨h'.1 j, not_not.1 fun h => hl j (lt_of_le_not_ge (h'.1 j) h) hj⟩, hi⟩

中文:
定理 lex_lt_of_lt_of_preorder
  结论: [对任意 i, 预序 (β i)] {r} (hwf : 良基 r) {x y : 对任意 i, β i}
  证明: let h' := Pi.lt_def.1 hlt
  let ⟨i, hi, hl⟩ := hwf.has_min {i | x i < y i} h'.2
  ⟨i, fun j hj => ⟨h'.1 j, not_not.1 fun h => hl j (lt_of_le_not_ge (h'.1 j) h) hj⟩, hi⟩

Depends on / 依赖: Pi.lt_def, has_min, hwf.has_min, lt_def, lt_of_le_not_ge, not_not
-/
theorem lex_lt_of_lt_of_preorder [forall i, Preorder (β i)] {r} (hwf : WellFounded r) {x y : forall i, β i}
    (hlt : x < y) : exists i, (forall j, r j i -> x j <= y j ∧ y j <= x j) ∧ x i < y i :=
  let h' := Pi.lt_def.1 hlt
  let ⟨i, hi, hl⟩ := hwf.has_min {i | x i < y i} h'.2
  ⟨i, fun j hj => ⟨h'.1 j, not_not.1 fun h => hl j (lt_of_le_not_ge (h'.1 j) h) hj⟩, hi⟩

/--
theorem `lex_lt_of_lt` / 定理 `lex_lt_of_lt`

English:
theorem lex_lt_of_lt
  statement: [forall i, PartialOrder (β i)] {r} (hwf : WellFounded r) {x y : forall i, β i}
  proof: by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder hwf hlt

中文:
定理 lex_lt_of_lt
  结论: [对任意 i, 偏序 (β i)] {r} (hwf : 良基 r) {x y : 对任意 i, β i}
  证明: by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder hwf hlt

Depends on / 依赖: Pi.Lex, le_antisymm_iff, lex_lt_of_lt_of_preorder, simp_rw
-/
theorem lex_lt_of_lt [forall i, PartialOrder (β i)] {r} (hwf : WellFounded r) {x y : forall i, β i}
    (hlt : x < y) : Pi.Lex r (· < ·) x y := by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder hwf hlt

/--
theorem `lex_iff_of_unique` / 定理 `lex_iff_of_unique`

English:
theorem lex_iff_of_unique
  given: [Unique ι] [forall i, LT (β i)] {r} [Std.Irrefl r] {x y : forall i, β i}
  proof: by
  simp [Pi.Lex, Unique.forall_iff, Unique.exists_iff, irrefl]

中文:
定理 lex_iff_of_unique
  条件: [唯一 ι] [对任意 i, LT (β i)] {r} [Std.Irrefl r] {x y : 对任意 i, β i}
  证明: by
  simp [Pi.Lex, Unique.forall_iff, Unique.exists_iff, irrefl]

Depends on / 依赖: Pi.Lex, Unique, Unique.exists_iff, Unique.forall_iff, exists_iff, forall_iff, irrefl
-/
theorem lex_iff_of_unique [Unique ι] [forall i, LT (β i)] {r} [Std.Irrefl r] {x y : forall i, β i} :
    Pi.Lex r (· < ·) x y ↔ x default < y default := by
  simp [Pi.Lex, Unique.forall_iff, Unique.exists_iff, irrefl]

/--
theorem `trichotomous_lex` / 定理 `trichotomous_lex`

English:
theorem trichotomous_lex
  given: [forall i, Std.Trichotomous (α := β i) s] (wf : WellFounded r)
  proof: { trichotomous a b hab hba := by
      by_contra! h
      rw [Function.ne_iff] at h
      let i := wf.min {i | a i != b i} h
      have hri j (hr : r j i) : a j = b j := not_not.mp (fun h => wf.not_lt_min _ (by grind) hr)
      have := Std.Trichotomous.trichotomous (a i) (b i) (hab ⟨i, hri, ·⟩)
exac

中文:
定理 trichotomous_lex
  条件: [对任意 i, Std.三歧 (α := β i) s] (wf : 良基 r)
  证明: { trichotomous a b hab hba := by
      by_contra! h
      rw [Function.ne_iff] at h
      let i := wf.min {i | a i != b i} h
      have hri j (hr : r j i) : a j = b j := not_not.mp (fun h => wf.not_lt_min _ (by grind) hr)
      have := Std.Trichotomous.trichotomous (a i) (b i) (hab ⟨i, hri, ·⟩)
exac

Depends on / 依赖: WellFounded
-/
theorem trichotomous_lex [forall i, Std.Trichotomous (α := β i) s] (wf : WellFounded r) :
    Std.Trichotomous (Pi.Lex r @s) :=
  { trichotomous a b hab hba := by
      by_contra! h
      rw [Function.ne_iff] at h
      let i := wf.min {i | a i != b i} h
      have hri j (hr : r j i) : a j = b j := not_not.mp (fun h => wf.not_lt_min _ (by grind) hr)
      have := Std.Trichotomous.trichotomous (a i) (b i) (hab ⟨i, hri, ·⟩)
exact hba ⟨i, (hri · · |>.symm), Not.imp_symm this wf.min_mem {i | a i != b i} h⟩ }

@[deprecated (since := "2026-01-24")] alias isTrichotomous_lex := trichotomous_lex

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: ι] [forall a, LT (β a)] : LT (Lex (forall i, β i))
  body: id ⟨Pi.Lex (· < ·) (· < ·)⟩

中文:
实例 [LT
  签名: ι] [对任意 a, LT (β a)] : LT (Lex (对任意 i, β i))
  定义体: id ⟨Pi.Lex (· < ·) (· < ·)⟩

Depends on / 依赖: Pi.Lex
-/
instance [LT ι] [forall a, LT (β a)] : LT (Lex (forall i, β i)) :=
  id ⟨Pi.Lex (· < ·) (· < ·)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: ι] [forall a, LT (β a)] : LT (Colex (forall i, β i))
  body: id ⟨Pi.Lex (· > ·) (· < ·)⟩

中文:
实例 [LT
  签名: ι] [对任意 a, LT (β a)] : LT (Colex (对任意 i, β i))
  定义体: id ⟨Pi.Lex (· > ·) (· < ·)⟩

Depends on / 依赖: Pi.Lex
-/
instance [LT ι] [forall a, LT (β a)] : LT (Colex (forall i, β i)) :=
  id ⟨Pi.Lex (· > ·) (· < ·)⟩

-- If `Lex` and `Colex` are ever made into one-field structures, we need a `CoeFun` instance.
-- This will make `x i` syntactically equal to `ofLex x i` for `x : Πₗ i, α i`, thus making
-- the following theorems redundant.

/--
theorem `toLex_apply` / 定理 `toLex_apply`

English:
theorem toLex_apply
  given: (x : forall i, β i) (i : ι)
  statement: toLex x i = x i
  proof: rfl

中文:
定理 toLex_apply
  条件: (x : 对任意 i, β i) (i : ι)
  结论: toLex x i = x i
  证明: rfl
-/
@[simp] theorem toLex_apply (x : forall i, β i) (i : ι) : toLex x i = x i := rfl
/--
theorem `ofLex_apply` / 定理 `ofLex_apply`

English:
theorem ofLex_apply
  given: (x : Lex (forall i, β i)) (i : ι)
  statement: ofLex x i = x i
  proof: rfl

中文:
定理 ofLex_apply
  条件: (x : Lex (对任意 i, β i)) (i : ι)
  结论: ofLex x i = x i
  证明: rfl
-/
@[simp] theorem ofLex_apply (x : Lex (forall i, β i)) (i : ι) : ofLex x i = x i := rfl

/--
theorem `toColex_apply` / 定理 `toColex_apply`

English:
theorem toColex_apply
  given: (x : forall i, β i) (i : ι)
  statement: toColex x i = x i
  proof: rfl

中文:
定理 toColex_apply
  条件: (x : 对任意 i, β i) (i : ι)
  结论: toColex x i = x i
  证明: rfl
-/
@[simp] theorem toColex_apply (x : forall i, β i) (i : ι) : toColex x i = x i := rfl
/--
theorem `ofColex_apply` / 定理 `ofColex_apply`

English:
theorem ofColex_apply
  given: (x : Colex (forall i, β i)) (i : ι)
  statement: ofColex x i = x i
  proof: rfl

中文:
定理 ofColex_apply
  条件: (x : Colex (对任意 i, β i)) (i : ι)
  结论: ofColex x i = x i
  证明: rfl
-/
@[simp] theorem ofColex_apply (x : Colex (forall i, β i)) (i : ι) : ofColex x i = x i := rfl

/--
theorem `Lex.lt_iff_of_unique` / 定理 `Lex.lt_iff_of_unique`

English:
theorem Lex.lt_iff_of_unique
  given: [Unique ι] [forall i, LT (β i)] [Preorder ι] {x y : Lex (forall i, β i)}
  proof: lex_iff_of_unique

中文:
定理 Lex.lt_iff_of_unique
  条件: [唯一 ι] [对任意 i, LT (β i)] [预序 ι] {x y : Lex (对任意 i, β i)}
  证明: lex_iff_of_unique
-/
theorem Lex.lt_iff_of_unique [Unique ι] [forall i, LT (β i)] [Preorder ι] {x y : Lex (forall i, β i)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique

/--
theorem `Colex.lt_iff_of_unique` / 定理 `Colex.lt_iff_of_unique`

English:
theorem Colex.lt_iff_of_unique
  given: [Unique ι] [forall i, LT (β i)] [Preorder ι] {x y : Colex (forall i, β i)}
  proof: lex_iff_of_unique

中文:
定理 Colex.lt_iff_of_unique
  条件: [唯一 ι] [对任意 i, LT (β i)] [预序 ι] {x y : Colex (对任意 i, β i)}
  证明: lex_iff_of_unique
-/
theorem Colex.lt_iff_of_unique [Unique ι] [forall i, LT (β i)] [Preorder ι] {x y : Colex (forall i, β i)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique

/--
Instance `Lex.isStrictOrder` / 实例 `Lex.isStrictOrder`

English:
instance Lex.isStrictOrder
  signature: [LinearOrder ι] [forall a, PartialOrder (β a)]
  body: fun a ⟨k, _, hk₂⟩ => lt_irrefl (a k) hk₂
  trans := by
    rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩
    rcases lt_trichotomy N₁ N₂ with (H | rfl | H)
    exacts [⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ <| hj.trans H), lt_N₂ _ H ▸ a_lt_b⟩,
      ⟨N₁, fun j hj => (lt_N₁ _ hj).trans (l

中文:
实例 Lex.isStrictOrder
  签名: [线性序 ι] [对任意 a, 偏序 (β a)]
  定义体: fun a ⟨k, _, hk₂⟩ => lt_irrefl (a k) hk₂
  trans := by
    rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩
    rcases lt_trichotomy N₁ N₂ with (H | rfl | H)
    exacts [⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ <| hj.trans H), lt_N₂ _ H ▸ a_lt_b⟩,
      ⟨N₁, fun j hj => (lt_N₁ _ hj).trans (l
-/
instance Lex.isStrictOrder [LinearOrder ι] [forall a, PartialOrder (β a)] :
    IsStrictOrder (Lex (forall i, β i)) (· < ·) where
  irrefl := fun a ⟨k, _, hk₂⟩ => lt_irrefl (a k) hk₂
  trans := by
    rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩
    rcases lt_trichotomy N₁ N₂ with (H | rfl | H)
    exacts [⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ <| hj.trans H), lt_N₂ _ H ▸ a_lt_b⟩,
      ⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ hj), a_lt_b.trans b_lt_c⟩,
      ⟨N₂, fun j hj => (lt_N₁ _ (hj.trans H)).trans (lt_N₂ _ hj), (lt_N₁ _ H).symm ▸ b_lt_c⟩]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `Colex.isStrictOrder` / 实例 `Colex.isStrictOrder`

English:
instance Colex.isStrictOrder
  signature: [LinearOrder ι] [forall a, PartialOrder (β a)]
  body: Lex.isStrictOrder (ι := ιᵒᵈ)

中文:
实例 Colex.isStrictOrder
  签名: [线性序 ι] [对任意 a, 偏序 (β a)]
  定义体: Lex.isStrictOrder (ι := ιᵒᵈ)
-/
instance Colex.isStrictOrder [LinearOrder ι] [forall a, PartialOrder (β a)] :
    IsStrictOrder (Colex (forall i, β i)) (· < ·) :=
  Lex.isStrictOrder (ι := ιᵒᵈ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: ι] [forall a, PartialOrder (β a)] : PartialOrder (Lex (forall i, β i))
  body: partialOrderOfSO (· < ·)

中文:
实例 [线性序
  签名: ι] [对任意 a, 偏序 (β a)] : 偏序 (Lex (对任意 i, β i))
  定义体: partialOrderOfSO (· < ·)

Depends on / 依赖: partialOrderOfSO
-/
instance [LinearOrder ι] [forall a, PartialOrder (β a)] : PartialOrder (Lex (forall i, β i)) :=
  partialOrderOfSO (· < ·)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: ι] [forall a, PartialOrder (β a)] : PartialOrder (Colex (forall i, β i))
  body: partialOrderOfSO (· < ·)

中文:
实例 [线性序
  签名: ι] [对任意 a, 偏序 (β a)] : 偏序 (Colex (对任意 i, β i))
  定义体: partialOrderOfSO (· < ·)

Depends on / 依赖: partialOrderOfSO
-/
instance [LinearOrder ι] [forall a, PartialOrder (β a)] : PartialOrder (Colex (forall i, β i)) :=
  partialOrderOfSO (· < ·)

/--
Instance `Lex.linearOrder` / 实例 `Lex.linearOrder`

English:
instance Lex.linearOrder
  signature: [LinearOrder ι] [WellFoundedLT ι]
  body: @linearOrderOfSTO (Πₗ i, β i) (· < ·)
    { trichotomous := (trichotomous_lex _ _ IsWellFounded.wf).1 } (Classical.decRel _)

中文:
实例 Lex.linearOrder
  签名: [线性序 ι] [WellFoundedLT ι]
  定义体: @linearOrderOfSTO (Πₗ i, β i) (· < ·)
    { trichotomous := (trichotomous_lex _ _ IsWellFounded.wf).1 } (Classical.decRel _)
-/
noncomputable instance Lex.linearOrder [LinearOrder ι] [WellFoundedLT ι]
    [forall a, LinearOrder (β a)] : LinearOrder (Lex (forall i, β i)) :=
  @linearOrderOfSTO (Πₗ i, β i) (· < ·)
    { trichotomous := (trichotomous_lex _ _ IsWellFounded.wf).1 } (Classical.decRel _)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `Colex.linearOrder` / 实例 `Colex.linearOrder`

English:
instance Colex.linearOrder
  signature: [LinearOrder ι] [WellFoundedGT ι]
  body: Lex.linearOrder (ι := ιᵒᵈ)

中文:
实例 Colex.linearOrder
  签名: [线性序 ι] [WellFoundedGT ι]
  定义体: Lex.linearOrder (ι := ιᵒᵈ)
-/
noncomputable instance Colex.linearOrder [LinearOrder ι] [WellFoundedGT ι]
    [forall a, LinearOrder (β a)] : LinearOrder (Colex (forall i, β i)) :=
  Lex.linearOrder (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lex_le_iff_of_unique` / 定理 `lex_le_iff_of_unique`

English:
theorem lex_le_iff_of_unique
  statement: [Unique ι] [LinearOrder ι] [forall i, PartialOrder (β i)]
  proof: by
  simp_rw [le_iff_lt_or_eq, Pi.Lex.lt_iff_of_unique, ← ofLex_inj, funext_iff, Unique.forall_iff,
    ofLex_apply]

中文:
定理 lex_le_iff_of_unique
  结论: [唯一 ι] [线性序 ι] [对任意 i, 偏序 (β i)]
  证明: by
  simp_rw [le_iff_lt_or_eq, Pi.Lex.lt_iff_of_unique, ← ofLex_inj, funext_iff, Unique.forall_iff,
    ofLex_apply]

Depends on / 依赖: Pi.Lex.lt_iff_of_unique, Unique, Unique.forall_iff, forall_iff, funext_iff, le_iff_lt_or_eq, lt_iff_of_unique, ofLex_apply, ofLex_inj, simp_rw
-/
theorem lex_le_iff_of_unique [Unique ι] [LinearOrder ι] [forall i, PartialOrder (β i)]
    {x y : Lex (forall i, β i)} : x <= y ↔ x default <= y default := by
  simp_rw [le_iff_lt_or_eq, Pi.Lex.lt_iff_of_unique, ← ofLex_inj, funext_iff, Unique.forall_iff,
    ofLex_apply]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `colex_le_iff_of_unique` / 定理 `colex_le_iff_of_unique`

English:
theorem colex_le_iff_of_unique
  statement: [Unique ι] [LinearOrder ι] [forall i, PartialOrder (β i)]
  proof: by
  simp_rw [le_iff_lt_or_eq, Pi.Colex.lt_iff_of_unique, ← ofColex_inj, funext_iff, Unique.forall_iff,
    ofColex_apply]

中文:
定理 colex_le_iff_of_unique
  结论: [唯一 ι] [线性序 ι] [对任意 i, 偏序 (β i)]
  证明: by
  simp_rw [le_iff_lt_or_eq, Pi.Colex.lt_iff_of_unique, ← ofColex_inj, funext_iff, Unique.forall_iff,
    ofColex_apply]

Depends on / 依赖: Pi.Colex.lt_iff_of_unique, Unique, Unique.forall_iff, forall_iff, funext_iff, le_iff_lt_or_eq, lt_iff_of_unique, ofColex_apply, ofColex_inj, simp_rw
-/
theorem colex_le_iff_of_unique [Unique ι] [LinearOrder ι] [forall i, PartialOrder (β i)]
    {x y : Colex (forall i, β i)} : x <= y ↔ x default <= y default := by
  simp_rw [le_iff_lt_or_eq, Pi.Colex.lt_iff_of_unique, ← ofColex_inj, funext_iff, Unique.forall_iff,
    ofColex_apply]

section PartialOrder
variable [LinearOrder ι] {x : forall i, β i} {i : ι} {a : β i} [forall i, PartialOrder (β i)]

open Function

section Lex
variable [WellFoundedLT ι]

/--
theorem `toLex_monotone` / 定理 `toLex_monotone`

English:
theorem toLex_monotone
  statement: Monotone (@toLex (forall i, β i))
  proof: fun a b h =>
  or_iff_not_imp_left.2 fun hne =>
    let ⟨i, hi, hl⟩ := IsWellFounded.wf.has_min (r := (· < ·)) { i | a i != b i }
      (Function.ne_iff.1 hne)
    ⟨i, fun j hj => by
      contrapose! hl
      exact ⟨j, hl, hj⟩, (h i).lt_of_ne hi⟩

中文:
定理 toLex_monotone
  结论: 递增 (@toLex (对任意 i, β i))
  证明: fun a b h =>
  or_iff_not_imp_left.2 fun hne =>
    let ⟨i, hi, hl⟩ := IsWellFounded.wf.has_min (r := (· < ·)) { i | a i != b i }
      (Function.ne_iff.1 hne)
    ⟨i, fun j hj => by
      contrapose! hl
      exact ⟨j, hl, hj⟩, (h i).lt_of_ne hi⟩
-/
theorem toLex_monotone : Monotone (@toLex (forall i, β i)) := fun a b h =>
  or_iff_not_imp_left.2 fun hne =>
    let ⟨i, hi, hl⟩ := IsWellFounded.wf.has_min (r := (· < ·)) { i | a i != b i }
      (Function.ne_iff.1 hne)
    ⟨i, fun j hj => by
      contrapose! hl
      exact ⟨j, hl, hj⟩, (h i).lt_of_ne hi⟩

/--
theorem `toLex_strictMono` / 定理 `toLex_strictMono`

English:
theorem toLex_strictMono
  statement: StrictMono (@toLex (forall i, β i))
  proof: fun a b h =>
  let ⟨i, hi, hl⟩ := IsWellFounded.wf.has_min (r := (· < ·)) { i | a i != b i }
    (Function.ne_iff.1 h.ne)
  ⟨i, fun j hj => by
    contrapose! hl
    exact ⟨j, hl, hj⟩, (h.le i).lt_of_ne hi⟩

@[simp]

中文:
定理 toLex_strictMono
  结论: 严格递增 (@toLex (对任意 i, β i))
  证明: fun a b h =>
  let ⟨i, hi, hl⟩ := IsWellFounded.wf.has_min (r := (· < ·)) { i | a i != b i }
    (Function.ne_iff.1 h.ne)
  ⟨i, fun j hj => by
    contrapose! hl
    exact ⟨j, hl, hj⟩, (h.le i).lt_of_ne hi⟩

@[simp]
-/
theorem toLex_strictMono : StrictMono (@toLex (forall i, β i)) := fun a b h =>
  let ⟨i, hi, hl⟩ := IsWellFounded.wf.has_min (r := (· < ·)) { i | a i != b i }
    (Function.ne_iff.1 h.ne)
  ⟨i, fun j hj => by
    contrapose! hl
    exact ⟨j, hl, hj⟩, (h.le i).lt_of_ne hi⟩

@[simp]
/--
theorem `lt_toLex_update_self_iff` / 定理 `lt_toLex_update_self_iff`

English:
theorem lt_toLex_update_self_iff
  statement: toLex x < toLex (update x i a) ↔ x i < a
  proof: by
refine ⟨?_, fun h => toLex_strictMono lt_update_self_iff.2 h⟩
  rintro ⟨j, hj, h⟩
  dsimp at h
  obtain rfl : j = i := by
    by_contra H
    rw [update_of_ne H] at h
    exact h.false
  rwa [update_self] at h

@[simp]

中文:
定理 lt_toLex_update_self_iff
  结论: toLex x < toLex (update x i a) ↔ x i < a
  证明: by
refine ⟨?_, fun h => toLex_strictMono lt_update_self_iff.2 h⟩
  rintro ⟨j, hj, h⟩
  dsimp at h
  obtain rfl : j = i := by
    by_contra H
    rw [update_of_ne H] at h
    exact h.false
  rwa [update_self] at h

@[simp]

Depends on / 依赖: h.false, lt_update_self_iff, toLex_strictMono, update_of_ne, update_self
-/
theorem lt_toLex_update_self_iff : toLex x < toLex (update x i a) ↔ x i < a := by
refine ⟨?_, fun h => toLex_strictMono lt_update_self_iff.2 h⟩
  rintro ⟨j, hj, h⟩
  dsimp at h
  obtain rfl : j = i := by
    by_contra H
    rw [update_of_ne H] at h
    exact h.false
  rwa [update_self] at h

@[simp]
/--
theorem `toLex_update_lt_self_iff` / 定理 `toLex_update_lt_self_iff`

English:
theorem toLex_update_lt_self_iff
  statement: toLex (update x i a) < toLex x ↔ a < x i
  proof: by
refine ⟨?_, fun h => toLex_strictMono update_lt_self_iff.2 h⟩
  rintro ⟨j, hj, h⟩
  dsimp at h
  obtain rfl : j = i := by
    by_contra H
    rw [update_of_ne H] at h
    exact h.false
  rwa [update_self] at h

中文:
定理 toLex_update_lt_self_iff
  结论: toLex (update x i a) < toLex x ↔ a < x i
  证明: by
refine ⟨?_, fun h => toLex_strictMono update_lt_self_iff.2 h⟩
  rintro ⟨j, hj, h⟩
  dsimp at h
  obtain rfl : j = i := by
    by_contra H
    rw [update_of_ne H] at h
    exact h.false
  rwa [update_self] at h

Depends on / 依赖: h.false, toLex_strictMono, update_lt_self_iff, update_of_ne, update_self
-/
theorem toLex_update_lt_self_iff : toLex (update x i a) < toLex x ↔ a < x i := by
refine ⟨?_, fun h => toLex_strictMono update_lt_self_iff.2 h⟩
  rintro ⟨j, hj, h⟩
  dsimp at h
  obtain rfl : j = i := by
    by_contra H
    rw [update_of_ne H] at h
    exact h.false
  rwa [update_self] at h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `le_toLex_update_self_iff` / 定理 `le_toLex_update_self_iff`

English:
theorem le_toLex_update_self_iff
  statement: toLex x <= toLex (update x i a) ↔ x i <= a
  proof: by
  simp_rw [le_iff_lt_or_eq, lt_toLex_update_self_iff, toLex_inj, eq_update_self_iff]

中文:
定理 le_toLex_update_self_iff
  结论: toLex x <= toLex (update x i a) ↔ x i <= a
  证明: by
  simp_rw [le_iff_lt_or_eq, lt_toLex_update_self_iff, toLex_inj, eq_update_self_iff]

Depends on / 依赖: eq_update_self_iff, le_iff_lt_or_eq, lt_toLex_update_self_iff, simp_rw, toLex_inj
-/
theorem le_toLex_update_self_iff : toLex x <= toLex (update x i a) ↔ x i <= a := by
  simp_rw [le_iff_lt_or_eq, lt_toLex_update_self_iff, toLex_inj, eq_update_self_iff]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toLex_update_le_self_iff` / 定理 `toLex_update_le_self_iff`

English:
theorem toLex_update_le_self_iff
  statement: toLex (update x i a) <= toLex x ↔ a <= x i
  proof: by
  simp_rw [le_iff_lt_or_eq, toLex_update_lt_self_iff, toLex_inj, update_eq_self_iff]

中文:
定理 toLex_update_le_self_iff
  结论: toLex (update x i a) <= toLex x ↔ a <= x i
  证明: by
  simp_rw [le_iff_lt_or_eq, toLex_update_lt_self_iff, toLex_inj, update_eq_self_iff]

Depends on / 依赖: le_iff_lt_or_eq, simp_rw, toLex_inj, toLex_update_lt_self_iff, update_eq_self_iff
-/
theorem toLex_update_le_self_iff : toLex (update x i a) <= toLex x ↔ a <= x i := by
  simp_rw [le_iff_lt_or_eq, toLex_update_lt_self_iff, toLex_inj, update_eq_self_iff]

end Lex

section Colex
variable [WellFoundedGT ι]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `toColex_monotone` / 定理 `toColex_monotone`

English:
theorem toColex_monotone
  statement: Monotone (@toColex (forall i, β i))
  proof: toLex_monotone (ι := ιᵒᵈ)

中文:
定理 toColex_monotone
  结论: 递增 (@toColex (对任意 i, β i))
  证明: toLex_monotone (ι := ιᵒᵈ)

Depends on / 依赖: toLex_monotone
-/
theorem toColex_monotone : Monotone (@toColex (forall i, β i)) :=
  toLex_monotone (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `toColex_strictMono` / 定理 `toColex_strictMono`

English:
theorem toColex_strictMono
  statement: StrictMono (@toColex (forall i, β i))
  proof: toLex_strictMono (ι := ιᵒᵈ)

中文:
定理 toColex_strictMono
  结论: 严格递增 (@toColex (对任意 i, β i))
  证明: toLex_strictMono (ι := ιᵒᵈ)

Depends on / 依赖: IsFractionRing, IsFractionRing.div_surjective, IsFractionRing.of_field, algebraMap, div_surjective, eq.symm, of_field, toLex_strictMono
-/
theorem toColex_strictMono : StrictMono (@toColex (forall i, β i)) :=
  toLex_strictMono (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `lt_toColex_update_self_iff` / 定理 `lt_toColex_update_self_iff`

English:
theorem lt_toColex_update_self_iff
  statement: toColex x < toColex (update x i a) ↔ x i < a
  proof: lt_toLex_update_self_iff (ι := ιᵒᵈ)

中文:
定理 lt_toColex_update_self_iff
  结论: toColex x < toColex (update x i a) ↔ x i < a
  证明: lt_toLex_update_self_iff (ι := ιᵒᵈ)

Depends on / 依赖: lt_toLex_update_self_iff
-/
theorem lt_toColex_update_self_iff : toColex x < toColex (update x i a) ↔ x i < a :=
  lt_toLex_update_self_iff (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `toColex_update_lt_self_iff` / 定理 `toColex_update_lt_self_iff`

English:
theorem toColex_update_lt_self_iff
  statement: toColex (update x i a) < toColex x ↔ a < x i
  proof: toLex_update_lt_self_iff (ι := ιᵒᵈ)

中文:
定理 toColex_update_lt_self_iff
  结论: toColex (update x i a) < toColex x ↔ a < x i
  证明: toLex_update_lt_self_iff (ι := ιᵒᵈ)

Depends on / 依赖: toLex_update_lt_self_iff
-/
theorem toColex_update_lt_self_iff : toColex (update x i a) < toColex x ↔ a < x i :=
  toLex_update_lt_self_iff (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `le_toColex_update_self_iff` / 定理 `le_toColex_update_self_iff`

English:
theorem le_toColex_update_self_iff
  statement: toColex x <= toColex (update x i a) ↔ x i <= a
  proof: le_toLex_update_self_iff (ι := ιᵒᵈ)

中文:
定理 le_toColex_update_self_iff
  结论: toColex x <= toColex (update x i a) ↔ x i <= a
  证明: le_toLex_update_self_iff (ι := ιᵒᵈ)

Depends on / 依赖: le_toLex_update_self_iff
-/
theorem le_toColex_update_self_iff : toColex x <= toColex (update x i a) ↔ x i <= a :=
  le_toLex_update_self_iff (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `toColex_update_le_self_iff` / 定理 `toColex_update_le_self_iff`

English:
theorem toColex_update_le_self_iff
  statement: toColex (update x i a) <= toColex x ↔ a <= x i
  proof: toLex_update_le_self_iff (ι := ιᵒᵈ)

中文:
定理 toColex_update_le_self_iff
  结论: toColex (update x i a) <= toColex x ↔ a <= x i
  证明: toLex_update_le_self_iff (ι := ιᵒᵈ)

Depends on / 依赖: toLex_update_le_self_iff
-/
theorem toColex_update_le_self_iff : toColex (update x i a) <= toColex x ↔ a <= x i :=
  toLex_update_le_self_iff (ι := ιᵒᵈ)

end Colex

end PartialOrder

section LinearOrder
variable [LinearOrder ι] {x y : forall i, β i} {i : ι} {a : β i} [forall i, LinearOrder (β i)]

section Lex

/--
theorem `apply_le_of_toLex` / 定理 `apply_le_of_toLex`

English:
theorem apply_le_of_toLex
  given: (hxy : toLex x <= toLex y) (h : forall j < i, x j = y j)
  statement: x i <= y i
  proof: by
  contrapose! hxy
  apply not_le_of_gt
  use i
  aesop

中文:
定理 apply_le_of_toLex
  条件: (hxy : toLex x <= toLex y) (h : 对任意 j < i, x j = y j)
  结论: x i <= y i
  证明: by
  contrapose! hxy
  apply not_le_of_gt
  use i
  aesop

Depends on / 依赖: contrapose, not_le_of_gt
-/
theorem apply_le_of_toLex (hxy : toLex x <= toLex y) (h : forall j < i, x j = y j) : x i <= y i := by
  contrapose! hxy
  apply not_le_of_gt
  use i
  aesop

end Lex

section Colex

/--
theorem `apply_le_of_toColex` / 定理 `apply_le_of_toColex`

English:
theorem apply_le_of_toColex
  given: (hxy : toColex x <= toColex y) (h : forall j > i, x j = y j)
  statement: x i <= y i
  proof: by
  contrapose! hxy
  apply not_le_of_gt
  use i
  aesop

中文:
定理 apply_le_of_toColex
  条件: (hxy : toColex x <= toColex y) (h : 对任意 j > i, x j = y j)
  结论: x i <= y i
  证明: by
  contrapose! hxy
  apply not_le_of_gt
  use i
  aesop

Depends on / 依赖: contrapose, not_le_of_gt
-/
theorem apply_le_of_toColex (hxy : toColex x <= toColex y) (h : forall j > i, x j = y j) : x i <= y i := by
  contrapose! hxy
  apply not_le_of_gt
  use i
  aesop

end Colex

end LinearOrder

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: ι] [WellFoundedLT ι] [forall a, PartialOrder (β a)] [forall a, OrderBot (β a)] :
  body: toLex ⊥
  bot_le _ := toLex_monotone bot_le

中文:
实例 [线性序
  签名: ι] [WellFoundedLT ι] [对任意 a, 偏序 (β a)] [对任意 a, 有底序 (β a)] :
  定义体: toLex ⊥
  bot_le _ := toLex_monotone bot_le
-/
instance [LinearOrder ι] [WellFoundedLT ι] [forall a, PartialOrder (β a)] [forall a, OrderBot (β a)] :
    OrderBot (Lex (forall a, β a)) where
  bot := toLex ⊥
  bot_le _ := toLex_monotone bot_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: ι] [WellFoundedGT ι] [forall a, PartialOrder (β a)] [forall a, OrderBot (β a)] :
  body: toColex ⊥
  bot_le _ := toColex_monotone bot_le

中文:
实例 [线性序
  签名: ι] [WellFoundedGT ι] [对任意 a, 偏序 (β a)] [对任意 a, 有底序 (β a)] :
  定义体: toColex ⊥
  bot_le _ := toColex_monotone bot_le

Depends on / 依赖: toColex
-/
instance [LinearOrder ι] [WellFoundedGT ι] [forall a, PartialOrder (β a)] [forall a, OrderBot (β a)] :
    OrderBot (Colex (forall a, β a)) where
  bot := toColex ⊥
  bot_le _ := toColex_monotone bot_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: ι] [WellFoundedLT ι] [forall a, PartialOrder (β a)] [forall a, OrderTop (β a)] :
  body: toLex ⊤
  le_top _ := toLex_monotone le_top

中文:
实例 [线性序
  签名: ι] [WellFoundedLT ι] [对任意 a, 偏序 (β a)] [对任意 a, 有顶序 (β a)] :
  定义体: toLex ⊤
  le_top _ := toLex_monotone le_top

Depends on / 依赖: TensorProduct, TensorProduct.isBaseChange, isBaseChange, isLocalizedModule_iff_isBaseChange
-/
instance [LinearOrder ι] [WellFoundedLT ι] [forall a, PartialOrder (β a)] [forall a, OrderTop (β a)] :
    OrderTop (Lex (forall a, β a)) where
  top := toLex ⊤
  le_top _ := toLex_monotone le_top

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: ι] [WellFoundedGT ι] [forall a, PartialOrder (β a)] [forall a, OrderTop (β a)] :
  body: toColex ⊤
  le_top _ := toColex_monotone le_top

中文:
实例 [线性序
  签名: ι] [WellFoundedGT ι] [对任意 a, 偏序 (β a)] [对任意 a, 有顶序 (β a)] :
  定义体: toColex ⊤
  le_top _ := toColex_monotone le_top

Depends on / 依赖: toColex
-/
instance [LinearOrder ι] [WellFoundedGT ι] [forall a, PartialOrder (β a)] [forall a, OrderTop (β a)] :
    OrderTop (Colex (forall a, β a)) where
  top := toColex ⊤
  le_top _ := toColex_monotone le_top

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: ι] [WellFoundedLT ι] [forall a, PartialOrder (β a)]

中文:
实例 [线性序
  签名: ι] [WellFoundedLT ι] [对任意 a, 偏序 (β a)]
-/
instance [LinearOrder ι] [WellFoundedLT ι] [forall a, PartialOrder (β a)]
    [forall a, BoundedOrder (β a)] : BoundedOrder (Lex (forall a, β a)) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: ι] [WellFoundedGT ι] [forall a, PartialOrder (β a)]

中文:
实例 [线性序
  签名: ι] [WellFoundedGT ι] [对任意 a, 偏序 (β a)]
-/
instance [LinearOrder ι] [WellFoundedGT ι] [forall a, PartialOrder (β a)]
    [forall a, BoundedOrder (β a)] : BoundedOrder (Colex (forall a, β a)) where

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: ι] [forall i, LT (β i)] [forall i, DenselyOrdered (β i)] :
  body: ⟨by
    rintro _ a₂ ⟨i, h, hi⟩
    obtain ⟨a, ha₁, ha₂⟩ := exists_between hi
    classical
      refine ⟨Function.update a₂ _ a, ⟨i, fun j hj => ?_, ?_⟩, i, fun j hj => ?_, ?_⟩
      · rw [h j hj]
        dsimp only at hj
        rw [Function.update_of_ne hj.ne a]
      · rwa [Function.update_self i

中文:
实例 [预序
  签名: ι] [对任意 i, LT (β i)] [对任意 i, 稠密序 (β i)] :
  定义体: ⟨by
    rintro _ a₂ ⟨i, h, hi⟩
    obtain ⟨a, ha₁, ha₂⟩ := exists_between hi
    classical
      refine ⟨Function.update a₂ _ a, ⟨i, fun j hj => ?_, ?_⟩, i, fun j hj => ?_, ?_⟩
      · rw [h j hj]
        dsimp only at hj
        rw [Function.update_of_ne hj.ne a]
      · rwa [Function.update_self i

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.distribBaseChange, Function, Function.update, Function.update_of_ne, Function.update_self, IsLocalizedModule, IsLocalizedModule.linearEquiv, IsLocalizedModule.of_linearEquiv, LinearEquiv, LinearEquiv.eq_symm_apply, Localization, TensorProduct, TensorProduct.equivOfCompatibleSMul, TensorProduct.mk, classical, congrm, convert, distribBaseChange, eq_symm_apply
-/
instance [Preorder ι] [forall i, LT (β i)] [forall i, DenselyOrdered (β i)] :
    DenselyOrdered (Lex (forall i, β i)) :=
  ⟨by
    rintro _ a₂ ⟨i, h, hi⟩
    obtain ⟨a, ha₁, ha₂⟩ := exists_between hi
    classical
      refine ⟨Function.update a₂ _ a, ⟨i, fun j hj => ?_, ?_⟩, i, fun j hj => ?_, ?_⟩
      · rw [h j hj]
        dsimp only at hj
        rw [Function.update_of_ne hj.ne a]
      · rwa [Function.update_self i a]
      · rw [Function.update_of_ne hj.ne a]
      · rwa [Function.update_self i a]⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: ι] [forall i, LT (β i)] [forall i, DenselyOrdered (β i)] :
  body: inferInstanceAs (DenselyOrdered (Lex (forall i : ιᵒᵈ, β (OrderDual.toDual i))))

中文:
实例 [预序
  签名: ι] [对任意 i, LT (β i)] [对任意 i, 稠密序 (β i)] :
  定义体: inferInstanceAs (DenselyOrdered (Lex (forall i : ιᵒᵈ, β (OrderDual.toDual i))))

Depends on / 依赖: DenselyOrdered, OrderDual, OrderDual.toDual, toDual
-/
instance [Preorder ι] [forall i, LT (β i)] [forall i, DenselyOrdered (β i)] :
    DenselyOrdered (Colex (forall i, β i)) :=
  inferInstanceAs (DenselyOrdered (Lex (forall i : ιᵒᵈ, β (OrderDual.toDual i))))

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Lex.noMaxOrder'` / 定理 `Lex.noMaxOrder'`

English:
theorem Lex.noMaxOrder'
  given: [Preorder ι] [forall i, LT (β i)] (i : ι) [NoMaxOrder (β i)]
  proof: ⟨fun a => by
    let ⟨b, hb⟩ := exists_gt (a i)
    classical
    exact ⟨Function.update a i b, i, fun j hj =>
      (Function.update_of_ne hj.ne b a).symm, by rwa [Function.update_self i b]⟩⟩

中文:
定理 Lex.noMaxOrder'
  条件: [预序 ι] [对任意 i, LT (β i)] (i : ι) [NoMax序 (β i)]
  证明: ⟨fun a => by
    let ⟨b, hb⟩ := exists_gt (a i)
    classical
    exact ⟨Function.update a i b, i, fun j hj =>
      (Function.update_of_ne hj.ne b a).symm, by rwa [Function.update_self i b]⟩⟩

Depends on / 依赖: Function, Function.update, Function.update_of_ne, Function.update_self, classical, exists_gt, hj.ne, update, update_of_ne, update_self
-/
theorem Lex.noMaxOrder' [Preorder ι] [forall i, LT (β i)] (i : ι) [NoMaxOrder (β i)] :
    NoMaxOrder (Lex (forall i, β i)) :=
  ⟨fun a => by
    let ⟨b, hb⟩ := exists_gt (a i)
    classical
    exact ⟨Function.update a i b, i, fun j hj =>
      (Function.update_of_ne hj.ne b a).symm, by rwa [Function.update_self i b]⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Colex.noMaxOrder'` / 定理 `Colex.noMaxOrder'`

English:
theorem Colex.noMaxOrder'
  given: [Preorder ι] [forall i, LT (β i)] (i : ι) [NoMaxOrder (β i)]
  proof: Lex.noMaxOrder' (ι := ιᵒᵈ) i

中文:
定理 Colex.noMaxOrder'
  条件: [预序 ι] [对任意 i, LT (β i)] (i : ι) [NoMax序 (β i)]
  证明: Lex.noMaxOrder' (ι := ιᵒᵈ) i

Depends on / 依赖: Lex.noMaxOrder, noMaxOrder
-/
theorem Colex.noMaxOrder' [Preorder ι] [forall i, LT (β i)] (i : ι) [NoMaxOrder (β i)] :
    NoMaxOrder (Colex (forall i, β i)) :=
  Lex.noMaxOrder' (ι := ιᵒᵈ) i

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: ι] [WellFoundedLT ι] [Nonempty ι] [forall i, PartialOrder (β i)]
  body: ⟨fun a =>
    let ⟨_, hb⟩ := exists_gt (ofLex a)
    ⟨_, toLex_strictMono hb⟩⟩

中文:
实例 [线性序
  签名: ι] [WellFoundedLT ι] [非空 ι] [对任意 i, 偏序 (β i)]
  定义体: ⟨fun a =>
    let ⟨_, hb⟩ := exists_gt (ofLex a)
    ⟨_, toLex_strictMono hb⟩⟩

Depends on / 依赖: exists_gt, toLex_strictMono
-/
instance [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι] [forall i, PartialOrder (β i)]
    [forall i, NoMaxOrder (β i)] : NoMaxOrder (Lex (forall i, β i)) :=
  ⟨fun a =>
    let ⟨_, hb⟩ := exists_gt (ofLex a)
    ⟨_, toLex_strictMono hb⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: ι] [WellFoundedGT ι] [Nonempty ι] [forall i, PartialOrder (β i)]
  body: inferInstanceAs (NoMaxOrder (Lex (forall i : ιᵒᵈ, β (OrderDual.toDual i))))

中文:
实例 [线性序
  签名: ι] [WellFoundedGT ι] [非空 ι] [对任意 i, 偏序 (β i)]
  定义体: inferInstanceAs (NoMaxOrder (Lex (forall i : ιᵒᵈ, β (OrderDual.toDual i))))

Depends on / 依赖: NoMaxOrder, OrderDual, OrderDual.toDual, toDual
-/
instance [LinearOrder ι] [WellFoundedGT ι] [Nonempty ι] [forall i, PartialOrder (β i)]
    [forall i, NoMaxOrder (β i)] : NoMaxOrder (Colex (forall i, β i)) :=
  inferInstanceAs (NoMaxOrder (Lex (forall i : ιᵒᵈ, β (OrderDual.toDual i))))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: ι] [WellFoundedLT ι] [Nonempty ι] [forall i, PartialOrder (β i)]
  body: ⟨fun a =>
    let ⟨_, hb⟩ := exists_lt (ofLex a)
    ⟨_, toLex_strictMono hb⟩⟩

中文:
实例 [线性序
  签名: ι] [WellFoundedLT ι] [非空 ι] [对任意 i, 偏序 (β i)]
  定义体: ⟨fun a =>
    let ⟨_, hb⟩ := exists_lt (ofLex a)
    ⟨_, toLex_strictMono hb⟩⟩

Depends on / 依赖: exists_lt, toLex_strictMono
-/
instance [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι] [forall i, PartialOrder (β i)]
    [forall i, NoMinOrder (β i)] : NoMinOrder (Lex (forall i, β i)) :=
  ⟨fun a =>
    let ⟨_, hb⟩ := exists_lt (ofLex a)
    ⟨_, toLex_strictMono hb⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: ι] [WellFoundedGT ι] [Nonempty ι] [forall i, PartialOrder (β i)]
  body: inferInstanceAs (NoMinOrder (Lex (forall i : ιᵒᵈ, β (OrderDual.toDual i))))

中文:
实例 [线性序
  签名: ι] [WellFoundedGT ι] [非空 ι] [对任意 i, 偏序 (β i)]
  定义体: inferInstanceAs (NoMinOrder (Lex (forall i : ιᵒᵈ, β (OrderDual.toDual i))))

Depends on / 依赖: NoMinOrder, OrderDual, OrderDual.toDual, toDual
-/
instance [LinearOrder ι] [WellFoundedGT ι] [Nonempty ι] [forall i, PartialOrder (β i)]
    [forall i, NoMinOrder (β i)] : NoMinOrder (Colex (forall i, β i)) :=
  inferInstanceAs (NoMinOrder (Lex (forall i : ιᵒᵈ, β (OrderDual.toDual i))))

/--
theorem `lex_desc` / 定理 `lex_desc`

English:
theorem lex_desc
  statement: {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι -> α} {i j : ι} (h₁ : i <= j)
  proof: ⟨i, fun _ hik => congr_arg f (Equiv.swap_apply_of_ne_of_ne hik.ne (hik.trans_le h₁).ne), by
    simpa only [Pi.toLex_apply, Function.comp_apply, Equiv.swap_apply_left] using h₂⟩

中文:
定理 lex_desc
  结论: {α} [预序 ι] [DecidableEq ι] [LT α] {f : ι -> α} {i j : ι} (h₁ : i <= j)
  证明: ⟨i, fun _ hik => congr_arg f (Equiv.swap_apply_of_ne_of_ne hik.ne (hik.trans_le h₁).ne), by
    simpa only [Pi.toLex_apply, Function.comp_apply, Equiv.swap_apply_left] using h₂⟩

Depends on / 依赖: Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne, Function, Function.comp_apply, Pi.toLex_apply, comp_apply, congr_arg, hik.ne, hik.trans_le, swap_apply_left, swap_apply_of_ne_of_ne, toLex_apply, trans_le
-/
theorem lex_desc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι -> α} {i j : ι} (h₁ : i <= j)
    (h₂ : f j < f i) : toLex (f ∘ Equiv.swap i j) < toLex f :=
  ⟨i, fun _ hik => congr_arg f (Equiv.swap_apply_of_ne_of_ne hik.ne (hik.trans_le h₁).ne), by
    simpa only [Pi.toLex_apply, Function.comp_apply, Equiv.swap_apply_left] using h₂⟩

/--
theorem `colex_asc` / 定理 `colex_asc`

English:
theorem colex_asc
  statement: {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι -> α} {i j : ι} (h₁ : i <= j)
  proof: by
  rw [Equiv.swap_comm]
  exact lex_desc (ι := ιᵒᵈ) h₁ h₂

中文:
定理 colex_asc
  结论: {α} [预序 ι] [DecidableEq ι] [LT α] {f : ι -> α} {i j : ι} (h₁ : i <= j)
  证明: by
  rw [Equiv.swap_comm]
  exact lex_desc (ι := ιᵒᵈ) h₁ h₂

Depends on / 依赖: Equiv.swap_comm, lex_desc, swap_comm
-/
theorem colex_asc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι -> α} {i j : ι} (h₁ : i <= j)
    (h₂ : f i < f j) : toColex (f ∘ Equiv.swap i j) < toColex f := by
  rw [Equiv.swap_comm]
  exact lex_desc (ι := ιᵒᵈ) h₁ h₂

end Pi
