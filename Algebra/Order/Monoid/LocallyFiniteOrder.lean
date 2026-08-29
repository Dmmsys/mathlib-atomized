/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.Algebra.Order.Hom.TypeTags
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Order.Interval.Finset.Basic

/-!

# Locally Finite Linearly Ordered Abelian Groups

## Main results
- `LocallyFiniteOrder.orderAddMonoidEquiv`:
  Any nontrivial linearly ordered additive abelian group that is locally finite is
  isomorphic to `ℤ`.
- `LocallyFiniteOrder.orderMonoidEquiv`:
  Any nontrivial linearly ordered abelian group that is locally finite is isomorphic to
  `Multiplicative ℤ`.
- `LocallyFiniteOrder.orderMonoidWithZeroEquiv`:
  Any nontrivial linearly ordered abelian group with zero that is locally finite
  is isomorphic to `ℤᵐ⁰`.

-/

@[expose] public section

open Finset

section Multiplicative

variable {M : Type*} [CancelCommMonoid M] [LinearOrder M] [IsOrderedMonoid M] [LocallyFiniteOrder M]

@[to_additive]
/--
lemma `Finset.card_Ico_mul_right` / 引理 `Finset.card_Ico_mul_right`

English:
lemma Finset.card_Ico_mul_right
  given: [ExistsMulOfLE M] (a b c : M)
  proof: by
  have : (Ico (a * c) (b * c)) = (Ico a b).map (mulRightEmbedding c) := by
    ext x
    simp only [mem_Ico, mem_map, mulRightEmbedding_apply]
    constructor
    · rintro ⟨h₁, h₂⟩
      obtain ⟨d, rfl⟩ := exists_mul_of_le h₁
      exact ⟨a * d, ⟨by simpa using h₁, by simpa [mul_right_comm a c d] using h₂⟩,
        by simp_rw [mul_assoc, mul_comm]⟩
    · aesop
  simp [this]

@[to_additive]

中文:
引理 有限集.card_Ico_mul_right
  条件: [ExistsMulOfLE M] (a b c : M)
  证明: by
  have : (Ico (a * c) (b * c)) = (Ico a b).map (mulRightEmbedding c) := by
    ext x
    simp only [mem_Ico, mem_map, mulRightEmbedding_apply]
    constructor
    · rintro ⟨h₁, h₂⟩
      obtain ⟨d, rfl⟩ := exists_mul_of_le h₁
      exact ⟨a * d, ⟨by simpa using h₁, by simpa [mul_right_comm a c d] using h₂⟩,
        by simp_rw [mul_assoc, mul_comm]⟩
    · aesop
  simp [this]

@[to_additive]

Depends on / 依赖: exists_mul_of_le, mem_Ico, mem_map, mulRightEmbedding, mulRightEmbedding_apply, mul_assoc, mul_comm, mul_right_comm, simp_rw
-/
lemma Finset.card_Ico_mul_right [ExistsMulOfLE M] (a b c : M) :
    #(Ico (a * c) (b * c)) = #(Ico a b) := by
  have : (Ico (a * c) (b * c)) = (Ico a b).map (mulRightEmbedding c) := by
    ext x
    simp only [mem_Ico, mem_map, mulRightEmbedding_apply]
    constructor
    · rintro ⟨h₁, h₂⟩
      obtain ⟨d, rfl⟩ := exists_mul_of_le h₁
      exact ⟨a * d, ⟨by simpa using h₁, by simpa [mul_right_comm a c d] using h₂⟩,
        by simp_rw [mul_assoc, mul_comm]⟩
    · aesop
  simp [this]

@[to_additive]
/--
lemma `card_Ico_one_mul` / 引理 `card_Ico_one_mul`

English:
lemma card_Ico_one_mul
  statement: [ExistsMulOfLE M] (a b : M)
  proof: by
  have : Ico 1 b union Ico (1 * b) (a * b) = Ico 1 (a * b) := by
    simp [Ico_union_Ico, ha, hb, Right.one_le_mul ha hb]
  rw [← this]; rw [Finset.card_union]; rw [Finset.card_Ico_mul_right]
  simp [add_comm]

中文:
引理 card_Ico_one_mul
  结论: [ExistsMulOfLE M] (a b : M)
  证明: by
  have : Ico 1 b union Ico (1 * b) (a * b) = Ico 1 (a * b) := by
    simp [Ico_union_Ico, ha, hb, Right.one_le_mul ha hb]
  rw [← this]; rw [Finset.card_union]; rw [Finset.card_Ico_mul_right]
  simp [add_comm]

Depends on / 依赖: Finset, Finset.card_Ico_mul_right, Finset.card_union, Ico_union_Ico, Right.one_le_mul, add_comm, card_Ico_mul_right, card_union, one_le_mul
-/
lemma card_Ico_one_mul [ExistsMulOfLE M] (a b : M)
    (ha : 1 <= a) (hb : 1 <= b) :
    #(Ico 1 (a * b)) = #(Ico 1 a) + #(Ico 1 b) := by
  have : Ico 1 b union Ico (1 * b) (a * b) = Ico 1 (a * b) := by
    simp [Ico_union_Ico, ha, hb, Right.one_le_mul ha hb]
  rw [← this]; rw [Finset.card_union]; rw [Finset.card_Ico_mul_right]
  simp [add_comm]

end Multiplicative

variable {M G : Type*} [AddCancelCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]
    [LocallyFiniteOrder M] [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

variable (G) in
/--
Definition of `LocallyFiniteOrder.addMonoidHom` / `LocallyFiniteOrder.addMonoidHom` 的定义

English:
definition LocallyFiniteOrder.addMonoidHom
  signature: :
  body: #(Ico 0 a) - #(Ico 0 (-a))
  map_zero' := by simp
  map_add' a b := by
    wlog hab : a <= b generalizing a b
    · convert! this b a (le_of_not_ge hab) using 1 <;> simp only [add_comm]
    obtain ha | ha := le_total 0 a <;> obtain hb | hb := le_total 0 b
    · have : -b <= a := by trans 0 <;> simp [ha, hb]
      simp [ha, hb, card_Ico_zero_add, this]
    · obtain rfl := hb.antisymm (ha.trans hab)
      obtain rfl := ha.antisymm hab
      simp
    · simp only [neg_add_rev, ha, Ico_eq_empty_of_le, card_empty, Nat.cast_zero, zero_sub,
        Left.neg_nonpos_iff, hb, sub_zero]
      obtain ⟨b, rfl⟩ : exists r, b = r - a := ⟨a + b, by abel⟩
      simp only [add_sub_cancel, neg_sub, sub_add_eq_add_sub, add_neg_cancel, zero_sub]
      obtain hb' | hb' := le_total 0 b
      · simp [hb', neg_add_eq_sub, eq_sub_iff_add_eq, ← Nat.cast_add,
          ← card_Ico_zero_add, ha, ← sub_eq_add_neg]
      · simp [hb', neg_add_eq_sub, eq_sub_iff_add_eq, sub_eq_iff_eq_add,
          ← Nat.cast_add, ← card_Ico_zero_add, hb, sub_add_eq_add_sub]
    · have : ¬0 < a + b := by simpa using add_nonpos ha hb
      simp [ha, hb, card_Ico_zero_add, Ico_eq_empty, this]

中文:
定义 局部有限序.addMonoidHom
  签名: :
  定义体: #(Ico 0 a) - #(Ico 0 (-a))
  map_zero' := by simp
  map_add' a b := by
    wlog hab : a <= b generalizing a b
    · convert! this b a (le_of_not_ge hab) using 1 <;> simp only [add_comm]
    obtain ha | ha := le_total 0 a <;> obtain hb | hb := le_total 0 b
    · have : -b <= a := by trans 0 <;> simp [ha, hb]
      simp [ha, hb, card_Ico_zero_add, this]
    · obtain rfl := hb.antisymm (ha.trans hab)
      obtain rfl := ha.antisymm hab
      simp
    · simp only [neg_add_rev, ha, Ico_eq_empty_of_le, card_empty, Nat.cast_zero, zero_sub,
        Left.neg_nonpos_iff, hb, sub_zero]
      obtain ⟨b, rfl⟩ : exists r, b = r - a := ⟨a + b, by abel⟩
      simp only [add_sub_cancel, neg_sub, sub_add_eq_add_sub, add_neg_cancel, zero_sub]
      obtain hb' | hb' := le_total 0 b
      · simp [hb', neg_add_eq_sub, eq_sub_iff_add_eq, ← Nat.cast_add,
          ← card_Ico_zero_add, ha, ← sub_eq_add_neg]
      · simp [hb', neg_add_eq_sub, eq_sub_iff_add_eq, sub_eq_iff_eq_add,
          ← Nat.cast_add, ← card_Ico_zero_add, hb, sub_add_eq_add_sub]
    · have : ¬0 < a + b := by simpa using add_nonpos ha hb
      simp [ha, hb, card_Ico_zero_add, Ico_eq_empty, this]
-/
def LocallyFiniteOrder.addMonoidHom :
    G ->+ Int where
  toFun a := #(Ico 0 a) - #(Ico 0 (-a))
  map_zero' := by simp
  map_add' a b := by
    wlog hab : a <= b generalizing a b
    · convert! this b a (le_of_not_ge hab) using 1 <;> simp only [add_comm]
    obtain ha | ha := le_total 0 a <;> obtain hb | hb := le_total 0 b
    · have : -b <= a := by trans 0 <;> simp [ha, hb]
      simp [ha, hb, card_Ico_zero_add, this]
    · obtain rfl := hb.antisymm (ha.trans hab)
      obtain rfl := ha.antisymm hab
      simp
    · simp only [neg_add_rev, ha, Ico_eq_empty_of_le, card_empty, Nat.cast_zero, zero_sub,
        Left.neg_nonpos_iff, hb, sub_zero]
      obtain ⟨b, rfl⟩ : exists r, b = r - a := ⟨a + b, by abel⟩
      simp only [add_sub_cancel, neg_sub, sub_add_eq_add_sub, add_neg_cancel, zero_sub]
      obtain hb' | hb' := le_total 0 b
      · simp [hb', neg_add_eq_sub, eq_sub_iff_add_eq, ← Nat.cast_add,
          ← card_Ico_zero_add, ha, ← sub_eq_add_neg]
      · simp [hb', neg_add_eq_sub, eq_sub_iff_add_eq, sub_eq_iff_eq_add,
          ← Nat.cast_add, ← card_Ico_zero_add, hb, sub_add_eq_add_sub]
    · have : ¬0 < a + b := by simpa using add_nonpos ha hb
      simp [ha, hb, card_Ico_zero_add, Ico_eq_empty, this]

variable (G) in
/--
Definition of `LocallyFiniteOrder.orderAddMonoidHom` / `LocallyFiniteOrder.orderAddMonoidHom` 的定义

English:
definition LocallyFiniteOrder.orderAddMonoidHom
  signature: :
  body: addMonoidHom G
  monotone' a b hab := by
    obtain ⟨b, rfl⟩ := add_left_surjective a b
    replace hab : 0 <= b := by simpa using hab
    suffices 0 <= addMonoidHom G b by simpa
    simp [addMonoidHom, hab]

@[simp]

中文:
定义 局部有限序.orderAddMonoidHom
  签名: :
  定义体: addMonoidHom G
  monotone' a b hab := by
    obtain ⟨b, rfl⟩ := add_left_surjective a b
    replace hab : 0 <= b := by simpa using hab
    suffices 0 <= addMonoidHom G b by simpa
    simp [addMonoidHom, hab]

@[simp]

Depends on / 依赖: addMonoidHom
-/
def LocallyFiniteOrder.orderAddMonoidHom :
    G ->+o Int where
  __ := addMonoidHom G
  monotone' a b hab := by
    obtain ⟨b, rfl⟩ := add_left_surjective a b
    replace hab : 0 <= b := by simpa using hab
    suffices 0 <= addMonoidHom G b by simpa
    simp [addMonoidHom, hab]

@[simp]
/--
lemma `LocallyFiniteOrder.orderAddMonoidHom_toAddMonoidHom` / 引理 `LocallyFiniteOrder.orderAddMonoidHom_toAddMonoidHom`

English:
lemma LocallyFiniteOrder.orderAddMonoidHom_toAddMonoidHom
  proof: rfl

@[simp]

中文:
引理 局部有限序.orderAddMonoidHom_toAddMonoidHom
  证明: rfl

@[simp]
-/
lemma LocallyFiniteOrder.orderAddMonoidHom_toAddMonoidHom :
    orderAddMonoidHom G = addMonoidHom G := rfl

@[simp]
/--
lemma `LocallyFiniteOrder.orderAddMonoidHom_apply` / 引理 `LocallyFiniteOrder.orderAddMonoidHom_apply`

English:
lemma LocallyFiniteOrder.orderAddMonoidHom_apply
  given: (x : G)
  proof: rfl

中文:
引理 局部有限序.orderAddMonoidHom_apply
  条件: (x : G)
  证明: rfl
-/
lemma LocallyFiniteOrder.orderAddMonoidHom_apply (x : G) :
    orderAddMonoidHom G x = addMonoidHom G x := rfl

/--
lemma `LocallyFiniteOrder.orderAddMonoidHom_strictMono` / 引理 `LocallyFiniteOrder.orderAddMonoidHom_strictMono`

English:
lemma LocallyFiniteOrder.orderAddMonoidHom_strictMono
  proof: by
  rw [strictMono_iff_map_pos]
  intro g H
  simpa [addMonoidHom, H.le]

中文:
引理 局部有限序.orderAddMonoidHom_strictMono
  证明: by
  rw [strictMono_iff_map_pos]
  intro g H
  simpa [addMonoidHom, H.le]

Depends on / 依赖: H.le, addMonoidHom, strictMono_iff_map_pos
-/
lemma LocallyFiniteOrder.orderAddMonoidHom_strictMono :
    StrictMono (orderAddMonoidHom G) := by
  rw [strictMono_iff_map_pos]
  intro g H
  simpa [addMonoidHom, H.le]

/--
lemma `LocallyFiniteOrder.orderAddMonoidHom_bijective` / 引理 `LocallyFiniteOrder.orderAddMonoidHom_bijective`

English:
lemma LocallyFiniteOrder.orderAddMonoidHom_bijective
  given: [Nontrivial G]
  proof: by
  refine ⟨orderAddMonoidHom_strictMono.injective, ?_⟩
  suffices 1 in (orderAddMonoidHom G).range by
    obtain ⟨x, hx⟩ := this
    exact fun a => ⟨a • x, by simp_all⟩
  have ⟨a, ha⟩ := exists_zero_lt (α := G)
  obtain ⟨b, hb⟩ := exists_covBy_of_wellFoundedLT (α := Icc 0 a) (a := ⟨0, by simpa using! ha.le⟩)
    (fun H => ha.not_ge (@H ⟨a, by simpa using! ha.le⟩ ha.le))
  use b.1
  have : 0 <= b.1 := hb.1.le
  suffices Ico 0 b.1 = {0} by simpa [orderAddMonoidHom, addMonoidHom, this]
  ext x
  simp only [mem_Ico, mem_singleton]
  constructor
  · rintro ⟨h₁, h₂⟩
    by_contra hx'
    have := b.2
    simp only [Finset.mem_Icc] at this
    exact hb.2 (c := ⟨x, by simpa [h₁] using! h₂.le.trans this.2⟩)
      (lt_of_le_of_ne h₁ (by simpa using! Ne.symm hx')) h₂
  · rintro rfl
    simpa using! hb.1

中文:
引理 局部有限序.orderAddMonoidHom_bijective
  条件: [非平凡 G]
  证明: by
  refine ⟨orderAddMonoidHom_strictMono.injective, ?_⟩
  suffices 1 in (orderAddMonoidHom G).range by
    obtain ⟨x, hx⟩ := this
    exact fun a => ⟨a • x, by simp_all⟩
  have ⟨a, ha⟩ := exists_zero_lt (α := G)
  obtain ⟨b, hb⟩ := exists_covBy_of_wellFoundedLT (α := Icc 0 a) (a := ⟨0, by simpa using! ha.le⟩)
    (fun H => ha.not_ge (@H ⟨a, by simpa using! ha.le⟩ ha.le))
  use b.1
  have : 0 <= b.1 := hb.1.le
  suffices Ico 0 b.1 = {0} by simpa [orderAddMonoidHom, addMonoidHom, this]
  ext x
  simp only [mem_Ico, mem_singleton]
  constructor
  · rintro ⟨h₁, h₂⟩
    by_contra hx'
    have := b.2
    simp only [Finset.mem_Icc] at this
    exact hb.2 (c := ⟨x, by simpa [h₁] using! h₂.le.trans this.2⟩)
      (lt_of_le_of_ne h₁ (by simpa using! Ne.symm hx')) h₂
  · rintro rfl
    simpa using! hb.1

Depends on / 依赖: addMonoidHom, exists_covBy_of_wellFoundedLT, exists_zero_lt, ha.le, ha.not_ge, injective, mem_Ico, mem_single, not_ge, orderAddMonoidHom, orderAddMonoidHom_strictMono, orderAddMonoidHom_strictMono.injective
-/
lemma LocallyFiniteOrder.orderAddMonoidHom_bijective [Nontrivial G] :
    Function.Bijective (orderAddMonoidHom G) := by
  refine ⟨orderAddMonoidHom_strictMono.injective, ?_⟩
  suffices 1 in (orderAddMonoidHom G).range by
    obtain ⟨x, hx⟩ := this
    exact fun a => ⟨a • x, by simp_all⟩
  have ⟨a, ha⟩ := exists_zero_lt (α := G)
  obtain ⟨b, hb⟩ := exists_covBy_of_wellFoundedLT (α := Icc 0 a) (a := ⟨0, by simpa using! ha.le⟩)
    (fun H => ha.not_ge (@H ⟨a, by simpa using! ha.le⟩ ha.le))
  use b.1
  have : 0 <= b.1 := hb.1.le
  suffices Ico 0 b.1 = {0} by simpa [orderAddMonoidHom, addMonoidHom, this]
  ext x
  simp only [mem_Ico, mem_singleton]
  constructor
  · rintro ⟨h₁, h₂⟩
    by_contra hx'
    have := b.2
    simp only [Finset.mem_Icc] at this
    exact hb.2 (c := ⟨x, by simpa [h₁] using! h₂.le.trans this.2⟩)
      (lt_of_le_of_ne h₁ (by simpa using! Ne.symm hx')) h₂
  · rintro rfl
    simpa using! hb.1

variable (G) in
/-- Any nontrivial linearly ordered abelian group that is locally finite is isomorphic to `ℤ`. -/
noncomputable
/--
Definition of `LocallyFiniteOrder.orderAddMonoidEquiv` / `LocallyFiniteOrder.orderAddMonoidEquiv` 的定义

English:
definition LocallyFiniteOrder.orderAddMonoidEquiv
  signature: [Nontrivial G]
  body: orderAddMonoidHom G
  __ := AddEquiv.ofBijective (orderAddMonoidHom G) orderAddMonoidHom_bijective
  map_le_map_iff' {a b} := by
    obtain ⟨b, rfl⟩ := add_left_surjective a b
    suffices 0 <= orderAddMonoidHom G b ↔ 0 <= b by simpa
    obtain hb | hb := le_total 0 b
    · simp [orderAddMonoidHom, addMonoidHom, hb]
    · simp [orderAddMonoidHom, addMonoidHom, hb]

中文:
定义 局部有限序.orderAddMonoidEquiv
  签名: [非平凡 G]
  定义体: orderAddMonoidHom G
  __ := AddEquiv.ofBijective (orderAddMonoidHom G) orderAddMonoidHom_bijective
  map_le_map_iff' {a b} := by
    obtain ⟨b, rfl⟩ := add_left_surjective a b
    suffices 0 <= orderAddMonoidHom G b ↔ 0 <= b by simpa
    obtain hb | hb := le_total 0 b
    · simp [orderAddMonoidHom, addMonoidHom, hb]
    · simp [orderAddMonoidHom, addMonoidHom, hb]

Depends on / 依赖: orderAddMonoidHom
-/
def LocallyFiniteOrder.orderAddMonoidEquiv [Nontrivial G] :
    G ≃+o Int where
  __ := orderAddMonoidHom G
  __ := AddEquiv.ofBijective (orderAddMonoidHom G) orderAddMonoidHom_bijective
  map_le_map_iff' {a b} := by
    obtain ⟨b, rfl⟩ := add_left_surjective a b
    suffices 0 <= orderAddMonoidHom G b ↔ 0 <= b by simpa
    obtain hb | hb := le_total 0 b
    · simp [orderAddMonoidHom, addMonoidHom, hb]
    · simp [orderAddMonoidHom, addMonoidHom, hb]

/--
lemma `LocallyFiniteOrder.orderAddMonoidEquiv_apply` / 引理 `LocallyFiniteOrder.orderAddMonoidEquiv_apply`

English:
lemma LocallyFiniteOrder.orderAddMonoidEquiv_apply
  given: [Nontrivial G] (x : G)
  proof: rfl

中文:
引理 局部有限序.orderAddMonoidEquiv_apply
  条件: [非平凡 G] (x : G)
  证明: rfl
-/
lemma LocallyFiniteOrder.orderAddMonoidEquiv_apply [Nontrivial G] (x : G) :
    orderAddMonoidEquiv G x = addMonoidHom G x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Any linearly ordered abelian group that is locally finite embeds to `Multiplicative ℤ`. -/
noncomputable
/--
Definition of `LocallyFiniteOrder.orderMonoidEquiv` / `LocallyFiniteOrder.orderMonoidEquiv` 的定义

English:
definition LocallyFiniteOrder.orderMonoidEquiv
  signature: (G : Type*) [CommGroup G] [LinearOrder G]
  body: have : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  (orderAddMonoidEquiv (Additive G)).toMultiplicative

中文:
定义 局部有限序.orderMonoidEquiv
  签名: (G : 类型) [交换群 G] [线性序 G]
  定义体: have : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  (orderAddMonoidEquiv (Additive G)).toMultiplicative

Depends on / 依赖: Additive, LocallyFiniteOrder, orderAddMonoidEquiv, toMultiplicative
-/
def LocallyFiniteOrder.orderMonoidEquiv (G : Type*) [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [LocallyFiniteOrder G] [Nontrivial G] :
    G ≃*o Multiplicative Int :=
  have : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  (orderAddMonoidEquiv (Additive G)).toMultiplicative

set_option backward.isDefEq.respectTransparency false in
/-- Any linearly ordered abelian group that is locally finite embeds into `Multiplicative ℤ`. -/
noncomputable
/--
Definition of `LocallyFiniteOrder.orderMonoidHom` / `LocallyFiniteOrder.orderMonoidHom` 的定义

English:
definition LocallyFiniteOrder.orderMonoidHom
  signature: (G : Type*) [CommGroup G] [LinearOrder G]
  body: have : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  ⟨(orderAddMonoidHom (Additive G)).toMultiplicative, (orderAddMonoidHom (Additive G)).2⟩

中文:
定义 局部有限序.orderMonoidHom
  签名: (G : 类型) [交换群 G] [线性序 G]
  定义体: have : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  ⟨(orderAddMonoidHom (Additive G)).toMultiplicative, (orderAddMonoidHom (Additive G)).2⟩

Depends on / 依赖: Additive, LocallyFiniteOrder, orderAddMonoidHom, toMultiplicative
-/
def LocallyFiniteOrder.orderMonoidHom (G : Type*) [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [LocallyFiniteOrder G] :
    G ->*o Multiplicative Int :=
  have : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  ⟨(orderAddMonoidHom (Additive G)).toMultiplicative, (orderAddMonoidHom (Additive G)).2⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `LocallyFiniteOrder.orderMonoidHom_strictMono` / 引理 `LocallyFiniteOrder.orderMonoidHom_strictMono`

English:
lemma LocallyFiniteOrder.orderMonoidHom_strictMono
  statement: {G : Type*} [CommGroup G] [LinearOrder G]
  proof: let : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  fun a b h => orderAddMonoidHom_strictMono h

中文:
引理 局部有限序.orderMonoidHom_strictMono
  结论: {G : 类型} [交换群 G] [线性序 G]
  证明: let : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  fun a b h => orderAddMonoidHom_strictMono h

Depends on / 依赖: Additive, LocallyFiniteOrder, orderAddMonoidHom_strictMono
-/
lemma LocallyFiniteOrder.orderMonoidHom_strictMono {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [LocallyFiniteOrder G] :
    StrictMono (orderMonoidHom G) :=
  let : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  fun a b h => orderAddMonoidHom_strictMono h

open scoped WithZero in
/-- Any nontrivial linearly ordered abelian group with zero that is locally finite
is isomorphic to `ℤᵐ⁰`. -/
noncomputable
/--
Definition of `LocallyFiniteOrder.orderMonoidWithZeroEquiv` / `LocallyFiniteOrder.orderMonoidWithZeroEquiv` 的定义

English:
definition LocallyFiniteOrder.orderMonoidWithZeroEquiv
  signature: (G : Type*) [LinearOrderedCommGroupWithZero G]
  body: OrderMonoidIso.withZeroUnits.symm.trans (LocallyFiniteOrder.orderMonoidEquiv _).withZero

中文:
定义 局部有限序.orderMonoidWithZeroEquiv
  签名: (G : 类型) [带零LinearOrderedComm群 G]
  定义体: OrderMonoidIso.withZeroUnits.symm.trans (LocallyFiniteOrder.orderMonoidEquiv _).withZero

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.orderMonoidEquiv, OrderMonoidIso, OrderMonoidIso.withZeroUnits.symm.trans, orderMonoidEquiv, withZero, withZeroUnits
-/
def LocallyFiniteOrder.orderMonoidWithZeroEquiv (G : Type*) [LinearOrderedCommGroupWithZero G]
    [LocallyFiniteOrder Gˣ] [Nontrivial Gˣ] : G ≃*o Intᵐ⁰ :=
  OrderMonoidIso.withZeroUnits.symm.trans (LocallyFiniteOrder.orderMonoidEquiv _).withZero

open scoped WithZero in
/-- Any linearly ordered abelian group with zero that is locally finite embeds into `ℤᵐ⁰`. -/
noncomputable
/--
Definition of `LocallyFiniteOrder.orderMonoidWithZeroHom` / `LocallyFiniteOrder.orderMonoidWithZeroHom` 的定义

English:
definition LocallyFiniteOrder.orderMonoidWithZeroHom
  signature: (G : Type*) [LinearOrderedCommGroupWithZero G]
  body: (WithZero.map' (orderMonoidHom Gˣ)).comp
    OrderMonoidIso.withZeroUnits.symm.toMonoidWithZeroHom
  monotone' a b h := by have := (orderMonoidHom Gˣ).monotone'; aesop

中文:
定义 局部有限序.orderMonoidWithZeroHom
  签名: (G : 类型) [带零LinearOrderedComm群 G]
  定义体: (WithZero.map' (orderMonoidHom Gˣ)).comp
    OrderMonoidIso.withZeroUnits.symm.toMonoidWithZeroHom
  monotone' a b h := by have := (orderMonoidHom Gˣ).monotone'; aesop

Depends on / 依赖: WithZero, WithZero.map, orderMonoidHom
-/
def LocallyFiniteOrder.orderMonoidWithZeroHom (G : Type*) [LinearOrderedCommGroupWithZero G]
    [LocallyFiniteOrder Gˣ] : G ->*₀o Intᵐ⁰ where
  __ := (WithZero.map' (orderMonoidHom Gˣ)).comp
    OrderMonoidIso.withZeroUnits.symm.toMonoidWithZeroHom
  monotone' a b h := by have := (orderMonoidHom Gˣ).monotone'; aesop

/--
lemma `LocallyFiniteOrder.orderMonoidWithZeroHom_strictMono` / 引理 `LocallyFiniteOrder.orderMonoidWithZeroHom_strictMono`

English:
lemma LocallyFiniteOrder.orderMonoidWithZeroHom_strictMono
  statement: {G : Type*}
  proof: by
  have := orderMonoidHom_strictMono (G := Gˣ)
  intro a b h
  aesop (add simp orderMonoidWithZeroHom)

中文:
引理 局部有限序.orderMonoidWithZeroHom_strictMono
  结论: {G : 类型}
  证明: by
  have := orderMonoidHom_strictMono (G := Gˣ)
  intro a b h
  aesop (add simp orderMonoidWithZeroHom)

Depends on / 依赖: orderMonoidHom_strictMono, orderMonoidWithZeroHom
-/
lemma LocallyFiniteOrder.orderMonoidWithZeroHom_strictMono {G : Type*}
    [LinearOrderedCommGroupWithZero G] [LocallyFiniteOrder Gˣ] :
    StrictMono (orderMonoidWithZeroHom G) := by
  have := orderMonoidHom_strictMono (G := Gˣ)
  intro a b h
  aesop (add simp orderMonoidWithZeroHom)
