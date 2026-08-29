/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Ordered structures on localizations of commutative monoids

-/

@[expose] public section

open Function

namespace Localization

variable {α : Type*}

section OrderedCancelCommMonoid

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] {s : Submonoid α}
  {a₁ b₁ : α} {a₂ b₂ : s}

@[to_additive]
/--
Instance `le` / 实例 `le`

English:
instance le
  signature: : LE (Localization s)
  body: ⟨fun a b =>
    Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ <= a₂ * b₁)
fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd => propext by
        obtain ⟨e, he⟩ := r_iff_exists.1 hab
        obtain ⟨f, hf⟩ := r_iff_exists.1 hcd
        simp only [mul_right_inj] at he hf
        rw [← mul_le_mul_iff_righ

中文:
实例 le
  签名: : LE (Localization s)
  定义体: ⟨fun a b =>
    Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ <= a₂ * b₁)
fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd => propext by
        obtain ⟨e, he⟩ := r_iff_exists.1 hab
        obtain ⟨f, hf⟩ := r_iff_exists.1 hcd
        simp only [mul_right_inj] at he hf
        rw [← mul_le_mul_iff_righ

Depends on / 依赖: Localization, Localization.liftOn, mul_le_mul_i, mul_le_mul_iff_left, mul_le_mul_iff_right, mul_left_comm, mul_right_comm, mul_right_inj, propext, r_iff_exists
-/
instance le : LE (Localization s) :=
  ⟨fun a b =>
    Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ <= a₂ * b₁)
fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd => propext by
        obtain ⟨e, he⟩ := r_iff_exists.1 hab
        obtain ⟨f, hf⟩ := r_iff_exists.1 hcd
        simp only [mul_right_inj] at he hf
        rw [← mul_le_mul_iff_right]; rw [mul_right_comm]; rw [← hf]; rw [mul_right_comm]; rw [mul_right_comm (a₂ : α)]; rw [mul_le_mul_iff_right]; rw [← mul_le_mul_iff_left]; rw [mul_left_comm]; rw [he]; rw [mul_left_comm]; rw [mul_left_comm (b₂ : α)]; rw [mul_le_mul_iff_left]⟩

@[to_additive]
/--
Instance `lt` / 实例 `lt`

English:
instance lt
  signature: : LT (Localization s)
  body: ⟨fun a b =>
    Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ < a₂ * b₁)
fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd => propext by
        obtain ⟨e, he⟩ := r_iff_exists.1 hab
        obtain ⟨f, hf⟩ := r_iff_exists.1 hcd
        simp only [mul_right_inj] at he hf
        rw [← mul_lt_mul_iff_right

中文:
实例 lt
  签名: : LT (Localization s)
  定义体: ⟨fun a b =>
    Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ < a₂ * b₁)
fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd => propext by
        obtain ⟨e, he⟩ := r_iff_exists.1 hab
        obtain ⟨f, hf⟩ := r_iff_exists.1 hcd
        simp only [mul_right_inj] at he hf
        rw [← mul_lt_mul_iff_right

Depends on / 依赖: Localization, Localization.liftOn, mul_left_comm, mul_lt_mul_if, mul_lt_mul_iff_left, mul_lt_mul_iff_right, mul_right_comm, mul_right_inj, propext, r_iff_exists
-/
instance lt : LT (Localization s) :=
  ⟨fun a b =>
    Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ < a₂ * b₁)
fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd => propext by
        obtain ⟨e, he⟩ := r_iff_exists.1 hab
        obtain ⟨f, hf⟩ := r_iff_exists.1 hcd
        simp only [mul_right_inj] at he hf
        rw [← mul_lt_mul_iff_right]; rw [mul_right_comm]; rw [← hf]; rw [mul_right_comm]; rw [mul_right_comm (a₂ : α)]; rw [mul_lt_mul_iff_right]; rw [← mul_lt_mul_iff_left]; rw [mul_left_comm]; rw [he]; rw [mul_left_comm]; rw [mul_left_comm (b₂ : α)]; rw [mul_lt_mul_iff_left]⟩

@[to_additive]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  statement: mk a₁ a₂ <= mk b₁ b₂ ↔ ↑b₂ * a₁ <= a₂ * b₁
  proof: Iff.rfl

@[to_additive]

中文:
定理 mk_le_mk
  结论: mk a₁ a₂ <= mk b₁ b₂ ↔ ↑b₂ * a₁ <= a₂ * b₁
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mk_le_mk : mk a₁ a₂ <= mk b₁ b₂ ↔ ↑b₂ * a₁ <= a₂ * b₁ :=
  Iff.rfl

@[to_additive]
/--
theorem `mk_lt_mk` / 定理 `mk_lt_mk`

English:
theorem mk_lt_mk
  statement: mk a₁ a₂ < mk b₁ b₂ ↔ ↑b₂ * a₁ < a₂ * b₁
  proof: Iff.rfl

中文:
定理 mk_lt_mk
  结论: mk a₁ a₂ < mk b₁ b₂ ↔ ↑b₂ * a₁ < a₂ * b₁
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mk_lt_mk : mk a₁ a₂ < mk b₁ b₂ ↔ ↑b₂ * a₁ < a₂ * b₁ :=
  Iff.rfl

-- declaring this separately to the instance below makes things faster
@[to_additive]
/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: : PartialOrder (Localization s) where
  body: Localization.induction_on a fun _ => le_rfl
  le_trans a b c :=
    Localization.induction_on₃ a b c fun a b c hab hbc => by
      simp only [mk_le_mk] at hab hbc ⊢
      apply le_of_mul_le_mul_left' _
      · exact ↑b.2
      grw [mul_left_comm, hab]
      rwa [mul_left_comm, mul_left_comm (b.2 : α

中文:
实例 partialOrder
  签名: : PartialOrder (Localization s) where
  定义体: Localization.induction_on a fun _ => le_rfl
  le_trans a b c :=
    Localization.induction_on₃ a b c fun a b c hab hbc => by
      simp only [mk_le_mk] at hab hbc ⊢
      apply le_of_mul_le_mul_left' _
      · exact ↑b.2
      grw [mul_left_comm, hab]
      rwa [mul_left_comm, mul_left_comm (b.2 : α

Depends on / 依赖: Localization, Localization.induction_on, induction_on, le_rfl
-/
instance partialOrder : PartialOrder (Localization s) where
  le_refl a := Localization.induction_on a fun _ => le_rfl
  le_trans a b c :=
    Localization.induction_on₃ a b c fun a b c hab hbc => by
      simp only [mk_le_mk] at hab hbc ⊢
      apply le_of_mul_le_mul_left' _
      · exact ↑b.2
      grw [mul_left_comm, hab]
      rwa [mul_left_comm, mul_left_comm (b.2 : α), mul_le_mul_iff_left]
  le_antisymm a b := by
    induction a using Localization.rec
    on_goal 1 =>
      induction b using Localization.rec
      · simp_rw [mk_le_mk, mk_eq_mk_iff, r_iff_exists]
        exact fun hab hba => ⟨1, by rw [hab.antisymm hba]⟩
    all_goals rfl
  lt_iff_le_not_ge a b := Localization.induction_on₂ a b fun _ _ => lt_iff_le_not_ge

@[to_additive]
/--
Instance `isOrderedCancelMonoid` / 实例 `isOrderedCancelMonoid`

English:
instance isOrderedCancelMonoid
  signature: : IsOrderedCancelMonoid (Localization s) where
  body: fun a b =>
    Localization.induction_on₂ a b fun a b hab c =>
      Localization.induction_on c fun c => by
        simp only [mk_mul, mk_le_mk, Submonoid.coe_mul, mul_mul_mul_comm _ (c.2 : α)] at hab ⊢
        exact mul_le_mul_left hab _
  le_of_mul_le_mul_left := fun a b c =>
    Localization.ind

中文:
实例 isOrderedCancelMonoid
  签名: : IsOrderedCancelMonoid (Localization s) where
  定义体: fun a b =>
    Localization.induction_on₂ a b fun a b hab c =>
      Localization.induction_on c fun c => by
        simp only [mk_mul, mk_le_mk, Submonoid.coe_mul, mul_mul_mul_comm _ (c.2 : α)] at hab ⊢
        exact mul_le_mul_left hab _
  le_of_mul_le_mul_left := fun a b c =>
    Localization.ind
-/
instance isOrderedCancelMonoid : IsOrderedCancelMonoid (Localization s) where
  mul_le_mul_left := fun a b =>
    Localization.induction_on₂ a b fun a b hab c =>
      Localization.induction_on c fun c => by
        simp only [mk_mul, mk_le_mk, Submonoid.coe_mul, mul_mul_mul_comm _ (c.2 : α)] at hab ⊢
        exact mul_le_mul_left hab _
  le_of_mul_le_mul_left := fun a b c =>
    Localization.induction_on₃ a b c fun a b c hab => by
      simp only [mk_mul, mk_le_mk, Submonoid.coe_mul, mul_mul_mul_comm _ _ a.1] at hab ⊢
      exact le_of_mul_le_mul_left' hab

@[to_additive]
/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: [DecidableLE α]
  body: fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_le_mk

@[to_additive]

中文:
实例 decidableLE
  签名: [DecidableLE α]
  定义体: fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_le_mk

@[to_additive]
-/
instance decidableLE [DecidableLE α] : DecidableLE (Localization s) := fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_le_mk

@[to_additive]
/--
Instance `decidableLT` / 实例 `decidableLT`

English:
instance decidableLT
  signature: [DecidableLT α]
  body: fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_lt_mk

中文:
实例 decidableLT
  签名: [DecidableLT α]
  定义体: fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_lt_mk
-/
instance decidableLT [DecidableLT α] : DecidableLT (Localization s) := fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_lt_mk

/-- An ordered cancellative monoid injects into its localization by sending `a` to `a / b`. -/
@[to_additive (attr := simps!) /-- An ordered cancellative monoid injects into its localization by
sending `a` to `a - b`. -/]
/--
Definition of `mkOrderEmbedding` / `mkOrderEmbedding` 的定义

English:
definition mkOrderEmbedding
  signature: (b : s)
  body: mk a b
  inj' := mk_left_injective _
  map_rel_iff' {a b} := by simp [mk_le_mk]

中文:
定义 mkOrderEmbedding
  签名: (b : s)
  定义体: mk a b
  inj' := mk_left_injective _
  map_rel_iff' {a b} := by simp [mk_le_mk]
-/
def mkOrderEmbedding (b : s) : α ↪o Localization s where
  toFun a := mk a b
  inj' := mk_left_injective _
  map_rel_iff' {a b} := by simp [mk_le_mk]

end OrderedCancelCommMonoid

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: α] [LinearOrder α] [IsOrderedCancelMonoid α] {s
  body: { le_total := fun a b =>
      Localization.induction_on₂ a b fun _ _ => by
        simp_rw [mk_le_mk]
        exact le_total _ _
    toDecidableLE := Localization.decidableLE
    toDecidableLT := Localization.decidableLT
    toDecidableEq := Localization.decidableEq }

中文:
实例 [CommMonoid
  签名: α] [LinearOrder α] [IsOrderedCancelMonoid α] {s
  定义体: { le_total := fun a b =>
      Localization.induction_on₂ a b fun _ _ => by
        simp_rw [mk_le_mk]
        exact le_total _ _
    toDecidableLE := Localization.decidableLE
    toDecidableLT := Localization.decidableLT
    toDecidableEq := Localization.decidableEq }

Depends on / 依赖: Localization, Localization.decidableEq, Localization.decidableLE, Localization.decidableLT, Localization.induction_on, decidableEq, decidableLE, decidableLT, le_total, mk_le_mk, simp_rw, toDecidableEq, toDecidableLE, toDecidableLT
-/
instance [CommMonoid α] [LinearOrder α] [IsOrderedCancelMonoid α] {s : Submonoid α} :
    LinearOrder (Localization s) :=
  { le_total := fun a b =>
      Localization.induction_on₂ a b fun _ _ => by
        simp_rw [mk_le_mk]
        exact le_total _ _
    toDecidableLE := Localization.decidableLE
    toDecidableLT := Localization.decidableLT
    toDecidableEq := Localization.decidableEq }

end Localization
