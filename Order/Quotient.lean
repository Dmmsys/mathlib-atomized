/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected

/-!
### Order instances on quotients

We define a `Preorder` instance on a general `Quotient`, as the transitive closure of the
`x ≤ y ∨ x ≈ y` relation. This is the quotient object in the category of preorders.

We show that in the case of a linear order with `Set.OrdConnected` equivalence classes, this
relation is automatically transitive (we don't need to take the transitive closure), and gives a
`LinearOrder` structure on the quotient. In that case, the resulting order is sometimes called a
**condensation**.
-/

@[expose] public section

open Set

variable {α : Type*} {s : Setoid α}

namespace Quotient

section LE
variable [LE α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Quotient s)
  body: Quotient.lift₂ (Relation.TransGen fun x y => x <= y ∨ x ≈ y) by
    refine fun x₁ x₂ y₁ y₂ hx hy => propext ⟨?_, ?_⟩ <;> intro h
· exact .trans (.single <| .inr (symm hx)) .trans h (.single <| .inr hy)
· exact .trans (.single <| .inr hx) .trans h (.single <| .inr (symm hy))

中文:
实例 :
  签名: LE (Quotient s)
  定义体: Quotient.lift₂ (Relation.TransGen fun x y => x <= y ∨ x ≈ y) by
    refine fun x₁ x₂ y₁ y₂ hx hy => propext ⟨?_, ?_⟩ <;> intro h
· exact .trans (.single <| .inr (symm hx)) .trans h (.single <| .inr hy)
· exact .trans (.single <| .inr hx) .trans h (.single <| .inr (symm hy))

Depends on / 依赖: Quotient, Quotient.lift, Relation, Relation.TransGen, TransGen, propext, single
-/
instance : LE (Quotient s) where
le := Quotient.lift₂ (Relation.TransGen fun x y => x <= y ∨ x ≈ y) by
    refine fun x₁ x₂ y₁ y₂ hx hy => propext ⟨?_, ?_⟩ <;> intro h
· exact .trans (.single <| .inr (symm hx)) .trans h (.single <| .inr hy)
· exact .trans (.single <| .inr hx) .trans h (.single <| .inr (symm hy))

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {x y : α}
  proof: .rfl

中文:
定理 le_def
  条件: {x y : α}
  证明: .rfl

Depends on / 依赖: _spec, lift_mk, toLocalizationMap
-/
theorem le_def {x y : α} :
    Quotient.mk s x <= Quotient.mk s y ↔ Relation.TransGen (fun x y => x <= y ∨ x ≈ y) x y := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Refl (Quotient s) (· <= ·)
  body: by
    induction x using Quotient.inductionOn with | h x
exact .single .inr (refl x)

中文:
实例 :
  签名: @Std.Refl (Quotient s) (· <= ·)
  定义体: by
    induction x using Quotient.inductionOn with | h x
exact .single .inr (refl x)

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, single
-/
instance : @Std.Refl (Quotient s) (· <= ·) where
  refl x := by
    induction x using Quotient.inductionOn with | h x
exact .single .inr (refl x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrans (Quotient s) (· <= ·)
  body: by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    induction z using Quotient.inductionOn with | h z
    exact Relation.TransGen.trans h₁ h₂

中文:
实例 :
  签名: IsTrans (Quotient s) (· <= ·)
  定义体: by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    induction z using Quotient.inductionOn with | h z
    exact Relation.TransGen.trans h₁ h₂

Depends on / 依赖: Quotient, Quotient.inductionOn, Relation, Relation.TransGen.trans, TransGen, inductionOn
-/
instance : IsTrans (Quotient s) (· <= ·) where
  trans x y z h₁ h₂ := by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    induction z using Quotient.inductionOn with | h z
    exact Relation.TransGen.trans h₁ h₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [@Std.Total
  signature: α (· <= ·)] : @Std.Total (Quotient s) (· <= ·) where
  body: by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    obtain h | h := total_of (· <= ·) x y
· exact .inl .single .inl h
· exact .inr .single .inl h

中文:
实例 [@Std.Total
  签名: α (· <= ·)] : @Std.Total (Quotient s) (· <= ·) where
  定义体: by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    obtain h | h := total_of (· <= ·) x y
· exact .inl .single .inl h
· exact .inr .single .inl h

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, single, total_of
-/
instance [@Std.Total α (· <= ·)] : @Std.Total (Quotient s) (· <= ·) where
  total x y := by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    obtain h | h := total_of (· <= ·) x y
· exact .inl .single .inl h
· exact .inr .single .inl h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (Quotient s)
  body: refl
  le_trans _ _ _ := _root_.trans

中文:
实例 :
  签名: Preorder (Quotient s)
  定义体: refl
  le_trans _ _ _ := _root_.trans
-/
instance : Preorder (Quotient s) where
  le_refl := refl
  le_trans _ _ _ := _root_.trans

end LE

section Preorder
variable [Preorder α]

/--
theorem `mk_monotone` / 定理 `mk_monotone`

English:
theorem mk_monotone
  statement: Monotone (Quotient.mk s)
  proof: fun _ _ h => .single (.inl h)

中文:
定理 mk_monotone
  结论: Monotone (Quotient.mk s)
  证明: fun _ _ h => .single (.inl h)

Depends on / 依赖: single
-/
theorem mk_monotone : Monotone (Quotient.mk s) :=
  fun _ _ h => .single (.inl h)

/--
theorem `lift_monotone` / 定理 `lift_monotone`

English:
theorem lift_monotone
  statement: {α β : Type*} [Preorder α] {s : Setoid α} [Preorder β]
  proof: by
  intro x y h
  induction x using Quotient.inductionOn with | h x
  induction y using Quotient.inductionOn with | h y
  induction h
  on_goal 2 => rename_i IH; apply IH.trans
  all_goals
    rename_i h
    cases h with
    | inl h => exact hf h
    | inr h => exact (H _ _ h).le

中文:
定理 lift_monotone
  结论: {α β : 类型} [Preorder α] {s : Setoid α} [Preorder β]
  证明: by
  intro x y h
  induction x using Quotient.inductionOn with | h x
  induction y using Quotient.inductionOn with | h y
  induction h
  on_goal 2 => rename_i IH; apply IH.trans
  all_goals
    rename_i h
    cases h with
    | inl h => exact hf h
    | inr h => exact (H _ _ h).le

Depends on / 依赖: IH.trans, Quotient, Quotient.inductionOn, all_goals, inductionOn, on_goal, rename_i
-/
theorem lift_monotone {α β : Type*} [Preorder α] {s : Setoid α} [Preorder β]
    (f : α -> β) (hf : Monotone f) (H : forall x₁ x₂, x₁ ≈ x₂ -> f x₁ = f x₂) :
    Monotone (Quotient.lift f H) := by
  intro x y h
  induction x using Quotient.inductionOn with | h x
  induction y using Quotient.inductionOn with | h y
  induction h
  on_goal 2 => rename_i IH; apply IH.trans
  all_goals
    rename_i h
    cases h with
    | inl h => exact hf h
    | inr h => exact (H _ _ h).le

end Preorder

section LinearOrder
variable [LinearOrder α] [H : forall x, OrdConnected (Quotient.mk s ⁻¹' {x})]

/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: {x y : α}
  statement: Quotient.mk s x <= Quotient.mk s y ↔ x <= y ∨ x ≈ y
  proof: by
  rw [← propext_iff]
  revert x y
apply congrFun₂ @Relation.transGen_eq_self α _ ⟨fun x y z h₁ h₂ => ?_⟩
  cases h₁ <;> cases h₂ <;> rename_i h₁ h₂
· exact .inl h₁.trans h₂
  · rw [or_iff_not_imp_left, not_le]
    rw [← Quotient.eq_iff_equiv] at *
    exact fun h => ((H _).out h₂.symm rfl ⟨h.le, 

中文:
定理 mk_le_mk
  条件: {x y : α}
  结论: Quotient.mk s x <= Quotient.mk s y ↔ x <= y ∨ x ≈ y
  证明: by
  rw [← propext_iff]
  revert x y
apply congrFun₂ @Relation.transGen_eq_self α _ ⟨fun x y z h₁ h₂ => ?_⟩
  cases h₁ <;> cases h₂ <;> rename_i h₁ h₂
· exact .inl h₁.trans h₂
  · rw [or_iff_not_imp_left, not_le]
    rw [← Quotient.eq_iff_equiv] at *
    exact fun h => ((H _).out h₂.symm rfl ⟨h.le, 

Depends on / 依赖: Quotient, Quotient.eq_iff_equiv, Relation, Relation.transGen_eq_self, _root_, _root_.trans, eq_iff_equiv, h.le, not_le, or_iff_not_imp_left, propext_iff, rename_i, revert, transGen_eq_self
-/
theorem mk_le_mk {x y : α} : Quotient.mk s x <= Quotient.mk s y ↔ x <= y ∨ x ≈ y := by
  rw [← propext_iff]
  revert x y
apply congrFun₂ @Relation.transGen_eq_self α _ ⟨fun x y z h₁ h₂ => ?_⟩
  cases h₁ <;> cases h₂ <;> rename_i h₁ h₂
· exact .inl h₁.trans h₂
  · rw [or_iff_not_imp_left, not_le]
    rw [← Quotient.eq_iff_equiv] at *
    exact fun h => ((H _).out h₂.symm rfl ⟨h.le, h₁⟩).trans h₂
  · rw [or_iff_not_imp_left, not_le]
    rw [← Quotient.eq_iff_equiv] at *
    exact fun h => ((H _).out h₁.symm rfl ⟨h₂, h.le⟩).symm
  · exact .inr (_root_.trans h₁ h₂)

/--
Instance `instLinearOrder` / 实例 `instLinearOrder`

English:
instance instLinearOrder
  signature: [DecidableRel (· ≈ · : α -> α -> Prop)]
  body: by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    rw [mk_le_mk] at h₁ h₂
    cases h₁ with
    | inr h => exact Quotient.sound h
    | inl h₁ =>
      cases h₂ with
      | inr h => exact (Quotient.sound h).symm
      | inl h₂ => exact

中文:
实例 instLinearOrder
  签名: [DecidableRel (· ≈ · : α -> α -> 命题)]
  定义体: by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    rw [mk_le_mk] at h₁ h₂
    cases h₁ with
    | inr h => exact Quotient.sound h
    | inl h₁ =>
      cases h₂ with
      | inr h => exact (Quotient.sound h).symm
      | inl h₂ => exact

Depends on / 依赖: Quotient, Quotient.inductionOn, Quotient.recOnSubsingleton, Quotient.sound, antisymm, decidable_of_iff, inductionOn, le_total, mk_le_mk, toDecidableLE, total_of
-/
instance instLinearOrder [DecidableRel (· ≈ · : α -> α -> Prop)] : LinearOrder (Quotient s) where
  le_antisymm x y h₁ h₂ := by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    rw [mk_le_mk] at h₁ h₂
    cases h₁ with
    | inr h => exact Quotient.sound h
    | inl h₁ =>
      cases h₂ with
      | inr h => exact (Quotient.sound h).symm
      | inl h₂ => exact congrArg _ (h₁.antisymm h₂)
  le_total := total_of _
  toDecidableLE x y := Quotient.recOnSubsingleton₂ x y fun x y => decidable_of_iff' _ mk_le_mk

/--
theorem `mk_lt_mk` / 定理 `mk_lt_mk`

English:
theorem mk_lt_mk
  given: {x y : α}
  statement: Quotient.mk s x < Quotient.mk s y ↔ x < y ∧ ¬ x ≈ y
  proof: by
  classical
  contrapose! +distrib
  rw [mk_le_mk]; rw [comm_of (· ≈ ·)]

中文:
定理 mk_lt_mk
  条件: {x y : α}
  结论: Quotient.mk s x < Quotient.mk s y ↔ x < y ∧ ¬ x ≈ y
  证明: by
  classical
  contrapose! +distrib
  rw [mk_le_mk]; rw [comm_of (· ≈ ·)]

Depends on / 依赖: classical, comm_of, contrapose, distrib, mk_le_mk
-/
theorem mk_lt_mk {x y : α} : Quotient.mk s x < Quotient.mk s y ↔ x < y ∧ ¬ x ≈ y := by
  classical
  contrapose! +distrib
  rw [mk_le_mk]; rw [comm_of (· ≈ ·)]

/--
theorem `lt_of_mk_lt_mk` / 定理 `lt_of_mk_lt_mk`

English:
theorem lt_of_mk_lt_mk
  given: {x y : α} (h : Quotient.mk s x < Quotient.mk s y)
  statement: x < y
  proof: (mk_lt_mk.1 h).1

中文:
定理 lt_of_mk_lt_mk
  条件: {x y : α} (h : Quotient.mk s x < Quotient.mk s y)
  结论: x < y
  证明: (mk_lt_mk.1 h).1

Depends on / 依赖: mk_lt_mk
-/
theorem lt_of_mk_lt_mk {x y : α} (h : Quotient.mk s x < Quotient.mk s y) : x < y :=
  (mk_lt_mk.1 h).1

end LinearOrder
end Quotient
