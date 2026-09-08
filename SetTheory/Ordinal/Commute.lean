/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Ordinal arithmetic commutativity

Results on the commutativity of ordinal arithmetic operations.

## References

* [Wacław Sierpiński, *Cardinal and Ordinal Numbers*][sierpinski1958]
-/

public section

namespace Ordinal

/-
**Ordinal.addCommute_iff_eq_mul_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：addCommute_iff_eq_mul_natCast {o₁ o₂ : Ordinal} : AddCommute o₁ o₂ ↔ exist
s (o : Ordinal) (n₁ n₂ : Nat), o * n₁ = o₁ ∧ o * n₂ = o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `Ordinal.instIsLeftCancelAdd`：IsLeftCancelAdd Ordinal.{u_4}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AddCommute.eq`：∀ {S : Type u_3} [inst : Add S] {a b : S}, AddCommute a b
 → a + b = b + a
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `addCommute_iff_eq`：∀ {S : Type u_3} [inst : Add S] (a b : S), AddCommute
 a b ↔ a + b = b + a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem addCommute_iff_eq_mul_natCast {o₁ o₂ : Ordinal} :
    AddCommute o₁ o₂ ↔ ∃ (o : Ordinal) (n₁ n₂ : ℕ), o * n₁ = o₁ ∧ o * n₂ = o₂ := by
  refine ⟨fun hcomm ↦ ?_, ?_⟩
  · induction h : o₁ + o₂ using WellFoundedLT.induction generalizing o₁ o₂ with | ind o ih
    subst h
    wlog hle : o₁ ≤ o₂
    · grind [hcomm.symm]
    rcases eq_or_ne o₁ 0 with (rfl | h₁)
    · exact ⟨o₂, 0, 1, by simp, by simp⟩
    let o₃ := o₂ - o₁
    have hsub : o₁ + o₃ = o₂ := Ordinal.add_sub_cancel_of_le hle
    have hcomm' : AddCommute o₁ o₃ := add_left_cancel (a := o₁) <| by grind
    have hlt : o₁ + o₃ < o₁ + o₂ := by simpa [hsub, hcomm.eq] using h₁.pos
    rcases ih _ hlt hcomm' rfl with ⟨o, n₁, n₃, hn₁, hn₃⟩
    use o, n₁, n₁ + n₃, hn₁
    rw [Nat.cast_add, mul_add, hn₁, hn₃, hsub]
  · rintro ⟨o, n₁, n₂, rfl, rfl⟩
    rw [addCommute_iff_eq, ← mul_add, ← mul_add, ← Nat.cast_add, add_comm, Nat.cast_add]

end Ordinal

