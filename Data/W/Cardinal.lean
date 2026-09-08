/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.W.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinality of W-types

This file proves some theorems about the cardinality of W-types. The main result is
`cardinalMk_le_max_aleph0_of_finite` which says that if for any `a : α`,
`β a` is finite, then the cardinality of `WType β` is at most the maximum of the
cardinality of `α` and `ℵ₀`.
This can be used to prove theorems about the cardinality of algebraic constructions such as
polynomials. There is a surjection from a `WType` to `MvPolynomial` for example, and
this surjection can be used to put an upper bound on the cardinality of `MvPolynomial`.

## Tags

W, W type, cardinal, first order
-/

public section


universe u v

variable {α : Type u} {β : α → Type v}

noncomputable section

namespace WType

open Cardinal


/-
**WType.cardinalMk_eq_sum_lift** 是 Mathlib 中的一个定理，位于命名空间 `WType`。
形式化陈述：cardinalMk_eq_sum_lift : #(WType β) = sum fun a => #(WType β) ^ lift.{u} #
(β a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.mk_arrow`：mk_arrow (α : Type u) (β : Type v) : #(α -> β) = (lif
t.{u} #β ^ lift.{v} #α)
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
-/
theorem cardinalMk_eq_sum_lift : #(WType β) = sum fun a ↦ #(WType β) ^ lift.{u} #(β a) :=
  (mk_congr <| equivSigma β).trans <| by
    simp_rw [mk_sigma, mk_arrow]; rw [lift_id'.{v, u}, lift_umax.{v, u}]

/-- `#(WType β)` is the least cardinal `κ` such that `sum (fun a : α ↦ κ ^ #(β a)) ≤ κ` -/
/-
**WType.cardinalMk_le_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `WType`。
形式化陈述：cardinalMk_le_of_le' {κ : Cardinal.{max u v}} (hκ : (sum fun a : α => κ ^ 
lift.{u} #(β a)) <= κ) : #(WType β) <= κ
参数：hκ : (sum fun a : α => κ ^ lift.{u} #(β a)) <= κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_le_of_injective`：mk_le_of_injective {α β : Type u} {f : α ->
 β} (hf : Injective f) : #α <= #β
· 使用定理 `WType.elim_injective`：elim_injective (γ : Type*) (fγ : (Σ a : α, β a -> 
γ) -> γ) (fγ_injective : Function.Injective fγ) : Function.Injective (elim γ fγ)
 | ⟨a₁, f₁…
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun

--- 原说明 ---
`#(WType β)` is the least cardinal `κ` such that `sum (fun a : α ↦ κ ^ #(β a)) ≤
 κ`
-/
theorem cardinalMk_le_of_le' {κ : Cardinal.{max u v}}
    (hκ : (sum fun a : α => κ ^ lift.{u} #(β a)) ≤ κ) :
    #(WType β) ≤ κ := by
  induction κ using Cardinal.inductionOn with | _ γ
  simp_rw [← lift_umax.{v, u}] at hκ
  nth_rewrite 1 [← lift_id'.{v, u} #γ] at hκ
  simp_rw [← mk_arrow, ← mk_sigma, le_def] at hκ
  obtain ⟨hκ⟩ := hκ
  exact Cardinal.mk_le_of_injective (elim_injective _ hκ.1 hκ.2)

/-- If, for any `a : α`, `β a` is finite, then the cardinality of `WType β`
is at most the maximum of the cardinality of `α` and `ℵ₀` -/
/-
**WType.cardinalMk_le_max_aleph0_of_finite'** 是 Mathlib 中的一个定理，位于命名空间 `WType`。
形式化陈述：cardinalMk_le_max_aleph0_of_finite' [forall a, Finite (β a)] : #(WType β) 
<= max (lift.{v} #α) ℵ₀
参数：β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `WType.instIsEmpty`：∀ {α : Type u_1} {β : α → Type u_2} [hα : IsEmpty α],
 IsEmpty (WType β)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.lift_zero`：lift_zero : lift 0 = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `WType.cardinalMk_le_of_le'`：cardinalMk_le_of_le' {κ : Cardinal.{max u v}
} (hκ : (sum fun a : α => κ ^ lift.{u} #(β a)) <= κ) : #(WType β) <= κ
· 使用定理 `Cardinal.sum_le_lift_mk_mul_iSup`：sum_le_lift_mk_mul_iSup {ι : Type u} (
f : ι -> Cardinal.{max u v}) : sum f <= lift #ι * ⨆ i, f i
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Cardinal.mul_eq_left`：mul_eq_left {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 
b <= a) (hb' : b != 0) : a * b = a
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `Cardinal.pow_le`：pow_le {κ μ : Cardinal.{u}} (H1 : ℵ₀ <= κ) (H2 : μ < ℵ₀
) : κ ^ μ <= κ
· 使用定理 `Cardinal.lt_aleph0_of_finite`：lt_aleph0_of_finite (α : Type u) [Finite α
] : #α < ℵ₀
· 使用定理 `instFiniteULift`：∀ {α : Type v} [Finite α], Finite (ULift.{u, v} α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Cardinal.succ_zero`：succ_zero : succ (0 : Cardinal) = 1
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If, for any `a : α`, `β a` is finite, then the cardinality of `WType β`
is at most the maximum of the cardinality of `α` and `ℵ₀`
-/
theorem cardinalMk_le_max_aleph0_of_finite' [∀ a, Finite (β a)] :
    #(WType β) ≤ max (lift.{v} #α) ℵ₀ :=
  (isEmpty_or_nonempty α).elim (fun _ ↦ by simp)
    fun hn =>
    let m := max (lift.{v} #α) ℵ₀
    cardinalMk_le_of_le' <|
      calc
        (Cardinal.sum fun a => m ^ lift.{u} #(β a)) ≤ lift.{v} #α * ⨆ a, m ^ lift.{u} #(β a) :=
          Cardinal.sum_le_lift_mk_mul_iSup _
        _ ≤ m * ⨆ a, m ^ lift.{u} #(β a) := mul_le_mul' (le_max_left _ _) le_rfl
        _ = m :=
          mul_eq_left (le_max_right _ _)
              (ciSup_le' fun _ => pow_le (le_max_right _ _) (lt_aleph0_of_finite _)) <|
            pos_iff_ne_zero.1 <|
              Order.succ_le_iff.1
                (by
                  rw [succ_zero]
                  obtain ⟨a⟩ : Nonempty α := hn
                  refine le_trans ?_ (le_ciSup bddAbove_of_small a)
                  rw [← power_zero]
                  exact
                    power_le_power_left
                      (pos_iff_ne_zero.1 (aleph0_pos.trans_le (le_max_right _ _))) zero_le)

variable {β : α → Type u}
/-
**WType.cardinalMk_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `WType`。
形式化陈述：cardinalMk_eq_sum : #(WType β) = sum (fun a : α => #(WType β) ^ #(β a))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WType.cardinalMk_eq_sum_lift`：cardinalMk_eq_sum_lift : #(WType β) = sum 
fun a => #(WType β) ^ lift.{u} #(β a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardinalMk_eq_sum : #(WType β) = sum (fun a : α => #(WType β) ^ #(β a)) :=
  cardinalMk_eq_sum_lift.trans <| by simp_rw [lift_id]

/-- `#(WType β)` is the least cardinal `κ` such that `sum (fun a : α ↦ κ ^ #(β a)) ≤ κ` -/
/-
**WType.cardinalMk_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `WType`。
形式化陈述：cardinalMk_le_of_le {κ : Cardinal.{u}} (hκ : (sum fun a : α => κ ^ #(β a))
 <= κ) : #(WType β) <= κ
参数：hκ : (sum fun a : α => κ ^ #(β a)) <= κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WType.cardinalMk_le_of_le'`：cardinalMk_le_of_le' {κ : Cardinal.{max u v}
} (hκ : (sum fun a : α => κ ^ lift.{u} #(β a)) <= κ) : #(WType β) <= κ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a

--- 原说明 ---
`#(WType β)` is the least cardinal `κ` such that `sum (fun a : α ↦ κ ^ #(β a)) ≤
 κ`
-/
theorem cardinalMk_le_of_le {κ : Cardinal.{u}} (hκ : (sum fun a : α => κ ^ #(β a)) ≤ κ) :
    #(WType β) ≤ κ := cardinalMk_le_of_le' <| by simp_rw [lift_id]; exact hκ

/-- If, for any `a : α`, `β a` is finite, then the cardinality of `WType β`
is at most the maximum of the cardinality of `α` and `ℵ₀` -/
/-
**WType.cardinalMk_le_max_aleph0_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `WType`。
形式化陈述：cardinalMk_le_max_aleph0_of_finite [forall a, Finite (β a)] : #(WType β) <
= max #α ℵ₀
参数：β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `WType.cardinalMk_le_max_aleph0_of_finite'`：cardinalMk_le_max_aleph0_of_f
inite' [forall a, Finite (β a)] : #(WType β) <= max (lift.{v} #α) ℵ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a

--- 原说明 ---
If, for any `a : α`, `β a` is finite, then the cardinality of `WType β`
is at most the maximum of the cardinality of `α` and `ℵ₀`
-/
theorem cardinalMk_le_max_aleph0_of_finite [∀ a, Finite (β a)] : #(WType β) ≤ max #α ℵ₀ :=
  cardinalMk_le_max_aleph0_of_finite'.trans_eq <| by rw [lift_id]

end WType

