/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.SuccPred.InitialSeg
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Ordinal arithmetic

Ordinals have an addition (corresponding to the disjoint union) that turns them into an additive
monoid, and a multiplication (corresponding to the lexicographic order on the product) that turns
them into a monoid. One can also define (truncated) subtraction and division operators.

Ordinal powers and logarithms are defined in `Mathlib.SetTheory.Ordinal.Exponential`.

## Main definitions and results

* `a + b` is the order type of the lexicographic sum `a ⊕ₗ b`.
* `a - b` is the unique ordinal `c` such that `b + c = a`, when `b ≤ a`.
* `a * b` is the order type of the lexicographic product `b ×ₗ a`.
* `a / b` is the ordinal `q` such that `a = b * q + r` with `r < b`. We also define the
  divisibility predicate, and a modulo operation.
* `limitRecOn` is limit recursion on ordinals, i.e. well-founded recursion separating out the zero,
  successor, and limit cases.

We discuss the properties of casts of natural numbers of and of `ω` with respect to these
operations.

Note that some basic functions and properties of ordinals have been generalized to other orders, and
exist on other files:

* `Order.succ o = o + 1` is the successor of `o`.
* `Order.IsSuccLimit o`: an ordinal is a limit ordinal if it is neither `0` nor a successor.
* `Order.IsNormal`: a function `f : Ordinal → Ordinal` is normal if it is strictly increasing and
  order-continuous, i.e., the image `f o` of a limit ordinal `o` is the supremum of `f a`
  for `a < o`.

Various other basic arithmetic results are given in `Principal.lean` instead.
-/

@[expose] public noncomputable section

assert_not_exists Field Module

open Function Cardinal Set Equiv Order

universe u v w

namespace Ordinal

variable {α β γ : Type*} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Further properties of addition on ordinals -/

@[simp]
/-
**Ordinal.lift_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_add (a b : Ordinal.{v}) : lift.{u} (a + b) = lift.{u} a + lift.{u} b
参数：a b : Ordinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Sum.instIsWellOrderLex`：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Pro
p) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s],   IsWellOrder (α ⊕ β)
 (Sum.Lex r …

--- 原说明 ---
### Further properties of addition on ordinals
-/
theorem lift_add (a b : Ordinal.{v}) : lift.{u} (a + b) = lift.{u} a + lift.{u} b :=
  Quotient.inductionOn₂ a b fun ⟨_α, _r, _⟩ ⟨_β, _s, _⟩ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans
          (RelIso.sumLexCongr (RelIso.preimage Equiv.ulift _) (RelIso.preimage Equiv.ulift _)).symm⟩
/-
**Ordinal.lift_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_add_one (a : Ordinal.{v}) : lift.{u} (a + 1) = lift.{u} a + 1
参数：a : Ordinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lift_add`：lift_add (a b : Ordinal.{v}) : lift.{u} (a + b) = lift
.{u} a + lift.{u} b
· 使用定理 `Ordinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_add_one (a : Ordinal.{v}) : lift.{u} (a + 1) = lift.{u} a + 1 := by
  simp

-- TODO: deprecate
/-
**Ordinal.lift_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_succ (a : Ordinal.{v}) : lift.{u} (succ a) = succ (lift.{u} a)
参数：a : Ordinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_add_one`：lift_add_one (a : Ordinal.{v}) : lift.{u} (a + 1) 
= lift.{u} a + 1
-/
theorem lift_succ (a : Ordinal.{v}) : lift.{u} (succ a) = succ (lift.{u} a) :=
  lift_add_one a
/-
**Ordinal.instAddLeftReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：instAddLeftReflectLE : AddLeftReflectLE Ordinal.{u} where le_of_add_le_add
_left {c a b}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOn₃`：inductionOn₃ {motive : Ordinal -> Ordinal -> Ordin
al -> Prop} (o₁ o₂ o₃ : Ordinal) (type : forall (α r) [IsWellOrder α r] (β s) [I
sWellOrder…
· 使用定理 `InitialSeg.eq`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β
 → β → Prop} [IsWellOrder β s] (f g : InitialSeg r s) (a : α),   f a = g a
· 使用定理 `Sum.instIsWellOrderLex`：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Pro
p) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s],   IsWellOrder (α ⊕ β)
 (Sum.Lex r …
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InitialSeg.inj`：inj (f : r ≼i s) {a b : α} : f a = f b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RelEmbedding.ordinal_type_le`：∀ {α β : Type u_1} {r : α → α → Prop} {s :
 β → β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ↪r s
), Ordinal.type r …
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `Sum.lex_inr_inr`：∀ {α : Type u_1} {r : α → α → Prop} {β : Type u_2} {s :
 β → β → Prop} {b₁ b₂ : β},   Sum.Lex r s (Sum.inr b₁) (Sum.inr b₂) ↔ s b₁ b₂
· 使用定理 `InitialSeg.map_rel_iff`：map_rel_iff {a b : α} (f : r ≼i s) : s (f a) (f 
b) ↔ r a b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
instance instAddLeftReflectLE : AddLeftReflectLE Ordinal.{u} where
  le_of_add_le_add_left {c a b} := by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ ↦ ?_
    have H₁ a : f (Sum.inl a) = Sum.inl a := by
      simpa using ((InitialSeg.leAdd t r).trans f).eq (InitialSeg.leAdd t s) a
    have H₂ a : ∃ b, f (Sum.inr a) = Sum.inr b := by
      generalize hx : f (Sum.inr a) = x
      obtain x | x := x
      · rw [← H₁, f.inj] at hx
        contradiction
      · exact ⟨x, rfl⟩
    choose g hg using H₂
    refine (RelEmbedding.ofMonotone g fun _ _ h ↦ ?_).ordinal_type_le
    rwa [← @Sum.lex_inr_inr _ t _ s, ← hg, ← hg, f.map_rel_iff, Sum.lex_inr_inr]
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLeftCancelAdd Ordinal where
  add_left_cancel a b c h := by simpa only [le_antisymm_iff, add_le_add_iff_left] using h
/-
**Ordinal.add_lt_add_iff_left'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem add_lt_add_iff_left' (a) {b c : Ordinal} : a + b < a + c ↔ b < c := by
  rw [← not_le, ← not_le, add_le_add_iff_left]
/-
**Ordinal.instAddLeftStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：instAddLeftStrictMono : AddLeftStrictMono Ordinal.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Arithmetic.0.Ordinal.add_lt_add_iff_l
eft'`：∀ (a : Ordinal.{u_4}) {b c : Ordinal.{u_4}}, a + b < a + c ↔ b < c
-/
instance instAddLeftStrictMono : AddLeftStrictMono Ordinal.{u} :=
  ⟨fun a _b _c ↦ (add_lt_add_iff_left' a).2⟩
/-
**Ordinal.instAddLeftReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：instAddLeftReflectLT : AddLeftReflectLT Ordinal.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Arithmetic.0.Ordinal.add_lt_add_iff_l
eft'`：∀ (a : Ordinal.{u_4}) {b c : Ordinal.{u_4}}, a + b < a + c ↔ b < c
-/
instance instAddLeftReflectLT : AddLeftReflectLT Ordinal.{u} :=
  ⟨fun a _b _c ↦ (add_lt_add_iff_left' a).1⟩
/-
**Ordinal.instAddRightReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：instAddRightReflectLT : AddRightReflectLT Ordinal.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
-/
instance instAddRightReflectLT : AddRightReflectLT Ordinal.{u} :=
  ⟨fun _a _b _c ↦ lt_imp_lt_of_le_imp_le fun h => add_le_add_left h _⟩
/-
**Ordinal.add_le_add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {a b : Ordinal.{u_4}} (n : ℕ), a + ↑n ≤ b + ↑n ↔ a ≤ b
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_le_add_iff_right {a b : Ordinal} : ∀ n : ℕ, a + n ≤ b + n ↔ a ≤ b
  | 0 => by simp
  | n + 1 => by simpa [← add_assoc] using add_le_add_iff_right n
/-
**Ordinal.add_right_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_right_cancel {a b : Ordinal} (n : Nat) : a + n = b + n ↔ a = b
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_right_cancel {a b : Ordinal} (n : ℕ) : a + n = b + n ↔ a = b := by
  simp only [le_antisymm_iff, add_le_add_iff_right]

@[simp]
/-
**Ordinal.add_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_eq_zero_iff {a b : Ordinal} : a + b = 0 ↔ a = 0 ∧ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOn₂`：inductionOn₂ {motive : Ordinal -> Ordinal -> Prop}
 (o₁ o₂ : Ordinal) (type : forall (α r) [IsWellOrder α r] (β s) [IsWellOrder β s
], motive …
· 使用定理 `Sum.instIsWellOrderLex`：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Pro
p) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s],   IsWellOrder (α ⊕ β)
 (Sum.Lex r …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isEmpty_sum`：isEmpty_sum {α β} : IsEmpty (α oplus β) ↔ IsEmpty α ∧ IsEmp
ty β
-/
theorem add_eq_zero_iff {a b : Ordinal} : a + b = 0 ↔ a = 0 ∧ b = 0 :=
  inductionOn₂ a b fun α r _ β s _ => by
    simp_rw [← type_sum_lex, type_eq_zero_iff_isEmpty]
    exact isEmpty_sum
/-
**Ordinal.left_eq_zero_of_add_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：left_eq_zero_of_add_eq_zero {a b : Ordinal} (h : a + b = 0) : a = 0
参数：h : a + b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.add_eq_zero_iff`：add_eq_zero_iff {a b : Ordinal} : a + b = 0 ↔ a
 = 0 ∧ b = 0
-/
theorem left_eq_zero_of_add_eq_zero {a b : Ordinal} (h : a + b = 0) : a = 0 :=
  (add_eq_zero_iff.1 h).1
/-
**Ordinal.right_eq_zero_of_add_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：right_eq_zero_of_add_eq_zero {a b : Ordinal} (h : a + b = 0) : b = 0
参数：h : a + b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.add_eq_zero_iff`：add_eq_zero_iff {a b : Ordinal} : a + b = 0 ↔ a
 = 0 ∧ b = 0
-/
theorem right_eq_zero_of_add_eq_zero {a b : Ordinal} (h : a + b = 0) : b = 0 :=
  (add_eq_zero_iff.1 h).2

/-! ### Limit ordinals -/

/-
**Ordinal.isSuccLimit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_iff {o : Ordinal} : IsSuccLimit o ↔ o != 0 ∧ IsSuccPrelimit o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isSuccLimit_iff_of_orderBot`：isSuccLimit_iff_of_orderBot [OrderBot
 α] : IsSuccLimit a ↔ a != ⊥ ∧ IsSuccPrelimit a

--- 原说明 ---
### Limit ordinals
-/
theorem isSuccLimit_iff {o : Ordinal} : IsSuccLimit o ↔ o ≠ 0 ∧ IsSuccPrelimit o :=
  isSuccLimit_iff_of_orderBot

@[simp]
/-
**Ordinal.isSuccPrelimit_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccPrelimit_zero : IsSuccPrelimit (0 : Ordinal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isSuccPrelimit_bot`：isSuccPrelimit_bot [OrderBot α] : IsSuccPrelim
it (⊥ : α)
-/
theorem isSuccPrelimit_zero : IsSuccPrelimit (0 : Ordinal) := isSuccPrelimit_bot

@[simp]
/-
**Ordinal.not_isSuccLimit_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：not_isSuccLimit_zero : ¬ IsSuccLimit (0 : Ordinal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.not_isSuccLimit_bot`：not_isSuccLimit_bot [OrderBot α] : ¬ IsSuccLi
mit (⊥ : α)
-/
theorem not_isSuccLimit_zero : ¬ IsSuccLimit (0 : Ordinal) := not_isSuccLimit_bot

@[simp]
/-
**Ordinal.isSuccPrelimit_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccPrelimit_lift {o : Ordinal} : IsSuccPrelimit (lift.{u, v} o) ↔ IsSuc
cPrelimit o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.isSuccPrelimit_apply_iff`：isSuccPrelimit_apply_iff (f : α <=i
 β) : IsSuccPrelimit (f a) ↔ IsSuccPrelimit a
-/
theorem isSuccPrelimit_lift {o : Ordinal} : IsSuccPrelimit (lift.{u, v} o) ↔ IsSuccPrelimit o :=
  liftInitialSeg.isSuccPrelimit_apply_iff

@[simp]
/-
**Ordinal.isSuccLimit_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_lift {o : Ordinal} : IsSuccLimit (lift.{u, v} o) ↔ IsSuccLimit
 o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.isSuccLimit_apply_iff`：isSuccLimit_apply_iff (f : α <=i β) : 
IsSuccLimit (f a) ↔ IsSuccLimit a
-/
theorem isSuccLimit_lift {o : Ordinal} : IsSuccLimit (lift.{u, v} o) ↔ IsSuccLimit o :=
  liftInitialSeg.isSuccLimit_apply_iff
/-
**Ordinal.natCast_lt_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_lt_of_isSuccLimit {o : Ordinal} (h : IsSuccLimit o) (n : Nat) : n 
< o
参数：h : IsSuccLimit o；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Order.IsSuccLimit.add_natCast_lt`：∀ {α : Type u_1} {x y : α} [inst : Par
tialOrder α] [inst_1 : AddMonoidWithOne α] [SuccAddOrder α],   Order.IsSuccLimit
 x → y < x → ∀ (n : ℕ)…
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
-/
theorem natCast_lt_of_isSuccLimit {o : Ordinal} (h : IsSuccLimit o) (n : ℕ) : n < o := by
  simpa using h.add_natCast_lt h.bot_lt n
/-
**Ordinal.one_lt_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_lt_of_isSuccLimit {o : Ordinal} (h : IsSuccLimit o) : 1 < o
参数：h : IsSuccLimit o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.natCast_lt_of_isSuccLimit`：natCast_lt_of_isSuccLimit {o : Ordina
l} (h : IsSuccLimit o) (n : Nat) : n < o
-/
theorem one_lt_of_isSuccLimit {o : Ordinal} (h : IsSuccLimit o) : 1 < o :=
  mod_cast natCast_lt_of_isSuccLimit h 1
/-
**Ordinal.zero_or_succ_or_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：zero_or_succ_or_isSuccLimit (o : Ordinal) : o = 0 ∨ o in range succ ∨ IsSu
ccLimit o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Order.isMin_or_mem_range_succ_or_isSuccLimit`：isMin_or_mem_range_succ_or
_isSuccLimit (a) : IsMin a ∨ a in range (succ : α -> α) ∨ IsSuccLimit a
-/
theorem zero_or_succ_or_isSuccLimit (o : Ordinal) : o = 0 ∨ o ∈ range succ ∨ IsSuccLimit o := by
  simpa using isMin_or_mem_range_succ_or_isSuccLimit o

/-- Limit induction on ordinals: if one can prove a property by induction at successor ordinals and
at limit ordinals, then it holds for all ordinals.

Note that this is just a special (though sometimes convenient) case of the more general
well-founded recursion `WellFoundedLT.fix`. -/
@[elab_as_elim]
/-
**Ordinal.limitRecOn** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：limitRecOn {motive : Ordinal -> Sort*} (o : Ordinal) (zero : motive 0) (ad
d_one : forall o, motive o -> motive (o + 1)) (limit : forall o, IsSuccLimit o -
> (forall o' < o, motive o') -> motive o) : motive o
参数：o : Ordinal；zero : motive 0；add_one : forall o, motive o -> motive (o + 1)；li
mit : forall o, IsSuccLimit o -> (forall o' < o, motive o') -> motive o。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Limit induction on ordinals: if one can prove a property by induction at success
or ordinals and
at limit ordinals, then it holds for all ordinals.

Note that this is just a special (though sometimes convenient) case of the more 
general
well-founded recursion `WellFoundedLT.fix`.
-/
def limitRecOn {motive : Ordinal → Sort*} (o : Ordinal)
    (zero : motive 0) (add_one : ∀ o, motive o → motive (o + 1))
    (limit : ∀ o, IsSuccLimit o → (∀ o' < o, motive o') → motive o) : motive o :=
  SuccOrder.limitRecOn o (fun _a ha ↦ ha.eq_bot ▸ zero) (fun a _ ↦ add_one a) limit

@[simp]
/-
**Ordinal.limitRecOn_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：limitRecOn_zero {motive} (H₁ H₂ H₃) : @limitRecOn motive 0 H₁ H₂ H₃ = H₁
参数：H₁ H₂ H₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.limitRecOn_isMin`：limitRecOn_isMin (hb : IsMin b) : limitRecOn
 b isMin succ isSuccLimit = isMin b hb
· 使用定理 `isMin_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α], IsM
in ⊥
-/
theorem limitRecOn_zero {motive} (H₁ H₂ H₃) : @limitRecOn motive 0 H₁ H₂ H₃ = H₁ :=
  SuccOrder.limitRecOn_isMin _ _ _ isMin_bot

@[simp]
/-
**Ordinal.limitRecOn_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：limitRecOn_add_one {motive} (o H₁ H₂ H₃) : @limitRecOn motive (o + 1) H₁ H
₂ H₃ = H₂ o (@limitRecOn motive o H₁ H₂ H₃)
参数：o H₁ H₂ H₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.limitRecOn_succ`：limitRecOn_succ [NoMaxOrder α] (b : α) : limi
tRecOn (Order.succ b) isMin succ isSuccLimit = succ b (not_isMax b) (limitRecOn 
b isMin succ is…
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem limitRecOn_add_one {motive} (o H₁ H₂ H₃) :
    @limitRecOn motive (o + 1) H₁ H₂ H₃ = H₂ o (@limitRecOn motive o H₁ H₂ H₃) :=
  SuccOrder.limitRecOn_succ ..

@[deprecated limitRecOn_add_one (since := "2026-05-21")]
/-
**Ordinal.limitRecOn_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：limitRecOn_succ {motive} (o H₁ H₂ H₃) : @limitRecOn motive (succ o) H₁ H₂ 
H₃ = H₂ o (@limitRecOn motive o H₁ H₂ H₃)
参数：o H₁ H₂ H₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.limitRecOn_add_one`：limitRecOn_add_one {motive} (o H₁ H₂ H₃) : @
limitRecOn motive (o + 1) H₁ H₂ H₃ = H₂ o (@limitRecOn motive o H₁ H₂ H₃)
-/
theorem limitRecOn_succ {motive} (o H₁ H₂ H₃) :
    @limitRecOn motive (succ o) H₁ H₂ H₃ = H₂ o (@limitRecOn motive o H₁ H₂ H₃) :=
  limitRecOn_add_one ..

@[simp]
/-
**Ordinal.limitRecOn_limit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：limitRecOn_limit {motive} (o H₁ H₂ H₃ h) : @limitRecOn motive o H₁ H₂ H₃ =
 H₃ o h fun x _h => @limitRecOn motive x H₁ H₂ H₃
参数：o H₁ H₂ H₃ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.limitRecOn_of_isSuccLimit`：limitRecOn_of_isSuccLimit (hb : IsS
uccLimit b) : limitRecOn b isMin succ isSuccLimit = isSuccLimit b hb fun x _ => 
limitRecOn x isMin succ i…
-/
theorem limitRecOn_limit {motive} (o H₁ H₂ H₃ h) :
    @limitRecOn motive o H₁ H₂ H₃ = H₃ o h fun x _h => @limitRecOn motive x H₁ H₂ H₃ :=
  SuccOrder.limitRecOn_of_isSuccLimit ..
/-
**Ordinal.orderTopToTypeSucc** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：orderTopToTypeSucc (o : Ordinal) : OrderTop (succ o).ToType
参数：o : Ordinal。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.le_enum_succ`：le_enum_succ {o : Ordinal} (a : (succ o).ToType) :
 a <= enum (α
-/
instance orderTopToTypeSucc (o : Ordinal) : OrderTop (succ o).ToType :=
  @OrderTop.mk _ _ (Top.mk _) le_enum_succ
/-
**Ordinal.enum_succ_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enum_succ_eq_top {o : Ordinal} : enum (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
-/
theorem enum_succ_eq_top {o : Ordinal} :
    enum (α := (succ o).ToType) (· < ·) ⟨o, type_toType _ ▸ lt_succ o⟩ = ⊤ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[deprecated isSuccPrelimit_type_lt_iff (since := "2026-04-12")]
/-
**Ordinal.has_succ_of_type_succ_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：has_succ_of_type_succ_lt {α} {r : α -> α -> Prop} [wo : IsWellOrder α r] (
h : forall a < type r, succ a < type r) (x : α) : exists y, r x y
参数：h : forall a < type r, succ a < type r；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.enum_typein`：enum_typein (r : α -> α -> Prop) [IsWellOrder α r] 
(a : α) : enum r ⟨typein r a, typein_lt_type r a⟩ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.enum_lt_enum`：enum_lt_enum {r : α -> α -> Prop} [IsWellOrder α r
] {o₁ o₂ : Iio (type r)} : r (enum r o₁) (enum r o₂) ↔ o₁ < o₂
· 使用定理 `Subtype.mk_lt_mk`：mk_lt_mk [LT α] {p : α -> Prop} {x y : α} {hx : p x} {
hy : p y} : (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem has_succ_of_type_succ_lt {α} {r : α → α → Prop} [wo : IsWellOrder α r]
    (h : ∀ a < type r, succ a < type r) (x : α) : ∃ y, r x y := by
  use enum r ⟨succ (typein r x), h _ (typein_lt_type r x)⟩
  convert! enum_lt_enum.mpr _
  · rw [enum_typein]
  · rw [Subtype.mk_lt_mk, lt_succ_iff]

@[deprecated isSuccPrelimit_type_lt_iff (since := "2026-04-12")]
/-
**Ordinal.toType_noMax_of_succ_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：toType_noMax_of_succ_lt {o : Ordinal} (ho : forall a < o, succ a < o) : No
MaxOrder o.ToType
参数：ho : forall a < o, succ a < o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.has_succ_of_type_succ_lt`：has_succ_of_type_succ_lt {α} {r : α ->
 α -> Prop} [wo : IsWellOrder α r] (h : forall a < type r, succ a < type r) (x :
 α) : exists y, r x y
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
-/
theorem toType_noMax_of_succ_lt {o : Ordinal} (ho : ∀ a < o, succ a < o) : NoMaxOrder o.ToType :=
  ⟨has_succ_of_type_succ_lt (type_toType _ ▸ ho)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Ordinal.bounded_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bounded_singleton {r : α -> α -> Prop} [IsWellOrder α r] (hr : IsSuccLimit
 (type r)) (x) : Bounded r {x}
参数：hr : IsSuccLimit (type r)；x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.enum_typein`：enum_typein (r : α -> α -> Prop) [IsWellOrder α r] 
(a : α) : enum r ⟨typein r a, typein_lt_type r a⟩ = a
· 使用定理 `Ordinal.enum_lt_enum`：enum_lt_enum {r : α -> α -> Prop} [IsWellOrder α r
] {o₁ o₂ : Iio (type r)} : r (enum r o₁) (enum r o₂) ↔ o₁ < o₂
· 使用定理 `Subtype.mk_lt_mk`：mk_lt_mk [LT α] {p : α -> Prop} {x y : α} {hx : p x} {
hy : p y} : (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem bounded_singleton {r : α → α → Prop} [IsWellOrder α r] (hr : IsSuccLimit (type r)) (x) :
    Bounded r {x} := by
  refine ⟨enum r ⟨succ (typein r x), hr.succ_lt (typein_lt_type r x)⟩, ?_⟩
  intro b hb
  rw [mem_singleton_iff.1 hb]
  nth_rw 1 [← enum_typein r x]
  rw [@enum_lt_enum _ r, Subtype.mk_lt_mk]
  apply lt_succ

/-! ### The predecessor of an ordinal -/

/-- The ordinal predecessor of `a` is `b` if `a = succ b`, and `a` otherwise. -/
/-
**Ordinal.pred** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：pred (o : Ordinal) : Ordinal
参数：o : Ordinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordinal predecessor of `a` is `b` if `a = succ b`, and `a` otherwise.
-/
def pred (o : Ordinal) : Ordinal :=
  isSuccPrelimitRecOn o (fun a _ ↦ a) (fun a _ ↦ a)

@[simp]
/-
**Ordinal.pred_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：pred_add_one (o) : pred (o + 1) = o
参数：o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isSuccPrelimitRecOn_succ`：isSuccPrelimitRecOn_succ [NoMaxOrder α] 
(b : α) : isSuccPrelimitRecOn (Order.succ b) succ isSuccPrelimit = succ b (not_i
sMax b)
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem pred_add_one (o) : pred (o + 1) = o :=
  isSuccPrelimitRecOn_succ ..

@[deprecated pred_add_one (since := "2026-05-25")]
/-
**Ordinal.pred_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：pred_succ (o) : pred (succ o) = o
参数：o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.pred_add_one`：pred_add_one (o) : pred (o + 1) = o
-/
theorem pred_succ (o) : pred (succ o) = o :=
  pred_add_one o
/-
**Ordinal.pred_eq_of_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：pred_eq_of_isSuccPrelimit {o} : IsSuccPrelimit o -> pred o = o
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isSuccPrelimitRecOn_of_isSuccPrelimit`：isSuccPrelimitRecOn_of_isSu
ccPrelimit (hb : IsSuccPrelimit b) : isSuccPrelimitRecOn b succ isSuccPrelimit =
 isSuccPrelimit b hb
-/
theorem pred_eq_of_isSuccPrelimit {o} : IsSuccPrelimit o → pred o = o :=
  isSuccPrelimitRecOn_of_isSuccPrelimit _ _

alias _root_.Order.IsSuccPrelimit.ordinalPred_eq := pred_eq_of_isSuccPrelimit
/-
**Ordinal._root_.Order.IsSuccLimit.ordinalPred_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ord
inal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Order.IsSuccLimit.ordinalPred_eq {o} (ho : IsSuccLimit o) : pred o = o :=
  ho.isSuccPrelimit.ordinalPred_eq

@[simp]
/-
**Ordinal.pred_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：pred_zero : pred 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.ordinalPred_eq`：∀ {o : Ordinal.{u_4}}, Order.IsSucc
Prelimit o → o.pred = o
· 使用定理 `Ordinal.isSuccPrelimit_zero`：isSuccPrelimit_zero : IsSuccPrelimit (0 : O
rdinal)
-/
theorem pred_zero : pred 0 = 0 :=
  isSuccPrelimit_zero.ordinalPred_eq

@[simp]
/-
**Ordinal.pred_le_iff_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：pred_le_iff_le_succ {a b} : pred a <= b ↔ a <= succ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.mem_range_succ_or_isSuccPrelimit`：mem_range_succ_or_isSuccPrelimit
 (a) : a in range (succ : α -> α) ∨ IsSuccPrelimit a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Ordinal.pred_add_one`：pred_add_one (o) : pred (o + 1) = o
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Order.IsSuccPrelimit.ordinalPred_eq`：∀ {o : Ordinal.{u_4}}, Order.IsSucc
Prelimit o → o.pred = o
· 使用定理 `Order.IsSuccPrelimit.le_succ_iff`：∀ {α : Type u_1} {a b : α} [inst : Lin
earOrder α] [inst_1 : SuccOrder α],   Order.IsSuccPrelimit b → (b ≤ Order.succ a
 ↔ b ≤ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pred_le_iff_le_succ {a b} : pred a ≤ b ↔ a ≤ succ b := by
  obtain ⟨a, rfl⟩ | ha := mem_range_succ_or_isSuccPrelimit a
  · simp
  · rw [ha.ordinalPred_eq, ha.le_succ_iff]

@[simp]
/-
**Ordinal.lt_pred_iff_succ_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_pred_iff_succ_lt {a b} : a < pred b ↔ succ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Ordinal.pred_le_iff_le_succ`：pred_le_iff_le_succ {a b} : pred a <= b ↔ a
 <= succ b
-/
theorem lt_pred_iff_succ_lt {a b} : a < pred b ↔ succ a < b :=
  le_iff_le_iff_lt_iff_lt.1 pred_le_iff_le_succ
/-
**Ordinal.pred_le_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：pred_le_self (o) : pred o <= o
参数：o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem pred_le_self (o) : pred o ≤ o := by
  simp

/-- `Ordinal.pred` and `Order.succ` form a Galois insertion. -/
/-
**Ordinal.pred_succ_gi** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：pred_succ_gi : GaloisInsertion pred succ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.pred_le_iff_le_succ`：pred_le_iff_le_succ {a b} : pred a <= b ↔ a
 <= succ b

--- 原说明 ---
`Ordinal.pred` and `Order.succ` form a Galois insertion.
-/
def pred_succ_gi : GaloisInsertion pred succ :=
  GaloisConnection.toGaloisInsertion @pred_le_iff_le_succ (by simp)
/-
**Ordinal.pred_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：pred_surjective : Function.Surjective pred
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_surjective`：l_surjective [Preorder α] [PartialOrder β]
 (gi : GaloisInsertion l u) : Surjective l
-/
theorem pred_surjective : Function.Surjective pred :=
  pred_succ_gi.l_surjective
/-
**Ordinal.self_le_succ_pred** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：self_le_succ_pred (o) : o <= succ (pred o)
参数：o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem self_le_succ_pred (o) : o ≤ succ (pred o) :=
  pred_succ_gi.gc.le_u_l o
/-
**Ordinal.pred_eq_iff_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：pred_eq_iff_isSuccPrelimit {o} : pred o = o ↔ IsSuccPrelimit o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.mem_range_succ_or_isSuccPrelimit`：mem_range_succ_or_isSuccPrelimit
 (a) : a in range (succ : α -> α) ∨ IsSuccPrelimit a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Ordinal.pred_add_one`：pred_add_one (o) : pred (o + 1) = o
· 使用定理 `Ordinal.instIsLeftCancelAdd`：IsLeftCancelAdd Ordinal.{u_4}
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Order.IsSuccPrelimit.ordinalPred_eq`：∀ {o : Ordinal.{u_4}}, Order.IsSucc
Prelimit o → o.pred = o
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem pred_eq_iff_isSuccPrelimit {o} : pred o = o ↔ IsSuccPrelimit o := by
  obtain ⟨a, rfl⟩ | ho := mem_range_succ_or_isSuccPrelimit o
  · simp
  · simp_rw [ho.ordinalPred_eq, ho]
/-
**Ordinal.pred_lt_iff_not_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：pred_lt_iff_not_isSuccPrelimit {o} : pred o < o ↔ ¬ IsSuccPrelimit o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `Ordinal.pred_le_self`：pred_le_self (o) : pred o <= o
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ordinal.pred_eq_iff_isSuccPrelimit`：pred_eq_iff_isSuccPrelimit {o} : pre
d o = o ↔ IsSuccPrelimit o
-/
theorem pred_lt_iff_not_isSuccPrelimit {o} : pred o < o ↔ ¬ IsSuccPrelimit o := by
  rw [(pred_le_self o).lt_iff_ne]
  exact pred_eq_iff_isSuccPrelimit.not
/-
**Ordinal.succ_pred_eq_iff_not_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal
`。
形式化陈述：succ_pred_eq_iff_not_isSuccPrelimit {o} : succ (pred o) = o ↔ ¬ IsSuccPrel
imit o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Ordinal.self_le_succ_pred`：self_le_succ_pred (o) : o <= succ (pred o)
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.pred_lt_iff_not_isSuccPrelimit`：pred_lt_iff_not_isSuccPrelimit {
o} : pred o < o ↔ ¬ IsSuccPrelimit o
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem succ_pred_eq_iff_not_isSuccPrelimit {o} : succ (pred o) = o ↔ ¬ IsSuccPrelimit o := by
  rw [← (self_le_succ_pred o).ge_iff_eq', succ_le_iff, pred_lt_iff_not_isSuccPrelimit]

@[simp]
/-
**Ordinal.lift_pred** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_pred (o : Ordinal.{v}) : lift.{u} (pred o) = pred (lift.{u} o)
参数：o : Ordinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.mem_range_succ_or_isSuccPrelimit`：mem_range_succ_or_isSuccPrelimit
 (a) : a in range (succ : α -> α) ∨ IsSuccPrelimit a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Ordinal.pred_add_one`：pred_add_one (o) : pred (o + 1) = o
· 使用定理 `Ordinal.lift_add`：lift_add (a b : Ordinal.{v}) : lift.{u} (a + b) = lift
.{u} a + lift.{u} b
· 使用定理 `Ordinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Order.IsSuccPrelimit.ordinalPred_eq`：∀ {o : Ordinal.{u_4}}, Order.IsSucc
Prelimit o → o.pred = o
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Ordinal.pred_eq_iff_isSuccPrelimit`：pred_eq_iff_isSuccPrelimit {o} : pre
d o = o ↔ IsSuccPrelimit o
· 使用定理 `Ordinal.isSuccPrelimit_lift`：isSuccPrelimit_lift {o : Ordinal} : IsSuccP
relimit (lift.{u, v} o) ↔ IsSuccPrelimit o
-/
theorem lift_pred (o : Ordinal.{v}) : lift.{u} (pred o) = pred (lift.{u} o) := by
  obtain ⟨a, rfl⟩ | ho := mem_range_succ_or_isSuccPrelimit o
  · simp
  · rwa [ho.ordinalPred_eq, eq_comm, pred_eq_iff_isSuccPrelimit, isSuccPrelimit_lift]

/-! ### Subtraction on ordinals -/

/-- `a - b` is the unique ordinal satisfying `b + (a - b) = a` when `b ≤ a`. -/
/-
**Ordinal.sub** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：sub : Sub Ordinal where sub a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a - b` is the unique ordinal satisfying `b + (a - b) = a` when `b ≤ a`.
-/
instance sub : Sub Ordinal where
  sub a b := if h : b ≤ a then Classical.choose (exists_add_of_le h) else 0
/-
**Ordinal.sub_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sub_eq_zero_of_lt {a b : Ordinal} (h : a < b) : a - b = 0 :=
  dif_neg h.not_ge
/-
**Ordinal.add_sub_cancel_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - b) = a
参数：a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
protected theorem add_sub_cancel_of_le {a b : Ordinal} (h : b ≤ a) : b + (a - b) = a := by
  change b + dite _ _ _ = a
  rw [dif_pos h]
  exact (Classical.choose_spec (exists_add_of_le h)).symm

@[simp]
/-
**Ordinal.add_sub_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_sub_cancel (a b : Ordinal) : a + b - a = b
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.instIsLeftCancelAdd`：IsLeftCancelAdd Ordinal.{u_4}
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
-/
theorem add_sub_cancel (a b : Ordinal) : a + b - a = b := by
  simpa using Ordinal.add_sub_cancel_of_le le_self_add
/-
**Ordinal.le_add_sub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_add_sub (a b : Ordinal) : a <= b + (a - b)
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Arithmetic.0.Ordinal.sub_eq_zero_of_l
t`：∀ {a b : Ordinal.{u_4}}, a < b → a - b = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem le_add_sub (a b : Ordinal) : a ≤ b + (a - b) := by
  obtain h | h := le_or_gt b a
  · exact (Ordinal.add_sub_cancel_of_le h).ge
  · simpa [sub_eq_zero_of_lt h] using h.le
/-
**Ordinal.sub_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sub_le {a b c : Ordinal} : a - b <= c ↔ a <= b + c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.le_add_sub`：le_add_sub (a b : Ordinal) : a <= b + (a - b)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Arithmetic.0.Ordinal.sub_eq_zero_of_l
t`：∀ {a b : Ordinal.{u_4}}, a < b → a - b = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem sub_le {a b c : Ordinal} : a - b ≤ c ↔ a ≤ b + c := by
  refine ⟨fun h ↦ (le_add_sub a b).trans (by gcongr), fun h ↦ ?_⟩
  obtain h' | h' := le_or_gt b a
  · rwa [← add_le_add_iff_left b, Ordinal.add_sub_cancel_of_le h']
  · simp [sub_eq_zero_of_lt h']
/-
**Ordinal.lt_sub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_sub {a b c : Ordinal} : a < b - c ↔ c + a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Ordinal.sub_le`：sub_le {a b c : Ordinal} : a - b <= c ↔ a <= b + c
-/
theorem lt_sub {a b c : Ordinal} : a < b - c ↔ c + a < b :=
  lt_iff_lt_of_le_iff_le sub_le
/-
**Ordinal.sub_eq_of_add_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sub_eq_of_add_eq {a b c : Ordinal} (h : a + b = c) : c - a = b
参数：h : a + b = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.add_sub_cancel`：add_sub_cancel (a b : Ordinal) : a + b - a = b
-/
theorem sub_eq_of_add_eq {a b c : Ordinal} (h : a + b = c) : c - a = b :=
  h ▸ add_sub_cancel _ _
/-
**Ordinal.sub_le_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sub_le_self (a b : Ordinal) : a - b <= a
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.sub_le`：sub_le {a b c : Ordinal} : a - b <= c ↔ a <= b + c
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
-/
theorem sub_le_self (a b : Ordinal) : a - b ≤ a := sub_le.2 le_add_self
/-
**Ordinal.le_sub_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_sub_of_le {a b c : Ordinal} (h : b <= a) : c <= a - b ↔ b + c <= a
参数：h : b <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_sub_of_le {a b c : Ordinal} (h : b ≤ a) : c ≤ a - b ↔ b + c ≤ a := by
  rw [← add_le_add_iff_left b, Ordinal.add_sub_cancel_of_le h]
/-
**Ordinal.sub_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sub_lt_of_le {a b c : Ordinal} (h : b <= a) : a - b < c ↔ a < b + c
参数：h : b <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Ordinal.le_sub_of_le`：le_sub_of_le {a b c : Ordinal} (h : b <= a) : c <=
 a - b ↔ b + c <= a
-/
theorem sub_lt_of_le {a b c : Ordinal} (h : b ≤ a) : a - b < c ↔ a < b + c :=
  lt_iff_lt_of_le_iff_le (le_sub_of_le h)

@[simp]
/-
**Ordinal.sub_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sub_zero (a : Ordinal) : a - 0 = a
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ordinal.add_sub_cancel`：add_sub_cancel (a b : Ordinal) : a + b - a = b
-/
theorem sub_zero (a : Ordinal) : a - 0 = a := by simpa only [zero_add] using add_sub_cancel 0 a

@[simp]
/-
**Ordinal.zero_sub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：zero_sub (a : Ordinal) : 0 - a = 0
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.sub_le_self`：sub_le_self (a b : Ordinal) : a - b <= a
-/
theorem zero_sub (a : Ordinal) : 0 - a = 0 := by simpa using sub_le_self 0 _

@[simp]
/-
**Ordinal.sub_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sub_self (a : Ordinal) : a - a = 0
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.add_sub_cancel`：add_sub_cancel (a b : Ordinal) : a + b - a = b
-/
theorem sub_self (a : Ordinal) : a - a = 0 := by simpa only [add_zero] using add_sub_cancel a 0
/-
**Ordinal.sub_eq_zero_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {a b : Ordinal.{u_4}}, a - b = 0 ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem sub_eq_zero_iff_le {a b : Ordinal} : a - b = 0 ↔ a ≤ b := by
  simp [← nonpos_iff_eq_zero, sub_le]
/-
**Ordinal.sub_ne_zero_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {a b : Ordinal.{u_4}}, a - b ≠ 0 ↔ b < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ordinal.sub_eq_zero_iff_le`：∀ {a b : Ordinal.{u_4}}, a - b = 0 ↔ a ≤ b
-/
protected theorem sub_ne_zero_iff_lt {a b : Ordinal} : a - b ≠ 0 ↔ b < a := by
  simpa using Ordinal.sub_eq_zero_iff_le.not
/-
**Ordinal.sub_sub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sub_sub (a b c : Ordinal) : a - b - c = a - (b + c)
参数：a b c : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.sub_le`：sub_le {a b c : Ordinal} : a - b <= c ↔ a <= b + c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_sub (a b c : Ordinal) : a - b - c = a - (b + c) :=
  eq_of_forall_ge_iff fun d => by rw [sub_le, sub_le, sub_le, add_assoc]

@[simp]
/-
**Ordinal.add_sub_add_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_sub_add_cancel (a b c : Ordinal) : a + b - (a + c) = b - c
参数：a b c : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.sub_sub`：sub_sub (a b c : Ordinal) : a - b - c = a - (b + c)
· 使用定理 `Ordinal.add_sub_cancel`：add_sub_cancel (a b : Ordinal) : a + b - a = b
-/
theorem add_sub_add_cancel (a b c : Ordinal) : a + b - (a + c) = b - c := by
  rw [← sub_sub, add_sub_cancel]
/-
**Ordinal.le_sub_of_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_sub_of_add_le {a b c : Ordinal} (h : b + c <= a) : c <= a - b
参数：h : b + c <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.le_add_sub`：le_add_sub (a b : Ordinal) : a <= b + (a - b)
-/
theorem le_sub_of_add_le {a b c : Ordinal} (h : b + c ≤ a) : c ≤ a - b := by
  rw [← add_le_add_iff_left b]
  exact h.trans (le_add_sub a b)
/-
**Ordinal.sub_lt_of_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sub_lt_of_lt_add {a b c : Ordinal} (h : a < b + c) (hc : 0 < c) : a - b < 
c
参数：h : a < b + c；hc : 0 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.sub_eq_zero_iff_le`：∀ {a b : Ordinal.{u_4}}, a - b = 0 ↔ a ≤ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.sub_lt_of_le`：sub_lt_of_le {a b c : Ordinal} (h : b <= a) : a - 
b < c ↔ a < b + c
-/
theorem sub_lt_of_lt_add {a b c : Ordinal} (h : a < b + c) (hc : 0 < c) : a - b < c := by
  obtain hab | hba := lt_or_ge a b
  · rwa [Ordinal.sub_eq_zero_iff_le.2 hab.le]
  · rwa [sub_lt_of_le hba]
/-
**Ordinal.lt_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_add_iff {a b c : Ordinal} (hc : c != 0) : a < b + c ↔ exists d < c, a <
= b + d
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.sub_lt_of_lt_add`：sub_lt_of_lt_add {a b c : Ordinal} (h : a < b 
+ c) (hc : 0 < c) : a - b < c
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Ordinal.le_add_sub`：le_add_sub (a b : Ordinal) : a <= b + (a - b)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
-/
theorem lt_add_iff {a b c : Ordinal} (hc : c ≠ 0) : a < b + c ↔ ∃ d < c, a ≤ b + d := by
  use fun h ↦ ⟨_, sub_lt_of_lt_add h hc.bot_lt, le_add_sub a b⟩
  rintro ⟨d, hd, ha⟩
  exact ha.trans_lt (by gcongr)
/-
**Ordinal.add_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_le_iff {a b c : Ordinal} (hb : b != 0) : a + b <= c ↔ forall d < b, a 
+ d < c
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ordinal.lt_add_iff`：lt_add_iff {a b c : Ordinal} (hc : c != 0) : a < b +
 c ↔ exists d < c, a <= b + d
-/
theorem add_le_iff {a b c : Ordinal} (hb : b ≠ 0) : a + b ≤ c ↔ ∀ d < b, a + d < c := by
  simpa using (lt_add_iff hb).not
/-
**Ordinal.lt_add_iff_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_add_iff_of_isSuccLimit {a b c : Ordinal} (hc : IsSuccLimit c) : a < b +
 c ↔ exists d < c, a < b + d
参数：hc : IsSuccLimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lt_add_iff`：lt_add_iff {a b c : Ordinal} (hc : c != 0) : a < b +
 c ↔ exists d < c, a <= b + d
· 使用定理 `Order.IsSuccLimit.ne_bot`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → a ≠ ⊥
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Order.lt_add_one_iff`：lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x <= y
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem lt_add_iff_of_isSuccLimit {a b c : Ordinal} (hc : IsSuccLimit c) :
    a < b + c ↔ ∃ d < c, a < b + d := by
  rw [lt_add_iff hc.ne_bot]
  constructor <;> rintro ⟨d, hd, ha⟩
  · refine ⟨_, hc.succ_lt hd, ?_⟩
    rwa [succ_eq_add_one, ← add_assoc, lt_add_one_iff]
  · exact ⟨d, hd, ha.le⟩
/-
**Ordinal.add_le_iff_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_le_iff_of_isSuccLimit {a b c : Ordinal} (hb : IsSuccLimit b) : a + b <
= c ↔ forall d < b, a + d <= c
参数：hb : IsSuccLimit b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ordinal.lt_add_iff_of_isSuccLimit`：lt_add_iff_of_isSuccLimit {a b c : Or
dinal} (hc : IsSuccLimit c) : a < b + c ↔ exists d < c, a < b + d
-/
theorem add_le_iff_of_isSuccLimit {a b c : Ordinal} (hb : IsSuccLimit b) :
    a + b ≤ c ↔ ∀ d < b, a + d ≤ c := by
  simpa using (lt_add_iff_of_isSuccLimit hb).not
/-
**Ordinal.isNormal_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_add_right (a : Ordinal) : IsNormal (a + ·)
参数：a : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isNormal_iff`：isNormal_iff [LinearOrder α] [LinearOrder β] {f : α 
-> β} : IsNormal f ↔ StrictMono f ∧ forall o, IsSuccLimit o -> forall a, (forall
 b < o, …
· 使用定理 `add_right_strictMono`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder
 α] [AddLeftStrictMono α] {a : α}, StrictMono fun x => a + x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.add_le_iff_of_isSuccLimit`：add_le_iff_of_isSuccLimit {a b c : Or
dinal} (hb : IsSuccLimit b) : a + b <= c ↔ forall d < b, a + d <= c
-/
theorem isNormal_add_right (a : Ordinal) : IsNormal (a + ·) := by
  rw [isNormal_iff]
  exact ⟨add_right_strictMono, fun _ l _ ↦ (add_le_iff_of_isSuccLimit l).2⟩
/-
**Ordinal.isSuccLimit_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_add (a : Ordinal) {b : Ordinal} : IsSuccLimit b -> IsSuccLimit
 (a + b)
参数：a : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.map_isSuccLimit`：map_isSuccLimit (hf : IsNormal f) (ha : 
IsSuccLimit a) : IsSuccLimit (f a)
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)
-/
theorem isSuccLimit_add (a : Ordinal) {b : Ordinal} : IsSuccLimit b → IsSuccLimit (a + b) :=
  (isNormal_add_right a).map_isSuccLimit
/-
**Ordinal.isSuccLimit_sub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_sub {a b : Ordinal} (ha : IsSuccPrelimit a) (h : b < a) : IsSu
ccLimit (a - b)
参数：ha : IsSuccPrelimit a；h : b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.isSuccLimit_iff`：isSuccLimit_iff {o : Ordinal} : IsSuccLimit o ↔
 o != 0 ∧ IsSuccPrelimit o
· 使用定理 `Ordinal.sub_ne_zero_iff_lt`：∀ {a b : Ordinal.{u_4}}, a - b ≠ 0 ↔ b < a
· 使用定理 `Order.isSuccPrelimit_iff_succ_lt`：isSuccPrelimit_iff_succ_lt : IsSuccPre
limit b ↔ forall a < b, succ a < b
· 使用定理 `Ordinal.lt_sub`：lt_sub {a b c : Ordinal} : a < b - c ↔ c + a < b
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Order.IsSuccPrelimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : Partial
Order α] [inst_1 : SuccOrder α],   Order.IsSuccPrelimit b → a < b → Order.succ a
 < b
-/
theorem isSuccLimit_sub {a b : Ordinal} (ha : IsSuccPrelimit a) (h : b < a) :
    IsSuccLimit (a - b) := by
  rw [isSuccLimit_iff, Ordinal.sub_ne_zero_iff_lt, isSuccPrelimit_iff_succ_lt]
  refine ⟨h, fun c hc ↦ ?_⟩
  rw [lt_sub] at hc ⊢
  rw [succ_eq_add_one, ← add_assoc]
  exact ha.succ_lt hc

/-! ### Multiplication of ordinals -/

/-- The multiplication of ordinals `a` and `b` is the order type of the lexicographic order on
`b × a`. -/
/-
**Ordinal.monoid** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：monoid : Monoid Ordinal.{u} where mul a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication of ordinals `a` and `b` is the order type of the lexicographi
c order on
`b × a`.
-/
instance monoid : Monoid Ordinal.{u} where
  mul a b :=
    Quotient.liftOn₂ a b (fun ⟨α, r, _⟩ ⟨β, s, _⟩ => ⟦⟨β × α, Prod.Lex s r, inferInstance⟩⟧)
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ ↦ Quot.sound ⟨RelIso.prodLexCongr g f⟩
  mul_assoc a b c :=
    Quotient.inductionOn₃ a b c fun _ _ _ ↦
      .symm <| Quotient.sound ⟨⟨prodAssoc .., by grind [Prod.mk.injEq]⟩⟩
  mul_one a := inductionOn a fun α _ _ ↦ Quotient.sound ⟨⟨punitProd α, by simp [Prod.lex_def]⟩⟩
  one_mul a := inductionOn a fun α _ _ ↦ Quotient.sound ⟨⟨prodPUnit α, by simp [Prod.lex_def]⟩⟩

@[simp]
/-
**Ordinal.type_prod_lex** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_prod_lex {α β : Type u} (r : α -> α -> Prop) (s : β -> β -> Prop) [Is
WellOrder α r] [IsWellOrder β s] : type (Prod.Lex s r) = type r * type s
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsWellOrderProdLex`：∀ {α : Type u} {β : Type v} {r : α → α → Prop} {
s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s],   IsWellOrder (α × β) (Pr
od.Lex r s)
-/
theorem type_prod_lex {α β : Type u} (r : α → α → Prop) (s : β → β → Prop) [IsWellOrder α r]
    [IsWellOrder β s] : type (Prod.Lex s r) = type r * type s :=
  rfl
/-
**Ordinal.mul_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_eq_zero' {a b : Ordinal} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  induction a, b using inductionOn₂ with | _ α _ β _
  simp_rw [← type_prod_lex, type_eq_zero_iff_isEmpty, isEmpty_prod, iff_true_intro or_comm]
/-
**Ordinal.monoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：monoidWithZero : MonoidWithZero Ordinal where mul_zero _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidWithZero : MonoidWithZero Ordinal where
  mul_zero _ := by exact mul_eq_zero'.2 (.inr rfl)
  zero_mul _ := by exact mul_eq_zero'.2 (.inl rfl)
/-
**Ordinal.noZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：noZeroDivisors : NoZeroDivisors Ordinal where eq_zero_or_eq_zero_of_mul_eq
_zero
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Arithmetic.0.Ordinal.mul_eq_zero'`：∀ 
{a b : Ordinal.{u_4}}, a * b = 0 ↔ a = 0 ∨ b = 0
-/
instance noZeroDivisors : NoZeroDivisors Ordinal where
  eq_zero_or_eq_zero_of_mul_eq_zero := mul_eq_zero'.1

@[simp]
/-
**Ordinal.lift_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_mul (a b : Ordinal.{v}) : lift.{u} (a * b) = lift.{u} a * lift.{u} b
参数：a b : Ordinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem lift_mul (a b : Ordinal.{v}) : lift.{u} (a * b) = lift.{u} a * lift.{u} b :=
  Quotient.inductionOn₂ a b fun ⟨_α, _r, _⟩ ⟨_β, _s, _⟩ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans
          (RelIso.prodLexCongr (RelIso.preimage Equiv.ulift _)
              (RelIso.preimage Equiv.ulift _)).symm⟩

@[simp]
/-
**Ordinal.card_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_mul (a b) : card (a * b) = card a * card b
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem card_mul (a b) : card (a * b) = card a * card b :=
  Quotient.inductionOn₂ a b fun ⟨α, _r, _⟩ ⟨β, _s, _⟩ => mul_comm #β #α
/-
**Ordinal.leftDistribClass** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：leftDistribClass : LeftDistribClass Ordinal where left_distrib a b c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₃`：∀ {α : Sort uA} {β : Sort uB} {φ : Sort uC} {s₁ :
 Setoid α} {s₂ : Setoid β} {s₃ : Setoid φ}   {motive : Quotient s₁ → Quotient s₂
 → Quotient…
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Sum.instIsWellOrderLex`：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Pro
p) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s],   IsWellOrder (α ⊕ β)
 (Sum.Lex r …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
-/
instance leftDistribClass : LeftDistribClass Ordinal where
  left_distrib a b c := Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ↦
    Quotient.sound ⟨⟨sumProdDistrib .., by simp [Prod.lex_def]⟩⟩
/-
**Ordinal.mul_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_succ (a b : Ordinal) : a * succ b = a * b + a
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
-/
theorem mul_succ (a b : Ordinal) : a * succ b = a * b + a :=
  mul_add_one a b
/-
**Ordinal.mulLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：mulLeftMono : MulLeftMono Ordinal.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₃`：∀ {α : Sort uA} {β : Sort uB} {φ : Sort uC} {s₁ :
 Setoid α} {s₂ : Setoid β} {s₃ : Setoid φ}   {motive : Quotient s₁ → Quotient s₂
 → Quotient…
· 使用定理 `RelEmbedding.ordinal_type_le`：∀ {α β : Type u_1} {r : α → α → Prop} {s :
 β → β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ↪r s
), Ordinal.type r …
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
· 使用定理 `Prod.instAsymmLex_mathlib`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → 
Prop} {s : β → β → Prop} [Std.Asymm r] [Std.Asymm s],   Std.Asymm (Prod.Lex r s)
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance mulLeftMono : MulLeftMono Ordinal.{u} :=
  ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : α × γ => (f a.1, a.2)) fun a b h => ?_).ordinal_type_le
      obtain ⟨-, -, h'⟩ | ⟨-, h'⟩ := h
      · exact Prod.Lex.left _ _ (f.toRelEmbedding.map_rel_iff.2 h')
      · exact Prod.Lex.right _ h'⟩
/-
**Ordinal.mulRightMono** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：mulRightMono : MulRightMono Ordinal.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₃`：∀ {α : Sort uA} {β : Sort uB} {φ : Sort uC} {s₁ :
 Setoid α} {s₂ : Setoid β} {s₃ : Setoid φ}   {motive : Quotient s₁ → Quotient s₂
 → Quotient…
· 使用定理 `RelEmbedding.ordinal_type_le`：∀ {α β : Type u_1} {r : α → α → Prop} {s :
 β → β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ↪r s
), Ordinal.type r …
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
· 使用定理 `Prod.instAsymmLex_mathlib`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → 
Prop} {s : β → β → Prop} [Std.Asymm r] [Std.Asymm s],   Std.Asymm (Prod.Lex r s)
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
instance mulRightMono : MulRightMono Ordinal.{u} :=
  ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : γ × α => (a.1, f a.2)) fun a b h => ?_).ordinal_type_le
      obtain ⟨-, -, h'⟩ | ⟨-, h'⟩ := h
      · exact Prod.Lex.left _ _ h'
      · exact Prod.Lex.right _ (f.toRelEmbedding.map_rel_iff.2 h')⟩
/-
**Ordinal.le_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_mul_left (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a <= a * b
参数：a : Ordinal；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem le_mul_left (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a ≤ a * b := by
  convert! mul_le_mul_right (one_le_iff_pos.2 hb) a
  rw [mul_one a]
/-
**Ordinal.le_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_mul_right (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a <= b * a
参数：a : Ordinal；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem le_mul_right (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a ≤ b * a := by
  convert! mul_le_mul_left (one_le_iff_pos.2 hb) a
  rw [one_mul a]

set_option backward.isDefEq.respectTransparency false in
/-
**Ordinal.mul_le_of_limit_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_le_of_limit_aux {α β r s} [IsWellOrder α r] [IsWellOrder β s] {c}
    (h : IsSuccLimit (type s)) (H : ∀ b' < type s, type r * b' ≤ c) (l : c < type r * type s) :
    False := by
  suffices ∀ a b, Prod.Lex s r (b, a) (enum _ ⟨_, l⟩) from irrefl _ (this _ _)
  intro a b
  rw [← typein_lt_typein (Prod.Lex s r), typein_enum]
  have := H _ (h.succ_lt (typein_lt_type s b))
  rw [mul_succ] at this
  have := ((add_lt_add_iff_left _).2 (typein_lt_type _ a)).trans_le this
  refine (RelEmbedding.ofMonotone (fun a => ?_) fun a b => ?_).ordinal_type_le.trans_lt this
  · rcases a with ⟨⟨b', a'⟩, h⟩
    by_cases e : b = b'
    · exact .inr ⟨a', by grind [asymm_of s]⟩
    · exact .inl (⟨b', by grind⟩, a')
  · grind [subrel_val, Sum.Lex.sep, asymm_of s]
/-
**Ordinal.mul_le_iff_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_le_iff_of_isSuccLimit {a b c : Ordinal} (h : IsSuccLimit b) : a * b <=
 c ↔ forall b' < b, a * b' <= c
参数：h : IsSuccLimit b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Ordinal.inductionOn₂`：inductionOn₂ {motive : Ordinal -> Ordinal -> Prop}
 (o₁ o₂ : Ordinal) (type : forall (α r) [IsWellOrder α r] (β s) [IsWellOrder β s
], motive …
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Arithmetic.0.Ordinal.mul_le_of_limit_
aux`：∀ {α β : Type u_4} {r : α → α → Prop} {s : β → β → Prop} [inst : IsWellOrde
r α r] [inst_1 : IsWellOrder β s]   {c : Ordinal.{u_4}},   Order.…
-/
theorem mul_le_iff_of_isSuccLimit {a b c : Ordinal} (h : IsSuccLimit b) :
    a * b ≤ c ↔ ∀ b' < b, a * b' ≤ c := by
  refine ⟨fun h _ l ↦ (mul_le_mul_right l.le _).trans h, fun H ↦ le_of_not_gt ?_⟩
  induction a, b using inductionOn₂ with | type α r β s
  exact mul_le_of_limit_aux h H
/-
**Ordinal.isNormal_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_mul_right {a : Ordinal} (h : 0 < a) : IsNormal (a * ·)
参数：h : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.of_succ_lt`：of_succ_lt (hs : forall a, f a < f (succ a)) 
(hl : forall {a}, IsSuccLimit a -> IsLUB (f '' Iio a) (f a)) : IsNormal f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `add_lt_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [Ad
dLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b c : α},   a + b < a + c ↔ b <
 c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ordinal.mul_le_iff_of_isSuccLimit`：mul_le_iff_of_isSuccLimit {a b c : Or
dinal} (h : IsSuccLimit b) : a * b <= c ↔ forall b' < b, a * b' <= c
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem isNormal_mul_right {a : Ordinal} (h : 0 < a) : IsNormal (a * ·) := by
  refine .of_succ_lt (fun b ↦ ?_) fun hb ↦ ?_
  · simpa [mul_add_one] using (add_lt_add_iff_left (a * b)).2 h
  · simpa [IsLUB, IsLeast, upperBounds, lowerBounds, mul_le_iff_of_isSuccLimit hb] using
      fun c hc ↦ mul_le_mul_right hc.le a
/-
**Ordinal.lt_mul_iff_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_mul_iff_of_isSuccLimit {a b c : Ordinal} (h : IsSuccLimit c) : a < b * 
c ↔ exists c' < c, a < b * c'
参数：h : IsSuccLimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ordinal.mul_le_iff_of_isSuccLimit`：mul_le_iff_of_isSuccLimit {a b c : Or
dinal} (h : IsSuccLimit b) : a * b <= c ↔ forall b' < b, a * b' <= c
-/
theorem lt_mul_iff_of_isSuccLimit {a b c : Ordinal} (h : IsSuccLimit c) :
    a < b * c ↔ ∃ c' < c, a < b * c' := by
  simpa using (mul_le_iff_of_isSuccLimit h).not
/-
**Ordinal.lt_mul_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_mul_add_one_iff {a b c : Ordinal} : a < b * (c + 1) ↔ exists d < b, a <
= b * c + d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
· 使用定理 `Ordinal.lt_add_iff`：lt_add_iff {a b c : Ordinal} (hc : c != 0) : a < b +
 c ↔ exists d < c, a <= b + d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_mul_add_one_iff {a b c : Ordinal} : a < b * (c + 1) ↔ ∃ d < b, a ≤ b * c + d := by
  obtain rfl | hb := eq_or_ne b 0
  · simp
  · rw [mul_add_one, lt_add_iff hb]
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PosMulStrictMono Ordinal where
  mul_lt_mul_of_pos_left _a ha := (isNormal_mul_right ha).strictMono
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLeftCancelMulZero Ordinal where
  mul_left_cancel_of_ne_zero h0 _ _ := mul_left_cancel_iff_of_pos h0.pos |>.mp
/-
**Ordinal.isSuccLimit_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_mul_right {a b : Ordinal} (a0 : 0 < a) (l : IsSuccLimit b) : I
sSuccLimit (a * b)
参数：a0 : 0 < a；l : IsSuccLimit b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.map_isSuccLimit`：map_isSuccLimit (hf : IsNormal f) (ha : 
IsSuccLimit a) : IsSuccLimit (f a)
· 使用定理 `Ordinal.isNormal_mul_right`：isNormal_mul_right {a : Ordinal} (h : 0 < a)
 : IsNormal (a * ·)
-/
theorem isSuccLimit_mul_right {a b : Ordinal} (a0 : 0 < a) (l : IsSuccLimit b) :
    IsSuccLimit (a * b) :=
  (isNormal_mul_right a0).map_isSuccLimit l

@[deprecated (since := "2026-02-01")]
alias isSuccLimit_mul := isSuccLimit_mul_right
/-
**Ordinal.isSuccPrelimit_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccPrelimit_mul_right {a b : Ordinal} (hb : IsSuccLimit b) : IsSuccPrel
imit (a * b)
参数：hb : IsSuccLimit b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Ordinal.isSuccPrelimit_zero`：isSuccPrelimit_zero : IsSuccPrelimit (0 : O
rdinal)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `Ordinal.isSuccLimit_mul_right`：isSuccLimit_mul_right {a b : Ordinal} (a0
 : 0 < a) (l : IsSuccLimit b) : IsSuccLimit (a * b)
-/
theorem isSuccPrelimit_mul_right {a b : Ordinal} (hb : IsSuccLimit b) : IsSuccPrelimit (a * b) := by
  obtain rfl | ha := eq_zero_or_pos a
  · rw [zero_mul]
    exact isSuccPrelimit_zero
  · exact (isSuccLimit_mul_right ha hb).isSuccPrelimit
/-
**Ordinal.isSuccLimit_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_mul_left {a b : Ordinal} (l : IsSuccLimit a) (b0 : 0 < b) : Is
SuccLimit (a * b)
参数：l : IsSuccLimit a；b0 : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.zero_or_succ_or_isSuccLimit`：zero_or_succ_or_isSuccLimit (o : Or
dinal) : o = 0 ∨ o in range succ ∨ IsSuccLimit o
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.mul_succ`：mul_succ (a b : Ordinal) : a * succ b = a * b + a
· 使用定理 `Ordinal.isSuccLimit_add`：isSuccLimit_add (a : Ordinal) {b : Ordinal} : I
sSuccLimit b -> IsSuccLimit (a + b)
· 使用定理 `Ordinal.isSuccLimit_mul_right`：isSuccLimit_mul_right {a b : Ordinal} (a0
 : 0 < a) (l : IsSuccLimit b) : IsSuccLimit (a * b)
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
-/
theorem isSuccLimit_mul_left {a b : Ordinal} (l : IsSuccLimit a) (b0 : 0 < b) :
    IsSuccLimit (a * b) := by
  rcases zero_or_succ_or_isSuccLimit b with (rfl | ⟨b, rfl⟩ | lb)
  · exact b0.false.elim
  · rw [mul_succ]
    exact isSuccLimit_add _ l
  · exact isSuccLimit_mul_right l.bot_lt lb
/-
**Ordinal.isSuccPrelimit_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccPrelimit_mul_left {a b : Ordinal} (ha : IsSuccLimit a) : IsSuccPreli
mit (a * b)
参数：ha : IsSuccLimit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Ordinal.isSuccPrelimit_zero`：isSuccPrelimit_zero : IsSuccPrelimit (0 : O
rdinal)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `Ordinal.isSuccLimit_mul_left`：isSuccLimit_mul_left {a b : Ordinal} (l : 
IsSuccLimit a) (b0 : 0 < b) : IsSuccLimit (a * b)
-/
theorem isSuccPrelimit_mul_left {a b : Ordinal} (ha : IsSuccLimit a) : IsSuccPrelimit (a * b) := by
  obtain rfl | hb := eq_zero_or_pos b
  · rw [mul_zero]
    exact isSuccPrelimit_zero
  · exact (isSuccLimit_mul_left ha hb).isSuccPrelimit

@[simp]
/-
**Ordinal.nsmul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ (n : ℕ) (a : Ordinal.{u_4}), n • a = a * ↑n
参数：n : ℕ；a : Ordinal.{u_4}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nsmul_eq_mul : ∀ (n : ℕ) (a : Ordinal), n • a = a * n
  | 0, a => by rw [zero_nsmul, Nat.cast_zero, mul_zero]
  | n + 1, a => by rw [succ_nsmul, nsmul_eq_mul, Nat.cast_add_one, mul_add_one]

@[deprecated (since := "2026-03-14")] alias smul_eq_mul := nsmul_eq_mul
/-
**Ordinal.add_mul_limit_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem add_mul_limit_aux {a b c : Ordinal} (ba : b + a = a) (l : IsSuccLimit c)
    (IH : ∀ c' < c, (a + b) * succ c' = a * succ c' + b) : (a + b) * c = a * c :=
  le_antisymm
    ((mul_le_iff_of_isSuccLimit l).2 fun c' h => by
      grw [le_succ c', IH _ h, le_self_add (a := b), ba, ← mul_succ, succ_le_of_lt <| l.succ_lt h])
    (by grw [← le_self_add])
/-
**Ordinal.add_mul_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_mul_add_one {a b : Ordinal} (c) (ba : b + a = a) : (a + b) * (c + 1) =
 a * (c + 1) + b
参数：c；ba : b + a = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Arithmetic.0.Ordinal.add_mul_limit_au
x`：∀ {a b c : Ordinal.{u_4}},   b + a = a → Order.IsSuccLimit c → (∀ c' < c, (a 
+ b) * Order.succ c' = a * Order.succ c' + b) → (a + b) * c = a…
-/
theorem add_mul_add_one {a b : Ordinal} (c) (ba : b + a = a) :
    (a + b) * (c + 1) = a * (c + 1) + b := by
  induction c using limitRecOn with
  | zero => simp
  | add_one c IH => rw [mul_add_one, IH, ← add_assoc, add_assoc _ b, ba, ← mul_add_one]
  | limit c l IH => rw [mul_add_one, add_mul_limit_aux ba l IH, mul_add_one, add_assoc]

-- TODO: deprecate
/-
**Ordinal.add_mul_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_mul_succ {a b : Ordinal} (c) (ba : b + a = a) : (a + b) * succ c = a *
 succ c + b
参数：c；ba : b + a = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.add_mul_add_one`：add_mul_add_one {a b : Ordinal} (c) (ba : b + a
 = a) : (a + b) * (c + 1) = a * (c + 1) + b
-/
theorem add_mul_succ {a b : Ordinal} (c) (ba : b + a = a) : (a + b) * succ c = a * succ c + b :=
  add_mul_add_one c ba
/-
**Ordinal.add_mul_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_mul_of_isSuccLimit {a b c : Ordinal} (ba : b + a = a) (l : IsSuccLimit
 c) : (a + b) * c = a * c
参数：ba : b + a = a；l : IsSuccLimit c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Arithmetic.0.Ordinal.add_mul_limit_au
x`：∀ {a b c : Ordinal.{u_4}},   b + a = a → Order.IsSuccLimit c → (∀ c' < c, (a 
+ b) * Order.succ c' = a * Order.succ c' + b) → (a + b) * c = a…
· 使用定理 `Ordinal.add_mul_succ`：add_mul_succ {a b : Ordinal} (c) (ba : b + a = a) 
: (a + b) * succ c = a * succ c + b
-/
theorem add_mul_of_isSuccLimit {a b c : Ordinal} (ba : b + a = a) (l : IsSuccLimit c) :
    (a + b) * c = a * c :=
  add_mul_limit_aux ba l fun c' _ => add_mul_succ c' ba
/-
**Ordinal.mul_two** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ (o : Ordinal.{u_4}), o * 2 = o + o
参数：o : Ordinal.{u_4}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
protected theorem mul_two (o : Ordinal) : o * 2 = o + o := by
  rw [← one_add_one_eq_two, mul_add, mul_one]

/-! ### Division on ordinals -/

/-- `a / b` is the unique ordinal `q` satisfying `a = b * q + r` with `r < b`. -/
@[no_expose]
/-
**Ordinal.div** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：div : Div Ordinal where div a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a / b` is the unique ordinal `q` satisfying `a = b * q + r` with `r < b`.
-/
instance div : Div Ordinal where
  div a b := sSup ((b * ·) ⁻¹' Iic a)

@[simp]
/-
**Ordinal.div_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_zero (a : Ordinal) : a / 0 = 0
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_zero (a : Ordinal) : a / 0 = 0 := by
  change sSup _ = _
  simp

/-- Multiplication and division by a non-zero ordinal form a Galois connection. -/
/-
**Ordinal.mul_div_gc** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_div_gc {a : Ordinal} (ha : a != 0) : GaloisConnection (a * ·) (· / a)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.le_iff_le_sSup'`：le_iff_le_sSup' [WellFoundedLT α] {f : α
 -> α} (hf : IsNormal f) {x y : α} (h : (f ⁻¹' Iic y).Nonempty) : f x <= y ↔ x <
= sSup (f ⁻¹' Iic y)
· 使用定理 `Ordinal.isNormal_mul_right`：isNormal_mul_right {a : Ordinal} (h : 0 < a)
 : IsNormal (a * ·)
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
Multiplication and division by a non-zero ordinal form a Galois connection.
-/
theorem mul_div_gc {a : Ordinal} (ha : a ≠ 0) : GaloisConnection (a * ·) (· / a) :=
  fun b c ↦ (isNormal_mul_right ha.pos).le_iff_le_sSup' ⟨0, by simp⟩
/-
**Ordinal.mul_le_iff_le_div** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_le_iff_le_div {a b c : Ordinal} (ha : a != 0) : a * b <= c ↔ b <= c / 
a
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_iff_le`：le_iff_le {a : α} {b : β} : l a <= b ↔ a <= 
u b
· 使用定理 `Ordinal.mul_div_gc`：mul_div_gc {a : Ordinal} (ha : a != 0) : GaloisConne
ction (a * ·) (· / a)
-/
theorem mul_le_iff_le_div {a b c : Ordinal} (ha : a ≠ 0) : a * b ≤ c ↔ b ≤ c / a :=
  (mul_div_gc ha).le_iff_le
/-
**Ordinal.lt_mul_iff_div_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_mul_iff_div_lt {a b c : Ordinal} (ha : a != 0) : c < a * b ↔ c / a < b
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.lt_iff_lt`：lt_iff_lt (gc : GaloisConnection l u) {a : α
} {b : β} : b < l a ↔ u b < a
· 使用定理 `Ordinal.mul_div_gc`：mul_div_gc {a : Ordinal} (ha : a != 0) : GaloisConne
ction (a * ·) (· / a)
-/
theorem lt_mul_iff_div_lt {a b c : Ordinal} (ha : a ≠ 0) : c < a * b ↔ c / a < b :=
  (mul_div_gc ha).lt_iff_lt
/-
**Ordinal.lt_mul_succ_div** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_mul_succ_div (a) {b : Ordinal} (h : b != 0) : a < b * succ (a / b)
参数：a；h : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lt_mul_iff_div_lt`：lt_mul_iff_div_lt {a b c : Ordinal} (ha : a !
= 0) : c < a * b ↔ c / a < b
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lt_mul_succ_div (a) {b : Ordinal} (h : b ≠ 0) : a < b * succ (a / b) := by
  rw [lt_mul_iff_div_lt h, lt_succ_iff]
/-
**Ordinal.lt_mul_div_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_mul_div_add (a) {b : Ordinal} (h : b != 0) : a < b * (a / b) + b
参数：a；h : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.mul_succ`：mul_succ (a b : Ordinal) : a * succ b = a * b + a
· 使用定理 `Ordinal.lt_mul_succ_div`：lt_mul_succ_div (a) {b : Ordinal} (h : b != 0) 
: a < b * succ (a / b)
-/
theorem lt_mul_div_add (a) {b : Ordinal} (h : b ≠ 0) : a < b * (a / b) + b := by
  simpa only [mul_succ] using lt_mul_succ_div a h
/-
**Ordinal.div_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_le {a b c : Ordinal} (b0 : b != 0) : a / b <= c ↔ a < b * succ c
参数：b0 : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.lt_mul_iff_div_lt`：lt_mul_iff_div_lt {a b c : Ordinal} (ha : a !
= 0) : c < a * b ↔ c / a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_le {a b c : Ordinal} (b0 : b ≠ 0) : a / b ≤ c ↔ a < b * succ c := by
  rw [← lt_succ_iff, ← lt_mul_iff_div_lt b0]
/-
**Ordinal.lt_div** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_div {a b c : Ordinal} (h : c != 0) : a < b / c ↔ c * succ a <= b
参数：h : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Ordinal.div_le`：div_le {a b c : Ordinal} (b0 : b != 0) : a / b <= c ↔ a 
< b * succ c
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_div {a b c : Ordinal} (h : c ≠ 0) : a < b / c ↔ c * succ a ≤ b := by
  rw [← not_le, div_le h, not_lt]
/-
**Ordinal.div_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_pos {b c : Ordinal} (h : c != 0) : 0 < b / c ↔ c <= b
参数：h : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lt_div`：lt_div {a b c : Ordinal} (h : c != 0) : a < b / c ↔ c * 
succ a <= b
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem div_pos {b c : Ordinal} (h : c ≠ 0) : 0 < b / c ↔ c ≤ b := by simp [lt_div h]

@[deprecated mul_le_iff_le_div (since := "2026-02-27")]
/-
**Ordinal.le_div** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_div {a b c : Ordinal} (c0 : c != 0) : a <= b / c ↔ c * a <= b
参数：c0 : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ordinal.mul_le_iff_le_div`：mul_le_iff_le_div {a b c : Ordinal} (ha : a !
= 0) : a * b <= c ↔ b <= c / a
-/
theorem le_div {a b c : Ordinal} (c0 : c ≠ 0) : a ≤ b / c ↔ c * a ≤ b :=
  (mul_le_iff_le_div c0).symm

@[deprecated lt_mul_iff_div_lt (since := "2026-02-27")]
/-
**Ordinal.div_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_lt {a b c : Ordinal} (b0 : b != 0) : a / b < c ↔ a < b * c
参数：b0 : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ordinal.lt_mul_iff_div_lt`：lt_mul_iff_div_lt {a b c : Ordinal} (ha : a !
= 0) : c < a * b ↔ c / a < b
-/
theorem div_lt {a b c : Ordinal} (b0 : b ≠ 0) : a / b < c ↔ a < b * c :=
  (lt_mul_iff_div_lt b0).symm
/-
**Ordinal.div_le_of_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_le_of_le_mul {a b c : Ordinal} (h : a <= b * c) : a / b <= c
参数：h : a <= b * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.div_zero`：div_zero (a : Ordinal) : a / 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.div_le`：div_le {a b c : Ordinal} (b0 : b != 0) : a / b <= c ↔ a 
< b * succ c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `Ordinal.instPosMulStrictMono`：PosMulStrictMono Ordinal.{u_4}
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
-/
theorem div_le_of_le_mul {a b c : Ordinal} (h : a ≤ b * c) : a / b ≤ c := by
  obtain rfl | b0 := eq_or_ne b 0
  · simp
  · exact (div_le b0).2 <| h.trans_lt <| mul_lt_mul_of_pos_left (lt_succ c) (pos_iff_ne_zero.2 b0)
/-
**Ordinal.mul_lt_of_lt_div** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_lt_of_lt_div {a b c : Ordinal} : a < b / c -> c * a < b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `Ordinal.div_le_of_le_mul`：div_le_of_le_mul {a b c : Ordinal} (h : a <= b
 * c) : a / b <= c
-/
theorem mul_lt_of_lt_div {a b c : Ordinal} : a < b / c → c * a < b :=
  lt_imp_lt_of_le_imp_le div_le_of_le_mul

@[simp]
/-
**Ordinal.zero_div** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：zero_div (a : Ordinal) : 0 / a = 0
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.div_le_of_le_mul`：div_le_of_le_mul {a b c : Ordinal} (h : a <= b
 * c) : a / b <= c
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
-/
theorem zero_div (a : Ordinal) : 0 / a = 0 := nonpos_iff_eq_zero.1 <| div_le_of_le_mul zero_le
/-
**Ordinal.mul_div_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_div_le (a b : Ordinal) : b * (a / b) <= a
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ordinal.div_zero`：div_zero (a : Ordinal) : a / 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.mul_le_iff_le_div`：mul_le_iff_le_div {a b c : Ordinal} (ha : a !
= 0) : a * b <= c ↔ b <= c / a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem mul_div_le (a b : Ordinal) : b * (a / b) ≤ a :=
  if b0 : b = 0 then by simp [b0] else (mul_le_iff_le_div b0).2 le_rfl
/-
**Ordinal.div_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_le_left {a b : Ordinal} (h : a <= b) (c : Ordinal) : a / c <= b / c
参数：h : a <= b；c : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.div_zero`：div_zero (a : Ordinal) : a / 0 = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.mul_le_iff_le_div`：mul_le_iff_le_div {a b c : Ordinal} (ha : a !
= 0) : a * b <= c ↔ b <= c / a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.mul_div_le`：mul_div_le (a b : Ordinal) : b * (a / b) <= a
-/
theorem div_le_left {a b : Ordinal} (h : a ≤ b) (c : Ordinal) : a / c ≤ b / c := by
  obtain rfl | hc := eq_or_ne c 0
  · rw [div_zero, div_zero]
  · rw [← mul_le_iff_le_div hc]
    exact (mul_div_le a c).trans h
/-
**Ordinal.mul_add_div** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_add_div (a) {b : Ordinal} (b0 : b != 0) (c) : (b * a + c) / b = a + c 
/ b
参数：a；b0 : b != 0；c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.div_le`：div_le {a b c : Ordinal} (b0 : b != 0) : a / b <= c ↔ a 
< b * succ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.mul_succ`：mul_succ (a b : Ordinal) : a * succ b = a * b + a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_lt_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [Ad
dLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b c : α},   a + b < a + c ↔ b <
 c
· 使用定理 `Ordinal.lt_mul_div_add`：lt_mul_div_add (a) {b : Ordinal} (h : b != 0) : 
a < b * (a / b) + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.mul_le_iff_le_div`：mul_le_iff_le_div {a b c : Ordinal} (ha : a !
= 0) : a * b <= c ↔ b <= c / a
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `Ordinal.mul_div_le`：mul_div_le (a b : Ordinal) : b * (a / b) <= a
-/
theorem mul_add_div (a) {b : Ordinal} (b0 : b ≠ 0) (c) : (b * a + c) / b = a + c / b := by
  apply le_antisymm
  · apply (div_le b0).2
    rw [mul_succ, mul_add, add_assoc, add_lt_add_iff_left]
    apply lt_mul_div_add _ b0
  · rw [← mul_le_iff_le_div b0, mul_add, add_le_add_iff_left]
    apply mul_div_le
/-
**Ordinal.div_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_eq_zero_of_lt {a b : Ordinal} (h : a < b) : a / b = 0
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.div_le`：div_le {a b c : Ordinal} (b0 : b != 0) : a / b <= c ↔ a 
< b * succ c
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem div_eq_zero_of_lt {a b : Ordinal} (h : a < b) : a / b = 0 := by
  rw [← nonpos_iff_eq_zero, div_le h.ne_bot]
  simpa

@[simp]
/-
**Ordinal.mul_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_div_cancel (a) {b : Ordinal} (b0 : b != 0) : b * a / b = a
参数：a；b0 : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.zero_div`：zero_div (a : Ordinal) : 0 / a = 0
· 使用定理 `Ordinal.mul_add_div`：mul_add_div (a) {b : Ordinal} (b0 : b != 0) (c) : (
b * a + c) / b = a + c / b
-/
theorem mul_div_cancel (a) {b : Ordinal} (b0 : b ≠ 0) : b * a / b = a := by
  simpa using mul_add_div a b0 0
/-
**Ordinal.mul_add_div_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_add_div_mul {a c : Ordinal} (hc : c < a) (b d : Ordinal) : (a * b + c)
 / (a * d) = b / d
参数：hc : c < a；b d : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Ordinal.div_zero`：div_zero (a : Ordinal) : a / 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.lt_mul_iff_div_lt`：lt_mul_iff_div_lt {a b c : Ordinal} (ha : a !
= 0) : c < a * b ↔ c / a < b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `Ordinal.mul_succ`：mul_succ (a b : Ordinal) : a * succ b = a * b + a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.lt_mul_succ_div`：lt_mul_succ_div (a) {b : Ordinal} (h : b != 0) 
: a < b * succ (a / b)
· 使用定理 `Ordinal.mul_le_iff_le_div`：mul_le_iff_le_div {a b c : Ordinal} (ha : a !
= 0) : a * b <= c ↔ b <= c / a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Ordinal.mul_div_le`：mul_div_le (a b : Ordinal) : b * (a / b) <= a
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
-/
theorem mul_add_div_mul {a c : Ordinal} (hc : c < a) (b d : Ordinal) :
    (a * b + c) / (a * d) = b / d := by
  obtain rfl | hd := eq_or_ne d 0
  · rw [mul_zero, div_zero, div_zero]
  · have H := mul_ne_zero hc.ne_zero hd
    apply le_antisymm
    · rw [← lt_succ_iff, ← lt_mul_iff_div_lt H, mul_assoc]
      · grw [hc, ← mul_succ]
        gcongr
        rw [succ_le_iff]
        exact lt_mul_succ_div b hd
    · grw [← mul_le_iff_le_div H, mul_assoc, mul_div_le b d, ← le_self_add]
/-
**Ordinal.mul_div_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_div_mul_cancel {a : Ordinal} (ha : a != 0) (b c) : a * b / (a * c) = b
 / c
参数：ha : a != 0；b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.mul_add_div_mul`：mul_add_div_mul {a c : Ordinal} (hc : c < a) (b
 d : Ordinal) : (a * b + c) / (a * d) = b / d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem mul_div_mul_cancel {a : Ordinal} (ha : a ≠ 0) (b c) : a * b / (a * c) = b / c := by
  convert! mul_add_div_mul (pos_iff_ne_zero.2 ha) b c using 1
  rw [add_zero]
/-
**Ordinal.div_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_eq {a b c : Ordinal} (hle : b * c <= a) (hlt : a < b * (c + 1)) : a / 
b = c
参数：hle : b * c <= a；hlt : a < b * (c + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.div_le`：div_le {a b c : Ordinal} (b0 : b != 0) : a / b <= c ↔ a 
< b * succ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.mul_le_iff_le_div`：mul_le_iff_le_div {a b c : Ordinal} (ha : a !
= 0) : a * b <= c ↔ b <= c / a
-/
theorem div_eq {a b c : Ordinal} (hle : b * c ≤ a) (hlt : a < b * (c + 1)) : a / b = c := by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp at hlt
  exact le_antisymm (div_le hb |>.mpr hlt) (mul_le_iff_le_div hb |>.mp hle)

/-- Characterization of `a / b = c` assuming `b ≠ 0`.
See `div_eq_iff'` for a version assuming `c ≠ 0` instead. -/
/-
**Ordinal.div_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_eq_iff {a b c : Ordinal} (hb : b != 0) : a / b = c ↔ b * c <= a ∧ a < 
b * (c + 1)
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.mul_div_le`：mul_div_le (a b : Ordinal) : b * (a / b) <= a
· 使用定理 `Ordinal.lt_mul_succ_div`：lt_mul_succ_div (a) {b : Ordinal} (h : b != 0) 
: a < b * succ (a / b)
· 使用定理 `Ordinal.div_eq`：div_eq {a b c : Ordinal} (hle : b * c <= a) (hlt : a < b
 * (c + 1)) : a / b = c

--- 原说明 ---
Characterization of `a / b = c` assuming `b ≠ 0`.
See `div_eq_iff'` for a version assuming `c ≠ 0` instead.
-/
theorem div_eq_iff {a b c : Ordinal} (hb : b ≠ 0) : a / b = c ↔ b * c ≤ a ∧ a < b * (c + 1) :=
  ⟨fun h ↦ h ▸ ⟨mul_div_le a b, lt_mul_succ_div a hb⟩, fun ⟨hle, hlt⟩ ↦ div_eq hle hlt⟩

/-- Characterization of `a / b = c` assuming `c ≠ 0`.
See `div_eq_iff` for a version assuming `b ≠ 0` instead. -/
/-
**Ordinal.div_eq_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_eq_iff' {a b c : Ordinal} (hc : c != 0) : a / b = c ↔ b * c <= a ∧ a <
 b * (c + 1)
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.div_zero`：div_zero (a : Ordinal) : a / 0 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.div_eq_iff`：div_eq_iff {a b c : Ordinal} (hb : b != 0) : a / b =
 c ↔ b * c <= a ∧ a < b * (c + 1)

--- 原说明 ---
Characterization of `a / b = c` assuming `c ≠ 0`.
See `div_eq_iff` for a version assuming `b ≠ 0` instead.
-/
theorem div_eq_iff' {a b c : Ordinal} (hc : c ≠ 0) : a / b = c ↔ b * c ≤ a ∧ a < b * (c + 1) := by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp [hc.symm]
  exact div_eq_iff hb
/-
**Ordinal.div_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_eq_one_iff {a b : Ordinal} : a / b = 1 ↔ b <= a ∧ a < b * 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.div_eq_iff'`：div_eq_iff' {a b c : Ordinal} (hc : c != 0) : a / b
 = c ↔ b * c <= a ∧ a < b * (c + 1)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_eq_one_iff {a b : Ordinal} : a / b = 1 ↔ b ≤ a ∧ a < b * 2 := by
  rw [div_eq_iff' one_ne_zero, mul_one, one_add_one_eq_two]

@[simp]
/-
**Ordinal.div_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_one (a : Ordinal) : a / 1 = a
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Ordinal.mul_div_cancel`：mul_div_cancel (a) {b : Ordinal} (b0 : b != 0) :
 b * a / b = a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem div_one (a : Ordinal) : a / 1 = a := by
  simpa only [one_mul] using mul_div_cancel a one_ne_zero

@[simp]
/-
**Ordinal.div_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_self {a : Ordinal} (h : a != 0) : a / a = 1
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ordinal.mul_div_cancel`：mul_div_cancel (a) {b : Ordinal} (b0 : b != 0) :
 b * a / b = a
-/
theorem div_self {a : Ordinal} (h : a ≠ 0) : a / a = 1 := by
  simpa only [mul_one] using mul_div_cancel 1 h
/-
**Ordinal.mul_sub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_sub (a b c : Ordinal) : a * (b - c) = a * b - a * c
参数：a b c : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Ordinal.sub_self`：sub_self (a : Ordinal) : a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `Ordinal.sub_le`：sub_le {a b c : Ordinal} : a - b <= c ↔ a <= b + c
· 使用定理 `Ordinal.mul_le_iff_le_div`：mul_le_iff_le_div {a b c : Ordinal} (ha : a !
= 0) : a * b <= c ↔ b <= c / a
· 使用定理 `Ordinal.mul_add_div`：mul_add_div (a) {b : Ordinal} (b0 : b != 0) (c) : (
b * a + c) / b = a + c / b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_sub (a b c : Ordinal) : a * (b - c) = a * b - a * c := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · refine eq_of_forall_ge_iff fun d ↦ ?_
    rw [sub_le, mul_le_iff_le_div ha, sub_le, mul_le_iff_le_div ha, mul_add_div _ ha]
/-
**Ordinal.isSuccLimit_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_add_iff {a b : Ordinal} : IsSuccLimit (a + b) ↔ IsSuccLimit b 
∨ b = 0 ∧ IsSuccLimit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.add_sub_cancel`：add_sub_cancel (a b : Ordinal) : a + b - a = b
· 使用定理 `Ordinal.isSuccLimit_sub`：isSuccLimit_sub {a b : Ordinal} (ha : IsSuccPre
limit a) (h : b < a) : IsSuccLimit (a - b)
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem isSuccLimit_add_iff {a b : Ordinal} :
    IsSuccLimit (a + b) ↔ IsSuccLimit b ∨ b = 0 ∧ IsSuccLimit a := by
  refine ⟨fun h ↦ ?_, by grind [isSuccLimit_add]⟩
  rcases eq_or_ne b 0 with (rfl | h')
  · grind
  rw [← add_sub_cancel a b]
  exact .inl <| isSuccLimit_sub h.isSuccPrelimit <| lt_add_of_pos_right a h'.pos
/-
**Ordinal.isSuccLimit_add_iff_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`
。
形式化陈述：isSuccLimit_add_iff_of_isSuccLimit {a b : Ordinal} (h : IsSuccLimit a) : I
sSuccLimit (a + b) ↔ IsSuccPrelimit b
参数：h : IsSuccLimit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.isSuccLimit_add_iff`：isSuccLimit_add_iff {a b : Ordinal} : IsSuc
cLimit (a + b) ↔ IsSuccLimit b ∨ b = 0 ∧ IsSuccLimit a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSuccLimit_add_iff_of_isSuccLimit {a b : Ordinal} (h : IsSuccLimit a) :
    IsSuccLimit (a + b) ↔ IsSuccPrelimit b := by
  rw [isSuccLimit_add_iff]
  obtain rfl | hb := eq_or_ne b 0
  · simpa
  · simp [hb, isSuccLimit_iff]
/-
**Ordinal.dvd_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {a b c : Ordinal.{u_4}}, a ∣ b → (a ∣ b + c ↔ a ∣ c)
参数：a ∣ b + c ↔ a ∣ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.mul_sub`：mul_sub (a b c : Ordinal) : a * (b - c) = a * b - a * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.add_sub_cancel`：add_sub_cancel (a b : Ordinal) : a + b - a = b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem dvd_add_iff : ∀ {a b c : Ordinal}, a ∣ b → (a ∣ b + c ↔ a ∣ c)
  | a, _, c, ⟨b, rfl⟩ =>
    ⟨fun ⟨d, e⟩ => ⟨d - b, by rw [mul_sub, ← e, add_sub_cancel]⟩, fun ⟨d, e⟩ => by
      rw [e, ← mul_add]
      apply dvd_mul_right⟩
/-
**Ordinal.div_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {a b : Ordinal.{u_4}}, a ≠ 0 → a ∣ b → a * (b / a) = b
参数：b / a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.mul_div_cancel`：mul_div_cancel (a) {b : Ordinal} (b0 : b != 0) :
 b * a / b = a
-/
theorem div_mul_cancel : ∀ {a b : Ordinal}, a ≠ 0 → a ∣ b → a * (b / a) = b
  | a, _, a0, ⟨b, rfl⟩ => by rw [mul_div_cancel _ a0]
/-
**Ordinal.le_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_of_dvd {a b : Ordinal} (b0 : b != 0) (h : a ∣ b) : a <= b
参数：b0 : b != 0；h : a ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_of_dvd {a b : Ordinal} (b0 : b ≠ 0) (h : a ∣ b) : a ≤ b := by
  rcases h with ⟨b, rfl⟩
  simpa using mul_le_mul_right (one_le_iff_ne_zero.mpr fun h ↦ by simp [h] at b0) a
/-
**Ordinal.dvd_antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：dvd_antisymm {a b : Ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b
参数：h₁ : a ∣ b；h₂ : b ∣ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_zero_of_zero_dvd`：eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.le_of_dvd`：le_of_dvd {a b : Ordinal} (b0 : b != 0) (h : a ∣ b) :
 a <= b
-/
theorem dvd_antisymm {a b : Ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b :=
  if a0 : a = 0 then by subst a; exact (eq_zero_of_zero_dvd h₁).symm
  else
    if b0 : b = 0 then by subst b; exact eq_zero_of_zero_dvd h₂
    else (le_of_dvd b0 h₁).antisymm (le_of_dvd a0 h₂)
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPartialOrder Ordinal (· ∣ ·) where
  refl := dvd_refl
  trans _ _ _ := dvd_trans
  antisymm := @dvd_antisymm

/-- `a % b` is the unique ordinal `r` satisfying `a = b * q + r` with `r < b`. -/
/-
**Ordinal.mod** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：mod : Mod Ordinal where mod a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a % b` is the unique ordinal `r` satisfying `a = b * q + r` with `r < b`.
-/
instance mod : Mod Ordinal where
  mod a b := a - b * (a / b)
/-
**Ordinal.mod_def** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mod_def (a b : Ordinal) : a % b = a - b * (a / b)
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mod_def (a b : Ordinal) : a % b = a - b * (a / b) :=
  rfl
/-
**Ordinal.mod_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mod_le (a b : Ordinal) : a % b <= a
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.sub_le_self`：sub_le_self (a b : Ordinal) : a - b <= a
-/
theorem mod_le (a b : Ordinal) : a % b ≤ a :=
  sub_le_self a _

@[simp]
/-
**Ordinal.mod_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mod_zero (a : Ordinal) : a % 0 = a
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.div_zero`：div_zero (a : Ordinal) : a / 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Ordinal.sub_zero`：sub_zero (a : Ordinal) : a - 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mod_zero (a : Ordinal) : a % 0 = a := by simp [mod_def]
/-
**Ordinal.mod_eq_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mod_eq_of_lt {a b : Ordinal} (h : a < b) : a % b = a
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.div_eq_zero_of_lt`：div_eq_zero_of_lt {a b : Ordinal} (h : a < b)
 : a / b = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Ordinal.sub_zero`：sub_zero (a : Ordinal) : a - 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mod_eq_of_lt {a b : Ordinal} (h : a < b) : a % b = a := by
  simp [mod_def, div_eq_zero_of_lt h]

@[simp]
/-
**Ordinal.zero_mod** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：zero_mod (b : Ordinal) : 0 % b = 0
参数：b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.zero_div`：zero_div (a : Ordinal) : 0 / a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Ordinal.sub_self`：sub_self (a : Ordinal) : a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_mod (b : Ordinal) : 0 % b = 0 := by simp [mod_def]
/-
**Ordinal.div_add_mod** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_add_mod (a b : Ordinal) : b * (a / b) + a % b = a
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
· 使用定理 `Ordinal.mul_div_le`：mul_div_le (a b : Ordinal) : b * (a / b) <= a
-/
theorem div_add_mod (a b : Ordinal) : b * (a / b) + a % b = a :=
  Ordinal.add_sub_cancel_of_le <| mul_div_le _ _
/-
**Ordinal.mod_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mod_lt (a) {b : Ordinal} (h : b != 0) : a % b < b
参数：a；h : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_lt_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [Ad
dLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b c : α},   a + b < a + c ↔ b <
 c
· 使用定理 `Ordinal.div_add_mod`：div_add_mod (a b : Ordinal) : b * (a / b) + a % b =
 a
· 使用定理 `Ordinal.lt_mul_div_add`：lt_mul_div_add (a) {b : Ordinal} (h : b != 0) : 
a < b * (a / b) + b
-/
theorem mod_lt (a) {b : Ordinal} (h : b ≠ 0) : a % b < b := by
  rw [← add_lt_add_iff_left, div_add_mod]
  exact lt_mul_div_add a h

@[simp]
/-
**Ordinal.mod_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mod_self (a : Ordinal) : a % a = 0
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.mod_zero`：mod_zero (a : Ordinal) : a % 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.div_self`：div_self {a : Ordinal} (h : a != 0) : a / a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ordinal.sub_self`：sub_self (a : Ordinal) : a - a = 0
-/
theorem mod_self (a : Ordinal) : a % a = 0 := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · simp [mod_def, ha]

@[simp]
/-
**Ordinal.mod_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mod_one (a : Ordinal) : a % 1 = 0
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.div_one`：div_one (a : Ordinal) : a / 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Ordinal.sub_self`：sub_self (a : Ordinal) : a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mod_one (a : Ordinal) : a % 1 = 0 := by simp [mod_def]
/-
**Ordinal.dvd_of_mod_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：dvd_of_mod_eq_zero {a b : Ordinal} (H : a % b = 0) : b ∣ a
参数：H : a % b = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.div_add_mod`：div_add_mod (a b : Ordinal) : b * (a / b) + a % b =
 a
-/
theorem dvd_of_mod_eq_zero {a b : Ordinal} (H : a % b = 0) : b ∣ a :=
  ⟨a / b, by simpa [H] using (div_add_mod a b).symm⟩
/-
**Ordinal.mod_eq_zero_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mod_eq_zero_of_dvd {a b : Ordinal} (H : b ∣ a) : a % b = 0
参数：H : b ∣ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Ordinal.mod_self`：mod_self (a : Ordinal) : a % a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.mul_div_cancel`：mul_div_cancel (a) {b : Ordinal} (b0 : b != 0) :
 b * a / b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ordinal.sub_self`：sub_self (a : Ordinal) : a - a = 0
-/
theorem mod_eq_zero_of_dvd {a b : Ordinal} (H : b ∣ a) : a % b = 0 := by
  rcases H with ⟨c, rfl⟩
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp
  · simp [mod_def, hb]
/-
**Ordinal.dvd_iff_mod_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：dvd_iff_mod_eq_zero {a b : Ordinal} : b ∣ a ↔ a % b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.mod_eq_zero_of_dvd`：mod_eq_zero_of_dvd {a b : Ordinal} (H : b ∣ 
a) : a % b = 0
· 使用定理 `Ordinal.dvd_of_mod_eq_zero`：dvd_of_mod_eq_zero {a b : Ordinal} (H : a % 
b = 0) : b ∣ a
-/
theorem dvd_iff_mod_eq_zero {a b : Ordinal} : b ∣ a ↔ a % b = 0 :=
  ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

@[simp]
/-
**Ordinal.mul_add_mod_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_add_mod_self (x y z : Ordinal) : (x * y + z) % x = z % x
参数：x y z : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ordinal.mod_zero`：mod_zero (a : Ordinal) : a % 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.mod_def`：mod_def (a b : Ordinal) : a % b = a - b * (a / b)
· 使用定理 `Ordinal.mul_add_div`：mul_add_div (a) {b : Ordinal} (b0 : b != 0) (c) : (
b * a + c) / b = a + c / b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Ordinal.sub_sub`：sub_sub (a b c : Ordinal) : a - b - c = a - (b + c)
· 使用定理 `Ordinal.add_sub_cancel`：add_sub_cancel (a b : Ordinal) : a + b - a = b
-/
theorem mul_add_mod_self (x y z : Ordinal) : (x * y + z) % x = z % x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rwa [mod_def, mul_add_div, mul_add, ← sub_sub, add_sub_cancel, mod_def]

@[simp]
/-
**Ordinal.mul_mod** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_mod (x y : Ordinal) : x * y % x = 0
参数：x y : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.zero_mod`：zero_mod (b : Ordinal) : 0 % b = 0
· 使用定理 `Ordinal.mul_add_mod_self`：mul_add_mod_self (x y z : Ordinal) : (x * y + 
z) % x = z % x
-/
theorem mul_mod (x y : Ordinal) : x * y % x = 0 := by
  simpa using mul_add_mod_self x y 0
/-
**Ordinal.mul_add_mod_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_add_mod_mul {w x : Ordinal} (hw : w < x) (y z : Ordinal) : (x * y + w)
 % (x * z) = x * (y % z) + w
参数：hw : w < x；y z : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.mod_def`：mod_def (a b : Ordinal) : a % b = a - b * (a / b)
· 使用定理 `Ordinal.mul_add_div_mul`：mul_add_div_mul {a c : Ordinal} (hc : c < a) (b
 d : Ordinal) : (a * b + c) / (a * d) = b / d
· 使用定理 `Ordinal.sub_eq_of_add_eq`：sub_eq_of_add_eq {a b c : Ordinal} (h : a + b 
= c) : c - a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Ordinal.div_add_mod`：div_add_mod (a b : Ordinal) : b * (a / b) + a % b =
 a
-/
theorem mul_add_mod_mul {w x : Ordinal} (hw : w < x) (y z : Ordinal) :
    (x * y + w) % (x * z) = x * (y % z) + w := by
  rw [mod_def, mul_add_div_mul hw]
  apply sub_eq_of_add_eq
  rw [← add_assoc, mul_assoc, ← mul_add, div_add_mod]
/-
**Ordinal.mul_mod_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_mod_mul (x y z : Ordinal) : (x * y) % (x * z) = x * (y % z)
参数：x y z : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Ordinal.mod_self`：mod_self (a : Ordinal) : a % a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.mul_add_mod_mul`：mul_add_mod_mul {w x : Ordinal} (hw : w < x) (y
 z : Ordinal) : (x * y + w) % (x * z) = x * (y % z) + w
-/
theorem mul_mod_mul (x y z : Ordinal) : (x * y) % (x * z) = x * (y % z) := by
  obtain rfl | hx := eq_zero_or_pos x
  · simp
  · convert! mul_add_mod_mul hx y z using 1 <;>
    rw [add_zero]
/-
**Ordinal.mod_mod_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mod_mod_of_dvd (a : Ordinal) {b c : Ordinal} (h : c ∣ b) : a % b % c = a %
 c
参数：a : Ordinal；h : c ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.div_add_mod`：div_add_mod (a b : Ordinal) : b * (a / b) + a % b =
 a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ordinal.mul_add_mod_self`：mul_add_mod_self (x y z : Ordinal) : (x * y + 
z) % x = z % x
-/
theorem mod_mod_of_dvd (a : Ordinal) {b c : Ordinal} (h : c ∣ b) : a % b % c = a % c := by
  nth_rw 2 [← div_add_mod a b]
  rcases h with ⟨d, rfl⟩
  rw [mul_assoc, mul_add_mod_self]

@[simp]
/-
**Ordinal.mod_mod** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mod_mod (a b : Ordinal) : a % b % b = a % b
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.mod_mod_of_dvd`：mod_mod_of_dvd (a : Ordinal) {b c : Ordinal} (h 
: c ∣ b) : a % b % c = a % c
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem mod_mod (a b : Ordinal) : a % b % b = a % b :=
  mod_mod_of_dvd a dvd_rfl
/-
**Ordinal.lt_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_mul_iff {a b c : Ordinal} : a < b * c ↔ exists q < c, exists r < b, a =
 b * q + r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_mul_iff_div_lt`：lt_mul_iff_div_lt {a b c : Ordinal} (ha : a !
= 0) : c < a * b ↔ c / a < b
· 使用定理 `Ordinal.mod_lt`：mod_lt (a) {b : Ordinal} (h : b != 0) : a % b < b
· 使用定理 `Ordinal.div_add_mod`：div_add_mod (a b : Ordinal) : b * (a / b) + a % b =
 a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.add_one_le_iff`：add_one_le_iff [NoMaxOrder α] : x + 1 <= y ↔ x < y
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem lt_mul_iff {a b c : Ordinal} : a < b * c ↔ ∃ q < c, ∃ r < b, a = b * q + r := by
  obtain rfl | hb₀ := eq_or_ne b 0; · simp
  refine ⟨fun h ↦ ⟨_, (lt_mul_iff_div_lt hb₀).1 h, _, mod_lt a hb₀, (div_add_mod ..).symm⟩, ?_⟩
  rintro ⟨q, hq, r, hr, rfl⟩
  grw [hr, ← mul_add_one, add_one_le_iff.2 hq]
/-
**Ordinal.forall_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：forall_lt_mul {b c : Ordinal} {P : Ordinal -> Prop} : (forall a < b * c, P
 a) ↔ forall q < c, forall r < b, P (b * q + r)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_lt_mul {b c : Ordinal} {P : Ordinal → Prop} :
    (∀ a < b * c, P a) ↔ ∀ q < c, ∀ r < b, P (b * q + r) := by
  grind [lt_mul_iff]
/-
**Ordinal.exists_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：exists_lt_mul {b c : Ordinal} {P : Ordinal -> Prop} : (exists a < b * c, P
 a) ↔ exists q < c, exists r < b, P (b * q + r)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_lt_mul {b c : Ordinal} {P : Ordinal → Prop} :
    (∃ a < b * c, P a) ↔ ∃ q < c, ∃ r < b, P (b * q + r) := by
  grind [lt_mul_iff]

/-! ### Casting naturals into ordinals, compatibility with operations -/

/-
**Ordinal.instCharZero** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：instCharZero : CharZero Ordinal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Cardinal.ord_inj`：ord_inj {c₁ c₂} : ord c₁ = ord c₂ ↔ c₁ = c₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_natCast`：ord_natCast (n : Nat) : ord n = n

--- 原说明 ---
### Casting naturals into ordinals, compatibility with operations
-/
instance instCharZero : CharZero Ordinal := by
  refine ⟨fun a b h ↦ ?_⟩
  rwa [← Cardinal.ord_natCast, ← Cardinal.ord_natCast, Cardinal.ord_inj, Nat.cast_inj] at h

@[deprecated Nat.cast_add_one_comm (since := "2026-05-10")]
/-
**Ordinal.one_add_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_add_natCast (m : Nat) : 1 + (m : Ordinal) = succ m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add_one_comm`：cast_add_one_comm (n : Nat) : (n : α) + 1 = 1 + n
-/
theorem one_add_natCast (m : ℕ) : 1 + (m : Ordinal) = succ m :=
  m.cast_add_one_comm.symm

@[deprecated Nat.cast_add_one_comm (since := "2026-05-10")]
/-
**Ordinal.one_add_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_add_ofNat (m : Nat) [m.AtLeastTwo] : 1 + (ofNat(m) : Ordinal) = Order.
succ (OfNat.ofNat m : Ordinal)
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add_one_comm`：cast_add_one_comm (n : Nat) : (n : α) + 1 = 1 + n
-/
theorem one_add_ofNat (m : ℕ) [m.AtLeastTwo] :
    1 + (ofNat(m) : Ordinal) = Order.succ (OfNat.ofNat m : Ordinal) :=
  m.cast_add_one_comm.symm

@[simp, norm_cast]
/-
**Ordinal.natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ (m n : ℕ), ↑(m * n) = ↑m * ↑n
参数：m n : ℕ；m * n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_mul (m : ℕ) : ∀ n : ℕ, ((m * n : ℕ) : Ordinal) = m * n
  | 0 => by simp
  | n + 1 => by rw [Nat.mul_succ, Nat.cast_add, natCast_mul m n, Nat.cast_succ, mul_add_one]

@[simp, norm_cast]
/-
**Ordinal.natCast_sub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_sub (m n : Nat) : ((m - n : Nat) : Ordinal) = m - n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `Ordinal.sub_eq_zero_iff_le`：∀ {a b : Ordinal.{u_4}}, a - b = 0 ↔ a ≤ b
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_left_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 {a b c : G}, a + b = a + c ↔ b = c
· 使用定理 `Ordinal.instIsLeftCancelAdd`：IsLeftCancelAdd Ordinal.{u_4}
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
-/
theorem natCast_sub (m n : ℕ) : ((m - n : ℕ) : Ordinal) = m - n := by
  rcases le_total m n with h | h
  · rw [tsub_eq_zero_iff_le.2 h, Ordinal.sub_eq_zero_iff_le.2 (Nat.cast_le.2 h), Nat.cast_zero]
  · rw [← add_left_cancel_iff (a := ↑n), ← Nat.cast_add, add_tsub_cancel_of_le h,
      Ordinal.add_sub_cancel_of_le (Nat.cast_le.2 h)]

@[simp, norm_cast]
/-
**Ordinal.natCast_div** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_div (m n : Nat) : ((m / n : Nat) : Ordinal) = m / n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Ordinal.div_zero`：div_zero (a : Ordinal) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.mul_le_iff_le_div`：mul_le_iff_le_div {a b c : Ordinal} (ha : a !
= 0) : a * b <= c ↔ b <= c / a
· 使用定理 `Ordinal.natCast_mul`：∀ (m n : ℕ), ↑(m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.div_mul_le_self`：∀ (m n : ℕ), m / n * n ≤ m
· 使用定理 `Ordinal.div_le`：div_le {a b c : Ordinal} (b0 : b != 0) : a / b <= c ↔ a 
< b * succ c
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `Nat.div_lt_iff_lt_mul`：∀ {k x y : ℕ}, 0 < k → (x / k < y ↔ x < y * k)
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem natCast_div (m n : ℕ) : ((m / n : ℕ) : Ordinal) = m / n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  · have hn' : (n : Ordinal) ≠ 0 := Nat.cast_ne_zero.2 hn
    apply le_antisymm
    · rw [← mul_le_iff_le_div hn', ← natCast_mul, Nat.cast_le, mul_comm]
      apply Nat.div_mul_le_self
    · rw [div_le hn', succ_eq_add_one, ← Nat.cast_succ, ← natCast_mul, Nat.cast_lt, mul_comm,
        ← Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hn)]
      apply Nat.lt_succ_self

@[simp, norm_cast]
/-
**Ordinal.natCast_mod** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_mod (m n : Nat) : ((m % n : Nat) : Ordinal) = m % n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_left_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 {a b c : G}, a + b = a + c ↔ b = c
· 使用定理 `Ordinal.instIsLeftCancelAdd`：IsLeftCancelAdd Ordinal.{u_4}
· 使用定理 `Ordinal.div_add_mod`：div_add_mod (a b : Ordinal) : b * (a / b) + a % b =
 a
· 使用定理 `Ordinal.natCast_div`：natCast_div (m n : Nat) : ((m / n : Nat) : Ordinal)
 = m / n
· 使用定理 `Ordinal.natCast_mul`：∀ (m n : ℕ), ↑(m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.div_add_mod`：∀ (m n : ℕ), n * (m / n) + m % n = m
-/
theorem natCast_mod (m n : ℕ) : ((m % n : ℕ) : Ordinal) = m % n := by
  rw [← add_left_cancel_iff, div_add_mod, ← natCast_div, ← natCast_mul, ← Nat.cast_add,
    Nat.div_add_mod]

@[simp]
/-
**Ordinal.lift_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_natCast : ∀ n : ℕ, lift.{u, v} n = n
  | 0 => by simp
  | n + 1 => by simp [lift_natCast n]

@[simp]
/-
**Ordinal.lift_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_ofNat (n : Nat) [n.AtLeastTwo] : lift.{u, v} ofNat(n) = OfNat.ofNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_natCast`：∀ (n : ℕ), Ordinal.lift.{u, v} ↑n = ↑n
-/
theorem lift_ofNat (n : ℕ) [n.AtLeastTwo] :
    lift.{u, v} ofNat(n) = OfNat.ofNat n :=
  lift_natCast n

@[simp]
/-
**Ordinal.typein_lt_nat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_lt_nat (x : Nat) : typein LT.lt x = x
参数：x : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_Iio_lt`：type_Iio_lt [LinearOrder α] [WellFoundedLT α] (x : 
α) : type (α
· 使用定理 `Ordinal.type_fintype`：type_fintype [IsWellOrder α r] [Fintype α] : type 
r = Fintype.card α
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem typein_lt_nat (x : ℕ) : typein LT.lt x = x := by
  have : Fintype <| Iio x := Nat.fintypeIio x
  rw [← type_Iio_lt, type_fintype, Nat.cast_inj]
  nth_rw 2 [← Fintype.card_fin x]
  exact Fintype.card_congr Fin.equivSubtype.symm

@[simp]
/-
**Ordinal.typein_lt_fin** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_lt_fin {n : Nat} (x : Fin n) : typein LT.lt x = x
参数：x : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.Lt.isWellOrder`：∀ (n : ℕ), IsWellOrder (Fin n) fun x1 x2 => x1 < x2
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_Iio_lt`：type_Iio_lt [LinearOrder α] [WellFoundedLT α] (x : 
α) : type (α
· 使用定理 `Ordinal.type_fintype`：type_fintype [IsWellOrder α r] [Fintype α] : type 
r = Fintype.card α
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Fintype.card_fin_lt_of_le`：Fintype.card_fin_lt_of_le {m n : Nat} (h : m 
<= n) : Fintype.card {i : Fin n // i < m} = m
· 使用定理 `Fin.is_le'`：∀ {n : ℕ} {a : Fin n}, ↑a ≤ n
-/
theorem typein_lt_fin {n : ℕ} (x : Fin n) : typein LT.lt x = x := by
  rw [← type_Iio_lt, type_fintype, Nat.cast_inj]
  exact Fintype.card_fin_lt_of_le x.is_le'

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Ordinal.enum_lt_fin** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enum_lt_fin {n : Nat} (x : Fin n) : enum LT.lt ⟨x, by simp⟩ = x
参数：x : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.Lt.isWellOrder`：∀ (n : ℕ), IsWellOrder (Fin n) fun x1 x2 => x1 < x2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.typein_inj`：typein_inj (r : α -> α -> Prop) [IsWellOrder α r] {a
 b} : typein r a = typein r b ↔ a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
· 使用定理 `Ordinal.typein_lt_fin`：typein_lt_fin {n : Nat} (x : Fin n) : typein LT.l
t x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem enum_lt_fin {n : ℕ} (x : Fin n) : enum LT.lt ⟨x, by simp⟩ = x := by
  simp [← typein_inj LT.lt]

/-! ### Properties of `ω` -/

/-
**Ordinal.lt_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Properties of `ω`
-/
theorem lt_omega0 {o : Ordinal} : o < ω ↔ ∃ n : ℕ, o = n := by
  simp_rw [← Cardinal.ord_aleph0, Cardinal.lt_ord, lt_aleph0, card_eq_nat]

@[simp]
/-
**Ordinal.natCast_lt_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_lt_omega0 (n : Nat) : ↑n < ω
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
-/
theorem natCast_lt_omega0 (n : ℕ) : ↑n < ω :=
  lt_omega0.2 ⟨_, rfl⟩

@[deprecated (since := "2026-03-08")] alias nat_lt_omega0 := natCast_lt_omega0

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Ordinal.enum_lt_nat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enum_lt_nat (x : Nat) : enum LT.lt ⟨x, by simp⟩ = x
参数：x : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.typein_inj`：typein_inj (r : α -> α -> Prop) [IsWellOrder α r] {a
 b} : typein r a = typein r b ↔ a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
· 使用定理 `Ordinal.typein_lt_nat`：typein_lt_nat (x : Nat) : typein LT.lt x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem enum_lt_nat (x : ℕ) : enum LT.lt ⟨x, by simp⟩ = x := by
  simp [← typein_inj LT.lt]
/-
**Ordinal.eq_natCast_of_le_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：eq_natCast_of_le_natCast {a : Ordinal} {b : Nat} (h : a <= b) : exists c :
 Nat, a = c
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
-/
theorem eq_natCast_of_le_natCast {a : Ordinal} {b : ℕ} (h : a ≤ b) : ∃ c : ℕ, a = c :=
  lt_omega0.1 (h.trans_lt (natCast_lt_omega0 b))
/-
**Ordinal.eq_natCast_or_omega0_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：eq_natCast_or_omega0_le (o : Ordinal) : (exists n : Nat, o = n) ∨ ω <= o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
-/
theorem eq_natCast_or_omega0_le (o : Ordinal) : (∃ n : ℕ, o = n) ∨ ω ≤ o := by
  obtain ho | ho := lt_or_ge o ω
  · exact Or.inl <| lt_omega0.1 ho
  · exact Or.inr ho

@[deprecated (since := "2026-03-12")] alias eq_nat_or_omega0_le := eq_natCast_or_omega0_le

@[simp]
/-
**Ordinal.natCast_image_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_image_Iio (n : Nat) : Nat.cast '' Set.Iio n = Set.Iio (n : Ordinal
)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ordinal.eq_natCast_of_le_natCast`：eq_natCast_of_le_natCast {a : Ordinal}
 {b : Nat} (h : a <= b) : exists c : Nat, a = c
-/
theorem natCast_image_Iio (n : ℕ) : Nat.cast '' Set.Iio n = Set.Iio (n : Ordinal) := by
  ext o
  have := @eq_natCast_of_le_natCast o
  grind [Nat.cast_lt]

@[simp]
/-
**Ordinal.omega0_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega0_pos : 0 < ω
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
-/
theorem omega0_pos : 0 < ω :=
  natCast_lt_omega0 0

@[simp]
/-
**Ordinal.omega0_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega0_ne_zero : ω != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ordinal.omega0_pos`：omega0_pos : 0 < ω
-/
theorem omega0_ne_zero : ω ≠ 0 :=
  omega0_pos.ne'

@[simp]
/-
**Ordinal.one_lt_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_lt_omega0 : 1 < ω
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
-/
theorem one_lt_omega0 : 1 < ω := by simpa only [Nat.cast_one] using natCast_lt_omega0 1

@[simp]
/-
**Ordinal.isSuccLimit_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_omega0 : IsSuccLimit ω
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.isSuccLimit_iff`：isSuccLimit_iff {o : Ordinal} : IsSuccLimit o ↔
 o != 0 ∧ IsSuccPrelimit o
· 使用定理 `Order.isSuccPrelimit_iff_succ_lt`：isSuccPrelimit_iff_succ_lt : IsSuccPre
limit b ↔ forall a < b, succ a < b
· 使用定理 `Ordinal.omega0_ne_zero`：omega0_ne_zero : ω != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isSuccLimit_omega0 : IsSuccLimit ω := by
  rw [isSuccLimit_iff, isSuccPrelimit_iff_succ_lt]
  refine ⟨omega0_ne_zero, fun o h => ?_⟩
  obtain ⟨n, rfl⟩ := lt_omega0.1 h
  exact natCast_lt_omega0 (n + 1)
/-
**Ordinal.omega0_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega0_le {o : Ordinal} : ω <= o ↔ forall n : Nat, ↑n <= o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem omega0_le {o : Ordinal} : ω ≤ o ↔ ∀ n : ℕ, ↑n ≤ o :=
  ⟨fun h n => (natCast_lt_omega0 _).le.trans h, fun H =>
    le_of_forall_lt fun a h => by
      let ⟨n, e⟩ := lt_omega0.1 h
      rw [e, ← succ_le_iff]; exact H (n + 1)⟩
/-
**Ordinal.omega0_le_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega0_le_of_isSuccLimit {o} (h : IsSuccLimit o) : ω <= o
参数：h : IsSuccLimit o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.omega0_le`：omega0_le {o : Ordinal} : ω <= o ↔ forall n : Nat, ↑n
 <= o
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.natCast_lt_of_isSuccLimit`：natCast_lt_of_isSuccLimit {o : Ordina
l} (h : IsSuccLimit o) (n : Nat) : n < o
-/
theorem omega0_le_of_isSuccLimit {o} (h : IsSuccLimit o) : ω ≤ o :=
  omega0_le.2 fun n => le_of_lt <| natCast_lt_of_isSuccLimit h n
/-
**Ordinal.natCast_add_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_add_omega0 (n : Nat) : n + ω = ω
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_add_iff`：lt_add_iff {a b c : Ordinal} (hc : c != 0) : a < b +
 c ↔ exists d < c, a <= b + d
· 使用定理 `Ordinal.omega0_ne_zero`：omega0_ne_zero : ω != 0
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
-/
theorem natCast_add_omega0 (n : ℕ) : n + ω = ω := by
  refine le_antisymm (le_of_forall_lt fun a ha ↦ ?_) le_add_self
  obtain ⟨b, hb', hb⟩ := (lt_add_iff omega0_ne_zero).1 ha
  obtain ⟨m, rfl⟩ := lt_omega0.1 hb'
  apply hb.trans_lt
  exact_mod_cast natCast_lt_omega0 (n + m)
/-
**Ordinal.one_add_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_add_omega0 : 1 + ω = ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.natCast_add_omega0`：natCast_add_omega0 (n : Nat) : n + ω = ω
-/
theorem one_add_omega0 : 1 + ω = ω :=
  mod_cast natCast_add_omega0 1
/-
**Ordinal.add_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_omega0 {a : Ordinal} (h : a < ω) : a + ω = ω
参数：h : a < ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
· 使用定理 `Ordinal.natCast_add_omega0`：natCast_add_omega0 (n : Nat) : n + ω = ω
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem add_omega0 {a : Ordinal} (h : a < ω) : a + ω = ω := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 h
  exact natCast_add_omega0 n

@[simp]
/-
**Ordinal.natCast_add_of_omega0_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_add_of_omega0_le {o} (h : ω <= o) (n : Nat) : n + o = o
参数：h : ω <= o；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Ordinal.natCast_add_omega0`：natCast_add_omega0 (n : Nat) : n + ω = ω
-/
theorem natCast_add_of_omega0_le {o} (h : ω ≤ o) (n : ℕ) : n + o = o := by
  rw [← Ordinal.add_sub_cancel_of_le h, ← add_assoc, natCast_add_omega0]

@[simp]
/-
**Ordinal.one_add_of_omega0_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_add_of_omega0_le {o} (h : ω <= o) : 1 + o = o
参数：h : ω <= o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.natCast_add_of_omega0_le`：natCast_add_of_omega0_le {o} (h : ω <=
 o) (n : Nat) : n + o = o
-/
theorem one_add_of_omega0_le {o} (h : ω ≤ o) : 1 + o = o :=
  mod_cast natCast_add_of_omega0_le h 1

open Ordinal
/-
**Ordinal.isSuccPrelimit_iff_omega0_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccPrelimit_iff_omega0_dvd {a : Ordinal} : IsSuccPrelimit a ↔ ω ∣ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.IsSuccPrelimit.le_iff_forall_le`：∀ {α : Type u_1} {a b : α} [inst 
: LinearOrder α], Order.IsSuccPrelimit a → (a ≤ b ↔ ∀ c < a, c ≤ b)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lt_mul_iff_div_lt`：lt_mul_iff_div_lt {a b c : Ordinal} (ha : a !
= 0) : c < a * b ↔ c / a < b
· 使用定理 `Ordinal.omega0_ne_zero`：omega0_ne_zero : ω != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.mul_le_iff_le_div`：mul_le_iff_le_div {a b c : Ordinal} (ha : a !
= 0) : a * b <= c ↔ b <= c / a
· 使用定理 `Ordinal.mul_succ`：mul_succ (a b : Ordinal) : a * succ b = a * b + a
· 使用定理 `Ordinal.add_le_iff_of_isSuccLimit`：add_le_iff_of_isSuccLimit {a b c : Or
dinal} (hb : IsSuccLimit b) : a + b <= c ↔ forall d < b, a + d <= c
· 使用定理 `Ordinal.isSuccLimit_omega0`：isSuccLimit_omega0 : IsSuccLimit ω
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Ordinal.mul_div_le`：mul_div_le (a b : Ordinal) : b * (a / b) <= a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.lt_sub`：lt_sub {a b c : Ordinal} : a < b - c ↔ c + a < b
· 使用定理 `Ordinal.natCast_lt_of_isSuccLimit`：natCast_lt_of_isSuccLimit {o : Ordina
l} (h : IsSuccLimit o) (n : Nat) : n < o
· 使用定理 `Ordinal.isSuccLimit_sub`：isSuccLimit_sub {a b : Ordinal} (ha : IsSuccPre
limit a) (h : b < a) : IsSuccLimit (a - b)
· 使用定理 `Ordinal.isSuccPrelimit_mul_left`：isSuccPrelimit_mul_left {a b : Ordinal}
 (ha : IsSuccLimit a) : IsSuccPrelimit (a * b)
-/
theorem isSuccPrelimit_iff_omega0_dvd {a : Ordinal} : IsSuccPrelimit a ↔ ω ∣ a := by
  refine ⟨fun l => ⟨a / ω, le_antisymm ?_ (mul_div_le _ _)⟩, fun h => ?_⟩
  · refine l.le_iff_forall_le.2 fun x hx => le_of_lt ?_
    rw [lt_mul_iff_div_lt omega0_ne_zero, ← succ_le_iff, ← mul_le_iff_le_div omega0_ne_zero,
      mul_succ, add_le_iff_of_isSuccLimit isSuccLimit_omega0]
    intro b hb
    rcases lt_omega0.1 hb with ⟨n, rfl⟩
    grw [mul_div_le]
    exact (lt_sub.1 <| natCast_lt_of_isSuccLimit (isSuccLimit_sub l hx) _).le
  · rcases h with ⟨a0, b, rfl⟩
    exact isSuccPrelimit_mul_left isSuccLimit_omega0

@[deprecated isSuccPrelimit_iff_omega0_dvd (since := "2026-02-01")]
/-
**Ordinal.isSuccLimit_iff_omega0_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_iff_omega0_dvd {a : Ordinal} : IsSuccLimit a ↔ a != 0 ∧ ω ∣ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.isSuccLimit_iff`：isSuccLimit_iff {o : Ordinal} : IsSuccLimit o ↔
 o != 0 ∧ IsSuccPrelimit o
· 使用定理 `Ordinal.isSuccPrelimit_iff_omega0_dvd`：isSuccPrelimit_iff_omega0_dvd {a 
: Ordinal} : IsSuccPrelimit a ↔ ω ∣ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSuccLimit_iff_omega0_dvd {a : Ordinal} : IsSuccLimit a ↔ a ≠ 0 ∧ ω ∣ a := by
  rw [isSuccLimit_iff, isSuccPrelimit_iff_omega0_dvd]

@[simp]
/-
**Ordinal.natCast_mod_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_mod_omega0 (n : Nat) : n % ω = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.mod_eq_of_lt`：mod_eq_of_lt {a b : Ordinal} (h : a < b) : a % b =
 a
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
-/
theorem natCast_mod_omega0 (n : ℕ) : n % ω = n :=
  mod_eq_of_lt (natCast_lt_omega0 n)

end Ordinal

namespace Cardinal

open Ordinal

@[simp]
/-
**Cardinal.add_one_of_aleph0_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_one_of_aleph0_le {c} (h : ℵ₀ <= c) : c + 1 = c
参数：h : ℵ₀ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Ordinal.card_one`：card_one : card 1 = 1
· 使用定理 `Ordinal.card_add`：card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ 
+ card o₂
· 使用定理 `Ordinal.one_add_of_omega0_le`：one_add_of_omega0_le {o} (h : ω <= o) : 1 
+ o = o
· 使用定理 `Cardinal.ord_aleph0`：ord_aleph0 : ord.{u} ℵ₀ = ω
· 使用定理 `Cardinal.ord_le_ord`：ord_le_ord {c₁ c₂} : ord c₁ <= ord c₂ ↔ c₁ <= c₂
-/
theorem add_one_of_aleph0_le {c} (h : ℵ₀ ≤ c) : c + 1 = c := by
  rw [add_comm, ← card_ord c, ← card_one, ← card_add, one_add_of_omega0_le]
  rwa [← ord_aleph0, ord_le_ord]
/-
**Cardinal.isSuccLimit_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLimit (ord c)
参数：hc : ℵ₀ <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.aleph0_pos`：aleph0_pos : 0 < ℵ₀
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Ordinal.card_add_one`：card_add_one (o : Ordinal) : card (o + 1) = card o
 + 1
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Cardinal.add_one_of_aleph0_le`：add_one_of_aleph0_le {c} (h : ℵ₀ <= c) : 
c + 1 = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_le`：ord_le {c o} : ord c <= o ↔ c <= o.card
· 使用定理 `Order.IsSuccLimit.le_succ_iff`：∀ {α : Type u_1} {a b : α} [inst : Linear
Order α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → (b ≤ Order.succ a ↔ b ≤
 a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Cardinal.ord_aleph0`：ord_aleph0 : ord.{u} ℵ₀ = ω
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem isSuccLimit_ord {c} (hc : ℵ₀ ≤ c) : IsSuccLimit (ord c) := by
  constructor
  · simpa using (aleph0_pos.trans_le hc).ne'
  · simp_rw [isSuccPrelimit_iff_succ_lt, succ_eq_add_one, lt_ord, card_add_one]
    refine fun a ha ↦ ?_
    contrapose! ha
    rwa [add_one_of_aleph0_le] at ha
    rw [← ord_le, ← IsSuccLimit.le_succ_iff, succ_eq_add_one, ord_le, card_add_one]
    · exact hc.trans ha
    · simp

-- TODO: deprecate in favor of `isSuccPrelimit_type_lt_iff`
/-
**Cardinal.noMaxOrder** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：noMaxOrder {c} (h : ℵ₀ <= c) : NoMaxOrder c.ord.ToType
参数：h : ℵ₀ <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.isSuccPrelimit_type_lt_iff`：isSuccPrelimit_type_lt_iff [LinearOr
der α] [WellFoundedLT α] : IsSuccPrelimit (typeLT α) ↔ NoMaxOrder α
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `Cardinal.isSuccLimit_ord`：isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLim
it (ord c)
-/
theorem noMaxOrder {c} (h : ℵ₀ ≤ c) : NoMaxOrder c.ord.ToType := by
  rw [← isSuccPrelimit_type_lt_iff, type_toType]
  exact (isSuccLimit_ord h).isSuccPrelimit
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (ℵ₀ : Cardinal.{u}).ord.ToType := by simp

/-- This can be made a local instance in order to get `⊥`
in `Cardinal.aleph0.ord.ToType`. -/
/-
**Cardinal.orderBotAleph0OrdToType** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cardinal`。
形式化陈述：orderBotAleph0OrdToType : OrderBot Cardinal.aleph0.{u}.ord.ToType
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.instNonemptyToTypeOrdAleph0`：Nonempty Cardinal.aleph0.ord.ToTyp
e

--- 原说明 ---
This can be made a local instance in order to get `⊥`
in `Cardinal.aleph0.ord.ToType`.
-/
abbrev orderBotAleph0OrdToType : OrderBot Cardinal.aleph0.{u}.ord.ToType :=
  WellFoundedLT.toOrderBot _

end Cardinal

