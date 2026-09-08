/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.SetTheory.Ordinal.Family

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.AList

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`Ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`.

## Implementation notes

We implement `Ordinal.CNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.

## Todo

- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/

public noncomputable section

universe u

open List

namespace Ordinal.CNF

/-! ### Cantor normal form as a list -/

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_elim]
/-
**Ordinal.CNF.rec** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal.CNF`。
形式化陈述：(b : Ordinal.{u_2}) →   {C : Ordinal.{u_2} → Sort u_1} →     C 0 → ((o : O
rdinal.{u_2}) → o ≠ 0 → C (o % b ^ Ordinal.log b o) → C o) → (o : Ordinal.{u_2})
 → C o
参数：o : Ordinal.{u_2}；o % b ^ Ordinal.log b o。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inducts on the base `b` expansion of an ordinal.
-/
protected def rec (b : Ordinal) {C : Ordinal → Sort*} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) (o : Ordinal) : C o :=
  if h : o = 0 then h ▸ H0 else H o h (CNF.rec b H0 H (o % b ^ log b o))
termination_by o
decreasing_by exact mod_opow_log_lt_self b h

@[simp]
/-
**Ordinal.CNF.rec_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：rec_zero {C : Ordinal -> Sort*} (b : Ordinal) (H0 : C 0) (H : forall o, o 
!= 0 -> C (o % b ^ log b o) -> C o) : CNF.rec b H0 H 0 = H0
参数：b : Ordinal；H0 : C 0；H : forall o, o != 0 -> C (o % b ^ log b o) -> C o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.CantorNormalForm.0.Ordinal.CNF.rec.eq
_1`：∀ (b : Ordinal.{u_2}) {C : Ordinal.{u_2} → Sort u_1} (H0 : C 0)   (H : (o : 
Ordinal.{u_2}) → o ≠ 0 → C (o % b ^ Ordinal.log b o) → C o) (o :…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem rec_zero {C : Ordinal → Sort*} (b : Ordinal) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : CNF.rec b H0 H 0 = H0 := by
  rw [CNF.rec, dif_pos rfl]
/-
**Ordinal.CNF.rec_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：rec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal -> Sort*} (ho : o != 0) (
H0 : C 0) (H : forall o, o != 0 -> C (o % b ^ log b o) -> C o) : CNF.rec b H0 H 
o = H o ho (@CNF.rec b C H0 H _)
参数：b : Ordinal；ho : o != 0；H0 : C 0；H : forall o, o != 0 -> C (o % b ^ log b o) 
-> C o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.CantorNormalForm.0.Ordinal.CNF.rec.eq
_1`：∀ (b : Ordinal.{u_2}) {C : Ordinal.{u_2} → Sort u_1} (H0 : C 0)   (H : (o : 
Ordinal.{u_2}) → o ≠ 0 → C (o % b ^ Ordinal.log b o) → C o) (o :…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem rec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal → Sort*} (ho : o ≠ 0) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) :
    CNF.rec b H0 H o = H o ho (@CNF.rec b C H0 H _) := by
  rw [CNF.rec, dif_neg]

/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
@[pp_nodot]
/-
**Ordinal.CNF._root_.Ordinal.CNF** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal.CNF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cantor normal form of an ordinal `o` is the list of coefficients and exponen
ts in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]`
-/
def _root_.Ordinal.CNF (b o : Ordinal) : List (Ordinal × Ordinal) :=
  CNF.rec b [] (fun o _ IH ↦ (log b o, o / b ^ log b o)::IH) o

@[simp]
/-
**Ordinal.CNF.zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：zero_right (b : Ordinal) : CNF b 0 = []
参数：b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.CNF.rec_zero`：rec_zero {C : Ordinal -> Sort*} (b : Ordinal) (H0 
: C 0) (H : forall o, o != 0 -> C (o % b ^ log b o) -> C o) : CNF.rec b H0 H 0 =
 H0
-/
theorem zero_right (b : Ordinal) : CNF b 0 = [] :=
  rec_zero b _ _

/-- Recursive definition for the Cantor normal form. -/
/-
**Ordinal.CNF.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：∀ {b o : Ordinal.{u_1}},   o ≠ 0 → Ordinal.CNF b o = (Ordinal.log b o, o /
 b ^ Ordinal.log b o) :: Ordinal.CNF b (o % b ^ Ordinal.log b o)
参数：Ordinal.log b o, o / b ^ Ordinal.log b o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.CNF.rec_pos`：rec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal ->
 Sort*} (ho : o != 0) (H0 : C 0) (H : forall o, o != 0 -> C (o % b ^ log b o) ->
 C o) : C…

--- 原说明 ---
Recursive definition for the Cantor normal form.
-/
protected theorem ne_zero {b o : Ordinal} (ho : o ≠ 0) :
    CNF b o = (log b o, o / b ^ log b o)::CNF b (o % b ^ log b o) :=
  rec_pos b ho _ _
/-
**Ordinal.CNF.opow_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：∀ {b e x y : Ordinal.{u_1}},   1 < b → x ≠ 0 → x < b → y < b ^ e → Ordinal
.CNF b (b ^ e * x + y) = (e, x) :: Ordinal.CNF b y
参数：b ^ e * x + y；e, x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.CNF.ne_zero`：∀ {b o : Ordinal.{u_1}},   o ≠ 0 → Ordinal.CNF b o 
= (Ordinal.log b o, o / b ^ Ordinal.log b o) :: Ordinal.CNF b (o % b ^ Ordinal.l
og b o)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ordinal.log_opow_mul_add`：log_opow_mul_add {b u v w : Ordinal} (hb : 1 <
 b) (hv : v != 0) (hw : w < b ^ u) : log b (b ^ u * v + w) = u + log b v
· 使用定理 `Ordinal.log_eq_zero`：log_eq_zero {b o : Ordinal} (hbo : o < b) : log b o
 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.mul_add_div`：mul_add_div (a) {b : Ordinal} (b0 : b != 0) (c) : (
b * a + c) / b = a + c / b
· 使用定理 `Ordinal.opow_ne_zero`：opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a !
= 0) : a ^ b != 0
· 使用定理 `Ordinal.div_eq_zero_of_lt`：div_eq_zero_of_lt {a b : Ordinal} (h : a < b)
 : a / b = 0
· 使用定理 `Ordinal.mul_add_mod_self`：mul_add_mod_self (x y z : Ordinal) : (x * y + 
z) % x = z % x
· 使用定理 `Ordinal.mod_eq_of_lt`：mod_eq_of_lt {a b : Ordinal} (h : a < b) : a % b =
 a
-/
protected theorem opow_mul_add {b e x y : Ordinal}
    (hb : 1 < b) (hx : x ≠ 0) (hxb : x < b) (hy : y < b ^ e) :
    CNF b (b ^ e * x + y) = (e, x) :: CNF b y := by
  have hb' := hb.ne_bot
  rw [CNF.ne_zero]
  · rw [log_opow_mul_add hb hx hy, log_eq_zero hxb, add_zero,
      mul_add_div _ (opow_ne_zero _ hb'), Ordinal.div_eq_zero_of_lt hy, add_zero,
      mul_add_mod_self, mod_eq_of_lt hy]
  · simp_all
/-
**Ordinal.CNF.zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：∀ {o : Ordinal.{u_1}}, o ≠ 0 → Ordinal.CNF 0 o = [(0, o)]
参数：0, o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.CNF.ne_zero`：∀ {b o : Ordinal.{u_1}},   o ≠ 0 → Ordinal.CNF b o 
= (Ordinal.log b o, o / b ^ Ordinal.log b o) :: Ordinal.CNF b (o % b ^ Ordinal.l
og b o)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Ordinal.div_one`：div_one (a : Ordinal) : a / 1 = a
· 使用定理 `Ordinal.mod_one`：mod_one (a : Ordinal) : a % 1 = 0
· 使用定理 `Ordinal.CNF.zero_right`：zero_right (b : Ordinal) : CNF b 0 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem zero_left {o : Ordinal} (ho : o ≠ 0) : CNF 0 o = [(0, o)] := by
  simp [CNF.ne_zero ho]
/-
**Ordinal.CNF.one_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：∀ {o : Ordinal.{u_1}}, o ≠ 0 → Ordinal.CNF 1 o = [(0, o)]
参数：0, o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.CNF.ne_zero`：∀ {b o : Ordinal.{u_1}},   o ≠ 0 → Ordinal.CNF b o 
= (Ordinal.log b o, o / b ^ Ordinal.log b o) :: Ordinal.CNF b (o % b ^ Ordinal.l
og b o)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Ordinal.div_one`：div_one (a : Ordinal) : a / 1 = a
· 使用定理 `Ordinal.mod_one`：mod_one (a : Ordinal) : a % 1 = 0
· 使用定理 `Ordinal.CNF.zero_right`：zero_right (b : Ordinal) : CNF b 0 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem one_left {o : Ordinal} (ho : o ≠ 0) : CNF 1 o = [(0, o)] := by
  simp [CNF.ne_zero ho]
/-
**Ordinal.CNF.of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：∀ {b o : Ordinal.{u_1}}, b ≤ 1 → o ≠ 0 → Ordinal.CNF b o = [(0, o)]
参数：0, o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.le_one_iff`：le_one_iff : x <= 1 ↔ x = 0 ∨ x = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.CNF.zero_left`：∀ {o : Ordinal.{u_1}}, o ≠ 0 → Ordinal.CNF 0 o = 
[(0, o)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.CNF.one_left`：∀ {o : Ordinal.{u_1}}, o ≠ 0 → Ordinal.CNF 1 o = [
(0, o)]
-/
protected theorem of_le_one {b o : Ordinal} (hb : b ≤ 1) (ho : o ≠ 0) : CNF b o = [(0, o)] := by
  rcases Order.le_one_iff.1 hb with (rfl | rfl)
  exacts [CNF.zero_left ho, CNF.one_left ho]
/-
**Ordinal.CNF.of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：∀ {b o : Ordinal.{u_1}}, o ≠ 0 → o < b → Ordinal.CNF b o = [(0, o)]
参数：0, o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.CNF.ne_zero`：∀ {b o : Ordinal.{u_1}},   o ≠ 0 → Ordinal.CNF b o 
= (Ordinal.log b o, o / b ^ Ordinal.log b o) :: Ordinal.CNF b (o % b ^ Ordinal.l
og b o)
· 使用定理 `Ordinal.log_eq_zero`：log_eq_zero {b o : Ordinal} (hbo : o < b) : log b o
 = 0
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Ordinal.div_one`：div_one (a : Ordinal) : a / 1 = a
· 使用定理 `Ordinal.mod_one`：mod_one (a : Ordinal) : a % 1 = 0
· 使用定理 `Ordinal.CNF.zero_right`：zero_right (b : Ordinal) : CNF b 0 = []
-/
protected theorem of_lt {b o : Ordinal} (ho : o ≠ 0) (hb : o < b) : CNF b o = [(0, o)] := by
  rw [CNF.ne_zero ho, log_eq_zero hb, opow_zero, div_one, mod_one, zero_right]

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
/-
**Ordinal.CNF.foldr** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：∀ (b o : Ordinal.{u_1}), List.foldr (fun p r => b ^ p.1 * p.2 + r) 0 (Ordi
nal.CNF b o) = o
参数：b o : Ordinal.{u_1}；fun p r => b ^ p.1 * p.2 + r；Ordinal.CNF b o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.CNF.zero_right`：zero_right (b : Ordinal) : CNF b 0 = []
· 使用定理 `List.foldr_nil`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1 → α_1} {b
 : α_1}, List.foldr f b [] = b
· 使用定理 `Ordinal.CNF.ne_zero`：∀ {b o : Ordinal.{u_1}},   o ≠ 0 → Ordinal.CNF b o 
= (Ordinal.log b o, o / b ^ Ordinal.log b o) :: Ordinal.CNF b (o % b ^ Ordinal.l
og b o)
· 使用定理 `List.foldr_cons`：∀ {α : Type u} {β : Type v} {a : α} {l : List α} {f : α
 → β → β} {b : β},   List.foldr f b (a :: l) = f a (List.foldr f b l)
· 使用定理 `Ordinal.div_add_mod`：div_add_mod (a b : Ordinal) : b * (a / b) + a % b =
 a

--- 原说明 ---
Evaluating the Cantor normal form of an ordinal returns the ordinal.
-/
protected theorem foldr (b o : Ordinal) : (CNF b o).foldr (fun p r ↦ b ^ p.1 * p.2 + r) 0 = o := by
  refine CNF.rec b ?_ ?_ o
  · rw [zero_right, foldr_nil]
  · intro o ho IH
    rw [CNF.ne_zero ho, foldr_cons, IH, div_add_mod]

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
/-
**Ordinal.CNF.fst_le_log** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x in CNF b o -> x
.1 <= log b o
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.CNF.zero_right`：zero_right (b : Ordinal) : CNF b 0 = []
· 使用定理 `Ordinal.log_zero_right`：log_zero_right (b : Ordinal) : log b 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Ordinal.CNF.ne_zero`：∀ {b o : Ordinal.{u_1}},   o ≠ 0 → Ordinal.CNF b o 
= (Ordinal.log b o, o / b ^ Ordinal.log b o) :: Ordinal.CNF b (o % b ^ Ordinal.l
og b o)
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.log_mono_right`：log_mono_right (b : Ordinal) {x y : Ordinal} (xy
 : x <= y) : log b x <= log b y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.mod_opow_log_lt_self`：mod_opow_log_lt_self (b : Ordinal) {o : Or
dinal} (ho : o != 0) : o % (b ^ log b o) < o

--- 原说明 ---
Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`
.
-/
theorem fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ CNF b o → x.1 ≤ log b o := by
  refine CNF.rec b ?_ (fun o ho H ↦ ?_) o
  · simp
  · rw [CNF.ne_zero ho, mem_cons]
    rintro (rfl | h)
    · rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)

/-- Every coefficient in a Cantor normal form is positive. -/
/-
**Ordinal.CNF.snd_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：snd_pos {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x in CNF b o -> 0 < 
x.2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.CNF.zero_right`：zero_right (b : Ordinal) : CNF b 0 = []
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Ordinal.CNF.ne_zero`：∀ {b o : Ordinal.{u_1}},   o ≠ 0 → Ordinal.CNF b o 
= (Ordinal.log b o, o / b ^ Ordinal.log b o) :: Ordinal.CNF b (o % b ^ Ordinal.l
og b o)
· 使用定理 `Ordinal.div_opow_log_pos`：div_opow_log_pos (b : Ordinal) {o : Ordinal} (
ho : o != 0) : 0 < o / b ^ log b o
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
Every coefficient in a Cantor normal form is positive.
-/
theorem snd_pos {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ CNF b o → 0 < x.2 := by
  refine CNF.rec b (by simp) (fun o ho IH ↦ ?_) o
  rw [CNF.ne_zero ho]
  rintro (h | ⟨_, h⟩)
  · exact div_opow_log_pos b ho
  · exact IH h

@[deprecated (since := "2026-01-11")]
alias lt_snd := snd_pos

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
/-
**Ordinal.CNF.snd_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：snd_lt {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal} : x in CNF
 b o -> x.2 < b
参数：hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.CNF.zero_right`：zero_right (b : Ordinal) : CNF b 0 = []
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Ordinal.CNF.ne_zero`：∀ {b o : Ordinal.{u_1}},   o ≠ 0 → Ordinal.CNF b o 
= (Ordinal.log b o, o / b ^ Ordinal.log b o) :: Ordinal.CNF b (o % b ^ Ordinal.l
og b o)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `Ordinal.div_opow_log_lt`：div_opow_log_lt {b : Ordinal} (o : Ordinal) (hb
 : 1 < b) : o / b ^ log b o < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Every coefficient in the Cantor normal form `CNF b o` is less than `b`.
-/
theorem snd_lt {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal} :
    x ∈ CNF b o → x.2 < b := by
  refine CNF.rec b ?_ (fun o ho IH ↦ ?_) o
  · simp
  · rw [CNF.ne_zero ho]
    intro h
    obtain rfl | h := mem_cons.mp h
    · exact div_opow_log_lt o hb
    · exact IH h

/-- The exponents of the Cantor normal form are decreasing. -/
/-
**Ordinal.CNF.sortedGT** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：∀ (b o : Ordinal.{u_1}), (List.map Prod.fst (Ordinal.CNF b o)).SortedGT
参数：b o : Ordinal.{u_1}；List.map Prod.fst (Ordinal.CNF b o)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.CNF.zero_right`：zero_right (b : Ordinal) : CNF b 0 = []
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Ordinal.CNF.of_le_one`：∀ {b o : Ordinal.{u_1}}, b ≤ 1 → o ≠ 0 → Ordinal.
CNF b o = [(0, o)]
· 使用定理 `List.pairwise_singleton`：∀ {α : Type u_1} (R : α → α → Prop) (a : α), Li
st.Pairwise R [a]
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Ordinal.CNF.of_lt`：∀ {b o : Ordinal.{u_1}}, o ≠ 0 → o < b → Ordinal.CNF 
b o = [(0, o)]
· 使用定理 `Ordinal.CNF.ne_zero`：∀ {b o : Ordinal.{u_1}},   o ≠ 0 → Ordinal.CNF b o 
= (Ordinal.log b o, o / b ^ Ordinal.log b o) :: Ordinal.CNF b (o % b ^ Ordinal.l
og b o)
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ordinal.CNF.fst_le_log`：fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Or
dinal} : x in CNF b o -> x.1 <= log b o
· 使用定理 `Ordinal.log_mod_opow_log_lt_log_self`：log_mod_opow_log_lt_log_self {b o 
: Ordinal} (hb : 1 < b) (hbo : b <= o) : log b (o % (b ^ log b o)) < log b o

--- 原说明 ---
The exponents of the Cantor normal form are decreasing.
-/
protected theorem sortedGT (b o : Ordinal) : ((CNF b o).map Prod.fst).SortedGT := by
  simp_rw [sortedGT_iff_pairwise]
  refine CNF.rec b ?_ (fun o ho IH ↦ ?_) o
  · rw [zero_right]
    exact .nil
  · rcases le_or_gt b 1 with hb | hb
    · rw [CNF.of_le_one hb ho]
      exact pairwise_singleton _ _
    · obtain hob | hbo := lt_or_ge o b
      · rw [CNF.of_lt ho hob]
        exact pairwise_singleton _ _
      · rw [CNF.ne_zero ho, map_cons, pairwise_cons]
        refine ⟨fun a H ↦ ?_, IH⟩
        rw [mem_map] at H
        rcases H with ⟨⟨a, a'⟩, H, rfl⟩
        exact (fst_le_log H).trans_lt (log_mod_opow_log_lt_log_self hb hbo)

@[deprecated (since := "2026-01-11")]
alias sorted := CNF.sortedGT
/-
**Ordinal.CNF.nodupKeys** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem nodupKeys (b o : Ordinal) : (map Prod.toSigma (CNF b o)).NodupKeys := by
  rw [NodupKeys, List.keys, map_map, Prod.fst_comp_toSigma]
  exact (CNF.sortedGT ..).nodup

/-! ### Cantor normal form as a finsupp -/

open AList Finsupp

/-- `CNF.coeff b o` is the finitely supported function returning the coefficient of `b ^ e` in the
Cantor Normal Form (`CNF`) of `o`, for each `e`. -/
@[pp_nodot]
/-
**Ordinal.CNF.coeff** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff (b o : Ordinal) : Ordinal ->₀ Ordinal
参数：b o : Ordinal。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.CantorNormalForm.0.Ordinal.CNF.nodupK
eys`：∀ (b o : Ordinal.{u_1}), (List.map Prod.toSigma (Ordinal.CNF b o)).NodupKey
s

--- 原说明 ---
`CNF.coeff b o` is the finitely supported function returning the coefficient of 
`b ^ e` in the
Cantor Normal Form (`CNF`) of `o`, for each `e`.
-/
def coeff (b o : Ordinal) : Ordinal →₀ Ordinal :=
  lookupFinsupp ⟨_, nodupKeys b o⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Ordinal.CNF.support_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：support_coeff (b o : Ordinal) : (coeff b o).support = ((CNF b o).map Prod.
fst).toFinset
参数：b o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.CantorNormalForm.0.Ordinal.CNF.nodupK
eys`：∀ (b o : Ordinal.{u_1}), (List.map Prod.toSigma (Ordinal.CNF b o)).NodupKey
s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.CantorNormalForm.0.Ordinal.CNF.coeff.
eq_1`：∀ (b o : Ordinal.{u_1}),   Ordinal.CNF.coeff b o = { entries := List.map P
rod.toSigma (Ordinal.CNF b o), nodupKeys := ⋯ }.lookupFinsupp
· 使用定理 `AList.lookupFinsupp_support`：lookupFinsupp_support [DecidableEq α] [Deci
dableEq M] (l : AList fun _x : α => M) : l.lookupFinsupp.support = (l.1.filter f
un x => Sigma.snd…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.filter_eq_self`：∀ {α : Type u_1} {p : α → Bool} {l : List α}, List.
filter p l = l ↔ ∀ a ∈ l, p a = true
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ordinal.CNF.snd_pos`：snd_pos {b o : Ordinal.{u}} {x : Ordinal × Ordinal}
 : x in CNF b o -> 0 < x.2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem support_coeff (b o : Ordinal) :
    (coeff b o).support = ((CNF b o).map Prod.fst).toFinset := by
  rw [coeff, lookupFinsupp_support, filter_eq_self.2]
  · simp [List.keys]
  · simp_rw [mem_map]
    rintro _ ⟨a, ⟨ha, rfl⟩⟩
    simpa using (snd_pos ha).ne'
/-
**Ordinal.CNF.coeff_of_mem_CNF** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff_of_mem_CNF {b o e c : Ordinal} (h : ⟨e, c⟩ in CNF b o) : coeff b o e
 = c
参数：h : ⟨e, c⟩ in CNF b o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.CantorNormalForm.0.Ordinal.CNF.nodupK
eys`：∀ (b o : Ordinal.{u_1}), (List.map Prod.toSigma (Ordinal.CNF b o)).NodupKey
s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.CantorNormalForm.0.Ordinal.CNF.coeff.
eq_1`：∀ (b o : Ordinal.{u_1}),   Ordinal.CNF.coeff b o = { entries := List.map P
rod.toSigma (Ordinal.CNF b o), nodupKeys := ⋯ }.lookupFinsupp
· 使用定理 `AList.lookupFinsupp_apply`：lookupFinsupp_apply [DecidableEq α] (l : ALis
t fun _x : α => M) (a : α) : l.lookupFinsupp a = (l.lookup a).getD 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AList.mem_lookup_iff`：mem_lookup_iff {a : α} {b : β a} {s : AList β} : b
 in lookup a s ↔ Sigma.mk a b in s.entries
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `Option.getD_some`：∀ {α : Type u_1} {a b : α}, (some a).getD b = a
-/
theorem coeff_of_mem_CNF {b o e c : Ordinal} (h : ⟨e, c⟩ ∈ CNF b o) :
    coeff b o e = c := by
  rw [coeff, lookupFinsupp_apply, mem_lookup_iff.2, Option.getD_some]
  simpa
/-
**Ordinal.CNF.coeff_of_notMem_CNF** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff_of_notMem_CNF {b o e : Ordinal} (h : e ∉ (CNF b o).map Prod.fst) : c
oeff b o e = 0
参数：h : e ∉ (CNF b o).map Prod.fst。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `Ordinal.CNF.support_coeff`：support_coeff (b o : Ordinal) : (coeff b o).s
upport = ((CNF b o).map Prod.fst).toFinset
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
-/
theorem coeff_of_notMem_CNF {b o e : Ordinal} (h : e ∉ (CNF b o).map Prod.fst) :
    coeff b o e = 0 := by
  rwa [← notMem_support_iff, support_coeff, mem_toFinset]

@[deprecated (since := "2026-01-11")]
alias coeff_of_not_mem_CNF := coeff_of_notMem_CNF
/-
**Ordinal.CNF.coeff_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff_eq_zero_of_lt {b o e : Ordinal} (h : o < b ^ e) : coeff b o e = 0
参数：h : o < b ^ e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.CNF.coeff_of_notMem_CNF`：coeff_of_notMem_CNF {b o e : Ordinal} (
h : e ∉ (CNF b o).map Prod.fst) : coeff b o e = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.CNF.zero_right`：zero_right (b : Ordinal) : CNF b 0 = []
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Ordinal.opow_le_of_le_log`：opow_le_of_le_log {b x c : Ordinal} (hc : c !
= 0) (h : c <= log b x) : b ^ c <= x
· 使用定理 `Ordinal.CNF.fst_le_log`：fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Or
dinal} : x in CNF b o -> x.1 <= log b o
-/
theorem coeff_eq_zero_of_lt {b o e : Ordinal} (h : o < b ^ e) : coeff b o e = 0 := by
  apply coeff_of_notMem_CNF
  intro he
  rw [mem_map] at he
  obtain ⟨⟨e, c⟩, he, rfl⟩ := he
  obtain rfl | he' := eq_or_ne e 0
  · simp_all
  · exact (opow_le_of_le_log he' (fst_le_log he)).not_gt h
/-
**Ordinal.CNF.coeff_zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff_zero_apply (b e : Ordinal) : coeff b 0 e = 0
参数：b e : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.CNF.coeff_of_notMem_CNF`：coeff_of_notMem_CNF {b o e : Ordinal} (
h : e ∉ (CNF b o).map Prod.fst) : coeff b o e = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.CNF.zero_right`：zero_right (b : Ordinal) : CNF b 0 = []
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem coeff_zero_apply (b e : Ordinal) : coeff b 0 e = 0 := by
  apply coeff_of_notMem_CNF
  simp

@[simp]
/-
**Ordinal.CNF.coeff_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff_zero_right (b : Ordinal) : coeff b 0 = 0
参数：b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Ordinal.CNF.coeff_zero_apply`：coeff_zero_apply (b e : Ordinal) : coeff b
 0 e = 0
-/
theorem coeff_zero_right (b : Ordinal) : coeff b 0 = 0 := by
  ext e
  exact coeff_zero_apply b e
/-
**Ordinal.CNF.coeff_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff_of_le_one {b : Ordinal} (hb : b <= 1) (o : Ordinal) : coeff b o = si
ngle 0 o
参数：hb : b <= 1；o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.CNF.coeff_zero_right`：coeff_zero_right (b : Ordinal) : coeff b 0
 = 0
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.CNF.coeff_of_mem_CNF`：coeff_of_mem_CNF {b o e c : Ordinal} (h : 
⟨e, c⟩ in CNF b o) : coeff b o e = c
· 使用定理 `Ordinal.CNF.of_le_one`：∀ {b o : Ordinal.{u_1}}, b ≤ 1 → o ≠ 0 → Ordinal.
CNF b o = [(0, o)]
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Ordinal.CNF.coeff_of_notMem_CNF`：coeff_of_notMem_CNF {b o e : Ordinal} (
h : e ∉ (CNF b o).map Prod.fst) : coeff b o e = 0
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
-/
theorem coeff_of_le_one {b : Ordinal} (hb : b ≤ 1) (o : Ordinal) : coeff b o = single 0 o := by
  ext a
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · obtain rfl | ha := eq_or_ne a 0
    · apply coeff_of_mem_CNF
      rw [CNF.of_le_one hb ho]
      simp
    · rw [single_eq_of_ne ha]
      apply coeff_of_notMem_CNF
      rw [CNF.of_le_one hb ho]
      simpa using ha

@[simp]
/-
**Ordinal.CNF.coeff_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff_zero_left (o : Ordinal) : coeff 0 o = single 0 o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.CNF.coeff_of_le_one`：coeff_of_le_one {b : Ordinal} (hb : b <= 1)
 (o : Ordinal) : coeff b o = single 0 o
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem coeff_zero_left (o : Ordinal) : coeff 0 o = single 0 o :=
  coeff_of_le_one zero_le_one o

@[simp]
/-
**Ordinal.CNF.coeff_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff_one_left (o : Ordinal) : coeff 1 o = single 0 o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.CNF.coeff_of_le_one`：coeff_of_le_one {b : Ordinal} (hb : b <= 1)
 (o : Ordinal) : coeff b o = single 0 o
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coeff_one_left (o : Ordinal) : coeff 1 o = single 0 o :=
  coeff_of_le_one le_rfl o
/-
**Ordinal.CNF.coeff_opow_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff_opow_mul_add {b e x y : Ordinal} (hb : 1 < b) (hx : x != 0) (hxb : x
 < b) (hy : y < b ^ e) : coeff b (b ^ e * x + y) = single e x + coeff b y
参数：hb : 1 < b；hx : x != 0；hxb : x < b；hy : y < b ^ e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.add_apply`：add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g
₁ a + g₂ a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Ordinal.CNF.coeff_eq_zero_of_lt`：coeff_eq_zero_of_lt {b o e : Ordinal} (
h : o < b ^ e) : coeff b o e = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.CNF.coeff_of_mem_CNF`：coeff_of_mem_CNF {b o e c : Ordinal} (h : 
⟨e, c⟩ in CNF b o) : coeff b o e = c
· 使用定理 `Ordinal.CNF.opow_mul_add`：∀ {b e x y : Ordinal.{u_1}},   1 < b → x ≠ 0 →
 x < b → y < b ^ e → Ordinal.CNF b (b ^ e * x + y) = (e, x) :: Ordinal.CNF b y
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `Ordinal.CNF.coeff_of_notMem_CNF`：coeff_of_notMem_CNF {b o e : Ordinal} (
h : e ∉ (CNF b o).map Prod.fst) : coeff b o e = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem coeff_opow_mul_add {b e x y : Ordinal}
    (hb : 1 < b) (hx : x ≠ 0) (hxb : x < b) (hy : y < b ^ e) :
    coeff b (b ^ e * x + y) = single e x + coeff b y := by
  ext e'
  rw [add_apply]
  obtain rfl | he := eq_or_ne e e'
  · rw [single_eq_same, coeff_eq_zero_of_lt hy, add_zero]
    apply coeff_of_mem_CNF
    rw [CNF.opow_mul_add hb hx hxb hy]
    exact mem_cons_self
  · rw [single_eq_of_ne' he, zero_add]
    by_cases h : e' ∈ (CNF b y).map Prod.fst
    · rw [mem_map] at h
      obtain ⟨⟨f, c⟩, hf, rfl⟩ := h
      rw [coeff_of_mem_CNF hf]
      apply coeff_of_mem_CNF
      rw [CNF.opow_mul_add hb hx hxb hy]
      exact mem_cons_of_mem _ hf
    · rw [coeff_of_notMem_CNF h, coeff_of_notMem_CNF]
      rw [mem_map] at h ⊢
      rw [CNF.opow_mul_add hb hx hxb hy]
      simp_all

/-! ### Evaluate a Cantor normal form -/

/-- `CNF.eval f` evaluates a Finsupp `f : Ordinal →₀ Ordinal`, interpreted as a
base `b` expansion on ordinals. -/
/-
**Ordinal.CNF.eval** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal.CNF`。
形式化陈述：eval (b : Ordinal) (f : Ordinal ->₀ Ordinal) : Ordinal
参数：b : Ordinal；f : Ordinal ->₀ Ordinal。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instAntisymmGe`：∀ {α : Type u} [inst : PartialOrder α], Std.Antisymm fun
 x1 x2 => x2 ≤ x1
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1

--- 原说明 ---
`CNF.eval f` evaluates a Finsupp `f : Ordinal →₀ Ordinal`, interpreted as a
base `b` expansion on ordinals.
-/
def eval (b : Ordinal) (f : Ordinal →₀ Ordinal) : Ordinal :=
  (f.support.sort (· ≥ ·)).foldr (fun p r ↦ b ^ p * f p + r) 0

@[simp]
/-
**Ordinal.CNF.eval_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：eval_zero_right (b : Ordinal) : eval b 0 = 0
参数：b : Ordinal。
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
· 使用定理 `instAntisymmGe`：∀ {α : Type u} [inst : PartialOrder α], Std.Antisymm fun
 x1 x2 => x2 ≤ x1
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sort.congr_simp`：∀ {α : Type u_1} (s s_1 : Finset α),   s = s_1 →
     ∀ (r r_1 : α → α → Prop) (e_r : r = r_1) {inst : DecidableRel r} [inst_1 : 
DecidableRel…
· 使用定理 `Finset.sort_empty`：sort_empty : sort ∅ r = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_zero_right (b : Ordinal) : eval b 0 = 0 := by
  simp [eval]

/-- For a slightly stronger version, see `eval_single_add`. -/
/-
**Ordinal.CNF.eval_single_add'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：eval_single_add' (b : Ordinal) {e x : Ordinal} {f : Ordinal ->₀ Ordinal} (
h : forall e' in f.support, e' < e) : eval b (.single e x + f) = b ^ e * x + eva
l b f
参数：b : Ordinal；h : forall e' in f.support, e' < e。
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
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `instAntisymmGe`：∀ {α : Type u} [inst : PartialOrder α], Std.Antisymm fun
 x1 x2 => x2 ≤ x1
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.CantorNormalForm.0.Ordinal.CNF.eval.e
q_1`：∀ (b : Ordinal.{u_1}) (f : Ordinal.{u_1} →₀ Ordinal.{u_1}),   Ordinal.CNF.e
val b f = List.foldr (fun p r => b ^ p * f p + r) 0 (f.support.so…
· 使用引理 `Finsupp.support_single_add`：support_single_add {a : ι} {b : M} {f : ι ->
₀ M} (ha : a ∉ f.support) (hb : b != 0) : support (single a b + f) = cons a f.su
pport ha
· 使用定理 `Finset.sort_cons`：sort_cons {a : α} (h₁ : forall b in s, r a b) (h₂ : a 
∉ s) : sort (cons a s h₂) r = a :: sort s r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finsupp.add_apply`：add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g
₁ a + g₂ a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.instIsLeftCancelAdd`：IsLeftCancelAdd Ordinal.{u_4}
· 使用定理 `List.foldr_ext`：foldr_ext (f g : α -> β -> β) (b : β) {l : List α} (H : 
forall a in l, forall b : β, f a b = g a b) : foldr f b l = foldr g b l
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Finset.sort.congr_simp`：∀ {α : Type u_1} (s s_1 : Finset α),   s = s_1 →
     ∀ (r r_1 : α → α → Prop) (e_r : r = r_1) {inst : DecidableRel r} [inst_1 : 
DecidableRel…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
For a slightly stronger version, see `eval_single_add`.
-/
theorem eval_single_add' (b : Ordinal) {e x : Ordinal} {f : Ordinal →₀ Ordinal}
    (h : ∀ e' ∈ f.support, e' < e) : eval b (.single e x + f) = b ^ e * x + eval b f := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  have hf : f e = 0 := by
    rw [← notMem_support_iff]
    exact fun he ↦ (h e he).false
  rw [eval, support_single_add (by simpa) hx, Finset.sort_cons]
  · simp only [add_apply, foldr_cons, single_eq_same, hf, add_zero, add_right_inj]
    apply foldr_ext
    intro e' he' _
    congr
    rw [single_eq_of_ne, zero_add]
    aesop
  · exact fun e' he' ↦ (h e' he').le

@[simp]
/-
**Ordinal.CNF.eval_single** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：eval_single (b e x : Ordinal) : eval b (.single e x) = b ^ e * x
参数：b e x : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.CNF.eval_zero_right`：eval_zero_right (b : Ordinal) : eval b 0 = 
0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Ordinal.CNF.eval_single_add'`：eval_single_add' (b : Ordinal) {e x : Ordi
nal} {f : Ordinal ->₀ Ordinal} (h : forall e' in f.support, e' < e) : eval b (.s
ingle e x + f) = b…
-/
theorem eval_single (b e x : Ordinal) : eval b (.single e x) = b ^ e * x := by
  simpa using eval_single_add' b (f := 0)
/-
**Ordinal.CNF.eval_single_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：eval_single_add (b : Ordinal) {e x : Ordinal} {f : Ordinal ->₀ Ordinal} (h
 : forall e' in f.support, e' <= e) : eval b (.single e x + f) = b ^ e * x + eva
l b f
参数：b : Ordinal；h : forall e' in f.support, e' <= e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction_on_max`：induction_on_max (f : ι ->₀ M) (zero : motive 
0) (single_add : forall a b (f : ι ->₀ M), (forall c in f.support, c < a) -> b !
= 0 -> motive …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.CNF.eval_single`：eval_single (b e x : Ordinal) : eval b (.single
 e x) = b ^ e * x
· 使用定理 `Ordinal.CNF.eval_zero_right`：eval_zero_right (b : Ordinal) : eval b 0 = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ordinal.CNF.eval_single_add'`：eval_single_add' (b : Ordinal) {e x : Ordi
nal} {f : Ordinal ->₀ Ordinal} (h : forall e' in f.support, e' < e) : eval b (.s
ingle e x + f) = b…
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem eval_single_add (b : Ordinal) {e x : Ordinal} {f : Ordinal →₀ Ordinal}
    (h : ∀ e' ∈ f.support, e' ≤ e) : eval b (.single e x + f) = b ^ e * x + eval b f := by
  cases f using Finsupp.induction_on_max with
  | zero => simp
  | single_add e' y f hf hy =>
    obtain rfl | he' := (h e' (by simp [hy])).eq_or_lt
    · simp only [← add_assoc, ← single_add, eval_single_add' _ hf, mul_add]
    · rw [eval_single_add']
      refine fun a ha ↦ (h a ha).lt_of_ne ?_
      rintro rfl
      apply (hf a _).not_gt he'
      simpa [he'.ne'] using ha
/-
**Ordinal.CNF.eval_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：eval_add (b : Ordinal) {f₁ f₂ : Ordinal ->₀ Ordinal} (h : forall e₁ in f₁.
support, forall e₂ in f₂.support, e₂ <= e₁) : eval b (f₁ + f₂) = eval b f₁ + eva
l b f₂
参数：b : Ordinal；h : forall e₁ in f₁.support, forall e₂ in f₂.support, e₂ <= e₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction_on_max`：induction_on_max (f : ι ->₀ M) (zero : motive 
0) (single_add : forall a b (f : ι ->₀ M), (forall c in f.support, c < a) -> b !
= 0 -> motive …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.CNF.eval_zero_right`：eval_zero_right (b : Ordinal) : eval b 0 = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Ordinal.CNF.eval_single_add`：eval_single_add (b : Ordinal) {e x : Ordina
l} {f : Ordinal ->₀ Ordinal} (h : forall e' in f.support, e' <= e) : eval b (.si
ngle e x + f) = b…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ordinal.CNF.eval_single_add'`：eval_single_add' (b : Ordinal) {e x : Ordi
nal} {f : Ordinal ->₀ Ordinal} (h : forall e' in f.support, e' < e) : eval b (.s
ingle e x + f) = b…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem eval_add (b : Ordinal) {f₁ f₂ : Ordinal →₀ Ordinal}
    (h : ∀ e₁ ∈ f₁.support, ∀ e₂ ∈ f₂.support, e₂ ≤ e₁) :
    eval b (f₁ + f₂) = eval b f₁ + eval b f₂ := by
  induction f₁ using Finsupp.induction_on_max with
  | zero => simp
  | single_add e₁ x f₁ hf₁ hx IH =>
    rw [add_assoc, eval_single_add, eval_single_add' _ hf₁, IH, add_assoc]
    · simp_all
    · intro e₂ he₂
      obtain he₂ | he₂ := Finset.mem_union.1 <| support_add he₂
      · exact (hf₁ _ he₂).le
      · apply h _ _ _ he₂
        simp_all
/-
**Ordinal.CNF.eval_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：eval_lt {b e : Ordinal} {f : Ordinal ->₀ Ordinal} (hb : forall e', f e' < 
b) (he : forall e' in f.support, e' < e) : eval b f < b ^ e
参数：hb : forall e', f e' < b；he : forall e' in f.support, e' < e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction_on_max`：induction_on_max (f : ι ->₀ M) (zero : motive 
0) (single_add : forall a b (f : ι ->₀ M), (forall c in f.support, c < a) -> b !
= 0 -> motive …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.CNF.eval_zero_right`：eval_zero_right (b : Ordinal) : eval b 0 = 
0
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Ordinal.CNF.eval_single_add'`：eval_single_add' (b : Ordinal) {e x : Ordi
nal} {f : Ordinal ->₀ Ordinal} (h : forall e' in f.support, e' < e) : eval b (.s
ingle e x + f) = b…
· 使用定理 `Ordinal.opow_mul_add_lt_opow`：opow_mul_add_lt_opow {b u v w x : Ordinal}
 (hv : v < b) (hw : w < b ^ u) (hu : u < x) : b ^ u * v + w < b ^ x
· 使用定理 `LT.lt.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LT α], b < a → b =
 c → c < a
· 使用引理 `Finsupp.add_apply`：add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g
₁ a + g₂ a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem eval_lt {b e : Ordinal} {f : Ordinal →₀ Ordinal}
    (hb : ∀ e', f e' < b) (he : ∀ e' ∈ f.support, e' < e) : eval b f < b ^ e := by
  induction f using Finsupp.induction_on_max generalizing e with
  | zero =>
    rw [eval_zero_right]
    exact opow_pos _ (hb 0)
  | single_add e' x f hf hx IH =>
    have he' : e' ∉ f.support := fun h ↦ (hf _ h).false
    rw [eval_single_add' _ hf]
    apply opow_mul_add_lt_opow _ (IH _ hf)
    · apply he e' _
      simp [hx]
    · apply (hb e').trans_eq'
      rw [add_apply, single_eq_same, notMem_support_iff.1, add_zero]
      exact fun h ↦ (hf _ h).false
    · intro a
      by_cases ha : a ∈ f.support
      · apply (hb a).trans_eq'
        rw [add_apply, single_eq_of_ne, zero_add]
        rintro rfl
        contradiction
      · rw [notMem_support_iff.1 ha]
        exact (hb 0).pos

@[simp]
/-
**Ordinal.CNF.eval_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：eval_coeff (b o : Ordinal) : eval b (coeff b o) = o
参数：b o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.CNF.foldr`：∀ (b o : Ordinal.{u_1}), List.foldr (fun p r => b ^ p
.1 * p.2 + r) 0 (Ordinal.CNF b o) = o
· 使用定理 `instAntisymmGe`：∀ {α : Type u} [inst : PartialOrder α], Std.Antisymm fun
 x1 x2 => x2 ≤ x1
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.CantorNormalForm.0.Ordinal.CNF.eval.e
q_1`：∀ (b : Ordinal.{u_1}) (f : Ordinal.{u_1} →₀ Ordinal.{u_1}),   Ordinal.CNF.e
val b f = List.foldr (fun p r => b ^ p * f p + r) 0 (f.support.so…
· 使用定理 `Ordinal.CNF.support_coeff`：support_coeff (b o : Ordinal) : (coeff b o).s
upport = ((CNF b o).map Prod.fst).toFinset
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.toFinset_sort`：∀ {α : Type u_1} (r : α → α → Prop) [inst : Decidabl
eRel r] [inst_1 : IsTrans α r] [inst_2 : Std.Antisymm r]   [inst_3 : Std.Total r
] [inst_…
· 使用定理 `List.SortedGT.nodup`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], 
l.SortedGT → l.Nodup
· 使用定理 `Ordinal.CNF.sortedGT`：∀ (b o : Ordinal.{u_1}), (List.map Prod.fst (Ordin
al.CNF b o)).SortedGT
· 使用定理 `List.SortedGE.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedGE → List.Pairwise (fun x1 x2 => x1 ≥ x2) l
· 使用定理 `List.SortedGT.sortedGE`：∀ {α : Type u_1} [inst : Preorder α] {l : List α
}, l.SortedGT → l.SortedGE
· 使用定理 `List.foldr_map`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} {f : α₁
 → α₂} {g : α₂ → β → β} {l : List α₁} {init : β},   List.foldr g init (List.map 
f l)…
· 使用定理 `List.foldr_ext`：foldr_ext (f g : α -> β -> β) (b : β) {l : List α} (H : 
forall a in l, forall b : β, f a b = g a b) : foldr f b l = foldr g b l
· 使用定理 `Ordinal.CNF.coeff_of_mem_CNF`：coeff_of_mem_CNF {b o e c : Ordinal} (h : 
⟨e, c⟩ in CNF b o) : coeff b o e = c
-/
theorem eval_coeff (b o : Ordinal) : eval b (coeff b o) = o := by
  conv_rhs => rw [← CNF.foldr b o]
  rw [eval, support_coeff, (toFinset_sort _ _).2, foldr_map]
  · apply foldr_ext
    intro a ha x
    rw [coeff_of_mem_CNF ha]
  · exact (CNF.sortedGT b o).sortedGE.pairwise
  · exact (CNF.sortedGT b o).nodup
/-
**Ordinal.CNF.coeff_eval** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff_eval {b : Ordinal} (hb : 1 < b) {f : Ordinal ->₀ Ordinal} (hf : fora
ll e, f e < b) : coeff b (eval b f) = f
参数：hb : 1 < b；hf : forall e, f e < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction_on_max`：induction_on_max (f : ι ->₀ M) (zero : motive 
0) (single_add : forall a b (f : ι ->₀ M), (forall c in f.support, c < a) -> b !
= 0 -> motive …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.CNF.eval_zero_right`：eval_zero_right (b : Ordinal) : eval b 0 = 
0
· 使用定理 `Ordinal.CNF.coeff_zero_right`：coeff_zero_right (b : Ordinal) : coeff b 0
 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LT α], b < a → b =
 c → c < a
· 使用引理 `Finsupp.add_apply`：add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g
₁ a + g₂ a
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.CNF.eval_single_add'`：eval_single_add' (b : Ordinal) {e x : Ordi
nal} {f : Ordinal ->₀ Ordinal} (h : forall e' in f.support, e' < e) : eval b (.s
ingle e x + f) = b…
· 使用定理 `Ordinal.CNF.coeff_opow_mul_add`：coeff_opow_mul_add {b e x y : Ordinal} (
hb : 1 < b) (hx : x != 0) (hxb : x < b) (hy : y < b ^ e) : coeff b (b ^ e * x + 
y) = single e x + co…
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.CNF.eval_lt`：eval_lt {b e : Ordinal} {f : Ordinal ->₀ Ordinal} (
hb : forall e', f e' < b) (he : forall e' in f.support, e' < e) : eval b f < b ^
 e
-/
theorem coeff_eval {b : Ordinal} (hb : 1 < b) {f : Ordinal →₀ Ordinal} (hf : ∀ e, f e < b) :
    coeff b (eval b f) = f := by
  induction f using Finsupp.induction_on_max with
  | zero => simp
  | single_add e x f hf' hx IH =>
    have IH' (e') : f e' < b := by
      by_cases he' : e' ∈ f.support
      · apply (hf e').trans_eq'
        rw [add_apply, single_eq_of_ne, zero_add]
        exact (hf' _ he').ne
      · rw [notMem_support_iff.1 he']
        exact hb.pos
    rw [eval_single_add' _ hf', coeff_opow_mul_add hb hx, IH IH']
    · apply (hf e).trans_eq'
      rw [add_apply, single_eq_same, notMem_support_iff.1, add_zero]
      exact fun h ↦ (hf' _ h).false
    · exact eval_lt IH' hf'
/-
**Ordinal.CNF.coeff_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff_injective (b : Ordinal) : Function.Injective (coeff b)
参数：b : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Ordinal.CNF.eval_coeff`：eval_coeff (b o : Ordinal) : eval b (coeff b o) 
= o
-/
theorem coeff_injective (b : Ordinal) : Function.Injective (coeff b) :=
  Function.LeftInverse.injective fun _ ↦ eval_coeff ..

@[simp]
/-
**Ordinal.CNF.coeff_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.CNF`。
形式化陈述：coeff_inj {b x y : Ordinal} : coeff b x = coeff b y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Ordinal.CNF.coeff_injective`：coeff_injective (b : Ordinal) : Function.In
jective (coeff b)
-/
theorem coeff_inj {b x y : Ordinal} : coeff b x = coeff b y ↔ x = y :=
  (coeff_injective b).eq_iff

end Ordinal.CNF

