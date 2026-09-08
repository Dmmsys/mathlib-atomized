/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Principal ordinals

If `op` is a binary operation on ordinals, we say that an ordinal `o` is `op`-principal (or
`op`-indecomposable) whenever `a < o` and `b < o` imply `op a b < o`. Most commonly, one talks of
additive and multiplicative principal ordinals.

Additive principal ordinals were originally called "gamma numbers" by Cantor, but this term now more
commonly refers to the values given by `Ordinal.gamma`. Likewise, multiplicative principal ordinals
are sometimes known as "delta numbers". Exponential principal ordinals are (barring edge cases)
equivalent to the epsilon numbers given by `Ordinal.epsilon`.

## Main definitions and results

* `IsPrincipal`: A principal (or indecomposable) ordinal under some binary operation. We include `0`
  and other typically excluded edge cases for simplicity.
* `not_bddAbove_setOfPred_isPrincipal`: Principal ordinals (under any operation) are unbounded.
* `isPrincipal_add_iff_zero_or_omega0_opow`: The additive principal ordinals are
  `0` and the ordinal powers of `ω`.
* `isPrincipal_mul_iff_le_two_or_omega0_opow_opow`: The multiplicative principal ordinals are
  `0`, `1`, `2`, and the ordinals `ω ^ ω ^ x`.

## TODO

* Prove that the exponential principal ordinals are `0`, `1`, `2`, `ω`, or `ε_ x`.

## Tags

additively indecomposable, multiplicatively indecomposable
-/

@[expose] public section

universe u

open Order

namespace Ordinal

variable {a b c o : Ordinal.{u}}

section Arbitrary

variable {op : Ordinal → Ordinal → Ordinal}

/-! ### Principal ordinals under an arbitrary operation -/

/-- An ordinal `o` is said to be principal (or indecomposable) under an operation when `Iio o` is
closed under that operation.

For simplicity, we break usual convention and regard `0` as principal. -/
/-
**Ordinal.IsPrincipal** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：IsPrincipal (op : Ordinal -> Ordinal -> Ordinal) (o : Ordinal) : Prop
参数：op : Ordinal -> Ordinal -> Ordinal；o : Ordinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordinal `o` is said to be principal (or indecomposable) under an operation wh
en `Iio o` is
closed under that operation.

For simplicity, we break usual convention and regard `0` as principal.
-/
def IsPrincipal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o

@[deprecated (since := "2026-03-17")]
alias Principal := IsPrincipal
/-
**Ordinal.isPrincipal_swap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_swap_iff : IsPrincipal (Function.swap op) o ↔ IsPrincipal op o
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isPrincipal_swap_iff : IsPrincipal (Function.swap op) o ↔ IsPrincipal op o := by
  constructor <;> exact fun h a b ha hb => h hb ha

@[deprecated (since := "2026-03-17")]
alias principal_swap_iff := isPrincipal_swap_iff
/-
**Ordinal.not_isPrincipal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：not_isPrincipal_iff : ¬ IsPrincipal op o ↔ exists a < o, exists b < o, o <
= op a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_isPrincipal_iff : ¬ IsPrincipal op o ↔ ∃ a < o, ∃ b < o, o ≤ op a b := by
  simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias not_principal_iff := not_isPrincipal_iff
/-
**Ordinal.isPrincipal_iff_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_iff_of_monotone (h₁ : forall a, Monotone (op a)) (h₂ : forall 
a, Monotone (Function.swap op a)) : IsPrincipal op o ↔ forall a < o, op a a < o
参数：h₁ : forall a, Monotone (op a)；h₂ : forall a, Monotone (Function.swap op a)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem isPrincipal_iff_of_monotone
    (h₁ : ∀ a, Monotone (op a)) (h₂ : ∀ a, Monotone (Function.swap op a)) :
    IsPrincipal op o ↔ ∀ a < o, op a a < o := by
  use fun h a ha => h ha ha
  intro H a b ha hb
  obtain hab | hba := le_or_gt a b
  · exact (h₂ b hab).trans_lt <| H b hb
  · exact (h₁ a hba.le).trans_lt <| H a ha

@[deprecated (since := "2026-03-17")]
alias principal_iff_of_monotone := isPrincipal_iff_of_monotone
/-
**Ordinal.not_isPrincipal_iff_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：not_isPrincipal_iff_of_monotone (h₁ : forall a, Monotone (op a)) (h₂ : for
all a, Monotone (Function.swap op a)) : ¬ IsPrincipal op o ↔ exists a < o, o <= 
op a a
参数：h₁ : forall a, Monotone (op a)；h₂ : forall a, Monotone (Function.swap op a)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.isPrincipal_iff_of_monotone`：isPrincipal_iff_of_monotone (h₁ : f
orall a, Monotone (op a)) (h₂ : forall a, Monotone (Function.swap op a)) : IsPri
ncipal op o ↔ forall a < …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_isPrincipal_iff_of_monotone
    (h₁ : ∀ a, Monotone (op a)) (h₂ : ∀ a, Monotone (Function.swap op a)) :
    ¬ IsPrincipal op o ↔ ∃ a < o, o ≤ op a a := by
  simp [isPrincipal_iff_of_monotone h₁ h₂]

@[deprecated (since := "2026-03-17")]
alias not_principal_iff_of_monotone := not_isPrincipal_iff_of_monotone
/-
**Ordinal.isPrincipal_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {op : Ordinal.{u_1} → Ordinal.{u_1} → Ordinal.{u_1}}, Ordinal.IsPrincipa
l op 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma isPrincipal_zero : IsPrincipal op 0 := by simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias principal_zero := isPrincipal_zero
/-
**Ordinal.isPrincipal_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {op : Ordinal.{u_1} → Ordinal.{u_1} → Ordinal.{u_1}}, Ordinal.IsPrincipa
l op 1 ↔ op 0 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem isPrincipal_one_iff : IsPrincipal op 1 ↔ op 0 0 = 0 := by simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias principal_one_iff := isPrincipal_one_iff
/-
**Ordinal.IsPrincipal.iterate_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsPrincipal`
。
形式化陈述：∀ {a o : Ordinal.{u}} {op : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}},   a 
< o → Ordinal.IsPrincipal op o → ∀ (n : ℕ), (op a)^[n] a < o
参数：n : ℕ；op a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_zero`：iterate_zero : f^[0] = id
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
-/
theorem IsPrincipal.iterate_lt (hao : a < o) (ho : IsPrincipal op o) (n : ℕ) :
    (op a)^[n] a < o := by
  induction n with
  | zero => rwa [Function.iterate_zero]
  | succ n hn =>
    rw [Function.iterate_succ']
    exact ho hao hn

@[deprecated (since := "2026-03-17")]
alias Principal.iterate_lt := IsPrincipal.iterate_lt
/-
**Ordinal.op_eq_self_of_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：op_eq_self_of_isPrincipal (hao : a < o) (H : IsNormal (op a)) (ho : IsPrin
cipal op o) (ho' : IsSuccLimit o) : op a o = o
参数：hao : a < o；H : IsNormal (op a)；ho : IsPrincipal op o；ho' : IsSuccLimit o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.IsNormal.apply_of_isSuccLimit`：apply_of_isSuccLimit (hf : IsNormal
 f) (ha : IsSuccLimit a) : f a = ⨆ b : Iio a, f b
· 使用定理 `Ordinal.iSup_le_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], ⨆ i, f i ≤ a ↔ ∀ (i : ι), f i ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem op_eq_self_of_isPrincipal (hao : a < o) (H : IsNormal (op a))
    (ho : IsPrincipal op o) (ho' : IsSuccLimit o) : op a o = o := by
  apply H.strictMono.le_apply.antisymm'
  rw [H.apply_of_isSuccLimit ho', Ordinal.iSup_le_iff]
  exact fun ⟨b, hbo⟩ ↦ (ho hao hbo).le

@[deprecated (since := "2026-03-17")]
alias op_eq_self_of_principal := op_eq_self_of_isPrincipal
/-
**Ordinal.nfp_le_of_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_le_of_isPrincipal (hao : a < o) (ho : IsPrincipal op o) : nfp (op a) a
 <= o
参数：hao : a < o；ho : IsPrincipal op o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.nfp_le`：nfp_le {a b} : (forall n, f^[n] a <= b) -> nfp f a <= b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.IsPrincipal.iterate_lt`：∀ {a o : Ordinal.{u}} {op : Ordinal.{u} 
→ Ordinal.{u} → Ordinal.{u}},   a < o → Ordinal.IsPrincipal op o → ∀ (n : ℕ), (o
p a)^[n] a < o
-/
theorem nfp_le_of_isPrincipal (hao : a < o) (ho : IsPrincipal op o) : nfp (op a) a ≤ o :=
  nfp_le fun n => (ho.iterate_lt hao n).le

@[deprecated (since := "2026-03-17")]
alias nfp_le_of_principal := nfp_le_of_isPrincipal
/-
**Ordinal.IsPrincipal.sSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsPrincipal`。
形式化陈述：∀ {op : Ordinal.{u_1} → Ordinal.{u_1} → Ordinal.{u_1}} {s : Set Ordinal.{u
_1}},   (∀ x ∈ s, Ordinal.IsPrincipal op x) → Ordinal.IsPrincipal op (sSup s)
参数：∀ x ∈ s, Ordinal.IsPrincipal op x；sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `lt_csSup_iff`：lt_csSup_iff (hb : BddAbove s) (hs : s.Nonempty) : a < sSu
p s ↔ exists b in s, a < b
· 使用定理 `max_rec'`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α} (p : α → Pro
p), p a → p b → p (max a b)
· 使用定理 `lt_max_of_lt_left`：lt_max_of_lt_left (h : a < b) : a < max b c
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
-/
protected theorem IsPrincipal.sSup {s : Set Ordinal} (H : ∀ x ∈ s, IsPrincipal op x) :
    IsPrincipal op (sSup s) := by
  have : IsPrincipal op (sSup ∅) := by simp
  by_cases hs : BddAbove s
  · obtain rfl | hs' := s.eq_empty_or_nonempty
    · assumption
    simp only [IsPrincipal, lt_csSup_iff hs hs', forall_exists_index, and_imp]
    intro x y a has ha b hbs hb
    have h : max a b ∈ s := max_rec' _ has hbs
    exact ⟨_, h, H (max a b) h (lt_max_of_lt_left ha) (lt_max_of_lt_right hb)⟩
  · rwa [csSup_of_not_bddAbove hs]

@[deprecated (since := "2026-03-17")]
protected alias Principal.sSup := IsPrincipal.sSup
/-
**Ordinal.IsPrincipal.iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsPrincipal`。
形式化陈述：∀ {op : Ordinal.{u_2} → Ordinal.{u_2} → Ordinal.{u_2}} {ι : Sort u_1} {f :
 ι → Ordinal.{u_2}},   (∀ (i : ι), Ordinal.IsPrincipal op (f i)) → Ordinal.IsPri
ncipal op (⨆ i, f i)
参数：∀ (i : ι), Ordinal.IsPrincipal op (f i)；⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.IsPrincipal.sSup`：∀ {op : Ordinal.{u_1} → Ordinal.{u_1} → Ordina
l.{u_1}} {s : Set Ordinal.{u_1}},   (∀ x ∈ s, Ordinal.IsPrincipal op x) → Ordina
l.IsPrincipal …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected theorem IsPrincipal.iSup {ι} {f : ι → Ordinal} (H : ∀ i, IsPrincipal op (f i)) :
    IsPrincipal op (⨆ i, f i) := IsPrincipal.sSup (by simpa)

@[deprecated (since := "2026-03-17")]
protected alias Principal.iSup := IsPrincipal.iSup

end Arbitrary

/-- We give an explicit construction for a principal ordinal larger or equal than `o`. -/
/-
**Ordinal.isPrincipal_nfp_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We give an explicit construction for a principal ordinal larger or equal than `o
`.
-/
private theorem isPrincipal_nfp_iSup (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) :
    IsPrincipal op (nfp (fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2)) o) := by
  intro a b ha hb
  rw [lt_nfp_iff] at *
  obtain ⟨m, ha⟩ := ha
  obtain ⟨n, hb⟩ := hb
  obtain h | h := le_total
    ((fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2))^[m] o)
    ((fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2))^[n] o)
  · use n + 1
    rw [Function.iterate_succ']
    apply (lt_succ _).trans_le
    exact Ordinal.le_iSup (fun y : Set.Iio _ ×ˢ Set.Iio _ ↦ succ (op y.1.1 y.1.2))
      ⟨_, Set.mk_mem_prod (ha.trans_le h) hb⟩
  · use m + 1
    rw [Function.iterate_succ']
    apply (lt_succ _).trans_le
    exact Ordinal.le_iSup (fun y : Set.Iio _ ×ˢ Set.Iio _ ↦ succ (op y.1.1 y.1.2))
      ⟨_, Set.mk_mem_prod ha (hb.trans_le h)⟩

/-- Principal ordinals under any operation are unbounded. -/
/-
**Ordinal.not_bddAbove_setOfPred_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`
。
形式化陈述：not_bddAbove_setOfPred_isPrincipal (op : Ordinal -> Ordinal -> Ordinal) : 
¬ BddAbove { o | IsPrincipal op o }
参数：op : Ordinal -> Ordinal -> Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.le_nfp`：le_nfp (f a) : a <= nfp f a
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Principal.0.Ordinal.isPrincipal_nfp_i
Sup`：∀ (op : Ordinal.{u_1} → Ordinal.{u_1} → Ordinal.{u_1}) (o : Ordinal.{u_1}),
   Ordinal.IsPrincipal op (Ordinal.nfp (fun x => ⨆ y, Order.succ …
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}

--- 原说明 ---
Principal ordinals under any operation are unbounded.
-/
theorem not_bddAbove_setOfPred_isPrincipal (op : Ordinal → Ordinal → Ordinal) :
    ¬ BddAbove { o | IsPrincipal op o } := by
  rintro ⟨a, ha⟩
  exact ((le_nfp _ _).trans (ha (isPrincipal_nfp_iSup op (succ a)))).not_gt (lt_succ a)

@[deprecated (since := "2026-07-09")]
alias not_bddAbove_setOf_isPrincipal := not_bddAbove_setOfPred_isPrincipal

@[deprecated (since := "2026-03-17")]
alias not_bddAbove_principal := not_bddAbove_setOfPred_isPrincipal

/-! ### Additive principal ordinals -/

/-
**Ordinal.isPrincipal_add_iff_add_self_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_add_iff_add_self_lt : IsPrincipal (· + ·) a ↔ forall b < a, b 
+ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.isPrincipal_iff_of_monotone`：isPrincipal_iff_of_monotone (h₁ : f
orall a, Monotone (op a)) (h₂ : forall a, Monotone (Function.swap op a)) : IsPri
ncipal op o ↔ forall a < …
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a

--- 原说明 ---
### Additive principal ordinals
-/
theorem isPrincipal_add_iff_add_self_lt : IsPrincipal (· + ·) a ↔ ∀ b < a, b + b < a :=
  isPrincipal_iff_of_monotone
    (fun x _ _ h ↦ add_le_add_right h x) (fun x _ _ h ↦ add_le_add_left h x)
/-
**Ordinal.IsPrincipal.mul_natCast_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsPrinci
pal`。
形式化陈述：∀ {a o : Ordinal.{u}}, Ordinal.IsPrincipal (fun x1 x2 => x1 + x2) o → a < 
o → ∀ (n : ℕ), a * ↑n < o
参数：fun x1 x2 => x1 + x2；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
-/
theorem IsPrincipal.mul_natCast_lt (ho : IsPrincipal (· + ·) o) (ha : a < o) (n : ℕ) :
    a * n < o := by
  induction n with
  | zero => simpa using ha.pos
  | succ n h =>
    rw [Nat.cast_add_one, mul_add_one]
    exact ho h ha
/-
**Ordinal.isPrincipal_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_add_one : IsPrincipal (· + ·) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isPrincipal_add_one : IsPrincipal (· + ·) 1 := by simp

@[deprecated (since := "2026-03-17")]
alias principal_add_one := isPrincipal_add_one
/-
**Ordinal.isPrincipal_add_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_add_of_le_one (ho : o <= 1) : IsPrincipal (· + ·) o
参数：ho : o <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.le_one_iff`：le_one_iff : x <= 1 ↔ x = 0 ∨ x = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.isPrincipal_zero`：∀ {op : Ordinal.{u_1} → Ordinal.{u_1} → Ordina
l.{u_1}}, Ordinal.IsPrincipal op 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.isPrincipal_add_one`：isPrincipal_add_one : IsPrincipal (· + ·) 1
-/
theorem isPrincipal_add_of_le_one (ho : o ≤ 1) : IsPrincipal (· + ·) o := by
  rcases le_one_iff.1 ho with (rfl | rfl)
  · exact isPrincipal_zero
  · exact isPrincipal_add_one

@[deprecated (since := "2026-03-17")]
alias principal_add_of_le_one := isPrincipal_add_of_le_one
/-
**Ordinal.isSuccLimit_of_isPrincipal_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_of_isPrincipal_add (ho₁ : 1 < o) (ho : IsPrincipal (· + ·) o) 
: IsSuccLimit o
参数：ho₁ : 1 < o；ho : IsPrincipal (· + ·) o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.isSuccLimit_iff`：isSuccLimit_iff {o : Ordinal} : IsSuccLimit o ↔
 o != 0 ∧ IsSuccPrelimit o
· 使用定理 `Order.isSuccPrelimit_iff_succ_lt`：isSuccPrelimit_iff_succ_lt : IsSuccPre
limit b ↔ forall a < b, succ a < b
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
-/
theorem isSuccLimit_of_isPrincipal_add (ho₁ : 1 < o) (ho : IsPrincipal (· + ·) o) :
    IsSuccLimit o := by
  rw [isSuccLimit_iff, isSuccPrelimit_iff_succ_lt]
  exact ⟨ho₁.ne_bot, fun _ ha ↦ ho ha ho₁⟩

@[deprecated (since := "2026-03-17")]
alias isSuccLimit_of_principal_add := isSuccLimit_of_isPrincipal_add
/-
**Ordinal.isPrincipal_add_iff_add_left_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordina
l`。
形式化陈述：isPrincipal_add_iff_add_left_eq_self : IsPrincipal (· + ·) o ↔ forall a < 
o, a + o = o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Ordinal.op_eq_self_of_isPrincipal`：op_eq_self_of_isPrincipal (hao : a < 
o) (H : IsNormal (op a)) (ho : IsPrincipal op o) (ho' : IsSuccLimit o) : op a o 
= o
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)
· 使用定理 `Ordinal.isSuccLimit_of_isPrincipal_add`：isSuccLimit_of_isPrincipal_add (
ho₁ : 1 < o) (ho : IsPrincipal (· + ·) o) : IsSuccLimit o
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.le_one_iff`：le_one_iff : x <= 1 ↔ x = 0 ∨ x = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
-/
theorem isPrincipal_add_iff_add_left_eq_self : IsPrincipal (· + ·) o ↔ ∀ a < o, a + o = o := by
  refine ⟨fun ho a hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases lt_or_ge 1 o with ho₁ | ho₁
    · exact op_eq_self_of_isPrincipal hao (isNormal_add_right a) ho
        (isSuccLimit_of_isPrincipal_add ho₁ ho)
    · cases le_one_iff.1 ho₁ <;> simp_all
  · rw [← h a hao]
    exact (isNormal_add_right a).strictMono hbo

@[deprecated (since := "2026-03-17")]
alias principal_add_iff_add_left_eq_self := isPrincipal_add_iff_add_left_eq_self
/-
**Ordinal.IsPrincipal.add_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsPrincipa
l`。
形式化陈述：∀ {a o : Ordinal.{u}}, Ordinal.IsPrincipal (fun x1 x2 => x1 + x2) o → a < 
o → a + o = o
参数：fun x1 x2 => x1 + x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.isPrincipal_add_iff_add_left_eq_self`：isPrincipal_add_iff_add_le
ft_eq_self : IsPrincipal (· + ·) o ↔ forall a < o, a + o = o
-/
theorem IsPrincipal.add_eq_right (ho : IsPrincipal (· + ·) o) (ha : a < o) : a + o = o :=
  isPrincipal_add_iff_add_left_eq_self.1 ho a ha
/-
**Ordinal.IsPrincipal.add_eq_right_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsPr
incipal`。
形式化陈述：∀ {a b c : Ordinal.{u}}, Ordinal.IsPrincipal (fun x1 x2 => x1 + x2) b → a 
< b → b ≤ c → a + c = c
参数：fun x1 x2 => x1 + x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Ordinal.IsPrincipal.add_eq_right`：∀ {a o : Ordinal.{u}}, Ordinal.IsPrinc
ipal (fun x1 x2 => x1 + x2) o → a < o → a + o = o
-/
theorem IsPrincipal.add_eq_right_of_le (hb : IsPrincipal (· + ·) b)
    (hab : a < b) (hbc : b ≤ c) : a + c = c := by
  rw [← Ordinal.add_sub_cancel_of_le hbc, ← add_assoc, hb.add_eq_right hab,
    Ordinal.add_sub_cancel_of_le hbc]
/-
**Ordinal.exists_lt_add_of_not_isPrincipal_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordina
l`。
形式化陈述：exists_lt_add_of_not_isPrincipal_add (ha : ¬ IsPrincipal (· + ·) a) : exis
ts b < a, exists c < a, b + c = a
参数：ha : ¬ IsPrincipal (· + ·) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.not_isPrincipal_iff`：not_isPrincipal_iff : ¬ IsPrincipal op o ↔ 
exists a < o, exists b < o, o <= op a b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ordinal.sub_le_self`：sub_le_self (a b : Ordinal) : a - b <= a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.sub_le`：sub_le {a b c : Ordinal} : a - b <= c ↔ a <= b + c
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem exists_lt_add_of_not_isPrincipal_add (ha : ¬ IsPrincipal (· + ·) a) :
    ∃ b < a, ∃ c < a, b + c = a := by
  rw [not_isPrincipal_iff] at ha
  rcases ha with ⟨b, hb, c, hc, H⟩
  refine
    ⟨b, hb, _, lt_of_le_of_ne (sub_le_self a b) fun hab => ?_, Ordinal.add_sub_cancel_of_le hb.le⟩
  rw [← sub_le, hab] at H
  exact H.not_gt hc

@[deprecated (since := "2026-03-17")]
alias exists_lt_add_of_not_principal_add := exists_lt_add_of_not_isPrincipal_add
/-
**Ordinal.isPrincipal_add_iff_add_lt_ne_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`
。
形式化陈述：isPrincipal_add_iff_add_lt_ne_self : IsPrincipal (· + ·) a ↔ forall b < a,
 forall c < a, b + c != a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ordinal.exists_lt_add_of_not_isPrincipal_add`：exists_lt_add_of_not_isPri
ncipal_add (ha : ¬ IsPrincipal (· + ·) a) : exists b < a, exists c < a, b + c = 
a
· 使用定理 `Ne.irrefl`：∀ {α : Sort u} {a : α}, a ≠ a → False
-/
theorem isPrincipal_add_iff_add_lt_ne_self : IsPrincipal (· + ·) a ↔ ∀ b < a, ∀ c < a, b + c ≠ a :=
  ⟨fun ha _ hb _ hc => (ha hb hc).ne, fun H => by
    by_contra ha
    rcases exists_lt_add_of_not_isPrincipal_add ha with ⟨b, hb, c, hc, rfl⟩
    exact (H b hb c hc).irrefl⟩

@[deprecated (since := "2026-03-17")]
alias principal_add_iff_add_lt_ne_self := isPrincipal_add_iff_add_lt_ne_self
/-
**Ordinal.isPrincipal_add_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_add_omega0 : IsPrincipal (· + ·) ω
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.isPrincipal_add_iff_add_left_eq_self`：isPrincipal_add_iff_add_le
ft_eq_self : IsPrincipal (· + ·) o ↔ forall a < o, a + o = o
· 使用定理 `Ordinal.add_omega0`：add_omega0 {a : Ordinal} (h : a < ω) : a + ω = ω
-/
theorem isPrincipal_add_omega0 : IsPrincipal (· + ·) ω :=
  isPrincipal_add_iff_add_left_eq_self.2 fun _ => add_omega0

@[deprecated (since := "2026-03-17")]
alias principal_add_omega0 := isPrincipal_add_omega0

-- `add_omega0` is proven in the Arithmetic file.
/-
**Ordinal.add_of_omega0_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_of_omega0_le : a < ω -> ω <= b -> a + b = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.IsPrincipal.add_eq_right_of_le`：∀ {a b c : Ordinal.{u}}, Ordinal
.IsPrincipal (fun x1 x2 => x1 + x2) b → a < b → b ≤ c → a + c = c
· 使用定理 `Ordinal.isPrincipal_add_omega0`：isPrincipal_add_omega0 : IsPrincipal (· 
+ ·) ω
-/
theorem add_of_omega0_le : a < ω → ω ≤ b → a + b = b :=
  isPrincipal_add_omega0.add_eq_right_of_le
/-
**Ordinal.isPrincipal_add_omega0_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_add_omega0_opow (o : Ordinal) : IsPrincipal (· + ·) (ω ^ o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Ordinal.isPrincipal_one_iff`：∀ {op : Ordinal.{u_1} → Ordinal.{u_1} → Ord
inal.{u_1}}, Ordinal.IsPrincipal op 1 ↔ op 0 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.isPrincipal_add_iff_add_self_lt`：isPrincipal_add_iff_add_self_lt
 : IsPrincipal (· + ·) a ↔ forall b < a, b + b < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0_opow`：lt_omega0_opow {a b : Ordinal} (hb : b != 0) : a
 < ω ^ b ↔ exists c < b, exists n : Nat, a < ω ^ c * n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `add_lt_add_of_le_of_lt`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftStrictMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c < d → a 
+ c < b + d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Ordinal.opow_mul_lt_opow`：opow_mul_lt_opow {b u v x : Ordinal} (hv : v <
 b) (hu : u < x) : b ^ u * v < b ^ x
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
-/
theorem isPrincipal_add_omega0_opow (o : Ordinal) : IsPrincipal (· + ·) (ω ^ o) := by
  obtain rfl | ha' := eq_or_ne o 0
  · rw [opow_zero, isPrincipal_one_iff, add_zero]
  · rw [isPrincipal_add_iff_add_self_lt]
    intro a ha
    obtain ⟨c, hc, m, hm⟩ := (lt_omega0_opow ha').1 ha
    apply (add_lt_add_of_le_of_lt hm.le hm).trans_le
    rw [← mul_add, ← Nat.cast_add]
    exact (opow_mul_lt_opow (natCast_lt_omega0 _) hc).le

@[deprecated (since := "2026-03-17")]
alias principal_add_omega0_opow := isPrincipal_add_omega0_opow
/-
**Ordinal.add_omega0_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_omega0_opow (h : a < ω ^ b) : a + ω ^ b = ω ^ b
参数：h : a < ω ^ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.IsPrincipal.add_eq_right`：∀ {a o : Ordinal.{u}}, Ordinal.IsPrinc
ipal (fun x1 x2 => x1 + x2) o → a < o → a + o = o
· 使用定理 `Ordinal.isPrincipal_add_omega0_opow`：isPrincipal_add_omega0_opow (o : Or
dinal) : IsPrincipal (· + ·) (ω ^ o)
-/
theorem add_omega0_opow (h : a < ω ^ b) : a + ω ^ b = ω ^ b :=
  (isPrincipal_add_omega0_opow b).add_eq_right h
/-
**Ordinal.add_of_omega0_opow_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_of_omega0_opow_le (h₁ : a < ω ^ b) (h₂ : ω ^ b <= c) : a + c = c
参数：h₁ : a < ω ^ b；h₂ : ω ^ b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.IsPrincipal.add_eq_right_of_le`：∀ {a b c : Ordinal.{u}}, Ordinal
.IsPrincipal (fun x1 x2 => x1 + x2) b → a < b → b ≤ c → a + c = c
· 使用定理 `Ordinal.isPrincipal_add_omega0_opow`：isPrincipal_add_omega0_opow (o : Or
dinal) : IsPrincipal (· + ·) (ω ^ o)
-/
theorem add_of_omega0_opow_le (h₁ : a < ω ^ b) (h₂ : ω ^ b ≤ c) : a + c = c :=
  (isPrincipal_add_omega0_opow b).add_eq_right_of_le h₁ h₂

@[deprecated (since := "2026-03-18")]
alias add_absorp := add_of_omega0_opow_le

/-- For `a ≠ 0`, the largest power of `ω` which is less or equal to it is also the smallest ordinal
`b` with `a - b < a`. -/
/-
**Ordinal.isLeast_sub_lt_omega0_opow_log** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isLeast_sub_lt_omega0_opow_log (h : a != 0) : IsLeast {b | a - b < a} (ω ^
 log ω a)
参数：h : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.sub_omega0_opow_log_lt`：sub_omega0_opow_log_lt {a : Ordinal} (ha
 : a != 0) : a - ω ^ log ω a < a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ordinal.le_sub_of_add_le`：le_sub_of_add_le {a b c : Ordinal} (h : b + c 
<= a) : c <= a - b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ordinal.add_of_omega0_opow_le`：add_of_omega0_opow_le (h₁ : a < ω ^ b) (h
₂ : ω ^ b <= c) : a + c = c
· 使用定理 `Ordinal.opow_log_le_self`：opow_log_le_self (b : Ordinal) {x : Ordinal} (
hx : x != 0) : b ^ log b x <= x

--- 原说明 ---
For `a ≠ 0`, the largest power of `ω` which is less or equal to it is also the s
mallest ordinal
`b` with `a - b < a`.
-/
theorem isLeast_sub_lt_omega0_opow_log (h : a ≠ 0) : IsLeast {b | a - b < a} (ω ^ log ω a) := by
  refine ⟨sub_omega0_opow_log_lt h, fun c (hc : a - _ < _) ↦ ?_⟩
  contrapose! hc
  exact le_sub_of_add_le (add_of_omega0_opow_le hc (opow_log_le_self ω h)).le

/-- The main characterization theorem for additive principal ordinals. -/
/-
**Ordinal.isPrincipal_add_iff_zero_or_omega0_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ord
inal`。
形式化陈述：isPrincipal_add_iff_zero_or_omega0_opow : IsPrincipal (· + ·) o ↔ o = 0 ∨ 
o in Set.range (ω ^ · : Ordinal -> Ordinal)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `Ordinal.opow_log_le_self`：opow_log_le_self (b : Ordinal) {x : Ordinal} (
hx : x != 0) : b ^ log b x <= x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0_opow_succ`：lt_omega0_opow_succ {a b : Ordinal} : a < ω
 ^ succ b ↔ exists n : Nat, a < ω ^ b * n
· 使用定理 `Ordinal.lt_opow_succ_log_self`：lt_opow_succ_log_self {b : Ordinal} (hb :
 1 < b) (x : Ordinal) : x < b ^ succ (log b x)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `Ordinal.IsPrincipal.mul_natCast_lt`：∀ {a o : Ordinal.{u}}, Ordinal.IsPri
ncipal (fun x1 x2 => x1 + x2) o → a < o → ∀ (n : ℕ), a * ↑n < o
· 使用定理 `Ordinal.isPrincipal_zero`：∀ {op : Ordinal.{u_1} → Ordinal.{u_1} → Ordina
l.{u_1}}, Ordinal.IsPrincipal op 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.isPrincipal_add_omega0_opow`：isPrincipal_add_omega0_opow (o : Or
dinal) : IsPrincipal (· + ·) (ω ^ o)

--- 原说明 ---
The main characterization theorem for additive principal ordinals.
-/
theorem isPrincipal_add_iff_zero_or_omega0_opow :
    IsPrincipal (· + ·) o ↔ o = 0 ∨ o ∈ Set.range (ω ^ · : Ordinal → Ordinal) := by
  constructor
  · rw [or_iff_not_imp_left]
    refine fun H ho ↦ ⟨log ω o, (opow_log_le_self ω ho).eq_of_not_lt ?_⟩
    obtain ⟨n, hn⟩ := lt_omega0_opow_succ.1 (lt_opow_succ_log_self one_lt_omega0 o)
    exact fun h ↦ hn.not_gt <| H.mul_natCast_lt h n
  · rintro (rfl | ⟨a, rfl⟩)
    exacts [isPrincipal_zero, isPrincipal_add_omega0_opow a]

@[deprecated (since := "2026-03-17")]
alias principal_add_iff_zero_or_omega0_opow := isPrincipal_add_iff_zero_or_omega0_opow
/-
**Ordinal.isPrincipal_add_opow_of_isPrincipal_add** 是 Mathlib 中的一个定理，位于命名空间 `Ord
inal`。
形式化陈述：isPrincipal_add_opow_of_isPrincipal_add {a} (ha : IsPrincipal (· + ·) a) (
b : Ordinal) : IsPrincipal (· + ·) (a ^ b)
参数：ha : IsPrincipal (· + ·) a；b : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.isPrincipal_add_iff_zero_or_omega0_opow`：isPrincipal_add_iff_zer
o_or_omega0_opow : IsPrincipal (· + ·) o ↔ o = 0 ∨ o in Set.range (ω ^ · : Ordin
al -> Ordinal)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Ordinal.isPrincipal_add_one`：isPrincipal_add_one : IsPrincipal (· + ·) 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `Ordinal.opow_mul`：opow_mul (a b c : Ordinal) : a ^ (b * c) = (a ^ b) ^ c
· 使用定理 `Ordinal.isPrincipal_add_omega0_opow`：isPrincipal_add_omega0_opow (o : Or
dinal) : IsPrincipal (· + ·) (ω ^ o)
-/
theorem isPrincipal_add_opow_of_isPrincipal_add {a} (ha : IsPrincipal (· + ·) a) (b : Ordinal) :
    IsPrincipal (· + ·) (a ^ b) := by
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 ha with (rfl | ⟨c, rfl⟩)
  · rcases eq_or_ne b 0 with (rfl | hb)
    · rw [opow_zero]
      exact isPrincipal_add_one
    · rwa [zero_opow hb]
  · rw [← opow_mul]
    exact isPrincipal_add_omega0_opow _

@[deprecated (since := "2026-03-17")]
alias principal_add_opow_of_principal_add := isPrincipal_add_opow_of_isPrincipal_add
/-
**Ordinal.isPrincipal_add_mul_of_isPrincipal_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordi
nal`。
形式化陈述：isPrincipal_add_mul_of_isPrincipal_add (a : Ordinal.{u}) {b : Ordinal.{u}}
 (hb₁ : b != 1) (hb : IsPrincipal (· + ·) b) : IsPrincipal (· + ·) (a * b)
参数：a : Ordinal.{u}；hb₁ : b != 1；hb : IsPrincipal (· + ·) b。
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
· 使用定理 `Ordinal.isPrincipal_zero`：∀ {op : Ordinal.{u_1} → Ordinal.{u_1} → Ordina
l.{u_1}}, Ordinal.IsPrincipal op 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Ordinal.lt_mul_iff_of_isSuccLimit`：lt_mul_iff_of_isSuccLimit {a b c : Or
dinal} (h : IsSuccLimit c) : a < b * c ↔ exists c' < c, a < b * c'
· 使用定理 `Ordinal.isSuccLimit_of_isPrincipal_add`：isSuccLimit_of_isPrincipal_add (
ho₁ : 1 < o) (ho : IsPrincipal (· + ·) o) : IsSuccLimit o
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Left.add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [
AddLeftStrictMono α] [AddRightMono α] {a b c d : α},   a < b → c < d → a + c < b
 + d
-/
theorem isPrincipal_add_mul_of_isPrincipal_add (a : Ordinal.{u}) {b : Ordinal.{u}} (hb₁ : b ≠ 1)
    (hb : IsPrincipal (· + ·) b) : IsPrincipal (· + ·) (a * b) := by
  rcases eq_zero_or_pos a with (rfl | _)
  · rw [zero_mul]
    exact isPrincipal_zero
  · rcases eq_zero_or_pos b with (rfl | hb₁')
    · rw [mul_zero]
      exact isPrincipal_zero
    · rw [← one_le_iff_pos] at hb₁'
      intro c d hc hd
      rw [lt_mul_iff_of_isSuccLimit
        (isSuccLimit_of_isPrincipal_add (lt_of_le_of_ne hb₁' hb₁.symm) hb)] at *
      rcases hc with ⟨x, hx, hx'⟩
      rcases hd with ⟨y, hy, hy'⟩
      use x + y, hb hx hy
      rw [mul_add]
      exact Left.add_lt_add hx' hy'

@[deprecated (since := "2026-03-17")]
alias principal_add_mul_of_principal_add := isPrincipal_add_mul_of_isPrincipal_add

/-! ### Multiplicative principal ordinals -/

/-
**Ordinal.isPrincipal_mul_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_mul_one : IsPrincipal (· * ·) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Multiplicative principal ordinals
-/
theorem isPrincipal_mul_one : IsPrincipal (· * ·) 1 := by simp

@[deprecated (since := "2026-03-17")]
alias principal_mul_one := isPrincipal_mul_one
/-
**Ordinal.isPrincipal_mul_two** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_mul_two : IsPrincipal (· * ·) 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.lt_two_iff`：lt_two_iff [AddMonoidWithOne α] [SuccAddOrder α] [NoMa
xOrder α] : x < 2 ↔ x <= 1
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
-/
theorem isPrincipal_mul_two : IsPrincipal (· * ·) 2 := by
  intro a b ha hb
  rw [lt_two_iff] at *
  simpa using mul_le_mul' ha hb

@[deprecated (since := "2026-03-17")]
alias principal_mul_two := isPrincipal_mul_two
/-
**Ordinal.isPrincipal_mul_of_le_two** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_mul_of_le_two (ho : o <= 2) : IsPrincipal (· * ·) o
参数：ho : o <= 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.le_two_iff`：le_two_iff : x <= 2 ↔ x = 0 ∨ x = 1 ∨ x = 2
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.isPrincipal_zero`：∀ {op : Ordinal.{u_1} → Ordinal.{u_1} → Ordina
l.{u_1}}, Ordinal.IsPrincipal op 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.isPrincipal_mul_one`：isPrincipal_mul_one : IsPrincipal (· * ·) 1
· 使用定理 `Ordinal.isPrincipal_mul_two`：isPrincipal_mul_two : IsPrincipal (· * ·) 2
-/
theorem isPrincipal_mul_of_le_two (ho : o ≤ 2) : IsPrincipal (· * ·) o := by
  obtain rfl | rfl | rfl := le_two_iff.1 ho
  exacts [isPrincipal_zero, isPrincipal_mul_one, isPrincipal_mul_two]

@[deprecated (since := "2026-03-17")]
alias principal_mul_of_le_two := isPrincipal_mul_of_le_two
/-
**Ordinal.isPrincipal_add_of_isPrincipal_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`
。
形式化陈述：isPrincipal_add_of_isPrincipal_mul (ho : IsPrincipal (· * ·) o) (ho₂ : o !
= 2) : IsPrincipal (· + ·) o
参数：ho : IsPrincipal (· * ·) o；ho₂ : o != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `Ordinal.isPrincipal_add_of_le_one`：isPrincipal_add_of_le_one (ho : o <= 
1) : IsPrincipal (· + ·) o
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.lt_two_iff`：lt_two_iff [AddMonoidWithOne α] [SuccAddOrder α] [NoMa
xOrder α] : x < 2 ↔ x <= 1
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem isPrincipal_add_of_isPrincipal_mul (ho : IsPrincipal (· * ·) o) (ho₂ : o ≠ 2) :
    IsPrincipal (· + ·) o := by
  rcases lt_or_gt_of_ne ho₂ with ho₁ | ho₂
  · exact isPrincipal_add_of_le_one <| lt_two_iff.mp ho₁
  · simp_rw [isPrincipal_add_iff_add_self_lt, ← Ordinal.mul_two]
    exact fun a ha ↦ ho ha ho₂

@[deprecated (since := "2026-03-17")]
alias principal_add_of_principal_mul := isPrincipal_add_of_isPrincipal_mul
/-
**Ordinal.isSuccLimit_of_isPrincipal_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_of_isPrincipal_mul (ho₂ : 2 < o) (ho : IsPrincipal (· * ·) o) 
: IsSuccLimit o
参数：ho₂ : 2 < o；ho : IsPrincipal (· * ·) o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Ordinal.isSuccLimit_of_isPrincipal_add`：isSuccLimit_of_isPrincipal_add (
ho₁ : 1 < o) (ho : IsPrincipal (· + ·) o) : IsSuccLimit o
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.isPrincipal_add_of_isPrincipal_mul`：isPrincipal_add_of_isPrincip
al_mul (ho : IsPrincipal (· * ·) o) (ho₂ : o != 2) : IsPrincipal (· + ·) o
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem isSuccLimit_of_isPrincipal_mul (ho₂ : 2 < o) (ho : IsPrincipal (· * ·) o) : IsSuccLimit o :=
  isSuccLimit_of_isPrincipal_add (one_lt_two.trans ho₂)
    (isPrincipal_add_of_isPrincipal_mul ho (ne_of_gt ho₂))

@[deprecated (since := "2026-03-17")]
alias isSuccLimit_of_principal_mul := isSuccLimit_of_isPrincipal_mul
/-
**Ordinal.isPrincipal_mul_iff_mul_left_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_mul_iff_mul_left_eq : IsPrincipal (· * ·) o ↔ forall a, 0 < a 
-> a < o -> a * o = o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.lt_add_one_iff`：lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x <= y
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Ordinal.op_eq_self_of_isPrincipal`：op_eq_self_of_isPrincipal (hao : a < 
o) (H : IsNormal (op a)) (ho : IsPrincipal op o) (ho' : IsSuccLimit o) : op a o 
= o
· 使用定理 `Ordinal.isNormal_mul_right`：isNormal_mul_right {a : Ordinal} (h : 0 < a)
 : IsNormal (a * ·)
· 使用定理 `Ordinal.isSuccLimit_of_isPrincipal_mul`：isSuccLimit_of_isPrincipal_mul (
ho₂ : 2 < o) (ho : IsPrincipal (· * ·) o) : IsSuccLimit o
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
-/
theorem isPrincipal_mul_iff_mul_left_eq :
    IsPrincipal (· * ·) o ↔ ∀ a, 0 < a → a < o → a * o = o := by
  refine ⟨fun h a ha₀ hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases le_or_gt o 2 with ho | ho
    · convert! one_mul o
      apply le_antisymm
      · rw [← lt_add_one_iff, one_add_one_eq_two]
        exact hao.trans_le ho
      · rwa [one_le_iff_pos]
    · exact op_eq_self_of_isPrincipal hao (isNormal_mul_right ha₀) h
        (isSuccLimit_of_isPrincipal_mul ho h)
  · rcases eq_or_ne a 0 with (rfl | ha)
    · dsimp only; rwa [zero_mul]
    rw [← pos_iff_ne_zero] at ha
    rw [← h a ha hao]
    exact (isNormal_mul_right ha).strictMono hbo

@[deprecated (since := "2026-03-17")]
alias principal_mul_iff_mul_left_eq := isPrincipal_mul_iff_mul_left_eq
/-
**Ordinal.isPrincipal_mul_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_mul_omega0 : IsPrincipal (· * ·) ω
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.natCast_mul`：∀ (m n : ℕ), ↑(m * n) = ↑m * ↑n
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
-/
theorem isPrincipal_mul_omega0 : IsPrincipal (· * ·) ω := fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    dsimp only; rw [← natCast_mul]
    apply natCast_lt_omega0

@[deprecated (since := "2026-03-17")]
alias principal_mul_omega0 := isPrincipal_mul_omega0
/-
**Ordinal.mul_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_omega0 (a0 : 0 < a) (ha : a < ω) : a * ω = ω
参数：a0 : 0 < a；ha : a < ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.isPrincipal_mul_iff_mul_left_eq`：isPrincipal_mul_iff_mul_left_eq
 : IsPrincipal (· * ·) o ↔ forall a, 0 < a -> a < o -> a * o = o
· 使用定理 `Ordinal.isPrincipal_mul_omega0`：isPrincipal_mul_omega0 : IsPrincipal (· 
* ·) ω
-/
theorem mul_omega0 (a0 : 0 < a) (ha : a < ω) : a * ω = ω :=
  isPrincipal_mul_iff_mul_left_eq.1 isPrincipal_mul_omega0 a a0 ha
/-
**Ordinal.natCast_mul_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_mul_omega0 {n : Nat} (hn : 0 < n) : n * ω = ω
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.mul_omega0`：mul_omega0 (a0 : 0 < a) (ha : a < ω) : a * ω = ω
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
-/
theorem natCast_mul_omega0 {n : ℕ} (hn : 0 < n) : n * ω = ω :=
  mul_omega0 (mod_cast hn) (natCast_lt_omega0 n)
/-
**Ordinal.mul_lt_omega0_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_lt_omega0_opow (c0 : 0 < c) (ha : a < ω ^ c) (hb : b < ω) : a * b < ω 
^ c
参数：c0 : 0 < c；ha : a < ω ^ c；hb : b < ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.zero_or_succ_or_isSuccLimit`：zero_or_succ_or_isSuccLimit (o : Or
dinal) : o = 0 ∨ o in range succ ∨ IsSuccLimit o
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.IsNormal.lt_iff_exists_lt`：lt_iff_exists_lt (hf : IsNormal f) (ha 
: IsSuccLimit a) {b : β} : b < f a ↔ exists a' < a, b < f a'
· 使用定理 `Ordinal.isNormal_mul_right`：isNormal_mul_right {a : Ordinal} (h : 0 < a)
 : IsNormal (a * ·)
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `Ordinal.omega0_pos`：omega0_pos : 0 < ω
· 使用定理 `Ordinal.isSuccLimit_omega0`：isSuccLimit_omega0 : IsSuccLimit ω
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_succ`：opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `Ordinal.instPosMulStrictMono`：PosMulStrictMono Ordinal.{u_4}
· 使用定理 `Ordinal.isPrincipal_mul_omega0`：isPrincipal_mul_omega0 : IsPrincipal (· 
* ·) ω
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ordinal.opow_lt_opow_iff_right`：opow_lt_opow_iff_right {a b c : Ordinal}
 (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
-/
theorem mul_lt_omega0_opow (c0 : 0 < c) (ha : a < ω ^ c) (hb : b < ω) : a * b < ω ^ c := by
  rcases zero_or_succ_or_isSuccLimit c with (rfl | ⟨c, rfl⟩ | l)
  · exact (lt_irrefl _).elim c0
  · rw [opow_succ] at ha
    obtain ⟨n, hn, an⟩ :=
      ((isNormal_mul_right <| opow_pos _ omega0_pos).lt_iff_exists_lt isSuccLimit_omega0).1 ha
    grw [an, opow_succ, mul_assoc]
    gcongr
    exacts [opow_pos _ omega0_pos, isPrincipal_mul_omega0 hn hb]
  · rcases ((isNormal_opow one_lt_omega0).lt_iff_exists_lt l).1 ha with ⟨x, hx, ax⟩
    refine (mul_le_mul' (le_of_lt ax) (le_of_lt hb)).trans_lt ?_
    rw [← opow_succ, opow_lt_opow_iff_right one_lt_omega0]
    exact l.succ_lt hx
/-
**Ordinal.mul_omega0_opow_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_omega0_opow_opow (a0 : 0 < a) (h : a < ω ^ ω ^ b) : a * ω ^ ω ^ b = ω 
^ ω ^ b
参数：a0 : 0 < a；h : a < ω ^ ω ^ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Ordinal.opow_one`：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
· 使用定理 `Ordinal.mul_omega0`：mul_omega0 (a0 : 0 < a) (ha : a < ω) : a * ω = ω
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_opow_of_isSuccLimit`：lt_opow_of_isSuccLimit {a b c : Ordinal}
 (b0 : b != 0) (h : IsSuccLimit c) : a < b ^ c ↔ exists c' < c, a < b ^ c'
· 使用定理 `Ordinal.omega0_ne_zero`：omega0_ne_zero : ω != 0
· 使用定理 `Ordinal.isSuccLimit_opow_left`：isSuccLimit_opow_left {a b : Ordinal} (l 
: IsSuccLimit a) (hb : b != 0) : IsSuccLimit (a ^ b)
· 使用定理 `Ordinal.isSuccLimit_omega0`：isSuccLimit_omega0 : IsSuccLimit ω
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ordinal.opow_add`：opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^
 c
· 使用定理 `Ordinal.add_omega0_opow`：add_omega0_opow (h : a < ω ^ b) : a + ω ^ b = ω
 ^ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem mul_omega0_opow_opow (a0 : 0 < a) (h : a < ω ^ ω ^ b) : a * ω ^ ω ^ b = ω ^ ω ^ b := by
  obtain rfl | b0 := eq_or_ne b 0
  · rw [opow_zero, opow_one] at h ⊢
    exact mul_omega0 a0 h
  · apply le_antisymm
    · obtain ⟨x, xb, ax⟩ :=
        (lt_opow_of_isSuccLimit omega0_ne_zero (isSuccLimit_opow_left isSuccLimit_omega0 b0)).1 h
      grw [ax, ← opow_add, add_omega0_opow xb]
    · conv_lhs => rw [← one_mul (ω ^ _)]
      grw [one_le_iff_pos.2 a0]
/-
**Ordinal.isPrincipal_mul_omega0_opow_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_mul_omega0_opow_opow (o : Ordinal) : IsPrincipal (· * ·) (ω ^ 
ω ^ o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.isPrincipal_mul_iff_mul_left_eq`：isPrincipal_mul_iff_mul_left_eq
 : IsPrincipal (· * ·) o ↔ forall a, 0 < a -> a < o -> a * o = o
· 使用定理 `Ordinal.mul_omega0_opow_opow`：mul_omega0_opow_opow (a0 : 0 < a) (h : a <
 ω ^ ω ^ b) : a * ω ^ ω ^ b = ω ^ ω ^ b
-/
theorem isPrincipal_mul_omega0_opow_opow (o : Ordinal) : IsPrincipal (· * ·) (ω ^ ω ^ o) :=
  isPrincipal_mul_iff_mul_left_eq.2 fun _ => mul_omega0_opow_opow

@[deprecated (since := "2026-03-17")]
alias principal_mul_omega0_opow_opow := isPrincipal_mul_omega0_opow_opow
/-
**Ordinal.isPrincipal_add_of_isPrincipal_mul_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ord
inal`。
形式化陈述：isPrincipal_add_of_isPrincipal_mul_opow (hb : 1 < b) (ho : IsPrincipal (· 
* ·) (b ^ o)) : IsPrincipal (· + ·) o
参数：hb : 1 < b；ho : IsPrincipal (· * ·) (b ^ o)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.opow_lt_opow_iff_right`：opow_lt_opow_iff_right {a b c : Ordinal}
 (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.opow_add`：opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^
 c
-/
theorem isPrincipal_add_of_isPrincipal_mul_opow (hb : 1 < b) (ho : IsPrincipal (· * ·) (b ^ o)) :
    IsPrincipal (· + ·) o := by
  intro x y hx hy
  have := ho ((opow_lt_opow_iff_right hb).2 hx) ((opow_lt_opow_iff_right hb).2 hy)
  dsimp only at *
  rwa [← opow_add, opow_lt_opow_iff_right hb] at this

@[deprecated (since := "2026-03-17")]
alias principal_add_of_principal_mul_opow := isPrincipal_add_of_isPrincipal_mul_opow

/-- The main characterization theorem for multiplicative principal ordinals. -/
/-
**Ordinal.isPrincipal_mul_iff_le_two_or_omega0_opow_opow** 是 Mathlib 中的一个定理，位于命名
空间 `Ordinal`。
形式化陈述：isPrincipal_mul_iff_le_two_or_omega0_opow_opow : IsPrincipal (· * ·) o ↔ o
 <= 2 ∨ o in Set.range (ω ^ ω ^ · : Ordinal -> Ordinal)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.isPrincipal_add_iff_zero_or_omega0_opow`：isPrincipal_add_iff_zer
o_or_omega0_opow : IsPrincipal (· + ·) o ↔ o = 0 ∨ o in Set.range (ω ^ · : Ordin
al -> Ordinal)
· 使用定理 `Ordinal.isPrincipal_add_of_isPrincipal_mul`：isPrincipal_add_of_isPrincip
al_mul (ho : IsPrincipal (· * ·) o) (ho₂ : o != 2) : IsPrincipal (· + ·) o
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_lt_zero`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], ¬a < 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.isPrincipal_add_of_isPrincipal_mul_opow`：isPrincipal_add_of_isPr
incipal_mul_opow (hb : 1 < b) (ho : IsPrincipal (· * ·) (b ^ o)) : IsPrincipal (
· + ·) o
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Ordinal.isPrincipal_mul_of_le_two`：isPrincipal_mul_of_le_two (ho : o <= 
2) : IsPrincipal (· * ·) o
· 使用定理 `Ordinal.isPrincipal_mul_omega0_opow_opow`：isPrincipal_mul_omega0_opow_op
ow (o : Ordinal) : IsPrincipal (· * ·) (ω ^ ω ^ o)

--- 原说明 ---
The main characterization theorem for multiplicative principal ordinals.
-/
theorem isPrincipal_mul_iff_le_two_or_omega0_opow_opow :
    IsPrincipal (· * ·) o ↔ o ≤ 2 ∨ o ∈ Set.range (ω ^ ω ^ · : Ordinal → Ordinal) := by
  refine ⟨fun ho => ?_, ?_⟩
  · rcases le_or_gt o 2 with ho₂ | ho₂
    · exact Or.inl ho₂
    · rcases isPrincipal_add_iff_zero_or_omega0_opow.1
        (isPrincipal_add_of_isPrincipal_mul ho ho₂.ne') with (rfl | ⟨a, rfl⟩)
      · exact (not_lt_zero ho₂).elim
      · rcases isPrincipal_add_iff_zero_or_omega0_opow.1
          (isPrincipal_add_of_isPrincipal_mul_opow one_lt_omega0 ho) with (rfl | ⟨b, rfl⟩)
        · simp
        · exact Or.inr ⟨b, rfl⟩
  · rintro (ho₂ | ⟨a, rfl⟩)
    · exact isPrincipal_mul_of_le_two ho₂
    · exact isPrincipal_mul_omega0_opow_opow a

@[deprecated (since := "2026-03-17")]
alias principal_mul_iff_le_two_or_omega0_opow_opow := isPrincipal_mul_iff_le_two_or_omega0_opow_opow
/-
**Ordinal.mul_omega0_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {a : Ordinal.{u}}, 0 < a → a < Ordinal.omega0 → ∀ {b : Ordinal.{u}}, Ord
inal.omega0 ∣ b → a * b = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ordinal.mul_omega0`：mul_omega0 (a0 : 0 < a) (ha : a < ω) : a * ω = ω
-/
theorem mul_omega0_dvd (a0 : 0 < a) (ha : a < ω) : ∀ {b}, ω ∣ b → a * b = b
  | _, ⟨b, rfl⟩ => by rw [← mul_assoc, mul_omega0 a0 ha]
/-
**Ordinal.mul_eq_opow_log_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_eq_opow_log_succ (ha : a != 0) (hb : IsPrincipal (· * ·) b) (hb₂ : 2 <
 b) : a * b = b ^ succ (log b a)
参数：ha : a != 0；hb : IsPrincipal (· * ·) b；hb₂ : 2 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.isSuccLimit_of_isPrincipal_mul`：isSuccLimit_of_isPrincipal_mul (
ho₂ : 2 < o) (ho : IsPrincipal (· * ·) o) : IsSuccLimit o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.IsNormal.apply_of_isSuccLimit`：apply_of_isSuccLimit (hf : IsNormal
 f) (ha : IsSuccLimit a) : f a = ⨆ b : Iio a, f b
· 使用定理 `Ordinal.isNormal_mul_right`：isNormal_mul_right {a : Ordinal} (h : 0 < a)
 : IsNormal (a * ·)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.iSup_le_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], ⨆ i, f i ≤ a ↔ ∀ (i : ι), f i ≤ a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.lt_mul_succ_div`：lt_mul_succ_div (a) {b : Ordinal} (h : b != 0) 
: a < b * succ (a / b)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ordinal.opow_succ`：opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lt_mul_iff_div_lt`：lt_mul_iff_div_lt {a b c : Ordinal} (ha : a !
= 0) : c < a * b ↔ c / a < b
· 使用定理 `Ordinal.lt_opow_succ_log_self`：lt_opow_succ_log_self {b : Ordinal} (hb :
 1 < b) (x : Ordinal) : x < b ^ succ (log b x)
（共 32 条，此处仅展示前 30 条）
-/
theorem mul_eq_opow_log_succ (ha : a ≠ 0) (hb : IsPrincipal (· * ·) b) (hb₂ : 2 < b) :
    a * b = b ^ succ (log b a) := by
  apply le_antisymm
  · have hbl := isSuccLimit_of_isPrincipal_mul hb₂ hb
    rw [(isNormal_mul_right (pos_iff_ne_zero.2 ha)).apply_of_isSuccLimit hbl,
      Ordinal.iSup_le_iff]
    intro ⟨c, hcb⟩
    have hb₁ : 1 < b := one_lt_two.trans hb₂
    have hbo₀ : b ^ log b a ≠ 0 := pos_iff_ne_zero.1 (opow_pos _ (zero_lt_one.trans hb₁))
    apply (mul_le_mul_left (le_of_lt (lt_mul_succ_div a hbo₀)) c).trans
    rw [mul_assoc, opow_succ]
    gcongr
    refine (hb (hbl.succ_lt ?_) hcb).le
    rw [← lt_mul_iff_div_lt hbo₀, ← opow_succ]
    exact lt_opow_succ_log_self hb₁ _
  · grw [opow_succ, opow_log_le_self b ha]

/-! #### Exponential principal ordinals -/

/-
**Ordinal.isPrincipal_opow_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_opow_omega0 : IsPrincipal (· ^ ·) ω
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_natCast`：opow_natCast (a : Ordinal) (n : Nat) : a ^ (n : Or
dinal) = a ^ n

--- 原说明 ---
#### Exponential principal ordinals
-/
theorem isPrincipal_opow_omega0 : IsPrincipal (· ^ ·) ω := fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by simp [← natCast_pow]

@[deprecated (since := "2026-03-17")]
alias principal_opow_omega0 := isPrincipal_opow_omega0
/-
**Ordinal.opow_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_omega0 (a1 : 1 < a) (h : a < ω) : a ^ ω = ω
参数：a1 : 1 < a；h : a < ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.opow_le_of_isSuccLimit`：opow_le_of_isSuccLimit {a b c : Ordinal}
 (a0 : a != 0) (h : IsSuccLimit b) : a ^ b <= c ↔ forall b' < b, a ^ b' <= c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.isSuccLimit_omega0`：isSuccLimit_omega0 : IsSuccLimit ω
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.isPrincipal_opow_omega0`：isPrincipal_opow_omega0 : IsPrincipal (
· ^ ·) ω
· 使用定理 `Ordinal.right_le_opow`：right_le_opow {a : Ordinal} (b : Ordinal) (a1 : 1
 < a) : b <= a ^ b
-/
theorem opow_omega0 (a1 : 1 < a) (h : a < ω) : a ^ ω = ω :=
  ((opow_le_of_isSuccLimit (one_le_iff_ne_zero.1 <| le_of_lt a1) isSuccLimit_omega0).2 fun _ hb =>
      (isPrincipal_opow_omega0 h hb).le).antisymm
  (right_le_opow _ a1)
/-
**Ordinal.natCast_opow_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_opow_omega0 {n : Nat} (hn : 1 < n) : n ^ ω = ω
参数：hn : 1 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.opow_omega0`：opow_omega0 (a1 : 1 < a) (h : a < ω) : a ^ ω = ω
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
-/
theorem natCast_opow_omega0 {n : ℕ} (hn : 1 < n) : n ^ ω = ω :=
  opow_omega0 (mod_cast hn) (natCast_lt_omega0 n)

end Ordinal

