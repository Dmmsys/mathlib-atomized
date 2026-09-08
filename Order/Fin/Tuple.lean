/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.PiLex
public import Mathlib.Order.Interval.Set.Defs

/-!
# Order properties on tuples
-/

@[expose] public section

assert_not_exists Monoid

open Function Set

namespace Fin
variable {m n : ℕ} {α : Fin (n + 1) → Type*} (x : α 0) (q : ∀ i, α i) (p : ∀ i : Fin n, α i.succ)
  (i : Fin n) (y : α i.succ) (z : α 0)

/-
**Fin.pi_lex_lt_cons_cons** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：pi_lex_lt_cons_cons {x₀ y₀ : α 0} {x y : forall i : Fin n, α i.succ} (s : 
forall {i : Fin n.succ}, α i -> α i -> Prop) : Pi.Lex (· < ·) (@s) (Fin.cons x₀ 
x) (Fin.cons y₀ y) ↔ s x₀ y₀ ∨ x₀ = y₀ ∧ Pi.Lex (· < ·) (@fun i : Fin n => @s i.
succ) x y
参数：s : forall {i : Fin n.succ}, α i -> α i -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pi_lex_lt_cons_cons {x₀ y₀ : α 0} {x y : ∀ i : Fin n, α i.succ}
    (s : ∀ {i : Fin n.succ}, α i → α i → Prop) :
    Pi.Lex (· < ·) (@s) (Fin.cons x₀ x) (Fin.cons y₀ y) ↔
      s x₀ y₀ ∨ x₀ = y₀ ∧ Pi.Lex (· < ·) (@fun i : Fin n ↦ @s i.succ) x y := by
  simp_rw [Pi.Lex, Fin.exists_fin_succ, Fin.cons_succ, Fin.cons_zero, Fin.forall_iff_succ]
  simp [and_assoc, exists_and_left]

variable [∀ i, Preorder (α i)]
/-
**Fin.insertNth_mem_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：insertNth_mem_Icc {i : Fin (n + 1)} {x : α i} {p : forall j, α (i.succAbov
e j)} {q₁ q₂ : forall j, α j} : i.insertNth x p in Icc q₁ q₂ ↔ x in Icc (q₁ i) (
q₂ i) ∧ p in Icc (fun j => q₁ (i.succAbove j)) fun j => q₂ (i.succAbove j)
参数：n + 1；i.succAbove j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_left_comm`：∀ {a b c : Prop}, a ∧ b ∧ c ↔ b ∧ a ∧ c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma insertNth_mem_Icc {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)}
    {q₁ q₂ : ∀ j, α j} :
    i.insertNth x p ∈ Icc q₁ q₂ ↔
      x ∈ Icc (q₁ i) (q₂ i) ∧ p ∈ Icc (fun j ↦ q₁ (i.succAbove j)) fun j ↦ q₂ (i.succAbove j) := by
  simp only [mem_Icc, insertNth_le_iff, le_insertNth_iff, and_assoc, @and_left_comm (x ≤ q₂ i)]
/-
**Fin.preimage_insertNth_Icc_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：preimage_insertNth_Icc_of_mem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : forall 
j, α j} (hx : x in Icc (q₁ i) (q₂ i)) : i.insertNth x ⁻¹' Icc q₁ q₂ = Icc (fun j
 => q₁ (i.succAbove j)) fun j => q₂ (i.succAbove j)
参数：n + 1；hx : x in Icc (q₁ i) (q₂ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma preimage_insertNth_Icc_of_mem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : ∀ j, α j}
    (hx : x ∈ Icc (q₁ i) (q₂ i)) :
    i.insertNth x ⁻¹' Icc q₁ q₂ = Icc (fun j ↦ q₁ (i.succAbove j)) fun j ↦ q₂ (i.succAbove j) :=
  Set.ext fun p ↦ by simp only [mem_preimage, insertNth_mem_Icc, hx, true_and]
/-
**Fin.preimage_insertNth_Icc_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：preimage_insertNth_Icc_of_notMem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : fora
ll j, α j} (hx : x ∉ Icc (q₁ i) (q₂ i)) : i.insertNth x ⁻¹' Icc q₁ q₂ = ∅
参数：n + 1；hx : x ∉ Icc (q₁ i) (q₂ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma preimage_insertNth_Icc_of_notMem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : ∀ j, α j}
    (hx : x ∉ Icc (q₁ i) (q₂ i)) : i.insertNth x ⁻¹' Icc q₁ q₂ = ∅ :=
  Set.ext fun p ↦ by
    simp only [mem_preimage, insertNth_mem_Icc, hx, false_and, mem_empty_iff_false]

end Fin

open Fin Matrix

variable {α : Type*}

open scoped Relator in
/-
**liftFun_vecCons** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：liftFun_vecCons {n : Nat} (r : α -> α -> Prop) [IsTrans α r] {f : Fin (n +
 1) -> α} {a : α} : ((· < ·) ⇒ r) (vecCons a f) (vecCons a f) ↔ r a (f 0) ∧ ((· 
< ·) ⇒ r) f f
参数：r : α -> α -> Prop；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.liftFun_iff_succ`：liftFun_iff_succ {α : Type*} (r : α -> α -> Prop) 
[IsTrans α r] {f : Fin (n + 1) -> α} : ((· < ·) ⇒ r) f f ↔ forall i : Fin n, r (
f (castSuc…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma liftFun_vecCons {n : ℕ} (r : α → α → Prop) [IsTrans α r] {f : Fin (n + 1) → α} {a : α} :
    ((· < ·) ⇒ r) (vecCons a f) (vecCons a f) ↔ r a (f 0) ∧ ((· < ·) ⇒ r) f f := by
  simp only [liftFun_iff_succ r, forall_iff_succ, cons_val_succ, cons_val_zero, ← succ_castSucc,
    castSucc_zero]

open scoped Relator in
/-
**Fin.liftFun_cons** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.liftFun_cons {n : Nat} (r : α -> α -> Prop) [IsTrans α r] {f : Fin n -
> α} {a : α} : ((· < ·) ⇒ r) (cons a f) (cons a f) ↔ (forall i, r a (f i)) ∧ ((·
 < ·) ⇒ r) f f
参数：r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Fin.subsingleton_zero`：Subsingleton (Fin 0)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `liftFun_vecCons`：liftFun_vecCons {n : Nat} (r : α -> α -> Prop) [IsTrans
 α r] {f : Fin (n + 1) -> α} {a : α} : ((· < ·) ⇒ r) (vecCons a f) (vecCons a f)
 ↔ r …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
-/
lemma Fin.liftFun_cons {n : ℕ} (r : α → α → Prop) [IsTrans α r] {f : Fin n → α} {a : α} :
    ((· < ·) ⇒ r) (cons a f) (cons a f) ↔ (∀ i, r a (f i)) ∧ ((· < ·) ⇒ r) f f := by
  match n with
  | 0 => simp [Relator.LiftFun]
  | n + 1 =>
    apply (liftFun_vecCons r).trans
    simp only [forall_iff_succ, and_congr_left_iff, iff_self_and]
    intro h r0 i
    exact _root_.trans r0 (h (by grind))

variable [Preorder α] {n : ℕ}
/-
**Fin.strictMono_insertNth_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.strictMono_insertNth_iff (q : Fin (n + 1)) (x : α) (f : Fin n -> α) : 
StrictMono (q.insertNth x f) ↔ StrictMono f ∧ (forall i, i.castSucc < q -> f i <
 x) ∧ (forall i, q <= i.castSucc -> x < f i)
参数：q : Fin (n + 1)；x : α；f : Fin n -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Fin.strictMono_succAbove`：strictMono_succAbove (p : Fin (n + 1)) : Stric
tMono (succAbove p)
-/
lemma Fin.strictMono_insertNth_iff (q : Fin (n + 1)) (x : α) (f : Fin n → α) :
    StrictMono (q.insertNth x f) ↔
      StrictMono f ∧ (∀ i, i.castSucc < q → f i < x) ∧ (∀ i, q ≤ i.castSucc → x < f i) := by
  refine ⟨fun h ↦ ⟨fun a b hab ↦ ?_, ⟨fun i hlt ↦ ?_, fun i hlt ↦ ?_⟩⟩, ?_⟩
  · simpa [hab] using h (a := q.succAbove a) (b := q.succAbove b)
  · have : q.succAbove i < q := by simp [succAbove_of_castSucc_lt, hlt]
    simpa using h this
  · have : q < q.succAbove i := by simp [succAbove_of_le_castSucc, hlt, ← le_castSucc_iff]
    simpa using h this
  · rintro ⟨h, hlt, hgt⟩ a b hab
    cases a using succAboveCases q <;> cases b using succAboveCases q
    · simp at hab
    · rename_i j
      have : q ≤ j.castSucc := by simpa [lt_succAbove_iff_le_castSucc] using hab
      simpa using hgt _ this
    · rename_i j
      have : j.castSucc < q := by simpa [succAbove_lt_iff_castSucc_lt] using hab
      simpa using hlt _ this
    · simpa using h <| (strictMono_succAbove _).lt_iff_lt.mp hab
/-
**Fin.strictMono_cons** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.strictMono_cons {f : Fin n -> α} {a : α} : StrictMono (Fin.cons a f) ↔
 (forall j, a < f j) ∧ StrictMono f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.liftFun_cons`：Fin.liftFun_cons {n : Nat} (r : α -> α -> Prop) [IsTra
ns α r] {f : Fin n -> α} {a : α} : ((· < ·) ⇒ r) (cons a f) (cons a f) ↔ (forall
 i, r …
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
lemma Fin.strictMono_cons {f : Fin n → α} {a : α} :
    StrictMono (Fin.cons a f) ↔ (∀ j, a < f j) ∧ StrictMono f :=
  liftFun_cons (· < ·)
/-
**Fin.strictMono_cons_zero_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {f : Fin n → Fin (n + 1)}, StrictMono (Fin.cons 0 f) ↔ f = Fin.s
ucc
参数：n + 1；Fin.cons 0 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `Fin.Lt.isWellOrder`：∀ (n : ℕ), IsWellOrder (Fin n) fun x1 x2 => x1 < x2
· 使用定理 `StrictAnti.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictAn…
· 使用定理 `StrictAnti.comp_strictMono`：StrictAnti.comp_strictMono (hg : StrictAnti 
g) (hf : StrictMono f) : StrictAnti (g ∘ f)
· 使用引理 `Fin.rev_strictAnti`：rev_strictAnti : StrictAnti (@rev n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.cons_zero_succ`：cons_zero_succ : (cons 0 Fin.succ : Fin (n + 1) -> F
in (n + 1)) = id
-/
@[simp] lemma Fin.strictMono_cons_zero_succ {f : Fin n → Fin (n + 1)} :
    StrictMono (Fin.cons 0 f) ↔ f = Fin.succ := by
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ by simp [h, strictMono_id]⟩
  have key (g : Fin (n + 1) → Fin (n + 1)) (hg : StrictMono g) : g = id := by
    -- Import restrictions prevent us using `StrictMono.eq_id`: hence this manual proof.
    refine funext fun x ↦ le_antisymm ?_ (hg.id_le x)
    simpa using ((Fin.rev_strictAnti.comp_strictMono hg).comp Fin.rev_strictAnti).id_le (Fin.rev x)
  simpa using congrFun (key _ h) i.succ

variable {f : Fin (n + 1) → α} {a : α}
/-
**strictMono_vecCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f : Fin (n + 1) → α} {a : α}
,   StrictMono (Matrix.vecCons a f) ↔ a < f 0 ∧ StrictMono f
参数：n + 1；Matrix.vecCons a f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `liftFun_vecCons`：liftFun_vecCons {n : Nat} (r : α -> α -> Prop) [IsTrans
 α r] {f : Fin (n + 1) -> α} {a : α} : ((· < ·) ⇒ r) (vecCons a f) (vecCons a f)
 ↔ r …
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
@[simp] lemma strictMono_vecCons : StrictMono (vecCons a f) ↔ a < f 0 ∧ StrictMono f :=
  liftFun_vecCons (· < ·)

@[simp]
/-
**monotone_vecCons** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_vecCons : Monotone (vecCons a f) ↔ a <= f 0 ∧ Monotone f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `liftFun_vecCons`：liftFun_vecCons {n : Nat} (r : α -> α -> Prop) [IsTrans
 α r] {f : Fin (n + 1) -> α} {a : α} : ((· < ·) ⇒ r) (vecCons a f) (vecCons a f)
 ↔ r …
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
lemma monotone_vecCons : Monotone (vecCons a f) ↔ a ≤ f 0 ∧ Monotone f := by
  simpa only [monotone_iff_forall_lt] using! @liftFun_vecCons α n (· ≤ ·) _ f a
/-
**monotone_vecEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a : α}, Monotone ![a]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
@[simp] lemma monotone_vecEmpty : Monotone ![a]
  | ⟨0, _⟩, ⟨0, _⟩, _ => le_refl _
/-
**strictMono_vecEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a : α}, StrictMono ![a]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
-/
@[simp] lemma strictMono_vecEmpty : StrictMono ![a]
  | ⟨0, _⟩, ⟨0, _⟩, h => (irrefl _ h).elim
/-
**strictAnti_vecCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f : Fin (n + 1) → α} {a : α}
,   StrictAnti (Matrix.vecCons a f) ↔ f 0 < a ∧ StrictAnti f
参数：n + 1；Matrix.vecCons a f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `liftFun_vecCons`：liftFun_vecCons {n : Nat} (r : α -> α -> Prop) [IsTrans
 α r] {f : Fin (n + 1) -> α} {a : α} : ((· < ·) ⇒ r) (vecCons a f) (vecCons a f)
 ↔ r …
· 使用定理 `instIsTransGt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 < x1
-/
@[simp] lemma strictAnti_vecCons : StrictAnti (vecCons a f) ↔ f 0 < a ∧ StrictAnti f :=
  liftFun_vecCons (· > ·)
/-
**antitone_vecCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f : Fin (n + 1) → α} {a : α}
,   Antitone (Matrix.vecCons a f) ↔ f 0 ≤ a ∧ Antitone f
参数：n + 1；Matrix.vecCons a f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monotone_vecCons`：monotone_vecCons : Monotone (vecCons a f) ↔ a <= f 0 ∧
 Monotone f
-/
@[simp] lemma antitone_vecCons : Antitone (vecCons a f) ↔ f 0 ≤ a ∧ Antitone f :=
  monotone_vecCons (α := αᵒᵈ)
/-
**antitone_vecEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a : α}, Antitone ![a]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
@[simp] lemma antitone_vecEmpty : Antitone (vecCons a vecEmpty)
  | ⟨0, _⟩, ⟨0, _⟩, _ => le_rfl
/-
**strictAnti_vecEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a : α}, StrictAnti ![a]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
-/
@[simp] lemma strictAnti_vecEmpty : StrictAnti (vecCons a vecEmpty)
  | ⟨0, _⟩, ⟨0, _⟩, h => (irrefl _ h).elim
/-
**StrictMono.vecCons** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.vecCons (hf : StrictMono f) (ha : a < f 0) : StrictMono (vecCon
s a f)
参数：hf : StrictMono f；ha : a < f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `strictMono_vecCons`：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f : Fi
n (n + 1) → α} {a : α},   StrictMono (Matrix.vecCons a f) ↔ a < f 0 ∧ StrictMono
 f
-/
lemma StrictMono.vecCons (hf : StrictMono f) (ha : a < f 0) : StrictMono (vecCons a f) :=
  strictMono_vecCons.2 ⟨ha, hf⟩
/-
**StrictMono.removeNth** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.removeNth (hf : StrictMono f) (i : Fin (n + 1)) : StrictMono (i
.removeNth f)
参数：hf : StrictMono f；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用引理 `Fin.strictMono_succAbove`：strictMono_succAbove (p : Fin (n + 1)) : Stric
tMono (succAbove p)
-/
lemma StrictMono.removeNth (hf : StrictMono f) (i : Fin (n + 1)) : StrictMono (i.removeNth f) :=
  hf.comp (Fin.strictMono_succAbove i)
/-
**StrictAnti.vecCons** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.vecCons (hf : StrictAnti f) (ha : f 0 < a) : StrictAnti (vecCon
s a f)
参数：hf : StrictAnti f；ha : f 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `strictAnti_vecCons`：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f : Fi
n (n + 1) → α} {a : α},   StrictAnti (Matrix.vecCons a f) ↔ f 0 < a ∧ StrictAnti
 f
-/
lemma StrictAnti.vecCons (hf : StrictAnti f) (ha : f 0 < a) : StrictAnti (vecCons a f) :=
  strictAnti_vecCons.2 ⟨ha, hf⟩
/-
**Monotone.vecCons** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.vecCons (hf : Monotone f) (ha : a <= f 0) : Monotone (vecCons a f
)
参数：hf : Monotone f；ha : a <= f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `monotone_vecCons`：monotone_vecCons : Monotone (vecCons a f) ↔ a <= f 0 ∧
 Monotone f
-/
lemma Monotone.vecCons (hf : Monotone f) (ha : a ≤ f 0) : Monotone (vecCons a f) :=
  monotone_vecCons.2 ⟨ha, hf⟩
/-
**Antitone.vecCons** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.vecCons (hf : Antitone f) (ha : f 0 <= a) : Antitone (vecCons a f
)
参数：hf : Antitone f；ha : f 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `antitone_vecCons`：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f : Fin 
(n + 1) → α} {a : α},   Antitone (Matrix.vecCons a f) ↔ f 0 ≤ a ∧ Antitone f
-/
lemma Antitone.vecCons (hf : Antitone f) (ha : f 0 ≤ a) : Antitone (vecCons a f) :=
  antitone_vecCons.2 ⟨ha, hf⟩
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Monotone ![1, 2, 2, 3] := by decide


variable {n : ℕ}

/-- `Π i : Fin 2, α i` is order equivalent to `α 0 × α 1`. See also `OrderIso.finTwoArrowEquiv`
for a non-dependent version. -/
/-
**OrderIso.piFinTwoIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.piFinTwoIso (α : Fin 2 -> Type*) [forall i, Preorder (α i)] : (fo
rall i, α i) ≃o α 0 × α 1 where toEquiv
参数：α : Fin 2 -> Type*；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Π i : Fin 2, α i` is order equivalent to `α 0 × α 1`. See also `OrderIso.finTwo
ArrowEquiv`
for a non-dependent version.
-/
def OrderIso.piFinTwoIso (α : Fin 2 → Type*) [∀ i, Preorder (α i)] : (∀ i, α i) ≃o α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  map_rel_iff' := Iff.symm Fin.forall_fin_two

/-- The space of functions `Fin 2 → α` is order equivalent to `α × α`. See also
`OrderIso.piFinTwoIso`. -/
/-
**OrderIso.finTwoArrowIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.finTwoArrowIso (α : Type*) [Preorder α] : (Fin 2 -> α) ≃o α × α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of functions `Fin 2 → α` is order equivalent to `α × α`. See also
`OrderIso.piFinTwoIso`.
-/
def OrderIso.finTwoArrowIso (α : Type*) [Preorder α] : (Fin 2 → α) ≃o α × α :=
  { OrderIso.piFinTwoIso fun _ => α with toEquiv := finTwoArrowEquiv α }

namespace Fin

/-- Order isomorphism between tuples of length `n + 1` and pairs of an element and a tuple of length
`n` given by separating out the first element of the tuple.

This is `Fin.cons` as an `OrderIso`. -/
@[simps!, simps toEquiv]
/-
**Fin.consOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：consOrderIso (α : Fin (n + 1) -> Type*) [forall i, LE (α i)] : α 0 × (fora
ll i, α (succ i)) ≃o forall i, α i where toEquiv
参数：α : Fin (n + 1) -> Type*；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order isomorphism between tuples of length `n + 1` and pairs of an element and a
 tuple of length
`n` given by separating out the first element of the tuple.

This is `Fin.cons` as an `OrderIso`.
-/
def consOrderIso (α : Fin (n + 1) → Type*) [∀ i, LE (α i)] :
    α 0 × (∀ i, α (succ i)) ≃o ∀ i, α i where
  toEquiv := consEquiv α
  map_rel_iff' := forall_iff_succ

/-- Order isomorphism between tuples of length `n + 1` and pairs of an element and a tuple of length
`n` given by separating out the last element of the tuple.

This is `Fin.snoc` as an `OrderIso`. -/
@[simps!, simps toEquiv]
/-
**Fin.snocOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：snocOrderIso (α : Fin (n + 1) -> Type*) [forall i, LE (α i)] : α (last n) 
× (forall i, α (castSucc i)) ≃o forall i, α i where toEquiv
参数：α : Fin (n + 1) -> Type*；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order isomorphism between tuples of length `n + 1` and pairs of an element and a
 tuple of length
`n` given by separating out the last element of the tuple.

This is `Fin.snoc` as an `OrderIso`.
-/
def snocOrderIso (α : Fin (n + 1) → Type*) [∀ i, LE (α i)] :
    α (last n) × (∀ i, α (castSucc i)) ≃o ∀ i, α i where
  toEquiv := snocEquiv α
  map_rel_iff' := by simp [Pi.le_def, Prod.le_def, forall_iff_castSucc]

/-- Order isomorphism between tuples of length `n + 1` and pairs of an element and a tuple of length
`n` given by separating out the `p`-th element of the tuple.

This is `Fin.insertNth` as an `OrderIso`. -/
@[simps!, simps toEquiv]
/-
**Fin.insertNthOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：insertNthOrderIso (α : Fin (n + 1) -> Type*) [forall i, LE (α i)] (p : Fin
 (n + 1)) : α p × (forall i, α (p.succAbove i)) ≃o forall i, α i where toEquiv
参数：α : Fin (n + 1) -> Type*；α i；p : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order isomorphism between tuples of length `n + 1` and pairs of an element and a
 tuple of length
`n` given by separating out the `p`-th element of the tuple.

This is `Fin.insertNth` as an `OrderIso`.
-/
def insertNthOrderIso (α : Fin (n + 1) → Type*) [∀ i, LE (α i)] (p : Fin (n + 1)) :
    α p × (∀ i, α (p.succAbove i)) ≃o ∀ i, α i where
  toEquiv := insertNthEquiv α p
  map_rel_iff' := by simp [Pi.le_def, Prod.le_def, p.forall_iff_succAbove]

set_option backward.isDefEq.respectTransparency false in
/-
**Fin.insertNthOrderIso_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (α : Fin (n + 1) → Type u_2) [inst : (i : Fin (n + 1)) → LE (α i
)],   Fin.insertNthOrderIso α 0 = Fin.consOrderIso α
参数：α : Fin (n + 1) → Type u_2；i : Fin (n + 1)；α i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNthEquiv_zero`：∀ {n : ℕ} (α : Fin (n + 1) → Type u_3), Fin.ins
ertNthEquiv α 0 = Fin.consEquiv α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RelIso.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → Prop}
 {s : β → β → Prop} (toEquiv toEquiv_1 : α ≃ β)   (e_toEquiv : toEquiv = toEquiv
_1) (map_r…
· 使用定理 `Fin.consEquiv_apply`：∀ {n : ℕ} (α : Fin (n + 1) → Type u_1) (f : α 0 × (
(i : Fin n) → α i.succ)) (i : Fin (n + 1)),   (Fin.consEquiv α) f i = Fin.cons f
.1 f.2 i
· 使用定理 `Fin.consOrderIso_apply`：∀ {n : ℕ} (α : Fin (n + 1) → Type u_2) [inst : (
i : Fin (n + 1)) → LE (α i)] (f : α 0 × ((i : Fin n) → α i.succ))   (i : Fin (n 
+ 1)), (Fin.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma insertNthOrderIso_zero (α : Fin (n + 1) → Type*) [∀ i, LE (α i)] :
    insertNthOrderIso α 0 = consOrderIso α := by ext; simp [insertNthOrderIso]

/-- Note this lemma can only be written about non-dependent tuples as `insertNth (last n) = snoc` is
not a definitional equality. -/
/-
**Fin.insertNthOrderIso_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ (n : ℕ) (α : Type u_2) [inst : LE α], Fin.insertNthOrderIso (fun x => α)
 (Fin.last n) = Fin.snocOrderIso fun x => α
参数：n : ℕ；α : Type u_2；fun x => α；Fin.last n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNthOrderIso_apply`：∀ {n : ℕ} (α : Fin (n + 1) → Type u_2) [ins
t : (i : Fin (n + 1)) → LE (α i)] (p : Fin (n + 1))   (f : α p × ((i : Fin n) → 
α (p.succAbove i)…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.insertNth_last'`：insertNth_last' (x : β) (p : Fin n -> β) : @insertN
th _ (fun _ => β) (last n) x p = snoc p x
· 使用定理 `Fin.snocOrderIso_apply`：∀ {n : ℕ} (α : Fin (n + 1) → Type u_2) [inst : (
i : Fin (n + 1)) → LE (α i)]   (f : α (Fin.last n) × ((i : Fin n) → α i.castSucc
)) (x : Fin …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Note this lemma can only be written about non-dependent tuples as `insertNth (la
st n) = snoc` is
not a definitional equality.
-/
@[simp] lemma insertNthOrderIso_last (n : ℕ) (α : Type*) [LE α] :
    insertNthOrderIso (fun _ ↦ α) (last n) = snocOrderIso (fun _ ↦ α) := by ext; simp

end Fin

/-- `Fin.succAbove` as an order isomorphism between `Fin n` and `{x : Fin (n + 1) // x ≠ p}`. -/
/-
**finSuccAboveOrderIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finSuccAboveOrderIso (p : Fin (n + 1)) : Fin n ≃o { x : Fin (n + 1) // x !
= p } where __
参数：p : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fin.succAbove` as an order isomorphism between `Fin n` and `{x : Fin (n + 1) //
 x ≠ p}`.
-/
def finSuccAboveOrderIso (p : Fin (n + 1)) : Fin n ≃o { x : Fin (n + 1) // x ≠ p } where
  __ := finSuccAboveEquiv p
  map_rel_iff' := p.succAboveOrderEmb.map_rel_iff'
/-
**finSuccAboveOrderIso_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finSuccAboveOrderIso_apply (p : Fin (n + 1)) (i : Fin n) : finSuccAboveOrd
erIso p i = ⟨p.succAbove i, p.succAbove_ne i⟩
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finSuccAboveOrderIso_apply (p : Fin (n + 1)) (i : Fin n) :
    finSuccAboveOrderIso p i = ⟨p.succAbove i, p.succAbove_ne i⟩ := rfl
/-
**finSuccAboveOrderIso_symm_apply_last** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finSuccAboveOrderIso_symm_apply_last (x : { x : Fin (n + 1) // x != Fin.la
st n }) : (finSuccAboveOrderIso (Fin.last n)).symm x = Fin.castLT x.1 (Fin.val_l
t_last x.2)
参数：x : { x : Fin (n + 1) // x != Fin.last n }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.val_lt_last`：∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ Fin.last n → ↑i < n
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.optionSubtype_apply_symm_apply`：optionSubtype_apply_symm_apply [De
cidableEq β] (x : β) (e : { e : Option α ≃ β // e none = x }) (b : { y : β // y 
!= x }) : ↑((optionSubtype…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.succAbove_last`：∀ {n : ℕ}, (Fin.last n).succAbove = Fin.castSucc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finSuccAboveOrderIso_symm_apply_last (x : { x : Fin (n + 1) // x ≠ Fin.last n }) :
    (finSuccAboveOrderIso (Fin.last n)).symm x = Fin.castLT x.1 (Fin.val_lt_last x.2) := by
  rw [← Option.some_inj]
  simp [finSuccAboveOrderIso, finSuccAboveEquiv, OrderIso.symm]
/-
**finSuccAboveOrderIso_symm_apply_ne_last** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finSuccAboveOrderIso_symm_apply_ne_last {p : Fin (n + 1)} (h : p != Fin.la
st n) (x : { x : Fin (n + 1) // x != p }) : (finSuccAboveEquiv p).symm x = (p.ca
stLT (Fin.val_lt_last h)).predAbove x
参数：n + 1；h : p != Fin.last n；x : { x : Fin (n + 1) // x != p }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Fin.val_lt_last`：∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ Fin.last n → ↑i < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.optionSubtype_apply_symm_apply`：optionSubtype_apply_symm_apply [De
cidableEq β] (x : β) (e : { e : Option α ≃ β // e none = x }) (b : { y : β // y 
!= x }) : ↑((optionSubtype…
· 使用定理 `finSuccEquiv'_ne_last_apply`：∀ {n : ℕ} {i j : Fin (n + 1)} (hi : i ≠ Fin
.last n), j ≠ i → (finSuccEquiv' i) j = some ((i.castLT ⋯).predAbove j)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma finSuccAboveOrderIso_symm_apply_ne_last {p : Fin (n + 1)} (h : p ≠ Fin.last n)
    (x : { x : Fin (n + 1) // x ≠ p }) :
    (finSuccAboveEquiv p).symm x = (p.castLT (Fin.val_lt_last h)).predAbove x := by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv, OrderIso.symm] using finSuccEquiv'_ne_last_apply h x.property

set_option backward.isDefEq.respectTransparency false in
/-- Promote a `Fin n` into a larger `Fin m`, as a subtype where the underlying
values are retained. This is the `OrderIso` version of `Fin.castLE`. -/
@[simps apply symm_apply]
/-
**Fin.castLEOrderIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fin.castLEOrderIso {n m : Nat} (h : n <= m) : Fin n ≃o { i : Fin m // (i :
 Nat) < n } where toFun i
参数：h : n <= m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote a `Fin n` into a larger `Fin m`, as a subtype where the underlying
values are retained. This is the `OrderIso` version of `Fin.castLE`.
-/
def Fin.castLEOrderIso {n m : ℕ} (h : n ≤ m) : Fin n ≃o { i : Fin m // (i : ℕ) < n } where
  toFun i := ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := by simp [(strictMono_castLE h).le_iff_le]
