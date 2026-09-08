/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Fin.Tuple
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Order.Fin.Tuple

/-!
# Collections of tuples of naturals with the same sum

This file generalizes `List.Nat.Antidiagonal n`, `Multiset.Nat.Antidiagonal n`, and
`Finset.Nat.Antidiagonal n` from the pair of elements `x : ℕ × ℕ` such that `n = x.1 + x.2`, to
the sequence of elements `x : Fin k → ℕ` such that `n = ∑ i, x i`.

## Main definitions

* `List.Nat.antidiagonalTuple`
* `Multiset.Nat.antidiagonalTuple`
* `Finset.Nat.antidiagonalTuple`

## Main results

* `antidiagonalTuple 2 n` is analogous to `antidiagonal n`:

  * `List.Nat.antidiagonalTuple_two`
  * `Multiset.Nat.antidiagonalTuple_two`
  * `Finset.Nat.antidiagonalTuple_two`

## Implementation notes

While we could implement this by filtering `(Fintype.PiFinset fun _ ↦ range (n + 1))` or similar,
this implementation would be much slower.

In the future, we could consider generalizing `Finset.Nat.antidiagonalTuple` further to
support finitely-supported functions, as in `Finset.finsuppAntidiag` from
`Mathlib/Algebra/Order/Antidiag/Finsupp.lean`.
-/

@[expose] public section


/-! ### Lists -/


namespace List.Nat

/-- `List.antidiagonalTuple k n` is a list of all `k`-tuples which sum to `n`.

This list contains no duplicates (`List.Nat.nodup_antidiagonalTuple`), and is sorted
lexicographically (`List.Nat.antidiagonalTuple_pairwise_pi_lex`), starting with `![0, ..., n]`
and ending with `![n, ..., 0]`.

```
#eval antidiagonalTuple 3 2
-- [![0, 0, 2], ![0, 1, 1], ![0, 2, 0], ![1, 0, 1], ![1, 1, 0], ![2, 0, 0]]
```
-/
/-
**List.Nat.antidiagonalTuple** 是 Mathlib 中的一个定义，位于命名空间 `List.Nat`。
形式化陈述：(k : ℕ) → ℕ → List (Fin k → ℕ)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`List.antidiagonalTuple k n` is a list of all `k`-tuples which sum to `n`.

This list contains no duplicates (`List.Nat.nodup_antidiagonalTuple`), and is so
rted
lexicographically (`List.Nat.antidiagonalTuple_pairwise_pi_lex`), starting with 
`![0, ..., n]`
and ending with `![n, ..., 0]`.

```
#eval antidiagonalTuple 3 2
-- [![0, 0, 2], ![0, 1, 1], ![0, 2, 0], ![1, 0, 1], ![1, 1, 0], ![2, 0, 0]]
```
-/
def antidiagonalTuple : ∀ k, ℕ → List (Fin k → ℕ)
  | 0, 0 => [![]]
  | 0, _ + 1 => []
  | k + 1, n =>
    (List.Nat.antidiagonal n).flatMap fun ni =>
      (antidiagonalTuple k ni.2).map fun x => Fin.cons ni.1 x

@[simp]
/-
**List.Nat.antidiagonalTuple_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `List.Nat`。
形式化陈述：antidiagonalTuple_zero_zero : antidiagonalTuple 0 0 = [![]]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antidiagonalTuple_zero_zero : antidiagonalTuple 0 0 = [![]] :=
  rfl

@[simp]
/-
**List.Nat.antidiagonalTuple_zero_succ** 是 Mathlib 中的一个定理，位于命名空间 `List.Nat`。
形式化陈述：antidiagonalTuple_zero_succ (n : Nat) : antidiagonalTuple 0 (n + 1) = []
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antidiagonalTuple_zero_succ (n : ℕ) : antidiagonalTuple 0 (n + 1) = [] :=
  rfl
/-
**List.Nat.mem_antidiagonalTuple** 是 Mathlib 中的一个定理，位于命名空间 `List.Nat`。
形式化陈述：mem_antidiagonalTuple {n : Nat} {k : Nat} {x : Fin k -> Nat} : x in antidi
agonalTuple k n ↔ ∑ i, x i = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Fin.sum_cons`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (x : M) 
(f : Fin n → M), ∑ i, Fin.cons x f i = x + ∑ i, f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Prod.mk_inj`：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ =
 a₂ ∧ b₁ = b₂
-/
theorem mem_antidiagonalTuple {n : ℕ} {k : ℕ} {x : Fin k → ℕ} :
    x ∈ antidiagonalTuple k n ↔ ∑ i, x i = n := by
  induction x using Fin.consInduction generalizing n with
  | elim0 =>
    cases n
    · decide
    · simp
  | cons x₀ x ih =>
    simp_rw [Fin.sum_cons, antidiagonalTuple, List.mem_flatMap, List.mem_map,
      List.Nat.mem_antidiagonal, Fin.cons_inj, exists_eq_right_right, ih,
      @eq_comm _ _ (Prod.snd _), and_comm (a := Prod.snd _ = _),
      ← Prod.mk_inj (a₁ := Prod.fst _), exists_eq_right]

/-- The antidiagonal of `n` does not contain duplicate entries. -/
/-
**List.Nat.nodup_antidiagonalTuple** 是 Mathlib 中的一个定理，位于命名空间 `List.Nat`。
形式化陈述：nodup_antidiagonalTuple (k n : Nat) : List.Nodup (antidiagonalTuple k n)
参数：k n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Nodup.map`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β}, Fu
nction.Injective f → l.Nodup → (List.map f l).Nodup
· 使用定理 `Fin.cons_right_injective`：cons_right_injective (x₀ : α 0) : Function.Inj
ective (cons x₀)
· 使用定理 `List.pairwise_singleton`：∀ {α : Type u_1} (R : α → α → Prop) (a : α), Li
st.Pairwise R [a]
· 使用定理 `List.Nat.antidiagonal_succ`：antidiagonal_succ {n : Nat} : antidiagonal (
n + 1) = (0, n + 1) :: (antidiagonal n).map (Prod.map Nat.succ id)
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Fin.cons_inj`：cons_inj {x₀ y₀ : α 0} {x y : forall i : Fin n, α i.succ} 
: cons x₀ x = cons y₀ y ↔ x₀ = y₀ ∧ x = y
· 使用定理 `List.Pairwise.map`：∀ {β : Type u_1} {α : Type u_2} {R : α → α → Prop} {l
 : List α} {S : β → β → Prop} (f : α → β),   (∀ (a b : α), R a b → S (f a) (f b)
) → Lis…
· 使用定理 `Nat.succ_inj`：∀ {a b : ℕ}, a.succ = b.succ ↔ a = b
· 使用定理 `Function.onFun.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β 
→ β → φ) (g : α → β) (x y : α),   Function.onFun f g x y = f (g x) (g y)
· 使用定理 `List.mem_map_of_mem`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {a : α
} {f : α → β}, a ∈ l → f a ∈ List.map f l

--- 原说明 ---
The antidiagonal of `n` does not contain duplicate entries.
-/
theorem nodup_antidiagonalTuple (k n : ℕ) : List.Nodup (antidiagonalTuple k n) := by
  induction k generalizing n with
  | zero => cases n <;> simp
  | succ k ih => ?_
  simp_rw [antidiagonalTuple, List.nodup_flatMap]
  constructor
  · intro i _
    exact (ih i.snd).map (Fin.cons_right_injective (α := fun _ => ℕ) i.fst)
  induction n with
  | zero => exact List.pairwise_singleton _ _
  | succ n n_ih =>
    rw [List.Nat.antidiagonal_succ]
    refine List.Pairwise.cons (fun a ha x hx₁ hx₂ => ?_) (n_ih.map _ fun a b h x hx₁ hx₂ => ?_)
    · rw [List.mem_map] at hx₁ hx₂ ha
      obtain ⟨⟨a, -, rfl⟩, ⟨x₁, -, rfl⟩, ⟨x₂, -, h⟩⟩ := ha, hx₁, hx₂
      rw [Fin.cons_inj] at h
      injection h.1
    · rw [List.mem_map] at hx₁ hx₂
      obtain ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, h₁₂⟩⟩ := hx₁, hx₂
      dsimp at h₁₂
      rw [Fin.cons_inj, Nat.succ_inj] at h₁₂
      obtain ⟨h₁₂, rfl⟩ := h₁₂
      rw [Function.onFun, h₁₂] at h
      exact h (List.mem_map_of_mem hx₁) (List.mem_map_of_mem hx₂)
/-
**List.Nat.antidiagonalTuple_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Nat`。
形式化陈述：∀ (k : ℕ), List.Nat.antidiagonalTuple k 0 = [0]
参数：k : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antidiagonalTuple_zero_right : ∀ k, antidiagonalTuple k 0 = [0]
  | 0 => (congr_arg fun x => [x]) <| Subsingleton.elim _ _
  | k + 1 => by
    rw [antidiagonalTuple, antidiagonal_zero, List.flatMap_singleton,
      antidiagonalTuple_zero_right k, List.map_singleton]
    exact congr_arg (fun x => [x]) Matrix.cons_zero_zero

@[simp]
/-
**List.Nat.antidiagonalTuple_one** 是 Mathlib 中的一个定理，位于命名空间 `List.Nat`。
形式化陈述：antidiagonalTuple_one (n : Nat) : antidiagonalTuple 1 n = [![n]]
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `List.flatMap_append`：∀ {α : Type u} {β : Type v} {xs ys : List α} {f : α
 → List β},   List.flatMap f (xs ++ ys) = List.flatMap f xs ++ List.flatMap f ys
· 使用定理 `List.flatMap_singleton`：∀ {α : Type u_1} {β : Type u_2} (f : α → List β)
 (x : α), List.flatMap f [x] = f x
· 使用定理 `List.flatMap_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α 
→ β) (g : β → List γ) (l : List α),   List.flatMap g (List.map f l) = List.flatM
ap (fu…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.nil_append`：∀ {α : Type u} (as : List α), [] ++ as = as
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.exists_eq_add_of_lt`：∀ {m n : ℕ}, m < n → ∃ k, n = m + k + 1
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `List.Nat.antidiagonalTuple_zero_succ`：antidiagonalTuple_zero_succ (n : N
at) : antidiagonalTuple 0 (n + 1) = []
-/
theorem antidiagonalTuple_one (n : ℕ) : antidiagonalTuple 1 n = [![n]] := by
  simp_rw [antidiagonalTuple, antidiagonal, List.range_succ, List.map_append, List.map_singleton,
    Nat.sub_self, List.flatMap_append, List.flatMap_singleton, List.flatMap_map]
  conv_rhs => rw [← List.nil_append [![n]]]
  congr 1
  simp_rw [List.flatMap_eq_nil_iff, List.mem_range, List.map_eq_nil_iff]
  intro x hx
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hx
  rw [add_assoc, add_tsub_cancel_left, antidiagonalTuple_zero_succ]
/-
**List.Nat.antidiagonalTuple_two** 是 Mathlib 中的一个定理，位于命名空间 `List.Nat`。
形式化陈述：antidiagonalTuple_two (n : Nat) : antidiagonalTuple 2 n = (antidiagonal n)
.map fun i => ![i.1, i.2]
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Nat.antidiagonalTuple.eq_3`：∀ (x k : ℕ),   List.Nat.antidiagonalTup
le k.succ x =     List.flatMap (fun ni => List.map (fun x => Fin.cons ni.1 x) (L
ist.Nat.antidiagonalT…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.Nat.antidiagonalTuple_one`：antidiagonalTuple_one (n : Nat) : antidi
agonalTuple 1 n = [![n]]
· 使用定理 `List.map_eq_flatMap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Li
st α}, List.map f l = List.flatMap (fun x => [f x]) l
-/
theorem antidiagonalTuple_two (n : ℕ) :
    antidiagonalTuple 2 n = (antidiagonal n).map fun i => ![i.1, i.2] := by
  rw [antidiagonalTuple]
  simp_rw [antidiagonalTuple_one, List.map_singleton]
  rw [List.map_eq_flatMap]
  rfl
/-
**List.Nat.antidiagonalTuple_pairwise_pi_lex** 是 Mathlib 中的一个定理，位于命名空间 `List.Nat
`。
形式化陈述：∀ (k n : ℕ), List.Pairwise (Pi.Lex (fun x1 x2 => x1 < x2) fun x x1 x2 => x
1 < x2) (List.Nat.antidiagonalTuple k n)
参数：k n : ℕ；Pi.Lex (fun x1 x2 => x1 < x2) fun x x1 x2 => x1 < x2；List.Nat.antidia
gonalTuple k n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antidiagonalTuple_pairwise_pi_lex :
    ∀ k n, (antidiagonalTuple k n).Pairwise (Pi.Lex (· < ·) @fun _ => (· < ·))
  | 0, 0 => List.pairwise_singleton _ _
  | 0, _ + 1 => List.Pairwise.nil
  | k + 1, n => by
    simp_rw [antidiagonalTuple, List.pairwise_flatMap, List.pairwise_map, List.mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    simp only [mem_antidiagonal, Prod.forall]
    simp only [Fin.pi_lex_lt_cons_cons, true_and, lt_self_iff_false,
      false_or]
    refine ⟨fun _ _ _ => antidiagonalTuple_pairwise_pi_lex k _, ?_⟩
    induction n with
    | zero =>
      rw [antidiagonal_zero]
      exact List.pairwise_singleton _ _
    | succ n n_ih =>
      simp
      grind

end List.Nat

/-! ### Multisets -/


namespace Multiset.Nat

/-- `Multiset.Nat.antidiagonalTuple k n` is a multiset of `k`-tuples summing to `n` -/
/-
**Multiset.Nat.antidiagonalTuple** 是 Mathlib 中的一个定义，位于命名空间 `Multiset.Nat`。
形式化陈述：antidiagonalTuple (k n : Nat) : Multiset (Fin k -> Nat)
参数：k n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiset.Nat.antidiagonalTuple k n` is a multiset of `k`-tuples summing to `n`
-/
def antidiagonalTuple (k n : ℕ) : Multiset (Fin k → ℕ) :=
  List.Nat.antidiagonalTuple k n

@[simp]
/-
**Multiset.Nat.antidiagonalTuple_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.N
at`。
形式化陈述：antidiagonalTuple_zero_zero : antidiagonalTuple 0 0 = {![]}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antidiagonalTuple_zero_zero : antidiagonalTuple 0 0 = {![]} :=
  rfl

@[simp]
/-
**Multiset.Nat.antidiagonalTuple_zero_succ** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.N
at`。
形式化陈述：antidiagonalTuple_zero_succ (n : Nat) : antidiagonalTuple 0 n.succ = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antidiagonalTuple_zero_succ (n : ℕ) : antidiagonalTuple 0 n.succ = 0 :=
  rfl
/-
**Multiset.Nat.mem_antidiagonalTuple** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nat`。
形式化陈述：mem_antidiagonalTuple {n : Nat} {k : Nat} {x : Fin k -> Nat} : x in antidi
agonalTuple k n ↔ ∑ i, x i = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nat.mem_antidiagonalTuple`：mem_antidiagonalTuple {n : Nat} {k : Nat
} {x : Fin k -> Nat} : x in antidiagonalTuple k n ↔ ∑ i, x i = n
-/
theorem mem_antidiagonalTuple {n : ℕ} {k : ℕ} {x : Fin k → ℕ} :
    x ∈ antidiagonalTuple k n ↔ ∑ i, x i = n :=
  List.Nat.mem_antidiagonalTuple
/-
**Multiset.Nat.nodup_antidiagonalTuple** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nat`。
形式化陈述：nodup_antidiagonalTuple (k n : Nat) : (antidiagonalTuple k n).Nodup
参数：k n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nat.nodup_antidiagonalTuple`：nodup_antidiagonalTuple (k n : Nat) : 
List.Nodup (antidiagonalTuple k n)
-/
theorem nodup_antidiagonalTuple (k n : ℕ) : (antidiagonalTuple k n).Nodup :=
  List.Nat.nodup_antidiagonalTuple _ _
/-
**Multiset.Nat.antidiagonalTuple_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.
Nat`。
形式化陈述：antidiagonalTuple_zero_right (k : Nat) : antidiagonalTuple k 0 = {0}
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.Nat.antidiagonalTuple_zero_right`：∀ (k : ℕ), List.Nat.antidiagonalT
uple k 0 = [0]
-/
theorem antidiagonalTuple_zero_right (k : ℕ) : antidiagonalTuple k 0 = {0} :=
  congr_arg _ (List.Nat.antidiagonalTuple_zero_right k)

@[simp]
/-
**Multiset.Nat.antidiagonalTuple_one** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nat`。
形式化陈述：antidiagonalTuple_one (n : Nat) : antidiagonalTuple 1 n = {![n]}
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.Nat.antidiagonalTuple_one`：antidiagonalTuple_one (n : Nat) : antidi
agonalTuple 1 n = [![n]]
-/
theorem antidiagonalTuple_one (n : ℕ) : antidiagonalTuple 1 n = {![n]} :=
  congr_arg _ (List.Nat.antidiagonalTuple_one n)
/-
**Multiset.Nat.antidiagonalTuple_two** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nat`。
形式化陈述：antidiagonalTuple_two (n : Nat) : antidiagonalTuple 2 n = (antidiagonal n)
.map fun i => ![i.1, i.2]
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.Nat.antidiagonalTuple_two`：antidiagonalTuple_two (n : Nat) : antidi
agonalTuple 2 n = (antidiagonal n).map fun i => ![i.1, i.2]
-/
theorem antidiagonalTuple_two (n : ℕ) :
    antidiagonalTuple 2 n = (antidiagonal n).map fun i => ![i.1, i.2] :=
  congr_arg _ (List.Nat.antidiagonalTuple_two n)

end Multiset.Nat

/-! ### Finsets -/


namespace Finset.Nat

/-- `Finset.Nat.antidiagonalTuple k n` is a finset of `k`-tuples summing to `n` -/
/-
**Finset.Nat.antidiagonalTuple** 是 Mathlib 中的一个定义，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonalTuple (k n : Nat) : Finset (Fin k -> Nat)
参数：k n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nat.nodup_antidiagonalTuple`：nodup_antidiagonalTuple (k n : Nat
) : (antidiagonalTuple k n).Nodup

--- 原说明 ---
`Finset.Nat.antidiagonalTuple k n` is a finset of `k`-tuples summing to `n`
-/
def antidiagonalTuple (k n : ℕ) : Finset (Fin k → ℕ) :=
  ⟨Multiset.Nat.antidiagonalTuple k n, Multiset.Nat.nodup_antidiagonalTuple k n⟩

@[simp]
/-
**Finset.Nat.antidiagonalTuple_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonalTuple_zero_zero : antidiagonalTuple 0 0 = {![]}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antidiagonalTuple_zero_zero : antidiagonalTuple 0 0 = {![]} :=
  rfl

@[simp]
/-
**Finset.Nat.antidiagonalTuple_zero_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonalTuple_zero_succ (n : Nat) : antidiagonalTuple 0 n.succ = ∅
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antidiagonalTuple_zero_succ (n : ℕ) : antidiagonalTuple 0 n.succ = ∅ :=
  rfl
/-
**Finset.Nat.mem_antidiagonalTuple** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：mem_antidiagonalTuple {n : Nat} {k : Nat} {x : Fin k -> Nat} : x in antidi
agonalTuple k n ↔ ∑ i, x i = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nat.mem_antidiagonalTuple`：mem_antidiagonalTuple {n : Nat} {k : Nat
} {x : Fin k -> Nat} : x in antidiagonalTuple k n ↔ ∑ i, x i = n
-/
theorem mem_antidiagonalTuple {n : ℕ} {k : ℕ} {x : Fin k → ℕ} :
    x ∈ antidiagonalTuple k n ↔ ∑ i, x i = n :=
  List.Nat.mem_antidiagonalTuple
/-
**Finset.Nat.antidiagonalTuple_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`
。
形式化陈述：antidiagonalTuple_zero_right (k : Nat) : antidiagonalTuple k 0 = {0}
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.Nat.antidiagonalTuple_zero_right`：antidiagonalTuple_zero_right 
(k : Nat) : antidiagonalTuple k 0 = {0}
-/
theorem antidiagonalTuple_zero_right (k : ℕ) : antidiagonalTuple k 0 = {0} :=
  Finset.eq_of_veq (Multiset.Nat.antidiagonalTuple_zero_right k)

@[simp]
/-
**Finset.Nat.antidiagonalTuple_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonalTuple_one (n : Nat) : antidiagonalTuple 1 n = {![n]}
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.Nat.antidiagonalTuple_one`：antidiagonalTuple_one (n : Nat) : an
tidiagonalTuple 1 n = {![n]}
-/
theorem antidiagonalTuple_one (n : ℕ) : antidiagonalTuple 1 n = {![n]} :=
  Finset.eq_of_veq (Multiset.Nat.antidiagonalTuple_one n)
/-
**Finset.Nat.antidiagonalTuple_two** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonalTuple_two (n : Nat) : antidiagonalTuple 2 n = (antidiagonal n)
.map (piFinTwoEquiv fun _ => Nat).symm.toEmbedding
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Multiset.Nat.antidiagonalTuple_two`：antidiagonalTuple_two (n : Nat) : an
tidiagonalTuple 2 n = (antidiagonal n).map fun i => ![i.1, i.2]
-/
theorem antidiagonalTuple_two (n : ℕ) :
    antidiagonalTuple 2 n = (antidiagonal n).map (piFinTwoEquiv fun _ => ℕ).symm.toEmbedding :=
  Finset.eq_of_veq (Multiset.Nat.antidiagonalTuple_two n)

section EquivProd

/-- The disjoint union of antidiagonal tuples `Σ n, antidiagonalTuple k n` is equivalent to the
`k`-tuple `Fin k → ℕ`. This is such an equivalence, obtained by mapping `(n, x)` to `x`.

This is the tuple version of `Finset..HasAntidiagonal.sigmaAntidiagonalEquivProd`. -/
@[simps]
/-
**Finset.Nat.sigmaAntidiagonalTupleEquivTuple** 是 Mathlib 中的一个定义，位于命名空间 `Finset.
Nat`。
形式化陈述：sigmaAntidiagonalTupleEquivTuple (k : Nat) : (Σ n, antidiagonalTuple k n) 
≃ (Fin k -> Nat) where toFun x
参数：k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The disjoint union of antidiagonal tuples `Σ n, antidiagonalTuple k n` is equiva
lent to the
`k`-tuple `Fin k → ℕ`. This is such an equivalence, obtained by mapping `(n, x)`
 to `x`.

This is the tuple version of `Finset..HasAntidiagonal.sigmaAntidiagonalEquivProd
`.
-/
def sigmaAntidiagonalTupleEquivTuple (k : ℕ) : (Σ n, antidiagonalTuple k n) ≃ (Fin k → ℕ) where
  toFun x := x.2
  invFun x := ⟨∑ i, x i, x, mem_antidiagonalTuple.mpr rfl⟩
  left_inv := fun ⟨_, _, h⟩ => Sigma.subtype_ext (mem_antidiagonalTuple.mp h) rfl

end EquivProd

end Finset.Nat

