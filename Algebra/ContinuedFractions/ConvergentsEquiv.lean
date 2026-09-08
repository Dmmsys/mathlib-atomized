/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Algebra.ContinuedFractions.TerminatedStable
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# Equivalence of Recursive and Direct Computations of Convergents of Generalized Continued Fractions

## Summary

We show the equivalence of two computations of convergents (recurrence relation (`convs`) vs.
direct evaluation (`convs'`)) for generalized continued fractions
(`GenContFract`s) on linear ordered fields. We follow the proof from
[hardy2008introduction], Chapter 10. Here's a sketch:

Let `c` be a continued fraction `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`, visually:
$$
  c = h + \dfrac{a_0}
                {b_0 + \dfrac{a_1}
                             {b_1 + \dfrac{a_2}
                                          {b_2 + \dfrac{a_3}
                                                       {b_3 + \dots}}}}
$$
One can compute the convergents of `c` in two ways:
1. Directly evaluating the fraction described by `c` up to a given `n` (`convs'`)
2. Using the recurrence (`convs`):
  - `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
  - `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

To show the equivalence of the computations in the main theorem of this file
`convs_eq_convs'`, we proceed by induction. The case `n = 0` is trivial.

For `n + 1`, we first "squash" the `n + 1`th position of `c` into the `n`th position to obtain
another continued fraction
  `c' := [h; (a₀, b₀),..., (aₙ-₁, bₙ-₁), (aₙ, bₙ + aₙ₊₁ / bₙ₊₁), (aₙ₊₁, bₙ₊₁),...]`.
This squashing process is formalised in section `Squash`. Note that directly evaluating `c` up to
position `n + 1` is equal to evaluating `c'` up to `n`. This is shown in lemma
`succ_nth_conv'_eq_squashGCF_nth_conv'`.

By the inductive hypothesis, the two computations for the `n`th convergent of `c` coincide.
So all that is left to show is that the recurrence relation for `c` at `n + 1` and `c'` at
`n` coincide. This can be shown by another induction.
The corresponding lemma in this file is `succ_nth_conv_eq_squashGCF_nth_conv`.

## Main Theorems

- `GenContFract.convs_eq_convs'` shows the equivalence under a strict positivity restriction
  on the sequence.
- `ContFract.convs_eq_convs'` shows the equivalence for regular continued fractions.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction
- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]

## Tags

fractions, recurrence, equivalence
-/

@[expose] public section


variable {K : Type*} {n : ℕ}

namespace GenContFract

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

section Squash

/-!
We will show the equivalence of the computations by induction. To make the induction work, we need
to be able to *squash* the nth and (n + 1)th value of a sequence. This squashing itself and the
lemmas about it are not very interesting. As a reader, you hence might want to skip this section.
-/


section WithDivisionRing

variable [DivisionRing K]

/-- Given a sequence of `GenContFract.Pair`s `s = [(a₀, b₀), (a₁, b₁), ...]`, `squashSeq s n`
combines `⟨aₙ, bₙ⟩` and `⟨aₙ₊₁, bₙ₊₁⟩` at position `n` to `⟨aₙ, bₙ + aₙ₊₁ / bₙ₊₁⟩`. For example,
`squashSeq s 0 = [(a₀, b₀ + a₁ / b₁), (a₁, b₁),...]`.
If `s.TerminatedAt (n + 1)`, then `squashSeq s n = s`.
-/
/-
**GenContFract.squashSeq** 是 Mathlib 中的一个定义，位于命名空间 `GenContFract`。
形式化陈述：squashSeq (s : Stream'.Seq <| Pair K) (n : Nat) : Stream'.Seq (Pair K)
参数：s : Stream'.Seq <| Pair K；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sequence of `GenContFract.Pair`s `s = [(a₀, b₀), (a₁, b₁), ...]`, `squas
hSeq s n`
combines `⟨aₙ, bₙ⟩` and `⟨aₙ₊₁, bₙ₊₁⟩` at position `n` to `⟨aₙ, bₙ + aₙ₊₁ / bₙ₊₁
⟩`. For example,
`squashSeq s 0 = [(a₀, b₀ + a₁ / b₁), (a₁, b₁),...]`.
If `s.TerminatedAt (n + 1)`, then `squashSeq s n = s`.
-/
def squashSeq (s : Stream'.Seq <| Pair K) (n : ℕ) : Stream'.Seq (Pair K) :=
  match Prod.mk (s.get? n) (s.get? (n + 1)) with
  | ⟨some gp_n, some gp_succ_n⟩ =>
    Stream'.Seq.nats.zipWith
      -- return the squashed value at position `n`; otherwise, do nothing.
      (fun n' gp => if n' = n then ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ else gp) s
  | _ => s

/-! We now prove some simple lemmas about the squashed sequence -/


/-- If the sequence already terminated at position `n + 1`, nothing gets squashed. -/
/-
**GenContFract.squashSeq_eq_self_of_terminated** 是 Mathlib 中的一个定理，位于命名空间 `GenCon
tFract`。
形式化陈述：squashSeq_eq_self_of_terminated (terminatedAt_succ_n : s.TerminatedAt (n +
 1)) : squashSeq s n = s
参数：terminatedAt_succ_n : s.TerminatedAt (n + 1)。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sequence already terminated at position `n + 1`, nothing gets squashed.
-/
theorem squashSeq_eq_self_of_terminated (terminatedAt_succ_n : s.TerminatedAt (n + 1)) :
    squashSeq s n = s := by
  change s.get? (n + 1) = none at terminatedAt_succ_n
  cases s_nth_eq : s.get? n <;> simp only [*, squashSeq]

/-- If the sequence has not terminated before position `n + 1`, the value at `n + 1` gets
squashed into position `n`. -/
/-
**GenContFract.squashSeq_nth_of_not_terminated** 是 Mathlib 中的一个定理，位于命名空间 `GenCon
tFract`。
形式化陈述：squashSeq_nth_of_not_terminated {gp_n gp_succ_n : Pair K} (s_nth_eq : s.ge
t? n = some gp_n) (s_succ_nth_eq : s.get? (n + 1) = some gp_succ_n) : (squashSeq
 s n).get? n = some ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩
参数：s_nth_eq : s.get? n = some gp_n；s_succ_nth_eq : s.get? (n + 1) = some gp_succ
_n。
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
· 使用定理 `Option.map₂_coe_right`：map₂_coe_right (f : α -> β -> γ) (a : Option α) (
b : β) : map₂ f a b = a.map fun a => f a b
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the sequence has not terminated before position `n + 1`, the value at `n + 1`
 gets
squashed into position `n`.
-/
theorem squashSeq_nth_of_not_terminated {gp_n gp_succ_n : Pair K} (s_nth_eq : s.get? n = some gp_n)
    (s_succ_nth_eq : s.get? (n + 1) = some gp_succ_n) :
    (squashSeq s n).get? n = some ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ := by
  simp [*, squashSeq]

/-- The values before the squashed position stay the same. -/
/-
**GenContFract.squashSeq_nth_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：squashSeq_nth_of_lt {m : Nat} (m_lt_n : m < n) : (squashSeq s n).get? m = 
s.get? m
参数：m_lt_n : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.squashSeq_eq_self_of_terminated`：squashSeq_eq_self_of_termi
nated (terminatedAt_succ_n : s.TerminatedAt (n + 1)) : squashSeq s n = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Stream'.Seq.ge_stable`：ge_stable (s : Seq α) {aₙ : α} {n m : Nat} (m_le_
n : m <= n) (s_nth_eq_some : s.get? n = some aₙ) : exists aₘ : α, s.get? m = som
e aₘ
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Option.map_id_fun'`：∀ {α : Type u}, (Option.map fun a => a) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The values before the squashed position stay the same.
-/
theorem squashSeq_nth_of_lt {m : ℕ} (m_lt_n : m < n) : (squashSeq s n).get? m = s.get? m := by
  cases s_succ_nth_eq : s.get? (n + 1) with
  | none => rw [squashSeq_eq_self_of_terminated s_succ_nth_eq]
  | some =>
    obtain ⟨gp_n, s_nth_eq⟩ : ∃ gp_n, s.get? n = some gp_n :=
      s.ge_stable n.le_succ s_succ_nth_eq
    simp [*, squashSeq, m_lt_n.ne]

/-- Squashing at position `n + 1` and taking the tail is the same as squashing the tail of the
sequence at position `n`. -/
/-
**GenContFract.squashSeq_succ_n_tail_eq_squashSeq_tail_n** 是 Mathlib 中的一个定理，位于命名
空间 `GenContFract`。
形式化陈述：squashSeq_succ_n_tail_eq_squashSeq_tail_n : (squashSeq s (n + 1)).tail = s
quashSeq s.tail n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Stream'.Seq.ge_stable`：ge_stable (s : Seq α) {aₙ : α} {n m : Nat} (m_le_
n : m <= n) (s_nth_eq_some : s.get? n = some aₙ) : exists aₘ : α, s.get? m = som
e aₘ
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Stream'.Seq.ext`：∀ {α : Type u} {s t : Stream'.Seq α}, (∀ (n : ℕ), s.get
? n = t.get? n) → s = t
· 使用定理 `Decidable.em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
· 使用定理 `Option.map₂_coe_right`：map₂_coe_right (f : α -> β -> γ) (a : Option α) (
b : β) : map₂ f a b = a.map fun a => f a b
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Option.map₂_none_right`：map₂_none_right (f : α -> β -> γ) (a : Option α)
 : map₂ f a none = none
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
Squashing at position `n + 1` and taking the tail is the same as squashing the t
ail of the
sequence at position `n`.
-/
theorem squashSeq_succ_n_tail_eq_squashSeq_tail_n :
    (squashSeq s (n + 1)).tail = squashSeq s.tail n := by
  cases s_succ_succ_nth_eq : s.get? (n + 2) with
  | none =>
    cases s_succ_nth_eq : s.get? (n + 1) <;>
      simp only [squashSeq, Stream'.Seq.get?_tail, s_succ_nth_eq, s_succ_succ_nth_eq]
  | some gp_succ_succ_n =>
    obtain ⟨gp_succ_n, s_succ_nth_eq⟩ : ∃ gp_succ_n, s.get? (n + 1) = some gp_succ_n :=
      s.ge_stable (n + 1).le_succ s_succ_succ_nth_eq
    -- apply extensionality with `m` and continue by cases `m = n`.
    ext1 m
    rcases Decidable.em (m = n) with m_eq_n | m_ne_n
    · simp [*, squashSeq]
    · cases s_succ_mth_eq : s.get? (m + 1)
      · simp only [*, squashSeq, Stream'.Seq.get?_tail, Stream'.Seq.get?_zipWith,
          Option.map₂_none_right]
      · simp [*, squashSeq]

/-- The auxiliary function `convs'Aux` returns the same value for a sequence and the
corresponding squashed sequence at the squashed position. -/
/-
**GenContFract.succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq** 是 Mathlib
 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：∀ {K : Type u_1} {n : ℕ} {s : Stream'.Seq (GenContFract.Pair K)} [inst : D
ivisionRing K],   GenContFract.convs'Aux s (n + 2) = GenContFract.convs'Aux (Gen
ContFract.squashSeq s n) (n + 1)
参数：GenContFract.Pair K；n + 2；GenContFract.squashSeq s n；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.squashSeq_eq_self_of_terminated`：squashSeq_eq_self_of_termi
nated (terminatedAt_succ_n : s.TerminatedAt (n + 1)) : squashSeq s n = s
· 使用定理 `GenContFract.convs'Aux_stable_step_of_terminated`：∀ {K : Type u_1} {n : 
ℕ} [inst : DivisionRing K] {s : Stream'.Seq (GenContFract.Pair K)},   s.Terminat
edAt n → GenContFract.convs'Aux s (n +…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Stream'.Seq.ge_stable`：ge_stable (s : Seq α) {aₙ : α} {n m : Nat} (m_le_
n : m <= n) (s_nth_eq_some : s.get? n = some aₙ) : exists aₘ : α, s.get? m = som
e aₘ
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `GenContFract.squashSeq_nth_of_not_terminated`：squashSeq_nth_of_not_termi
nated {gp_n gp_succ_n : Pair K} (s_nth_eq : s.get? n = some gp_n) (s_succ_nth_eq
 : s.get? (n + 1) = some gp_succ_n…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `GenContFract.squashSeq_nth_of_lt`：squashSeq_nth_of_lt {m : Nat} (m_lt_n 
: m < n) : (squashSeq s n).get? m = s.get? m
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `GenContFract.squashSeq_succ_n_tail_eq_squashSeq_tail_n`：squashSeq_succ_n
_tail_eq_squashSeq_tail_n : (squashSeq s (n + 1)).tail = squashSeq s.tail n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
The auxiliary function `convs'Aux` returns the same value for a sequence and the
corresponding squashed sequence at the squashed position.
-/
theorem succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq :
    convs'Aux s (n + 2) = convs'Aux (squashSeq s n) (n + 1) := by
  cases s_succ_nth_eq : s.get? <| n + 1 with
  | none =>
    rw [squashSeq_eq_self_of_terminated s_succ_nth_eq,
      convs'Aux_stable_step_of_terminated s_succ_nth_eq]
  | some gp_succ_n =>
    induction n generalizing s gp_succ_n with
    | zero =>
      obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head :=
        s.ge_stable zero_le_one s_succ_nth_eq
      have : (squashSeq s 0).head = some ⟨gp_head.a, gp_head.b + gp_succ_n.a / gp_succ_n.b⟩ :=
        squashSeq_nth_of_not_terminated s_head_eq s_succ_nth_eq
      simp_all [convs'Aux, Stream'.Seq.head, Stream'.Seq.get?_tail]
    | succ m IH =>
      obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head :=
        s.ge_stable (m + 2).zero_le s_succ_nth_eq
      suffices
        gp_head.a / (gp_head.b + convs'Aux s.tail (m + 2)) =
          convs'Aux (squashSeq s (m + 1)) (m + 2)
        by simpa only [convs'Aux, s_head_eq]
      have : (squashSeq s (m + 1)).head = some gp_head :=
        (squashSeq_nth_of_lt m.succ_pos).trans s_head_eq
      simp_all [convs'Aux, squashSeq_succ_n_tail_eq_squashSeq_tail_n]

/-! Let us now lift the squashing operation to gcfs. -/


/-- Given a gcf `g = [h; (a₀, b₀), (a₁, b₁), ...]`, we have
- `squashGCF g 0 = [h + a₀ / b₀; (a₁, b₁), ...]`,
- `squashGCF g (n + 1) = ⟨g.h, squashSeq g.s n⟩`
-/
/-
**GenContFract.squashGCF** 是 Mathlib 中的一个定义，位于命名空间 `GenContFract`。
形式化陈述：{K : Type u_1} → [DivisionRing K] → GenContFract K → ℕ → GenContFract K
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a gcf `g = [h; (a₀, b₀), (a₁, b₁), ...]`, we have
- `squashGCF g 0 = [h + a₀ / b₀; (a₁, b₁), ...]`,
- `squashGCF g (n + 1) = ⟨g.h, squashSeq g.s n⟩`
-/
def squashGCF (g : GenContFract K) : ℕ → GenContFract K
  | 0 =>
    match g.s.get? 0 with
    | none => g
    | some gp => ⟨g.h + gp.a / gp.b, g.s⟩
  | n + 1 => ⟨g.h, squashSeq g.s n⟩

/-! Again, we derive some simple lemmas that are not really of interest. This time for the
squashed gcf. -/


/-- If the gcf already terminated at position `n`, nothing gets squashed. -/
/-
**GenContFract.squashGCF_eq_self_of_terminated** 是 Mathlib 中的一个定理，位于命名空间 `GenCon
tFract`。
形式化陈述：squashGCF_eq_self_of_terminated (terminatedAt_n : TerminatedAt g n) : squa
shGCF g n = g
参数：terminatedAt_n : TerminatedAt g n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GenContFract.mk.injEq`：∀ {α : Type u_1} (h : α) (s : Stream'.Seq (GenCon
tFract.Pair α)) (h_1 : α) (s_1 : Stream'.Seq (GenContFract.Pair α)),   ({ h := h
, s := s } …
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `GenContFract.squashSeq_eq_self_of_terminated`：squashSeq_eq_self_of_termi
nated (terminatedAt_succ_n : s.TerminatedAt (n + 1)) : squashSeq s n = s

--- 原说明 ---
If the gcf already terminated at position `n`, nothing gets squashed.
-/
theorem squashGCF_eq_self_of_terminated (terminatedAt_n : TerminatedAt g n) :
    squashGCF g n = g := by
  cases n with
  | zero =>
    change g.s.get? 0 = none at terminatedAt_n
    simp only [squashGCF, terminatedAt_n]
  | succ =>
    cases g
    simp only [squashGCF, mk.injEq, true_and]
    exact squashSeq_eq_self_of_terminated terminatedAt_n

/-- The values before the squashed position stay the same. -/
/-
**GenContFract.squashGCF_nth_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：squashGCF_nth_of_lt {m : Nat} (m_lt_n : m < n) : (squashGCF g (n + 1)).s.g
et? m = g.s.get? m
参数：m_lt_n : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.squashSeq_nth_of_lt`：squashSeq_nth_of_lt {m : Nat} (m_lt_n 
: m < n) : (squashSeq s n).get? m = s.get? m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The values before the squashed position stay the same.
-/
theorem squashGCF_nth_of_lt {m : ℕ} (m_lt_n : m < n) :
    (squashGCF g (n + 1)).s.get? m = g.s.get? m := by
  simp only [squashGCF, squashSeq_nth_of_lt m_lt_n]

/-- `convs'` returns the same value for a gcf and the corresponding squashed gcf at the
squashed position. -/
/-
**GenContFract.succ_nth_conv'_eq_squashGCF_nth_conv'** 是 Mathlib 中的一个定理，位于命名空间 `
GenContFract`。
形式化陈述：∀ {K : Type u_1} {n : ℕ} {g : GenContFract K} [inst : DivisionRing K], g.c
onvs' (n + 1) = (g.squashGCF n).convs' n
参数：n + 1；g.squashGCF n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GenContFract.succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq`：∀ {K
 : Type u_1} {n : ℕ} {s : Stream'.Seq (GenContFract.Pair K)} [inst : DivisionRin
g K],   GenContFract.convs'Aux s (n + 2) = GenContFract.…

--- 原说明 ---
`convs'` returns the same value for a gcf and the corresponding squashed gcf at 
the
squashed position.
-/
theorem succ_nth_conv'_eq_squashGCF_nth_conv' :
    g.convs' (n + 1) = (squashGCF g n).convs' n := by
  cases n with
  | zero =>
    cases g_s_head_eq : g.s.get? 0 <;>
      simp [g_s_head_eq, squashGCF, convs', convs'Aux, Stream'.Seq.head]
  | succ =>
    simp only [succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq, convs',
      squashGCF]

/-- The auxiliary continuants before the squashed position stay the same. -/
/-
**GenContFract.contsAux_eq_contsAux_squashGCF_of_le** 是 Mathlib 中的一个定理，位于命名空间 `G
enContFract`。
形式化陈述：contsAux_eq_contsAux_squashGCF_of_le {m : Nat} : m <= n -> contsAux g m = 
(squashGCF g n).contsAux m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Nat.not_succ_le_zero`：∀ (n : ℕ), n.succ ≤ 0 → False
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `GenContFract.squashGCF_nth_of_lt`：squashGCF_nth_of_lt {m : Nat} (m_lt_n 
: m < n) : (squashGCF g (n + 1)).s.get? m = g.s.get? m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_lt_succ_iff`：∀ {a b : ℕ}, a.succ < b.succ ↔ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The auxiliary continuants before the squashed position stay the same.
-/
theorem contsAux_eq_contsAux_squashGCF_of_le {m : ℕ} :
    m ≤ n → contsAux g m = (squashGCF g n).contsAux m :=
  Nat.strong_induction_on m
    (by
      clear m
      intro m IH m_le_n
      rcases m with - | m'
      · rfl
      · rcases n with - | n'
        · exact (m'.not_succ_le_zero m_le_n).elim
        -- 1 ≰ 0
        · rcases m' with - | m''
          · rfl
          · -- get some inequalities to instantiate the IH for m'' and m'' + 1
            have m'_lt_n : m'' + 1 < n' + 1 := m_le_n
            have succ_m''th_contsAux_eq := IH (m'' + 1) (lt_add_one (m'' + 1)) m'_lt_n.le
            have : m'' < m'' + 2 := lt_add_of_pos_right m'' zero_lt_two
            have m''th_contsAux_eq := IH m'' this (le_trans this.le m_le_n)
            have : (squashGCF g (n' + 1)).s.get? m'' = g.s.get? m'' :=
              squashGCF_nth_of_lt (Nat.succ_lt_succ_iff.mp m'_lt_n)
            simp [contsAux, succ_m''th_contsAux_eq, m''th_contsAux_eq, this])

end WithDivisionRing

/-- The convergents coincide in the expected way at the squashed position if the partial denominator
at the squashed position is not zero. -/
/-
**GenContFract.succ_nth_conv_eq_squashGCF_nth_conv** 是 Mathlib 中的一个定理，位于命名空间 `Ge
nContFract`。
形式化陈述：succ_nth_conv_eq_squashGCF_nth_conv [Field K] (nth_partDen_ne_zero : foral
l {b : K}, g.partDens.get? n = some b -> b != 0) : g.convs (n + 1) = (squashGCF 
g n).convs n
参数：nth_partDen_ne_zero : forall {b : K}, g.partDens.get? n = some b -> b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
· 使用定理 `GenContFract.squashGCF_eq_self_of_terminated`：squashGCF_eq_self_of_termi
nated (terminatedAt_n : TerminatedAt g n) : squashGCF g n = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.convs_stable_of_terminated`：convs_stable_of_terminated (n_l
e_m : n <= m) (terminatedAt_n : g.TerminatedAt n) : g.convs m = g.convs n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.ne_none_iff_exists'`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ 
∃ x, o = some x
· 使用定理 `GenContFract.partDen_eq_s_b`：partDen_eq_s_b {gp : Pair α} (s_nth_eq : g.
s.get? n = some gp) : g.partDens.get? n = some gp.b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `GenContFract.conts_recurrenceAux`：conts_recurrenceAux {gp ppred pred : P
air K} (nth_s_eq : g.s.get? n = some gp) (nth_contsAux_eq : g.contsAux n = ppred
) (succ_nth_contsAux_e…
· 使用定理 `GenContFract.zeroth_contAux_eq_one_zero`：zeroth_contAux_eq_one_zero : g.
contsAux 0 = ⟨1, 0⟩
· 使用定理 `GenContFract.first_contAux_eq_h_one`：first_contAux_eq_h_one : g.contsAux
 1 = ⟨g.h, 1⟩
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Stream'.Seq.ge_stable`：ge_stable (s : Seq α) {aₙ : α} {n m : Nat} (m_le_
n : m <= n) (s_nth_eq_some : s.get? n = some aₙ) : exists aₘ : α, s.get? m = som
e aₘ
· 使用定理 `GenContFract.squashSeq_nth_of_not_terminated`：squashSeq_nth_of_not_termi
nated {gp_n gp_succ_n : Pair K} (s_nth_eq : s.get? n = some gp_n) (s_succ_nth_eq
 : s.get? (n + 1) = some gp_succ_n…
· 使用定理 `GenContFract.conv_eq_conts_a_div_conts_b`：conv_eq_conts_a_div_conts_b : 
g.convs n = (g.conts n).a / (g.conts n).b
· 使用定理 `GenContFract.contsAux_recurrence`：contsAux_recurrence {gp ppred pred : P
air K} (nth_s_eq : g.s.get? n = some gp) (nth_contsAux_eq : g.contsAux n = ppred
) (succ_nth_contsAux_e…
· 使用定理 `GenContFract.contsAux_eq_contsAux_squashGCF_of_le`：contsAux_eq_contsAux_
squashGCF_of_le {m : Nat} : m <= n -> contsAux g m = (squashGCF g n).contsAux m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The convergents coincide in the expected way at the squashed position if the par
tial denominator
at the squashed position is not zero.
-/
theorem succ_nth_conv_eq_squashGCF_nth_conv [Field K]
    (nth_partDen_ne_zero : ∀ {b : K}, g.partDens.get? n = some b → b ≠ 0) :
    g.convs (n + 1) = (squashGCF g n).convs n := by
  rcases Decidable.em (g.TerminatedAt n) with terminatedAt_n | not_terminatedAt_n
  · have : squashGCF g n = g := squashGCF_eq_self_of_terminated terminatedAt_n
    simp only [this, convs_stable_of_terminated n.le_succ terminatedAt_n]
  · obtain ⟨⟨a, b⟩, s_nth_eq⟩ : ∃ gp_n, g.s.get? n = some gp_n :=
      Option.ne_none_iff_exists'.mp not_terminatedAt_n
    have b_ne_zero : b ≠ 0 := nth_partDen_ne_zero (partDen_eq_s_b s_nth_eq)
    cases n with
    | zero =>
      suffices (b * g.h + a) / b = g.h + a / b by
        simpa [squashGCF, s_nth_eq, conv_eq_conts_a_div_conts_b,
          conts_recurrenceAux s_nth_eq zeroth_contAux_eq_one_zero first_contAux_eq_h_one]
      grind
    | succ n' =>
      obtain ⟨⟨pa, pb⟩, s_n'th_eq⟩ : ∃ gp_n', g.s.get? n' = some gp_n' :=
        g.s.ge_stable n'.le_succ s_nth_eq
      -- Notations
      let g' := squashGCF g (n' + 1)
      set pred_conts := g.contsAux (n' + 1) with succ_n'th_contsAux_eq
      set ppred_conts := g.contsAux n' with n'th_contsAux_eq
      let pA := pred_conts.a
      let pB := pred_conts.b
      let ppA := ppred_conts.a
      let ppB := ppred_conts.b
      set pred_conts' := g'.contsAux (n' + 1) with succ_n'th_contsAux_eq'
      set ppred_conts' := g'.contsAux n' with n'th_contsAux_eq'
      let pA' := pred_conts'.a
      let pB' := pred_conts'.b
      let ppA' := ppred_conts'.a
      let ppB' := ppred_conts'.b
      -- first compute the convergent of the squashed gcf
      have : g'.convs (n' + 1) =
          ((pb + a / b) * pA' + pa * ppA') / ((pb + a / b) * pB' + pa * ppB') := by
        have : g'.s.get? n' = some ⟨pa, pb + a / b⟩ :=
          squashSeq_nth_of_not_terminated s_n'th_eq s_nth_eq
        rw [conv_eq_conts_a_div_conts_b,
          conts_recurrenceAux this n'th_contsAux_eq'.symm succ_n'th_contsAux_eq'.symm]
      rw [this]
      -- then compute the convergent of the original gcf by recursively unfolding the continuants
      -- computation twice
      have : g.convs (n' + 2) =
          (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB) := by
        -- use the recurrence once
        have : g.contsAux (n' + 2) = ⟨pb * pA + pa * ppA, pb * pB + pa * ppB⟩ :=
          contsAux_recurrence s_n'th_eq n'th_contsAux_eq.symm succ_n'th_contsAux_eq.symm
        -- and a second time
        rw [conv_eq_conts_a_div_conts_b,
          conts_recurrenceAux s_nth_eq succ_n'th_contsAux_eq.symm this]
      rw [this]
      suffices
        ((pb + a / b) * pA + pa * ppA) / ((pb + a / b) * pB + pa * ppB) =
          (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB) by
        obtain ⟨eq1, eq2, eq3, eq4⟩ : pA' = pA ∧ pB' = pB ∧ ppA' = ppA ∧ ppB' = ppB := by
          simp [*, g', pA, pB, ppA, ppB, pA', pB', ppA', ppB',
            (contsAux_eq_contsAux_squashGCF_of_le <| le_refl <| n' + 1).symm,
            (contsAux_eq_contsAux_squashGCF_of_le n'.le_succ).symm]
        symm
        simpa only [eq1, eq2, eq3, eq4, mul_div_cancel_right₀ _ b_ne_zero]
      grind

end Squash

/-- Shows that the recurrence relation (`convs`) and direct evaluation (`convs'`) of the
generalized continued fraction coincide at position `n` if the sequence of fractions contains
strictly positive values only.
Requiring positivity of all values is just one possible condition to obtain this result.
For example, the dual - sequences with strictly negative values only - would also work.

In practice, one most commonly deals with regular continued fractions, which satisfy the
positivity criterion required here. The analogous result for them
(see `ContFract.convs_eq_convs'`) hence follows directly from this theorem.
-/
/-
**GenContFract.convs_eq_convs'** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：convs_eq_convs' [Field K] [LinearOrder K] [IsStrictOrderedRing K] (s_pos :
 forall {gp : Pair K} {m : Nat}, m < n -> g.s.get? m = some gp -> 0 < gp.a ∧ 0 <
 gp.b) : g.convs n = g.convs' n
参数：s_pos : forall {gp : Pair K} {m : Nat}, m < n -> g.s.get? m = some gp -> 0 < 
gp.a ∧ 0 < gp.b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.zeroth_conv_eq_h`：zeroth_conv_eq_h : g.convs 0 = g.h
· 使用定理 `GenContFract.zeroth_conv'_eq_h`：∀ {K : Type u_1} {g : GenContFract K} [i
nst : DivisionRing K], g.convs' 0 = g.h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Decidable.em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
· 使用定理 `GenContFract.squashGCF_eq_self_of_terminated`：squashGCF_eq_self_of_termi
nated (terminatedAt_n : TerminatedAt g n) : squashGCF g n = g
· 使用定理 `GenContFract.convs_stable_of_terminated`：convs_stable_of_terminated (n_l
e_m : n <= m) (terminatedAt_n : g.TerminatedAt n) : g.convs m = g.convs n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用定理 `GenContFract.succ_nth_conv_eq_squashGCF_nth_conv`：succ_nth_conv_eq_squas
hGCF_nth_conv [Field K] (nth_partDen_ne_zero : forall {b : K}, g.partDens.get? n
 = some b -> b != 0) : g.convs (n + 1)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.ne_none_iff_exists'`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ 
∃ x, o = some x
· 使用定理 `Stream'.Seq.ge_stable`：ge_stable (s : Seq α) {aₙ : α} {n m : Nat} (m_le_
n : m <= n) (s_nth_eq_some : s.get? n = some aₙ) : exists aₘ : α, s.get? m = som
e aₘ
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Shows that the recurrence relation (`convs`) and direct evaluation (`convs'`) of
 the
generalized continued fraction coincide at position `n` if the sequence of fract
ions contains
strictly positive values only.
Requiring positivity of all values is just one possible condition to obtain this
 result.
For example, the dual - sequences with strictly negative values only - would als
o work.

In practice, one most commonly deals with regular continued fractions, which sat
isfy the
positivity criterion required here. The analogous result for them
(see `ContFract.convs_eq_convs'`) hence follows directly from this theorem.
-/
theorem convs_eq_convs' [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (s_pos : ∀ {gp : Pair K} {m : ℕ}, m < n → g.s.get? m = some gp → 0 < gp.a ∧ 0 < gp.b) :
    g.convs n = g.convs' n := by
  induction n generalizing g with
  | zero => simp
  | succ n IH =>
    let g' := squashGCF g n
    -- first replace the rhs with the squashed computation
    suffices g.convs (n + 1) = g'.convs' n by
      rwa [succ_nth_conv'_eq_squashGCF_nth_conv']
    rcases Decidable.em (TerminatedAt g n) with terminatedAt_n | not_terminatedAt_n
    · have g'_eq_g : g' = g := squashGCF_eq_self_of_terminated terminatedAt_n
      rw [convs_stable_of_terminated n.le_succ terminatedAt_n, g'_eq_g, IH _]
      intro _ _ m_lt_n s_mth_eq
      exact s_pos (Nat.lt_succ_of_lt m_lt_n) s_mth_eq
    · suffices g.convs (n + 1) = g'.convs n by
        -- invoke the IH for the squashed gcf
        rwa [← IH]
        intro gp' m m_lt_n s_mth_eq'
        -- case distinction on m + 1 = n or m + 1 < n
        rcases m_lt_n with n | succ_m_lt_n
        · -- the difficult case at the squashed position: we first obtain the values from
          -- the sequence
          obtain ⟨gp_succ_m, s_succ_mth_eq⟩ : ∃ gp_succ_m, g.s.get? (m + 1) = some gp_succ_m :=
            Option.ne_none_iff_exists'.mp not_terminatedAt_n
          obtain ⟨gp_m, mth_s_eq⟩ : ∃ gp_m, g.s.get? m = some gp_m :=
            g.s.ge_stable m.le_succ s_succ_mth_eq
          -- we then plug them into the recurrence
          suffices 0 < gp_m.a ∧ 0 < gp_m.b + gp_succ_m.a / gp_succ_m.b by
            have ot : g'.s.get? m = some ⟨gp_m.a, gp_m.b + gp_succ_m.a / gp_succ_m.b⟩ :=
              squashSeq_nth_of_not_terminated mth_s_eq s_succ_mth_eq
            grind
          have m_lt_n : m < m.succ := Nat.lt_succ_self m
          refine ⟨(s_pos (Nat.lt_succ_of_lt m_lt_n) mth_s_eq).left, ?_⟩
          refine add_pos (s_pos (Nat.lt_succ_of_lt m_lt_n) mth_s_eq).right ?_
          have : 0 < gp_succ_m.a ∧ 0 < gp_succ_m.b := s_pos (lt_add_one <| m + 1) s_succ_mth_eq
          exact div_pos this.left this.right
        · -- the easy case: before the squashed position, nothing changes
          refine s_pos (Nat.lt_succ_of_lt <| Nat.lt_succ_of_lt succ_m_lt_n) ?_
          exact Eq.trans (squashGCF_nth_of_lt succ_m_lt_n).symm s_mth_eq'
      -- now the result follows from the fact that the convergents coincide at the squashed position
      -- as established in `succ_nth_conv_eq_squashGCF_nth_conv`.
      have : ∀ ⦃b⦄, g.partDens.get? n = some b → b ≠ 0 := by
        intro _ nth_partDen_eq
        grind [exists_s_b_of_partDen nth_partDen_eq]
      exact succ_nth_conv_eq_squashGCF_nth_conv @this

end GenContFract

open GenContFract

namespace ContFract

/-- Shows that the recurrence relation (`convs`) and direct evaluation (`convs'`) of a
(regular) continued fraction coincide. -/
/-
**ContFract.convs_eq_convs'** 是 Mathlib 中的一个定理，位于命名空间 `ContFract`。
形式化陈述：convs_eq_convs' [Field K] [LinearOrder K] [IsStrictOrderedRing K] {c : Con
tFract K} : (↑c : GenContFract K).convs = (↑c : GenContFract K).convs'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.ext`：∀ {α : Type u} {s₁ s₂ : Stream' α}, (∀ (n : ℕ), s₁.get n = 
s₂.get n) → s₁ = s₂
· 使用定理 `GenContFract.convs_eq_convs'`：convs_eq_convs' [Field K] [LinearOrder K] 
[IsStrictOrderedRing K] (s_pos : forall {gp : Pair K} {m : Nat}, m < n -> g.s.ge
t? m = some gp -> …
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `GenContFract.partNum_eq_s_a`：partNum_eq_s_a {gp : Pair α} (s_nth_eq : g.
s.get? n = some gp) : g.partNums.get? n = some gp.a
· 使用定理 `GenContFract.partDen_eq_s_b`：partDen_eq_s_b {gp : Pair α} (s_nth_eq : g.
s.get? n = some gp) : g.partDens.get? n = some gp.b

--- 原说明 ---
Shows that the recurrence relation (`convs`) and direct evaluation (`convs'`) of
 a
(regular) continued fraction coincide.
-/
theorem convs_eq_convs' [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {c : ContFract K} :
    (↑c : GenContFract K).convs = (↑c : GenContFract K).convs' := by
  ext n
  apply GenContFract.convs_eq_convs'
  intro gp m _ s_nth_eq
  exact ⟨zero_lt_one.trans_le ((c : SimpContFract K).property m gp.a
    (partNum_eq_s_a s_nth_eq)).symm.le, c.property m gp.b <| partDen_eq_s_b s_nth_eq⟩

end ContFract

