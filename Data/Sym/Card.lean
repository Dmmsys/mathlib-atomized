/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Huỳnh Trần Khanh, Stuart Presnell
-/
module

public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Stars and bars

In this file, we prove (in `Sym.card_sym_eq_multichoose`) that the function `multichoose n k`
defined in `Data/Nat/Choose/Basic` counts the number of multisets of cardinality `k` over an
alphabet of cardinality `n`. In conjunction with `Nat.multichoose_eq` proved in
`Data/Nat/Choose/Basic`, which shows that `multichoose n k = choose (n + k - 1) k`,
this is central to the "stars and bars" technique in combinatorics, where we switch between
counting multisets of size `k` over an alphabet of size `n` to counting strings of `k` elements
("stars") separated by `n-1` dividers ("bars").

## Informal statement

Many problems in mathematics are of the form of (or can be reduced to) putting `k` indistinguishable
objects into `n` distinguishable boxes; for example, the problem of finding natural numbers
`x1, ..., xn` whose sum is `k`. This is equivalent to forming a multiset of cardinality `k` from
an alphabet of cardinality `n` -- for each box `i ∈ [1, n]` the multiset contains as many copies
of `i` as there are items in the `i`th box.

The "stars and bars" technique arises from another way of presenting the same problem. Instead of
putting `k` items into `n` boxes, we take a row of `k` items (the "stars") and separate them by
inserting `n-1` dividers (the "bars").  For example, the pattern `*|||**|*|` exhibits 4 items
distributed into 6 boxes -- note that any box, including the first and last, may be empty.
Such arrangements of `k` stars and `n-1` bars are in 1-1 correspondence with multisets of size `k`
over an alphabet of size `n`, and are counted by `choose (n + k - 1) k`.

Note that this problem is one component of Gian-Carlo Rota's "Twelvefold Way"
https://en.wikipedia.org/wiki/Twelvefold_way

## Formal statement

Here we generalise the alphabet to an arbitrary fintype `α`, and we use `Sym α k` as the type of
multisets of size `k` over `α`. Thus the statement that these are counted by `multichoose` is:
`Sym.card_sym_eq_multichoose : card (Sym α k) = multichoose (card α) k`
while the "stars and bars" technique gives
`Sym.card_sym_eq_choose : card (Sym α k) = choose (card α + k - 1) k`


## Tags

stars and bars, multichoose
-/

@[expose] public section


open Finset Fintype Function Sum Nat

variable {α : Type*}

namespace Sym

section Sym

variable (α) (n : ℕ)

/-- Over `Fin (n + 1)`, the multisets of size `k + 1` containing `0` are equivalent to those of size
`k`, as demonstrated by respectively erasing or appending `0`. -/
/-
**Sym.e1** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：{n k : ℕ} → { s // 0 ∈ s } ≃ Sym (Fin n.succ) k
参数：Fin n.succ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Over `Fin (n + 1)`, the multisets of size `k + 1` containing `0` are equivalent 
to those of size
`k`, as demonstrated by respectively erasing or appending `0`.
-/
protected def e1 {n k : ℕ} : { s : Sym (Fin (n + 1)) (k + 1) // ↑0 ∈ s } ≃ Sym (Fin n.succ) k where
  toFun s := s.1.erase 0 s.2
  invFun s := ⟨cons 0 s, mem_cons_self 0 s⟩
  left_inv s := by simp
  right_inv s := by simp

/-- The multisets of size `k` over `Fin n+2` not containing `0`
are equivalent to those of size `k` over `Fin n+1`,
as demonstrated by respectively decrementing or incrementing every element of the multiset.
-/
/-
**Sym.e2** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：{n k : ℕ} → { s // 0 ∉ s } ≃ Sym (Fin n.succ) k
参数：Fin n.succ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
The multisets of size `k` over `Fin n+2` not containing `0`
are equivalent to those of size `k` over `Fin n+1`,
as demonstrated by respectively decrementing or incrementing every element of th
e multiset.
-/
protected def e2 {n k : ℕ} : { s : Sym (Fin n.succ.succ) k // ↑0 ∉ s } ≃ Sym (Fin n.succ) k where
  toFun s := map (Fin.predAbove 0) s.1
  invFun s :=
    ⟨map (Fin.succAbove 0) s,
      (mt mem_map.1) (not_exists.2 fun t => not_and.2 fun _ => Fin.succAbove_ne _ t)⟩
  left_inv s := by
    ext1
    simp only [map_map]
    refine (Sym.map_congr fun v hv ↦ ?_).trans (map_id' _)
    exact Fin.succAbove_predAbove (ne_of_mem_of_not_mem hv s.2)
  right_inv s := by
    simp only [map_map, comp_apply, ← Fin.castSucc_zero, Fin.predAbove_succAbove, map_id']
/-
**Sym.card_sym_fin_eq_multichoose** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：∀ (n k : ℕ), Fintype.card (Sym (Fin n) k) = n.multichoose k
参数：n k : ℕ；Sym (Fin n) k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.card_sym_fin_eq_multichoose._unary`：∀ (_x : (_ : ℕ) ×' ℕ), Fintype.c
ard (Sym (Fin _x.1) _x.2) = _x.1.multichoose _x.2
-/
theorem card_sym_fin_eq_multichoose : ∀ n k : ℕ, card (Sym (Fin n) k) = multichoose n k
  | n, 0 => by simp
  | 0, k + 1 => by rw [multichoose_zero_succ]; exact card_eq_zero
  | 1, k + 1 => by simp
  | n + 2, k + 1 => by
    rw [multichoose_succ_succ, ← card_sym_fin_eq_multichoose (n + 1) (k + 1),
      ← card_sym_fin_eq_multichoose (n + 2) k, add_comm (Fintype.card _), ← card_sum]
    refine Fintype.card_congr (Equiv.symm ?_)
    apply (Sym.e1.symm.sumCongr Sym.e2.symm).trans
    apply Equiv.sumCompl

/-- For any fintype `α` of cardinality `n`, `card (Sym α k) = multichoose (card α) k`. -/
/-
**Sym.card_sym_eq_multichoose** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：card_sym_eq_multichoose (α : Type*) (k : Nat) [Fintype α] [Fintype (Sym α 
k)] : card (Sym α k) = multichoose (card α) k
参数：α : Type*；k : Nat；Sym α k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym.card_sym_fin_eq_multichoose`：∀ (n k : ℕ), Fintype.card (Sym (Fin n) 
k) = n.multichoose k
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β

--- 原说明 ---
For any fintype `α` of cardinality `n`, `card (Sym α k) = multichoose (card α) k
`.
-/
theorem card_sym_eq_multichoose (α : Type*) (k : ℕ) [Fintype α] [Fintype (Sym α k)] :
    card (Sym α k) = multichoose (card α) k := by
  rw [← card_sym_fin_eq_multichoose]
  exact card_congr (equivCongr (equivFin α))

/-- The *stars and bars* lemma: the cardinality of `Sym α k` is equal to
`Nat.choose (card α + k - 1) k`. -/
/-
**Sym.card_sym_eq_choose** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：card_sym_eq_choose {α : Type*} [Fintype α] (k : Nat) [Fintype (Sym α k)] :
 card (Sym α k) = (card α + k - 1).choose k
参数：k : Nat；Sym α k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym.card_sym_eq_multichoose`：card_sym_eq_multichoose (α : Type*) (k : Na
t) [Fintype α] [Fintype (Sym α k)] : card (Sym α k) = multichoose (card α) k
· 使用定理 `Nat.multichoose_eq`：multichoose_eq : forall n k : Nat, multichoose n k =
 (n + k - 1).choose k | _, 0 => by simp | 0, k + 1 => by simp | n + 1, k + 1 => 
by have …

--- 原说明 ---
The *stars and bars* lemma: the cardinality of `Sym α k` is equal to
`Nat.choose (card α + k - 1) k`.
-/
theorem card_sym_eq_choose {α : Type*} [Fintype α] (k : ℕ) [Fintype (Sym α k)] :
    card (Sym α k) = (card α + k - 1).choose k := by
  rw [card_sym_eq_multichoose, Nat.multichoose_eq]

end Sym

end Sym

namespace Sym2

variable [DecidableEq α]

/-- The `diag` of `s : Finset α` is sent on a finset of `Sym2 α` of card `#s`. -/
/-
**Sym2.card_image_diag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：card_image_diag (s : Finset α) : #(s.diag.image Sym2.mk.uncurry) = #s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image_diag`：image_diag [DecidableEq β] (f : α × α -> β) (s : Fins
et α) : s.diag.image f = s.image fun x => f (x, x)
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `diag` of `s : Finset α` is sent on a finset of `Sym2 α` of card `#s`.
-/
theorem card_image_diag (s : Finset α) : #(s.diag.image Sym2.mk.uncurry) = #s := by
  simp [card_image_of_injOn]
/-
**Sym2.two_mul_card_image_offDiag** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：two_mul_card_image_offDiag (s : Finset α) : 2 * #(s.offDiag.image Sym2.mk.
uncurry) = #s.offDiag
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_sum_card_image`：card_eq_sum_card_image [DecidableEq M] (f
 : ι -> M) (s : Finset ι) : #s = ∑ b in s.image f, #{a in s | f a = b}
· 使用定理 `Finset.sum_const_nat`：sum_const_nat {m : Nat} {f : ι -> Nat} (h₁ : foral
l x in s, f x = m) : ∑ x in s, f x = #s * m
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma two_mul_card_image_offDiag (s : Finset α) :
    2 * #(s.offDiag.image Sym2.mk.uncurry) = #s.offDiag := by
  rw [card_eq_sum_card_image (Sym2.mk.uncurry : α × α → _), sum_const_nat (Sym2.ind _), mul_comm]
  -- FIXME: Would be cool for the final `aesop` call not to require this `a ≠ b ∨ b ≠ a` trick.
  have (a b : α) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b ∨ b ≠ a) :
      {z ∈ s.offDiag | Sym2.mk.uncurry z = s(a, b)} = .cons (a, b) {(b, a)}
        (by simpa [eq_comm] using hab) := by aesop
  aesop

/-- The `offDiag` of `s : Finset α` is sent on a finset of `Sym2 α` of card `#s.offDiag / 2`.
This is because every element `s(x, y)` of `Sym2 α` not on the diagonal comes from exactly two
pairs: `(x, y)` and `(y, x)`. -/
/-
**Sym2.card_image_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：card_image_offDiag (s : Finset α) : #(s.offDiag.image Sym2.mk.uncurry) = (
#s).choose 2
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_two_right`：choose_two_right (n : Nat) : choose n 2 = n * (n -
 1) / 2
· 使用定理 `Nat.mul_sub_left_distrib`：∀ (n m k : ℕ), n * (m - k) = n * m - n * k
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.offDiag_card`：offDiag_card : (offDiag s).card = s.card * s.card -
 s.card
· 使用定理 `Nat.div_eq_of_eq_mul_right`：∀ {n m k : ℕ}, 0 < n → m = n * k → m / n = k
· 使用定理 `Nat.zero_lt_two`：0 < 2
· 使用引理 `Sym2.two_mul_card_image_offDiag`：two_mul_card_image_offDiag (s : Finset 
α) : 2 * #(s.offDiag.image Sym2.mk.uncurry) = #s.offDiag

--- 原说明 ---
The `offDiag` of `s : Finset α` is sent on a finset of `Sym2 α` of card `#s.offD
iag / 2`.
This is because every element `s(x, y)` of `Sym2 α` not on the diagonal comes fr
om exactly two
pairs: `(x, y)` and `(y, x)`.
-/
theorem card_image_offDiag (s : Finset α) :
    #(s.offDiag.image Sym2.mk.uncurry) = (#s).choose 2 := by
  rw [Nat.choose_two_right, Nat.mul_sub_left_distrib, mul_one, ← offDiag_card,
    Nat.div_eq_of_eq_mul_right Nat.zero_lt_two (two_mul_card_image_offDiag s).symm]
/-
**Sym2.card_subtype_diag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：card_subtype_diag [Fintype α] : card { a : Sym2 α // a.IsDiag } = card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem card_subtype_diag [Fintype α] : card { a : Sym2 α // a.IsDiag } = card α :=
  card_congr diagElemEquiv
/-
**Sym2.card_subtype_not_diag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：card_subtype_not_diag [Fintype α] : card { a : Sym2 α // ¬a.IsDiag } = (ca
rd α).choose 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.filter_image_mk_not_isDiag`：filter_image_mk_not_isDiag [DecidableEq
 α] (s : Finset α) : {x in (s ×ˢ s).image Sym2.mk.uncurry | ¬x.IsDiag} = s.offDi
ag.image Sym2.mk.uncu…
· 使用定理 `Fintype.card_of_subtype`：card_of_subtype {p : α -> Prop} (s : Finset α) 
(H : forall x : α, x in s ↔ p x) [Fintype { x // p x }] : card { x // p x } = #s
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.univ_product_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : Fintyp
e α] [inst_1 : Fintype β], Finset.univ ×ˢ Finset.univ = Finset.univ
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Sym2.card_image_offDiag`：card_image_offDiag (s : Finset α) : #(s.offDiag
.image Sym2.mk.uncurry) = (#s).choose 2
-/
theorem card_subtype_not_diag [Fintype α] :
    card { a : Sym2 α // ¬a.IsDiag } = (card α).choose 2 := by
  convert! card_image_offDiag (univ : Finset α)
  rw [← filter_image_mk_not_isDiag, Fintype.card_of_subtype]
  rintro x
  rw [mem_filter, univ_product_univ, mem_image]
  obtain ⟨a, ha⟩ := Quot.exists_rep x
  exact and_iff_right ⟨a, mem_univ _, ha⟩
/-
**Sym2.card_diagSet_compl** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：card_diagSet_compl [Fintype α] : card (diagSetᶜ : Set (Sym2 α)) = (card α)
.choose 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.card_subtype_not_diag`：card_subtype_not_diag [Fintype α] : card { a
 : Sym2 α // ¬a.IsDiag } = (card α).choose 2
-/
lemma card_diagSet_compl [Fintype α] : card (diagSetᶜ : Set (Sym2 α)) = (card α).choose 2 :=
  card_subtype_not_diag

/-- Type **stars and bars** for the case `n = 2`. -/
/-
**Sym2.card** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α], Fintype.card (Sym2 α) = (Fintype.card
 α + 1).choose 2
参数：Sym2 α；Fintype.card α + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_sym2`：card_sym2 (s : Finset α) : s.sym2.card = Nat.choose (s
.card + 1) 2

--- 原说明 ---
Type **stars and bars** for the case `n = 2`.
-/
protected theorem card {α} [Fintype α] : card (Sym2 α) = Nat.choose (card α + 1) 2 :=
  Finset.card_sym2 _

end Sym2

