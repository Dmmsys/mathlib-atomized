/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Kim Morrison, Eric Rodriguez
-/
module

public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Interval.Set.Monotone
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Order.WellFounded
public import Mathlib.Data.Finset.Sort

/-!
# The `n`th Number Satisfying a Predicate

This file defines a function for "what is the `n`th number that satisfies a given predicate `p`",
and provides lemmas that deal with this function and its connection to `Nat.count`.

## Main definitions

* `Nat.nth p n`: The `n`-th natural `k` (zero-indexed) such that `p k`. If there is no
  such natural (that is, `p` is true for at most `n` naturals), then `Nat.nth p n = 0`.

## Main results

* `Nat.nth_eq_orderEmbOfFin`: For a finitely-often true `p`, gives the cardinality of the set of
  numbers satisfying `p` above particular values of `nth p`
* `Nat.gc_count_nth`: Establishes a Galois connection between `Nat.nth p` and `Nat.count p`.
* `Nat.nth_eq_orderIsoOfNat`: For an infinitely-often true predicate, `nth` agrees with the
  order-isomorphism of the subtype to the natural numbers.

## Implementation details

Much of the below was written before `Set.encard` existed and partly for this reason uses the
pattern `∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card` rather than `n < {x | p x}.encard`.
We should consider changing this.

There has been some discussion on the subject of whether both of `nth` and
`Nat.Subtype.orderIsoOfNat` should exist. See discussion
[here](https://github.com/leanprover-community/mathlib/pull/9457#pullrequestreview-767221180).
Future work should address how lemmas that use these should be written.

-/

@[expose] public section


open Finset

namespace Nat

variable (p : ℕ → Prop)

/-- Find the `n`-th natural number satisfying `p` (indexed from `0`, so `nth p 0` is the first
natural number satisfying `p`), or `0` if there is no such number. See also
`Subtype.orderIsoOfNat` for the order isomorphism with ℕ when `p` is infinitely often true. -/
/-
**Nat.nth** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：nth (p : Nat -> Prop) (n : Nat) : Nat
参数：p : Nat -> Prop；n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2

--- 原说明 ---
Find the `n`-th natural number satisfying `p` (indexed from `0`, so `nth p 0` is
 the first
natural number satisfying `p`), or `0` if there is no such number. See also
`Subtype.orderIsoOfNat` for the order isomorphism with ℕ when `p` is infinitely 
often true.
-/
noncomputable def nth (p : ℕ → Prop) (n : ℕ) : ℕ := by
  classical exact
    if h : Set.Finite (Set.ofPred p) then h.toFinset.sort.getD n 0
    else @Nat.Subtype.orderIsoOfNat (Set.ofPred p) (Set.Infinite.to_subtype h) n

variable {p}

/-!
### Lemmas about `Nat.nth` on a finite set
-/


/-
**Nat.nth_of_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_of_card_le (hf : (Set.ofPred p).Finite) {n : Nat} (hn : #hf.toFinset <
= n) : nth p n = 0
参数：hf : (Set.ofPred p).Finite；hn : #hf.toFinset <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth.eq_1`：∀ (p : ℕ → Prop) (n : ℕ),   Nat.nth p n =     if h : (Set.
ofPred p).Finite then (h.toFinset.sort fun a b => a ≤ b).getD n 0     else ↑((Na
t.…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `List.getD_eq_default`：getD_eq_default {n : Nat} (hn : l.length <= n) : l
.getD n d = d
· 使用定理 `Finset.length_sort`：length_sort : (sort s r).length = s.card

--- 原说明 ---
### Lemmas about `Nat.nth` on a finite set
-/
theorem nth_of_card_le (hf : (Set.ofPred p).Finite) {n : ℕ} (hn : #hf.toFinset ≤ n) :
    nth p n = 0 := by rw [nth, dif_pos hf, List.getD_eq_default]; rwa [Finset.length_sort]
/-
**Nat.nth_eq_getD_sort** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_eq_getD_sort (h : (Set.ofPred p).Finite) (n : Nat) : nth p n = h.toFin
set.sort.getD n 0
参数：h : (Set.ofPred p).Finite；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2
-/
theorem nth_eq_getD_sort (h : (Set.ofPred p).Finite) (n : ℕ) :
    nth p n = h.toFinset.sort.getD n 0 :=
  dif_pos h
/-
**Nat.nth_eq_orderEmbOfFin** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_eq_orderEmbOfFin (hf : (Set.ofPred p).Finite) {n : Nat} (hn : n < #hf.
toFinset) : nth p n = hf.toFinset.orderEmbOfFin rfl ⟨n, hn⟩
参数：hf : (Set.ofPred p).Finite；hn : n < #hf.toFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_eq_getD_sort`：nth_eq_getD_sort (h : (Set.ofPred p).Finite) (n : 
Nat) : nth p n = h.toFinset.sort.getD n 0
· 使用定理 `Finset.orderEmbOfFin_apply`：orderEmbOfFin_apply (s : Finset α) {k : Nat}
 (h : s.card = k) (i : Fin k) : s.orderEmbOfFin h i = s.sort[i]'(by rw [length_s
ort, h]; exact i…
· 使用定理 `List.getD_eq_getElem`：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.
getD n d = l[n]
· 使用定理 `Fin.getElem_fin`：∀ {Cont : Type u_1} {Elem : Type u_2} {Dom : Cont → ℕ →
 Prop} {n : ℕ} [inst : GetElem Cont ℕ Elem Dom] (a : Cont)   (i : Fin n) (h : Do
m a ↑…
-/
theorem nth_eq_orderEmbOfFin (hf : (Set.ofPred p).Finite) {n : ℕ} (hn : n < #hf.toFinset) :
    nth p n = hf.toFinset.orderEmbOfFin rfl ⟨n, hn⟩ := by
  rw [nth_eq_getD_sort hf, Finset.orderEmbOfFin_apply, List.getD_eq_getElem, Fin.getElem_fin]
/-
**Nat.nth_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_strictMonoOn (hf : (Set.ofPred p).Finite) : StrictMonoOn (nth p) (Set.
Iio #hf.toFinset)
参数：hf : (Set.ofPred p).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_eq_orderEmbOfFin`：nth_eq_orderEmbOfFin (hf : (Set.ofPred p).Fini
te) {n : Nat} (hn : n < #hf.toFinset) : nth p n = hf.toFinset.orderEmbOfFin rfl 
⟨n, hn⟩
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
-/
theorem nth_strictMonoOn (hf : (Set.ofPred p).Finite) :
    StrictMonoOn (nth p) (Set.Iio #hf.toFinset) := by
  rintro m (hm : m < _) n (hn : n < _) h
  simp only [nth_eq_orderEmbOfFin, *]
  exact OrderEmbedding.strictMono _ h
/-
**Nat.nth_lt_nth_of_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_lt_nth_of_lt_card (hf : (Set.ofPred p).Finite) {m n : Nat} (h : m < n)
 (hn : n < #hf.toFinset) : nth p m < nth p n
参数：hf : (Set.ofPred p).Finite；h : m < n；hn : n < #hf.toFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_strictMonoOn`：nth_strictMonoOn (hf : (Set.ofPred p).Finite) : St
rictMonoOn (nth p) (Set.Iio #hf.toFinset)
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem nth_lt_nth_of_lt_card (hf : (Set.ofPred p).Finite) {m n : ℕ} (h : m < n)
    (hn : n < #hf.toFinset) : nth p m < nth p n :=
  nth_strictMonoOn hf (h.trans hn) hn h
/-
**Nat.nth_le_nth_of_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_le_nth_of_lt_card (hf : (Set.ofPred p).Finite) {m n : Nat} (h : m <= n
) (hn : n < #hf.toFinset) : nth p m <= nth p n
参数：hf : (Set.ofPred p).Finite；h : m <= n；hn : n < #hf.toFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : PartialOrde
r α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → Monoton
eOn f s
· 使用定理 `Nat.nth_strictMonoOn`：nth_strictMonoOn (hf : (Set.ofPred p).Finite) : St
rictMonoOn (nth p) (Set.Iio #hf.toFinset)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem nth_le_nth_of_lt_card (hf : (Set.ofPred p).Finite) {m n : ℕ} (h : m ≤ n)
    (hn : n < #hf.toFinset) : nth p m ≤ nth p n :=
  (nth_strictMonoOn hf).monotoneOn (h.trans_lt hn) hn h
/-
**Nat.lt_of_nth_lt_nth_of_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_of_nth_lt_nth_of_lt_card (hf : (Set.ofPred p).Finite) {m n : Nat} (h : 
nth p m < nth p n) (hm : m < #hf.toFinset) : m < n
参数：hf : (Set.ofPred p).Finite；h : nth p m < nth p n；hm : m < #hf.toFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.nth_le_nth_of_lt_card`：nth_le_nth_of_lt_card (hf : (Set.ofPred p).Fi
nite) {m n : Nat} (h : m <= n) (hn : n < #hf.toFinset) : nth p m <= nth p n
-/
theorem lt_of_nth_lt_nth_of_lt_card (hf : (Set.ofPred p).Finite) {m n : ℕ} (h : nth p m < nth p n)
    (hm : m < #hf.toFinset) : m < n :=
  not_le.1 fun hle => h.not_ge <| nth_le_nth_of_lt_card hf hle hm
/-
**Nat.le_of_nth_le_nth_of_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_of_nth_le_nth_of_lt_card (hf : (Set.ofPred p).Finite) {m n : Nat} (h : 
nth p m <= nth p n) (hm : m < #hf.toFinset) : m <= n
参数：hf : (Set.ofPred p).Finite；h : nth p m <= nth p n；hm : m < #hf.toFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.nth_lt_nth_of_lt_card`：nth_lt_nth_of_lt_card (hf : (Set.ofPred p).Fi
nite) {m n : Nat} (h : m < n) (hn : n < #hf.toFinset) : nth p m < nth p n
-/
theorem le_of_nth_le_nth_of_lt_card (hf : (Set.ofPred p).Finite) {m n : ℕ} (h : nth p m ≤ nth p n)
    (hm : m < #hf.toFinset) : m ≤ n :=
  not_lt.1 fun hlt => h.not_gt <| nth_lt_nth_of_lt_card hf hlt hm
/-
**Nat.nth_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_injOn (hf : (Set.ofPred p).Finite) : (Set.Iio #hf.toFinset).InjOn (nth
 p)
参数：hf : (Set.ofPred p).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用定理 `Nat.nth_strictMonoOn`：nth_strictMonoOn (hf : (Set.ofPred p).Finite) : St
rictMonoOn (nth p) (Set.Iio #hf.toFinset)
-/
theorem nth_injOn (hf : (Set.ofPred p).Finite) : (Set.Iio #hf.toFinset).InjOn (nth p) :=
  (nth_strictMonoOn hf).injOn
/-
**Nat.range_nth_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：range_nth_of_finite (hf : (Set.ofPred p).Finite) : Set.range (nth p) = ins
ert 0 (Set.ofPred p)
参数：hf : (Set.ofPred p).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.nth_eq_getD_sort`：nth_eq_getD_sort (h : (Set.ofPred p).Finite) (n : 
Nat) : nth p n = h.toFinset.sort.getD n 0
· 使用定理 `Set.range_list_getD`：range_list_getD (d : α) : (range fun n : Nat => l[n
]?.getD d) = insert d { x | x in l }
-/
theorem range_nth_of_finite (hf : (Set.ofPred p).Finite) :
    Set.range (nth p) = insert 0 (Set.ofPred p) := by
  simpa only [← List.getD_eq_getElem?_getD, ← nth_eq_getD_sort hf, mem_sort,
    Set.Finite.mem_toFinset] using! Set.range_list_getD (hf.toFinset.sort (· ≤ ·)) 0

@[simp]
/-
**Nat.image_nth_Iio_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_nth_Iio_card (hf : (Set.ofPred p).Finite) : nth p '' Set.Iio #hf.toF
inset = Set.ofPred p
参数：hf : (Set.ofPred p).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.nth_eq_orderEmbOfFin`：nth_eq_orderEmbOfFin (hf : (Set.ofPred p).Fini
te) {n : Nat} (hn : n < #hf.toFinset) : nth p n = hf.toFinset.orderEmbOfFin rfl 
⟨n, hn⟩
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.range_orderEmbOfFin`：range_orderEmbOfFin (s : Finset α) {k : Nat}
 (h : s.card = k) : Set.range (s.orderEmbOfFin h) = s
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
-/
theorem image_nth_Iio_card (hf : (Set.ofPred p).Finite) :
    nth p '' Set.Iio #hf.toFinset = Set.ofPred p :=
  calc
    nth p '' Set.Iio #hf.toFinset = Set.range (hf.toFinset.orderEmbOfFin rfl) := by
      ext x
      simp only [Set.mem_image, Set.mem_range, Fin.exists_iff, ← nth_eq_orderEmbOfFin hf,
        Set.mem_Iio, exists_prop]
    _ = Set.ofPred p := by rw [range_orderEmbOfFin, Set.Finite.coe_toFinset]
/-
**Nat.nth_mem_of_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_mem_of_lt_card {n : Nat} (hf : (Set.ofPred p).Finite) (hlt : n < #hf.t
oFinset) : p (nth p n)
参数：hf : (Set.ofPred p).Finite；hlt : n < #hf.toFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Nat.image_nth_Iio_card`：image_nth_Iio_card (hf : (Set.ofPred p).Finite) 
: nth p '' Set.Iio #hf.toFinset = Set.ofPred p
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem nth_mem_of_lt_card {n : ℕ} (hf : (Set.ofPred p).Finite) (hlt : n < #hf.toFinset) :
    p (nth p n) :=
  (image_nth_Iio_card hf).subset <| Set.mem_image_of_mem _ hlt
/-
**Nat.exists_lt_card_finite_nth_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_lt_card_finite_nth_eq (hf : (Set.ofPred p).Finite) {x} (h : p x) : 
exists n, n < #hf.toFinset ∧ nth p n = x
参数：hf : (Set.ofPred p).Finite；h : p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.image_nth_Iio_card`：image_nth_Iio_card (hf : (Set.ofPred p).Finite) 
: nth p '' Set.Iio #hf.toFinset = Set.ofPred p
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
-/
theorem exists_lt_card_finite_nth_eq (hf : (Set.ofPred p).Finite) {x} (h : p x) :
    ∃ n, n < #hf.toFinset ∧ nth p n = x := by
  rwa [← @Set.mem_ofPred_eq _ _ p, ← image_nth_Iio_card hf] at h

/-!
### Lemmas about `Nat.nth` on an infinite set
-/

/-- When `s` is an infinite set, `nth` agrees with `Nat.Subtype.orderIsoOfNat`. -/
/-
**Nat.nth_apply_eq_orderIsoOfNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_apply_eq_orderIsoOfNat (hf : (Set.ofPred p).Infinite) (n : Nat) : nth 
p n = @Nat.Subtype.orderIsoOfNat (Set.ofPred p) hf.to_subtype n
参数：hf : (Set.ofPred p).Infinite；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth.eq_1`：∀ (p : ℕ → Prop) (n : ℕ),   Nat.nth p n =     if h : (Set.
ofPred p).Finite then (h.toFinset.sort fun a b => a ≤ b).getD n 0     else ↑((Na
t.…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc

--- 原说明 ---
When `s` is an infinite set, `nth` agrees with `Nat.Subtype.orderIsoOfNat`.
-/
theorem nth_apply_eq_orderIsoOfNat (hf : (Set.ofPred p).Infinite) (n : ℕ) :
    nth p n = @Nat.Subtype.orderIsoOfNat (Set.ofPred p) hf.to_subtype n := by rw [nth, dif_neg hf]

/-- When `s` is an infinite set, `nth` agrees with `Nat.Subtype.orderIsoOfNat`. -/
/-
**Nat.nth_eq_orderIsoOfNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_eq_orderIsoOfNat (hf : (Set.ofPred p).Infinite) : nth p = (↑) ∘ @Nat.S
ubtype.orderIsoOfNat (Set.ofPred p) hf.to_subtype
参数：hf : (Set.ofPred p).Infinite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `Nat.nth_apply_eq_orderIsoOfNat`：nth_apply_eq_orderIsoOfNat (hf : (Set.of
Pred p).Infinite) (n : Nat) : nth p n = @Nat.Subtype.orderIsoOfNat (Set.ofPred p
) hf.to_subtype n

--- 原说明 ---
When `s` is an infinite set, `nth` agrees with `Nat.Subtype.orderIsoOfNat`.
-/
theorem nth_eq_orderIsoOfNat (hf : (Set.ofPred p).Infinite) :
    nth p = (↑) ∘ @Nat.Subtype.orderIsoOfNat (Set.ofPred p) hf.to_subtype :=
  funext <| nth_apply_eq_orderIsoOfNat hf
/-
**Nat.nth_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_strictMono (hf : (Set.ofPred p).Infinite) : StrictMono (nth p)
参数：hf : (Set.ofPred p).Infinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_eq_orderIsoOfNat`：nth_eq_orderIsoOfNat (hf : (Set.ofPred p).Infi
nite) : nth p = (↑) ∘ @Nat.Subtype.orderIsoOfNat (Set.ofPred p) hf.to_subtype
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Subtype.strictMono_coe`：Subtype.strictMono_coe [Preorder α] (p : α -> Pr
op) : StrictMono ((↑) : Subtype p -> α)
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
theorem nth_strictMono (hf : (Set.ofPred p).Infinite) : StrictMono (nth p) := by
  rw [nth_eq_orderIsoOfNat hf]
  exact (Subtype.strictMono_coe _).comp (OrderIso.strictMono _)
/-
**Nat.nth_injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_injective (hf : (Set.ofPred p).Infinite) : Function.Injective (nth p)
参数：hf : (Set.ofPred p).Infinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Nat.nth_strictMono`：nth_strictMono (hf : (Set.ofPred p).Infinite) : Stri
ctMono (nth p)
-/
theorem nth_injective (hf : (Set.ofPred p).Infinite) : Function.Injective (nth p) :=
  (nth_strictMono hf).injective
/-
**Nat.nth_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_monotone (hf : (Set.ofPred p).Infinite) : Monotone (nth p)
参数：hf : (Set.ofPred p).Infinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.nth_strictMono`：nth_strictMono (hf : (Set.ofPred p).Infinite) : Stri
ctMono (nth p)
-/
theorem nth_monotone (hf : (Set.ofPred p).Infinite) : Monotone (nth p) :=
  (nth_strictMono hf).monotone
/-
**Nat.nth_lt_nth** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_lt_nth (hf : (Set.ofPred p).Infinite) {k n} : nth p k < nth p n ↔ k < 
n
参数：hf : (Set.ofPred p).Infinite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Nat.nth_strictMono`：nth_strictMono (hf : (Set.ofPred p).Infinite) : Stri
ctMono (nth p)
-/
theorem nth_lt_nth (hf : (Set.ofPred p).Infinite) {k n} : nth p k < nth p n ↔ k < n :=
  (nth_strictMono hf).lt_iff_lt
/-
**Nat.nth_le_nth** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_le_nth (hf : (Set.ofPred p).Infinite) {k n} : nth p k <= nth p n ↔ k <
= n
参数：hf : (Set.ofPred p).Infinite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Nat.nth_strictMono`：nth_strictMono (hf : (Set.ofPred p).Infinite) : Stri
ctMono (nth p)
-/
theorem nth_le_nth (hf : (Set.ofPred p).Infinite) {k n} : nth p k ≤ nth p n ↔ k ≤ n :=
  (nth_strictMono hf).le_iff_le
/-
**Nat.range_nth_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：range_nth_of_infinite (hf : (Set.ofPred p).Infinite) : Set.range (nth p) =
 Set.ofPred p
参数：hf : (Set.ofPred p).Infinite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_eq_orderIsoOfNat`：nth_eq_orderIsoOfNat (hf : (Set.ofPred p).Infi
nite) : nth p = (↑) ∘ @Nat.Subtype.orderIsoOfNat (Set.ofPred p) hf.to_subtype
· 使用定理 `Nat.Subtype.coe_comp_ofNat_range`：coe_comp_ofNat_range : Set.range ((↑) 
∘ ofNat s : Nat -> Nat) = s
-/
theorem range_nth_of_infinite (hf : (Set.ofPred p).Infinite) :
    Set.range (nth p) = Set.ofPred p := by
  rw [nth_eq_orderIsoOfNat hf]
  have := hf.to_subtype
  classical exact Nat.Subtype.coe_comp_ofNat_range
/-
**Nat.nth_mem_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_mem_of_infinite (hf : (Set.ofPred p).Infinite) (n : Nat) : p (nth p n)
参数：hf : (Set.ofPred p).Infinite；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Nat.range_nth_of_infinite`：range_nth_of_infinite (hf : (Set.ofPred p).In
finite) : Set.range (nth p) = Set.ofPred p
-/
theorem nth_mem_of_infinite (hf : (Set.ofPred p).Infinite) (n : ℕ) : p (nth p n) :=
  Set.range_subset_iff.1 (range_nth_of_infinite hf).le n

/-!
### Lemmas that work for finite and infinite sets
-/

/-
**Nat.exists_lt_card_nth_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_lt_card_nth_eq {x} (h : p x) : exists n, (forall hf : (Set.ofPred p
).Finite, n < #hf.toFinset) ∧ nth p n = x
参数：h : p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Nat.exists_lt_card_finite_nth_eq`：exists_lt_card_finite_nth_eq (hf : (Se
t.ofPred p).Finite) {x} (h : p x) : exists n, n < #hf.toFinset ∧ nth p n = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.range_nth_of_infinite`：range_nth_of_infinite (hf : (Set.ofPred p).In
finite) : Set.range (nth p) = Set.ofPred p
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x

--- 原说明 ---
### Lemmas that work for finite and infinite sets
-/
theorem exists_lt_card_nth_eq {x} (h : p x) :
    ∃ n, (∀ hf : (Set.ofPred p).Finite, n < #hf.toFinset) ∧ nth p n = x := by
  refine (Set.ofPred p).finite_or_infinite.elim (fun hf => ?_) fun hf => ?_
  · rcases exists_lt_card_finite_nth_eq hf h with ⟨n, hn, hx⟩
    exact ⟨n, fun _ => hn, hx⟩
  · rw [← @Set.mem_ofPred_eq _ _ p, ← range_nth_of_infinite hf] at h
    rcases h with ⟨n, hx⟩
    exact ⟨n, fun hf' => absurd hf' hf, hx⟩
/-
**Nat.subset_range_nth** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：subset_range_nth : Set.ofPred p subseteq Set.range (nth p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_lt_card_nth_eq`：exists_lt_card_nth_eq {x} (h : p x) : exists 
n, (forall hf : (Set.ofPred p).Finite, n < #hf.toFinset) ∧ nth p n = x
-/
theorem subset_range_nth : Set.ofPred p ⊆ Set.range (nth p) := fun x (hx : p x) =>
  let ⟨n, _, hn⟩ := exists_lt_card_nth_eq hx
  ⟨n, hn⟩
/-
**Nat.range_nth_subset** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：range_nth_subset : Set.range (nth p) subseteq insert 0 (Set.ofPred p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Nat.range_nth_of_finite`：range_nth_of_finite (hf : (Set.ofPred p).Finite
) : Set.range (nth p) = insert 0 (Set.ofPred p)
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用定理 `Nat.range_nth_of_infinite`：range_nth_of_infinite (hf : (Set.ofPred p).In
finite) : Set.range (nth p) = Set.ofPred p
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
theorem range_nth_subset : Set.range (nth p) ⊆ insert 0 (Set.ofPred p) :=
  (Set.ofPred p).finite_or_infinite.elim (fun h => (range_nth_of_finite h).subset) fun h =>
    (range_nth_of_infinite h).trans_subset (Set.subset_insert _ _)
/-
**Nat.nth_mem** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_mem (n : Nat) (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset
) : p (nth p n)
参数：n : Nat；h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Nat.nth_mem_of_lt_card`：nth_mem_of_lt_card {n : Nat} (hf : (Set.ofPred p
).Finite) (hlt : n < #hf.toFinset) : p (nth p n)
· 使用定理 `Nat.nth_mem_of_infinite`：nth_mem_of_infinite (hf : (Set.ofPred p).Infini
te) (n : Nat) : p (nth p n)
-/
theorem nth_mem (n : ℕ) (h : ∀ hf : (Set.ofPred p).Finite, n < #hf.toFinset) : p (nth p n) :=
  (Set.ofPred p).finite_or_infinite.elim (fun hf => nth_mem_of_lt_card hf (h hf)) fun h =>
    nth_mem_of_infinite h n
/-
**Nat.nth_lt_nth'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_lt_nth' {m n : Nat} (hlt : m < n) (h : forall hf : (Set.ofPred p).Fini
te, n < #hf.toFinset) : nth p m < nth p n
参数：hlt : m < n；h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Nat.nth_lt_nth_of_lt_card`：nth_lt_nth_of_lt_card (hf : (Set.ofPred p).Fi
nite) {m n : Nat} (h : m < n) (hn : n < #hf.toFinset) : nth p m < nth p n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.nth_lt_nth`：nth_lt_nth (hf : (Set.ofPred p).Infinite) {k n} : nth p 
k < nth p n ↔ k < n
-/
theorem nth_lt_nth' {m n : ℕ} (hlt : m < n) (h : ∀ hf : (Set.ofPred p).Finite, n < #hf.toFinset) :
    nth p m < nth p n :=
  (Set.ofPred p).finite_or_infinite.elim (fun hf => nth_lt_nth_of_lt_card hf hlt (h _)) fun hf =>
    (nth_lt_nth hf).2 hlt
/-
**Nat.nth_le_nth'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_le_nth' {m n : Nat} (hle : m <= n) (h : forall hf : (Set.ofPred p).Fin
ite, n < #hf.toFinset) : nth p m <= nth p n
参数：hle : m <= n；h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Nat.nth_le_nth_of_lt_card`：nth_le_nth_of_lt_card (hf : (Set.ofPred p).Fi
nite) {m n : Nat} (h : m <= n) (hn : n < #hf.toFinset) : nth p m <= nth p n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.nth_le_nth`：nth_le_nth (hf : (Set.ofPred p).Infinite) {k n} : nth p 
k <= nth p n ↔ k <= n
-/
theorem nth_le_nth' {m n : ℕ} (hle : m ≤ n) (h : ∀ hf : (Set.ofPred p).Finite, n < #hf.toFinset) :
    nth p m ≤ nth p n :=
  (Set.ofPred p).finite_or_infinite.elim (fun hf => nth_le_nth_of_lt_card hf hle (h _)) fun hf =>
    (nth_le_nth hf).2 hle
/-
**Nat.le_nth** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_nth {n : Nat} (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset)
 : n <= nth p n
参数：h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `StrictMonoOn.Iic_id_le`：StrictMonoOn.Iic_id_le [SuccOrder α] [IsSuccArch
imedean α] [OrderBot α] {n : α} {φ : α -> α} (hφ : StrictMonoOn φ (Set.Iic n)) :
 forall m <=…
· 使用定理 `Nat.instIsSuccArchimedean`：IsSuccArchimedean ℕ
· 使用定理 `StrictMonoOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f s → s₂ ⊆ s → S
trictMo…
· 使用定理 `Nat.nth_strictMonoOn`：nth_strictMonoOn (hf : (Set.ofPred p).Finite) : St
rictMonoOn (nth p) (Set.Iio #hf.toFinset)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iio`：Iic_subset_Iio : Iic a subseteq Iio b ↔ a < b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `Nat.nth_strictMono`：nth_strictMono (hf : (Set.ofPred p).Infinite) : Stri
ctMono (nth p)
-/
theorem le_nth {n : ℕ} (h : ∀ hf : (Set.ofPred p).Finite, n < #hf.toFinset) : n ≤ nth p n :=
  (Set.ofPred p).finite_or_infinite.elim
    (fun hf => ((nth_strictMonoOn hf).mono <| Set.Iic_subset_Iio.2 (h _)).Iic_id_le _ le_rfl)
    fun hf => (nth_strictMono hf).id_le _
/-
**Nat.isLeast_nth** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：isLeast_nth {n} (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset) 
: IsLeast {i | p i ∧ forall k < n, nth p k < i} (nth p n)
参数：h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_mem`：nth_mem (n : Nat) (h : forall hf : (Set.ofPred p).Finite, n
 < #hf.toFinset) : p (nth p n)
· 使用定理 `Nat.nth_lt_nth'`：nth_lt_nth' {m n : Nat} (hlt : m < n) (h : forall hf : 
(Set.ofPred p).Finite, n < #hf.toFinset) : nth p m < nth p n
· 使用定理 `Nat.exists_lt_card_nth_eq`：exists_lt_card_nth_eq {x} (h : p x) : exists 
n, (forall hf : (Set.ofPred p).Finite, n < #hf.toFinset) ∧ nth p n = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.nth_le_nth'`：nth_le_nth' {m n : Nat} (hle : m <= n) (h : forall hf :
 (Set.ofPred p).Finite, n < #hf.toFinset) : nth p m <= nth p n
-/
theorem isLeast_nth {n} (h : ∀ hf : (Set.ofPred p).Finite, n < #hf.toFinset) :
    IsLeast {i | p i ∧ ∀ k < n, nth p k < i} (nth p n) :=
  ⟨⟨nth_mem n h, fun _k hk => nth_lt_nth' hk h⟩, fun _x hx =>
    let ⟨k, hk, hkx⟩ := exists_lt_card_nth_eq hx.1
    (lt_or_ge k n).elim (fun hlt => absurd hkx (hx.2 _ hlt).ne) fun hle => hkx ▸ nth_le_nth' hle hk⟩
/-
**Nat.isLeast_nth_of_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：isLeast_nth_of_lt_card {n : Nat} (hf : (Set.ofPred p).Finite) (hn : n < #h
f.toFinset) : IsLeast {i | p i ∧ forall k < n, nth p k < i} (nth p n)
参数：hf : (Set.ofPred p).Finite；hn : n < #hf.toFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.isLeast_nth`：isLeast_nth {n} (h : forall hf : (Set.ofPred p).Finite,
 n < #hf.toFinset) : IsLeast {i | p i ∧ forall k < n, nth p k < i} (nth p n)
-/
theorem isLeast_nth_of_lt_card {n : ℕ} (hf : (Set.ofPred p).Finite) (hn : n < #hf.toFinset) :
    IsLeast {i | p i ∧ ∀ k < n, nth p k < i} (nth p n) :=
  isLeast_nth fun _ => hn
/-
**Nat.isLeast_nth_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：isLeast_nth_of_infinite (hf : (Set.ofPred p).Infinite) (n : Nat) : IsLeast
 {i | p i ∧ forall k < n, nth p k < i} (nth p n)
参数：hf : (Set.ofPred p).Infinite；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.isLeast_nth`：isLeast_nth {n} (h : forall hf : (Set.ofPred p).Finite,
 n < #hf.toFinset) : IsLeast {i | p i ∧ forall k < n, nth p k < i} (nth p n)
-/
theorem isLeast_nth_of_infinite (hf : (Set.ofPred p).Infinite) (n : ℕ) :
    IsLeast {i | p i ∧ ∀ k < n, nth p k < i} (nth p n) :=
  isLeast_nth fun h => absurd h hf

/-- An alternative recursive definition of `Nat.nth`: `Nat.nth s n` is the infimum of `x ∈ s` such
that `Nat.nth s k < x` for all `k < n`, if this set is nonempty. We do not assume that the set is
nonempty because we use the same "garbage value" `0` both for `sInf` on `ℕ` and for `Nat.nth s n`
for `n ≥ #s`. -/
/-
**Nat.nth_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_eq_sInf (p : Nat -> Prop) (n : Nat) : nth p n = sInf {x | p x ∧ forall
 k < n, nth p k < x}
参数：p : Nat -> Prop；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLeast.csInf_eq`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialO
rderInf α] {s : Set α} {a : α}, IsLeast s a → sInf s = a
· 使用定理 `Nat.isLeast_nth`：isLeast_nth {n} (h : forall hf : (Set.ofPred p).Finite,
 n < #hf.toFinset) : IsLeast {i | p i ∧ forall k < n, nth p k < i} (nth p n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_of_card_le`：nth_of_card_le (hf : (Set.ofPred p).Finite) {n : Nat
} (hn : #hf.toFinset <= n) : nth p n = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅
· 使用定理 `Nat.exists_lt_card_nth_eq`：exists_lt_card_nth_eq {x} (h : p x) : exists 
n, (forall hf : (Set.ofPred p).Finite, n < #hf.toFinset) ∧ nth p n = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.sInf_empty`：sInf_empty : sInf ∅ = 0

--- 原说明 ---
An alternative recursive definition of `Nat.nth`: `Nat.nth s n` is the infimum o
f `x ∈ s` such
that `Nat.nth s k < x` for all `k < n`, if this set is nonempty. We do not assum
e that the set is
nonempty because we use the same "garbage value" `0` both for `sInf` on `ℕ` and 
for `Nat.nth s n`
for `n ≥ #s`.
-/
theorem nth_eq_sInf (p : ℕ → Prop) (n : ℕ) : nth p n = sInf {x | p x ∧ ∀ k < n, nth p k < x} := by
  by_cases! hn : ∀ hf : (Set.ofPred p).Finite, n < #hf.toFinset
  · exact (isLeast_nth hn).csInf_eq.symm
  · rcases hn with ⟨hf, hn⟩
    rw [nth_of_card_le _ hn]
    refine ((congr_arg sInf <| Set.eq_empty_of_forall_notMem fun k hk => ?_).trans sInf_empty).symm
    rcases exists_lt_card_nth_eq hk.1 with ⟨k, hlt, rfl⟩
    exact (hk.2 _ ((hlt hf).trans_le hn)).false
/-
**Nat.nth_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_zero : nth p 0 = sInf (Set.ofPred p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_eq_sInf`：nth_eq_sInf (p : Nat -> Prop) (n : Nat) : nth p n = sIn
f {x | p x ∧ forall k < n, nth p k < x}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nth_zero : nth p 0 = sInf (Set.ofPred p) := by rw [nth_eq_sInf]; simp

@[simp]
/-
**Nat.nth_zero_of_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_zero_of_zero (h : p 0) : nth p 0 = 0
参数：h : p 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_zero`：nth_zero : nth p 0 = sInf (Set.ofPred p)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem nth_zero_of_zero (h : p 0) : nth p 0 = 0 := by simp [nth_zero, h]

set_option backward.isDefEq.respectTransparency false in
/-
**Nat.nth_zero_of_exists** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_zero_of_exists [DecidablePred p] (h : exists n, p n) : nth p 0 = Nat.f
ind h
参数：h : exists n, p n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_zero`：nth_zero : nth p 0 = sInf (Set.ofPred p)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.sInf_def`：sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.fi
nd (fun n => n in s) _ h
-/
theorem nth_zero_of_exists [DecidablePred p] (h : ∃ n, p n) : nth p 0 = Nat.find h := by
  rw [nth_zero]; convert! Nat.sInf_def h
/-
**Nat.nth_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_eq_zero {n} : nth p n = 0 ↔ p 0 ∧ n = 0 ∨ exists hf : (Set.ofPred p).F
inite, #hf.toFinset <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Nat.nth_mem`：nth_mem (n : Nat) (h : forall hf : (Set.ofPred p).Finite, n
 < #hf.toFinset) : p (nth p n)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Nat.le_nth`：le_nth {n : Nat} (h : forall hf : (Set.ofPred p).Finite, n <
 #hf.toFinset) : n <= nth p n
· 使用定理 `Nat.nth_zero_of_zero`：nth_zero_of_zero (h : p 0) : nth p 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.nth_of_card_le`：nth_of_card_le (hf : (Set.ofPred p).Finite) {n : Nat
} (hn : #hf.toFinset <= n) : nth p n = 0
-/
theorem nth_eq_zero {n} :
    nth p n = 0 ↔ p 0 ∧ n = 0 ∨ ∃ hf : (Set.ofPred p).Finite, #hf.toFinset ≤ n := by
  refine ⟨fun h => ?_, ?_⟩
  · simp only [or_iff_not_imp_right, not_exists, not_le]
    exact fun hn => ⟨h ▸ nth_mem _ hn, nonpos_iff_eq_zero.1 <| h ▸ le_nth hn⟩
  · rintro (⟨h₀, rfl⟩ | ⟨hf, hle⟩)
    exacts [nth_zero_of_zero h₀, nth_of_card_le hf hle]
/-
**Nat.lt_card_toFinset_of_nth_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：lt_card_toFinset_of_nth_ne_zero {n : Nat} (h : nth p n != 0) (hf : (Set.of
Pred p).Finite) : n < #hf.toFinset
参数：h : nth p n != 0；hf : (Set.ofPred p).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma lt_card_toFinset_of_nth_ne_zero {n : ℕ} (h : nth p n ≠ 0) (hf : (Set.ofPred p).Finite) :
    n < #hf.toFinset := by
  simp only [ne_eq, nth_eq_zero, not_or, not_exists, not_le] at h
  exact h.2 hf
/-
**Nat.nth_mem_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nth_mem_of_ne_zero {n : Nat} (h : nth p n != 0) : p (Nat.nth p n)
参数：h : nth p n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_mem`：nth_mem (n : Nat) (h : forall hf : (Set.ofPred p).Finite, n
 < #hf.toFinset) : p (nth p n)
· 使用引理 `Nat.lt_card_toFinset_of_nth_ne_zero`：lt_card_toFinset_of_nth_ne_zero {n 
: Nat} (h : nth p n != 0) (hf : (Set.ofPred p).Finite) : n < #hf.toFinset
-/
lemma nth_mem_of_ne_zero {n : ℕ} (h : nth p n ≠ 0) : p (Nat.nth p n) :=
  nth_mem n (lt_card_toFinset_of_nth_ne_zero h)
/-
**Nat.nth_eq_zero_mono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_eq_zero_mono (h₀ : ¬p 0) {a b : Nat} (hab : a <= b) (ha : nth p a = 0)
 : nth p b = 0
参数：h₀ : ¬p 0；hab : a <= b；ha : nth p a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem nth_eq_zero_mono (h₀ : ¬p 0) {a b : ℕ} (hab : a ≤ b) (ha : nth p a = 0) : nth p b = 0 := by
  simp only [nth_eq_zero, h₀, false_and, false_or] at ha ⊢
  exact ha.imp fun hf hle => hle.trans hab
/-
**Nat.nth_ne_zero_anti** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nth_ne_zero_anti (h₀ : ¬p 0) {a b : Nat} (hab : a <= b) (hb : nth p b != 0
) : nth p a != 0
参数：h₀ : ¬p 0；hab : a <= b；hb : nth p b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Nat.nth_eq_zero_mono`：nth_eq_zero_mono (h₀ : ¬p 0) {a b : Nat} (hab : a 
<= b) (ha : nth p a = 0) : nth p b = 0
-/
lemma nth_ne_zero_anti (h₀ : ¬p 0) {a b : ℕ} (hab : a ≤ b) (hb : nth p b ≠ 0) : nth p a ≠ 0 :=
  mt (nth_eq_zero_mono h₀ hab) hb
/-
**Nat.le_nth_of_lt_nth_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_nth_of_lt_nth_succ {k a : Nat} (h : a < nth p (k + 1)) (ha : p a) : a <
= nth p k
参数：h : a < nth p (k + 1)；ha : p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Nat.exists_lt_card_finite_nth_eq`：exists_lt_card_finite_nth_eq (hf : (Se
t.ofPred p).Finite) {x} (h : p x) : exists n, n < #hf.toFinset ∧ nth p n = x
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b
· 使用定理 `Nat.nth_strictMonoOn`：nth_strictMonoOn (hf : (Set.ofPred p).Finite) : St
rictMonoOn (nth p) (Set.Iio #hf.toFinset)
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `StrictMonoOn.lt_iff_lt`：StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a < f b ↔ a < b
· 使用定理 `Nat.nth_of_card_le`：nth_of_card_le (hf : (Set.ofPred p).Finite) {n : Nat
} (hn : #hf.toFinset <= n) : nth p n = 0
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.subset_range_nth`：subset_range_nth : Set.ofPred p subseteq Set.range
 (nth p)
· 使用定理 `Nat.nth_le_nth`：nth_le_nth (hf : (Set.ofPred p).Infinite) {k n} : nth p 
k <= nth p n ↔ k <= n
· 使用定理 `Nat.nth_lt_nth`：nth_lt_nth (hf : (Set.ofPred p).Infinite) {k n} : nth p 
k < nth p n ↔ k < n
-/
theorem le_nth_of_lt_nth_succ {k a : ℕ} (h : a < nth p (k + 1)) (ha : p a) : a ≤ nth p k := by
  rcases (Set.ofPred p).finite_or_infinite with hf | hf
  · rcases exists_lt_card_finite_nth_eq hf ha with ⟨n, hn, rfl⟩
    rcases lt_or_ge (k + 1) #hf.toFinset with hk | hk
    · rwa [(nth_strictMonoOn hf).lt_iff_lt hn hk, Nat.lt_succ_iff,
        ← (nth_strictMonoOn hf).le_iff_le hn (k.lt_succ_self.trans hk)] at h
    · rw [nth_of_card_le _ hk] at h
      exact absurd h (zero_le _).not_gt
  · rcases subset_range_nth ha with ⟨n, rfl⟩
    rwa [nth_lt_nth hf, Nat.lt_succ_iff, ← nth_le_nth hf] at h
/-
**Nat.nth_mem_anti** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nth_mem_anti {a b : Nat} (hab : a <= b) (h : p (nth p b)) : p (nth p a)
参数：hab : a <= b；h : p (nth p b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_mem`：nth_mem (n : Nat) (h : forall hf : (Set.ofPred p).Finite, n
 < #hf.toFinset) : p (nth p n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma nth_mem_anti {a b : ℕ} (hab : a ≤ b) (h : p (nth p b)) : p (nth p a) := by
  by_cases h' : ∀ hf : (Set.ofPred p).Finite, a < #hf.toFinset
  · exact nth_mem a h'
  · simp only [not_forall, not_lt] at h'
    have h'b : ∃ hf : (Set.ofPred p).Finite, #hf.toFinset ≤ b := by
      rcases h' with ⟨hf, ha⟩
      exact ⟨hf, ha.trans hab⟩
    have ha0 : nth p a = 0 := by simp [nth_eq_zero, h']
    have hb0 : nth p b = 0 := by simp [nth_eq_zero, h'b]
    rw [ha0]
    rwa [hb0] at h

/-- `Nat.nth p` is the least strictly monotone function whose image is contained in
`Set.ofPred p` -/
/-
**Nat.nth_le_of_strictMonoOn_of_mapsTo** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nth_le_of_strictMonoOn_of_mapsTo {p : Nat -> Prop} (f : Nat -> Nat) (hmaps
 : Set.MapsTo f { n : Nat | forall hf : Set.Finite (Set.ofPred p), n < hf.toFins
et.card } (Set.ofPred p)) (hmono : StrictMonoOn f { n : Nat | forall hf : Set.Fi
nite (Set.ofPred p), n < hf.toFinset.card }) {n : Nat} : nth p n <= f n
参数：f : Nat -> Nat；hmaps : Set.MapsTo f { n : Nat | forall hf : Set.Finite (Set.o
fPred p), n < hf.toFinset.card } (Set.ofPred p)；hmono : StrictMonoOn f { n : Nat
 | forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_eq_sInf`：nth_eq_sInf (p : Nat -> Prop) (n : Nat) : nth p n = sIn
f {x | p x ∧ forall k < n, nth p k < x}
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2
· 使用定理 `Nat.nth.eq_1`：∀ (p : ℕ → Prop) (n : ℕ),   Nat.nth p n =     if h : (Set.
ofPred p).Finite then (h.toFinset.sort fun a b => a ≤ b).getD n 0     else ↑((Na
t.…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `List.getD_eq_default`：getD_eq_default {n : Nat} (hn : l.length <= n) : l
.getD n d = d
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.length_sort`：length_sort : (sort s r).length = s.card
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n

--- 原说明 ---
`Nat.nth p` is the least strictly monotone function whose image is contained in
`Set.ofPred p`
-/
lemma nth_le_of_strictMonoOn_of_mapsTo {p : ℕ → Prop} (f : ℕ → ℕ)
    (hmaps : Set.MapsTo f { n : ℕ | ∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card }
      (Set.ofPred p))
    (hmono : StrictMonoOn f { n : ℕ | ∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card })
      {n : ℕ} :
    nth p n ≤ f n := by
  by_cases! hn : (∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card)
  · induction n using Nat.strong_induction_on with | _ n ih =>
    rw [nth_eq_sInf]
    refine csInf_le (by simp) ⟨hmaps hn, fun k hk => ?_⟩
    have : f k < f n := by apply hmono <;> grind
    grind
  · rcases hn with ⟨hf, hn⟩
    rw [nth, dif_pos hf, List.getD_eq_default _ _ (by simp [hn])]
    exact Nat.zero_le _

/-- `Nat.nth p` is the greatest monotone function whose image contains `Set.ofPred p`. -/
/-
**Nat.le_nth_of_monotoneOn_of_surjOn** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：le_nth_of_monotoneOn_of_surjOn {p : Nat -> Prop} (f : Nat -> Nat) (hsurj :
 Set.SurjOn f { n : Nat | forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset
.card } (Set.ofPred p)) (hmono : MonotoneOn f { n : Nat | forall hf : Set.Finite
 (Set.ofPred p), n < hf.toFinset.card }) {n : Nat} (hn : forall hf : Set.Finite 
(Set.ofPred p), n < hf.toFinset.card) : f n <= nth p n
参数：f : Nat -> Nat；hsurj : Set.SurjOn f { n : Nat | forall hf : Set.Finite (Set.o
fPred p), n < hf.toFinset.card } (Set.ofPred p)；hmono : MonotoneOn f { n : Nat |
 forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card }；hn : forall hf : 
Set.Finite (Set.ofPred p), n < hf.toFinset.card。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_zero`：nth_zero : nth p 0 = sInf (Set.ofPred p)
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Nat.nth_mem`：nth_mem (n : Nat) (h : forall hf : (Set.ofPred p).Finite, n
 < #hf.toFinset) : p (nth p n)
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.nth_eq_sInf`：nth_eq_sInf (p : Nat -> Prop) (n : Nat) : nth p n = sIn
f {x | p x ∧ forall k < n, nth p k < x}
· 使用定理 `Nat.nth_lt_nth'`：nth_lt_nth' {m n : Nat} (hlt : m < n) (h : forall hf : 
(Set.ofPred p).Finite, n < #hf.toFinset) : nth p m < nth p n
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `MonotoneOn.reflect_lt`：MonotoneOn.reflect_lt (hf : MonotoneOn f s) {a b 
: α} (ha : a in s) (hb : b in s) (h : f a < f b) : a < b

--- 原说明 ---
`Nat.nth p` is the greatest monotone function whose image contains `Set.ofPred p
`.
-/
lemma le_nth_of_monotoneOn_of_surjOn {p : ℕ → Prop} (f : ℕ → ℕ)
    (hsurj : Set.SurjOn f { n : ℕ | ∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card }
      (Set.ofPred p))
    (hmono : MonotoneOn f { n : ℕ | ∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card })
      {n : ℕ}
    (hn : ∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card) : f n ≤ nth p n := by
  induction n with
  | zero =>
    rw [Nat.nth_zero]
    refine le_csInf ⟨_, nth_mem _ hn⟩ fun b hb => ?_
    rcases hsurj hb with ⟨k, hk, rfl⟩
    exact hmono hn hk (Nat.zero_le _)
  | succ n ih =>
    rw [nth_eq_sInf]
    refine le_csInf ?_ ?_
    · use nth p (n + 1), nth_mem _ hn
      exact fun k hk => nth_lt_nth' hk hn
    rintro b ⟨hb, h⟩
    rcases hsurj hb with ⟨m, hm, rfl⟩
    apply hmono hn hm
    rw [Nat.succ_le_iff]
    apply hmono.reflect_lt <;> grind

/-- `Nat.nth p` is the unique strictly monotone function whose image is `Set.ofPred p`. -/
/-
**Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn** 是 Mathlib 中的一个引理，位于命名空间 `Nat`
。
形式化陈述：eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn {p : Nat -> Prop} (f : Nat -> N
at) (hsurj : Set.SurjOn f { n : Nat | forall hf : Set.Finite (Set.ofPred p), n <
 hf.toFinset.card } (Set.ofPred p)) (hmaps : Set.MapsTo f { n : Nat | forall hf 
: Set.Finite (Set.ofPred p), n < hf.toFinset.card } (Set.ofPred p)) (hmono : Str
ictMonoOn f { n : Nat | forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.c
ard }) : Set.EqOn f (nth p) { n : Nat | forall hf : Set.Finite (Set.ofPred p), n
 < hf.toFinset.card }
参数：f : Nat -> Nat；hsurj : Set.SurjOn f { n : Nat | forall hf : Set.Finite (Set.o
fPred p), n < hf.toFinset.card } (Set.ofPred p)；hmaps : Set.MapsTo f { n : Nat |
 forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card } (Set.ofPred p)；hm
ono : StrictMonoOn f { n : Nat | forall hf : Set.Finite (Set.ofPred p), n < hf.t
oFinset.card }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Nat.le_nth_of_monotoneOn_of_surjOn`：le_nth_of_monotoneOn_of_surjOn {p : 
Nat -> Prop} (f : Nat -> Nat) (hsurj : Set.SurjOn f { n : Nat | forall hf : Set.
Finite (Set.ofPred p), n…
· 使用定理 `StrictMonoOn.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : PartialOrde
r α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → Monoton
eOn f s
· 使用引理 `Nat.nth_le_of_strictMonoOn_of_mapsTo`：nth_le_of_strictMonoOn_of_mapsTo {
p : Nat -> Prop} (f : Nat -> Nat) (hmaps : Set.MapsTo f { n : Nat | forall hf : 
Set.Finite (Set.ofPred p),…

--- 原说明 ---
`Nat.nth p` is the unique strictly monotone function whose image is `Set.ofPred 
p`.
-/
lemma eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn {p : ℕ → Prop} (f : ℕ → ℕ)
    (hsurj : Set.SurjOn f { n : ℕ | ∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card }
      (Set.ofPred p))
    (hmaps : Set.MapsTo f { n : ℕ | ∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card }
      (Set.ofPred p))
    (hmono : StrictMonoOn f { n : ℕ | ∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card }) :
    Set.EqOn f (nth p) { n : ℕ | ∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card } :=
  fun _ hi => le_antisymm
    (Nat.le_nth_of_monotoneOn_of_surjOn _ hsurj hmono.monotoneOn hi)
    (Nat.nth_le_of_strictMonoOn_of_mapsTo _ hmaps hmono)
/-
**Nat.nth_comp_of_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nth_comp_of_strictMono {n : Nat} {f : Nat -> Nat} (hf : StrictMono f) (h0 
: forall k, p k -> k in Set.range f) (h : forall hfi : (Set.ofPred p).Finite, n 
< hfi.toFinset.card) : f (nth (fun i => p (f i)) n) = nth p n
参数：hf : StrictMono f；h0 : forall k, p k -> k in Set.range f；h : forall hfi : (Se
t.ofPred p).Finite, n < hfi.toFinset.card。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.case_strong_induction_on`：∀ {p : ℕ → Prop} (a : ℕ), p 0 → (∀ (n : ℕ)
, (∀ m ≤ n, p m) → p (n + 1)) → p a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_zero`：nth_zero : nth p 0 = sInf (Set.ofPred p)
· 使用定理 `Nat.nth_mem`：nth_mem (n : Nat) (h : forall hf : (Set.ofPred p).Finite, n
 < #hf.toFinset) : p (nth p n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_csInf`：Monotone.map_csInf {β : Type*} [ConditionallyComplet
eLattice β] {f : α -> β} (hf : Monotone f) (hs : s.Nonempty) : f (sInf s) = sInf
 (f '' s…
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Nat.nth_eq_sInf`：nth_eq_sInf (p : Nat -> Prop) (n : Nat) : nth p n = sIn
f {x | p x ∧ forall k < n, nth p k < x}
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.nth_lt_nth'`：nth_lt_nth' {m n : Nat} (hlt : m < n) (h : forall hf : 
(Set.ofPred p).Finite, n < #hf.toFinset) : nth p m < nth p n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_add_one_iff`：∀ {m n : ℕ}, m < n + 1 ↔ m ≤ n
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nth_comp_of_strictMono {n : ℕ} {f : ℕ → ℕ} (hf : StrictMono f)
    (h0 : ∀ k, p k → k ∈ Set.range f) (h : ∀ hfi : (Set.ofPred p).Finite, n < hfi.toFinset.card) :
    f (nth (fun i ↦ p (f i)) n) = nth p n := by
  have hs {p' : ℕ → Prop} (h0p' : ∀ k, p' k → k ∈ Set.range f) :
      f '' {i | p' (f i)} = Set.ofPred p' := by
    ext i
    refine ⟨fun ⟨_, hi, h⟩ ↦ h ▸ hi, fun he ↦ ?_⟩
    rcases h0p' _ he with ⟨t, rfl⟩
    exact ⟨t, he, rfl⟩
  induction n using Nat.case_strong_induction_on
  case _ =>
    simp_rw [nth_zero]
    replace h := nth_mem _ h
    rw [← hs h0, ← hf.monotone.map_csInf]
    rcases h0 _ h with ⟨t, ht⟩
    exact ⟨t, Set.mem_ofPred_eq ▸ ht ▸ h⟩
  case _ n ih =>
    repeat nth_rw 1 [nth_eq_sInf]
    have h0' : ∀ k', (p k' ∧ ∀ k < n + 1, nth p k < k') → k' ∈ Set.range f := fun _ h ↦ h0 _ h.1
    rw [← hs h0', ← hf.monotone.map_csInf]
    · convert! rfl using 8 with k m' hm
      nth_rw 2 [← hf.lt_iff_lt]
      convert! Iff.rfl using 2
      exact ih m' (Nat.lt_add_one_iff.mp hm) fun hfi ↦ hm.trans (h hfi)
    · rcases h0 _ (nth_mem _ h) with ⟨t, ht⟩
      exact ⟨t, ht ▸ (nth_mem _ h), fun _ hk ↦ ht ▸ nth_lt_nth' hk h⟩
/-
**Nat.nth_add** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nth_add {m n : Nat} (h0 : forall k < m, ¬p k) (h : nth p n != 0) : nth (fu
n i => p (i + m)) n + m = nth p n
参数：h0 : forall k < m, ¬p k；h : nth p n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.nth_comp_of_strictMono`：nth_comp_of_strictMono {n : Nat} {f : Nat ->
 Nat} (hf : StrictMono f) (h0 : forall k, p k -> k in Set.range f) (h : forall h
fi : (Set.ofPred…
· 使用定理 `StrictMono.add_const`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α] [in
st_1 : Preorder α] [inst_2 : Preorder β] {f : β → α}   [AddRightStrictMono α], S
trictMono …
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `le_iff_exists_add'`：∀ {α : Type u} [inst : AddCommMagma α] [inst_1 : Pre
order α] [CanonicallyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = c + a
· 使用引理 `Nat.lt_card_toFinset_of_nth_ne_zero`：lt_card_toFinset_of_nth_ne_zero {n 
: Nat} (h : nth p n != 0) (hf : (Set.ofPred p).Finite) : n < #hf.toFinset
-/
lemma nth_add {m n : ℕ} (h0 : ∀ k < m, ¬p k) (h : nth p n ≠ 0) :
    nth (fun i ↦ p (i + m)) n + m = nth p n := by
  refine nth_comp_of_strictMono (strictMono_id.add_const m) (fun k hk ↦ ?_)
    (fun hf ↦ lt_card_toFinset_of_nth_ne_zero h hf)
  by_contra hn
  simp_rw [id_eq, Set.mem_range, eq_comm] at hn
  exact h0 _ (not_le.mp fun h ↦ hn (le_iff_exists_add'.mp h)) hk
/-
**Nat.nth_add_eq_sub** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nth_add_eq_sub {m n : Nat} (h0 : forall k < m, ¬p k) (h : nth p n != 0) : 
nth (fun i => p (i + m)) n = nth p n - m
参数：h0 : forall k < m, ¬p k；h : nth p n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.nth_add`：nth_add {m n : Nat} (h0 : forall k < m, ¬p k) (h : nth p n 
!= 0) : nth (fun i => p (i + m)) n + m = nth p n
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
-/
lemma nth_add_eq_sub {m n : ℕ} (h0 : ∀ k < m, ¬p k) (h : nth p n ≠ 0) :
    nth (fun i ↦ p (i + m)) n = nth p n - m := by
  rw [← nth_add h0 h, Nat.add_sub_cancel]
/-
**Nat.nth_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nth_add_one {n : Nat} (h0 : ¬p 0) (h : nth p n != 0) : nth (fun i => p (i 
+ 1)) n + 1 = nth p n
参数：h0 : ¬p 0；h : nth p n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.nth_add`：nth_add {m n : Nat} (h0 : forall k < m, ¬p k) (h : nth p n 
!= 0) : nth (fun i => p (i + m)) n + m = nth p n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
-/
lemma nth_add_one {n : ℕ} (h0 : ¬p 0) (h : nth p n ≠ 0) :
    nth (fun i ↦ p (i + 1)) n + 1 = nth p n :=
  nth_add (fun _ hk ↦ (lt_one_iff.1 hk ▸ h0)) h
/-
**Nat.nth_add_one_eq_sub** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nth_add_one_eq_sub {n : Nat} (h0 : ¬p 0) (h : nth p n != 0) : nth (fun i =
> p (i + 1)) n = nth p n - 1
参数：h0 : ¬p 0；h : nth p n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.nth_add_eq_sub`：nth_add_eq_sub {m n : Nat} (h0 : forall k < m, ¬p k)
 (h : nth p n != 0) : nth (fun i => p (i + m)) n = nth p n - m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
-/
lemma nth_add_one_eq_sub {n : ℕ} (h0 : ¬p 0) (h : nth p n ≠ 0) :
    nth (fun i ↦ p (i + 1)) n = nth p n - 1 :=
  nth_add_eq_sub (fun _ hk ↦ (lt_one_iff.1 hk ▸ h0)) h

section Count

variable (p) [DecidablePred p]

@[simp]
/-
**Nat.count_nth_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_nth_zero : count p (nth p 0) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_eq_card_filter_range`：count_eq_card_filter_range (n : Nat) : c
ount p n = #{x in range n | p x}
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Finset.filter_eq_empty_iff`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, Finset.filter p s = ∅ ↔ ∀ ⦃x : α⦄, x ∈ s → ¬p x
· 使用定理 `Nat.nth_zero`：nth_zero : nth p 0 = sInf (Set.ofPred p)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
-/
theorem count_nth_zero : count p (nth p 0) = 0 := by
  rw [count_eq_card_filter_range, card_eq_zero, filter_eq_empty_iff, nth_zero]
  exact fun n h₁ h₂ => (mem_range.1 h₁).not_ge (Nat.sInf_le h₂)
/-
**Nat.filter_range_nth_subset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：filter_range_nth_subset_insert (k : Nat) : {n in range (nth p (k + 1)) | p
 n} subseteq insert (nth p k) {n in range (nth p k) | p n}
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Nat.le_nth_of_lt_nth_succ`：le_nth_of_lt_nth_succ {k a : Nat} (h : a < nt
h p (k + 1)) (ha : p a) : a <= nth p k
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem filter_range_nth_subset_insert (k : ℕ) :
    {n ∈ range (nth p (k + 1)) | p n} ⊆ insert (nth p k) {n ∈ range (nth p k) | p n} := by
  intro a ha
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢
  exact (le_nth_of_lt_nth_succ ha.1 ha.2).eq_or_lt.imp_right fun h => ⟨h, ha.2⟩

variable {p}
/-
**Nat.filter_range_nth_eq_insert** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：filter_range_nth_eq_insert {k : Nat} (hlt : forall hf : (Set.ofPred p).Fin
ite, k + 1 < #hf.toFinset) : {n in range (nth p (k + 1)) | p n} = insert (nth p 
k) {n in range (nth p k) | p n}
参数：hlt : forall hf : (Set.ofPred p).Finite, k + 1 < #hf.toFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Nat.filter_range_nth_subset_insert`：filter_range_nth_subset_insert (k : 
Nat) : {n in range (nth p (k + 1)) | p n} subseteq insert (nth p k) {n in range 
(nth p k) | p n}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_lt_nth'`：nth_lt_nth' {m n : Nat} (hlt : m < n) (h : forall hf : 
(Set.ofPred p).Finite, n < #hf.toFinset) : nth p m < nth p n
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.nth_mem`：nth_mem (n : Nat) (h : forall hf : (Set.ofPred p).Finite, n
 < #hf.toFinset) : p (nth p n)
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem filter_range_nth_eq_insert {k : ℕ}
    (hlt : ∀ hf : (Set.ofPred p).Finite, k + 1 < #hf.toFinset) :
    {n ∈ range (nth p (k + 1)) | p n} = insert (nth p k) {n ∈ range (nth p k) | p n} := by
  refine (filter_range_nth_subset_insert p k).antisymm fun a ha => ?_
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢
  have : nth p k < nth p (k + 1) := nth_lt_nth' k.lt_succ_self hlt
  rcases ha with (rfl | ⟨hlt, hpa⟩)
  · exact ⟨this, nth_mem _ fun hf => k.lt_succ_self.trans (hlt hf)⟩
  · exact ⟨hlt.trans this, hpa⟩
/-
**Nat.filter_range_nth_eq_insert_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：filter_range_nth_eq_insert_of_finite (hf : (Set.ofPred p).Finite) {k : Nat
} (hlt : k + 1 < #hf.toFinset) : {n in range (nth p (k + 1)) | p n} = insert (nt
h p k) {n in range (nth p k) | p n}
参数：hf : (Set.ofPred p).Finite；hlt : k + 1 < #hf.toFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.filter_range_nth_eq_insert`：filter_range_nth_eq_insert {k : Nat} (hl
t : forall hf : (Set.ofPred p).Finite, k + 1 < #hf.toFinset) : {n in range (nth 
p (k + 1)) | p n} = …
-/
theorem filter_range_nth_eq_insert_of_finite (hf : (Set.ofPred p).Finite) {k : ℕ}
    (hlt : k + 1 < #hf.toFinset) :
    {n ∈ range (nth p (k + 1)) | p n} = insert (nth p k) {n ∈ range (nth p k) | p n} :=
  filter_range_nth_eq_insert fun _ => hlt
/-
**Nat.filter_range_nth_eq_insert_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：filter_range_nth_eq_insert_of_infinite (hp : (Set.ofPred p).Infinite) (k :
 Nat) : {n in range (nth p (k + 1)) | p n} = insert (nth p k) {n in range (nth p
 k) | p n}
参数：hp : (Set.ofPred p).Infinite；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.filter_range_nth_eq_insert`：filter_range_nth_eq_insert {k : Nat} (hl
t : forall hf : (Set.ofPred p).Finite, k + 1 < #hf.toFinset) : {n in range (nth 
p (k + 1)) | p n} = …
-/
theorem filter_range_nth_eq_insert_of_infinite (hp : (Set.ofPred p).Infinite) (k : ℕ) :
    {n ∈ range (nth p (k + 1)) | p n} = insert (nth p k) {n ∈ range (nth p k) | p n} :=
  filter_range_nth_eq_insert fun hf => absurd hf hp
/-
**Nat.count_nth** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_nth {n : Nat} (hn : forall hf : (Set.ofPred p).Finite, n < #hf.toFin
set) : count p (nth p n) = n
参数：hn : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.count_nth_zero`：count_nth_zero : count p (nth p 0) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_eq_card_filter_range`：count_eq_card_filter_range (n : Nat) : c
ount p n = #{x in range n | p x}
· 使用定理 `Nat.filter_range_nth_eq_insert`：filter_range_nth_eq_insert {k : Nat} (hl
t : forall hf : (Set.ofPred p).Finite, k + 1 < #hf.toFinset) : {n in range (nth 
p (k + 1)) | p n} = …
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_of_succ_lt`：∀ {n m : ℕ}, n.succ < m → n < m
-/
theorem count_nth {n : ℕ} (hn : ∀ hf : (Set.ofPred p).Finite, n < #hf.toFinset) :
    count p (nth p n) = n := by
  induction n with
  | zero => exact count_nth_zero _
  | succ k ihk =>
    rw [count_eq_card_filter_range, filter_range_nth_eq_insert hn, card_insert_of_notMem,
      ← count_eq_card_filter_range, ihk fun hf => lt_of_succ_lt (hn hf)]
    simp
/-
**Nat.count_nth_of_lt_card_finite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_nth_of_lt_card_finite {n : Nat} (hp : (Set.ofPred p).Finite) (hlt : 
n < #hp.toFinset) : count p (nth p n) = n
参数：hp : (Set.ofPred p).Finite；hlt : n < #hp.toFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.count_nth`：count_nth {n : Nat} (hn : forall hf : (Set.ofPred p).Fini
te, n < #hf.toFinset) : count p (nth p n) = n
-/
theorem count_nth_of_lt_card_finite {n : ℕ} (hp : (Set.ofPred p).Finite) (hlt : n < #hp.toFinset) :
    count p (nth p n) = n :=
  count_nth fun _ => hlt
/-
**Nat.count_nth_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_nth_of_infinite (hp : (Set.ofPred p).Infinite) (n : Nat) : count p (
nth p n) = n
参数：hp : (Set.ofPred p).Infinite；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.count_nth`：count_nth {n : Nat} (hn : forall hf : (Set.ofPred p).Fini
te, n < #hf.toFinset) : count p (nth p n) = n
-/
theorem count_nth_of_infinite (hp : (Set.ofPred p).Infinite) (n : ℕ) : count p (nth p n) = n :=
  count_nth fun hf => absurd hf hp
/-
**Nat.surjective_count_of_infinite_setOfPred** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：surjective_count_of_infinite_setOfPred (h : {n | p n}.Infinite) : Function
.Surjective (Nat.count p)
参数：h : {n | p n}.Infinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.count_nth_of_infinite`：count_nth_of_infinite (hp : (Set.ofPred p).In
finite) (n : Nat) : count p (nth p n) = n
-/
theorem surjective_count_of_infinite_setOfPred (h : {n | p n}.Infinite) :
    Function.Surjective (Nat.count p) :=
  fun n => ⟨nth p n, count_nth_of_infinite h n⟩

@[deprecated (since := "2026-07-09")]
alias surjective_count_of_infinite_setOf := surjective_count_of_infinite_setOfPred
/-
**Nat.count_nth_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_nth_succ {n : Nat} (hn : forall hf : (Set.ofPred p).Finite, n < #hf.
toFinset) : count p (nth p n + 1) = n + 1
参数：hn : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_succ`：count_succ (n : Nat) : count p (n + 1) = count p n + if 
p n then 1 else 0
· 使用定理 `Nat.count_nth`：count_nth {n : Nat} (hn : forall hf : (Set.ofPred p).Fini
te, n < #hf.toFinset) : count p (nth p n) = n
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.nth_mem`：nth_mem (n : Nat) (h : forall hf : (Set.ofPred p).Finite, n
 < #hf.toFinset) : p (nth p n)
-/
theorem count_nth_succ {n : ℕ} (hn : ∀ hf : (Set.ofPred p).Finite, n < #hf.toFinset) :
    count p (nth p n + 1) = n + 1 := by rw [count_succ, count_nth hn, if_pos (nth_mem _ hn)]
/-
**Nat.count_nth_succ_of_infinite** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：count_nth_succ_of_infinite (hp : (Set.ofPred p).Infinite) (n : Nat) : coun
t p (nth p n + 1) = n + 1
参数：hp : (Set.ofPred p).Infinite；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_succ`：count_succ (n : Nat) : count p (n + 1) = count p n + if 
p n then 1 else 0
· 使用定理 `Nat.count_nth_of_infinite`：count_nth_of_infinite (hp : (Set.ofPred p).In
finite) (n : Nat) : count p (nth p n) = n
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.nth_mem_of_infinite`：nth_mem_of_infinite (hf : (Set.ofPred p).Infini
te) (n : Nat) : p (nth p n)
-/
lemma count_nth_succ_of_infinite (hp : (Set.ofPred p).Infinite) (n : ℕ) :
    count p (nth p n + 1) = n + 1 := by
  rw [count_succ, count_nth_of_infinite hp, if_pos (nth_mem_of_infinite hp _)]

@[simp]
/-
**Nat.nth_count** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_count {n : Nat} (hpn : p n) : nth p (count p n) = n
参数：hpn : p n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.count_lt_card`：count_lt_card {n : Nat} (hp : (Set.ofPred p).Finite) 
(hpn : p n) : count p n < #hp.toFinset
· 使用定理 `Nat.count_injective`：count_injective {m n : Nat} (hm : p m) (hn : p n) (
heq : count p m = count p n) : m = n
· 使用定理 `Nat.nth_mem`：nth_mem (n : Nat) (h : forall hf : (Set.ofPred p).Finite, n
 < #hf.toFinset) : p (nth p n)
· 使用定理 `Nat.count_nth`：count_nth {n : Nat} (hn : forall hf : (Set.ofPred p).Fini
te, n < #hf.toFinset) : count p (nth p n) = n
-/
theorem nth_count {n : ℕ} (hpn : p n) : nth p (count p n) = n :=
  have : ∀ hf : (Set.ofPred p).Finite, count p n < #hf.toFinset := fun hf => count_lt_card hf hpn
  count_injective (nth_mem _ this) hpn (count_nth this)
/-
**Nat.nth_lt_of_lt_count** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_lt_of_lt_count {n k : Nat} (h : k < count p n) : nth p k < n
参数：h : k < count p n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用定理 `Nat.count_monotone`：count_monotone : Monotone (count p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_nth`：count_nth {n : Nat} (hn : forall hf : (Set.ofPred p).Fini
te, n < #hf.toFinset) : count p (nth p n) = n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.count_le_card`：count_le_card (hp : (Set.ofPred p).Finite) (n : Nat) 
: count p n <= #hp.toFinset
-/
theorem nth_lt_of_lt_count {n k : ℕ} (h : k < count p n) : nth p k < n := by
  refine (count_monotone p).reflect_lt ?_
  rwa [count_nth]
  exact fun hf => h.trans_le (count_le_card hf n)
/-
**Nat.le_nth_of_count_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_nth_of_count_le {n k : Nat} (h : n <= nth p k) : count p n <= k
参数：h : n <= nth p k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.nth_lt_of_lt_count`：nth_lt_of_lt_count {n k : Nat} (h : k < count p 
n) : nth p k < n
-/
theorem le_nth_of_count_le {n k : ℕ} (h : n ≤ nth p k) : count p n ≤ k :=
  not_lt.1 fun hlt => h.not_gt <| nth_lt_of_lt_count hlt
/-
**Nat.count_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {p : ℕ → Prop} [inst : DecidablePred p], (∃ n, p n) → ∀ {n : ℕ}, Nat.cou
nt p n = 0 ↔ n ≤ Nat.nth p 0
参数：∃ n, p n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.nth_zero_of_exists`：nth_zero_of_exists [DecidablePred p] (h : exists
 n, p n) : nth p 0 = Nat.find h
· 使用定理 `Nat.le_find_iff`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (h : ∃ n, p n
) (n : ℕ), n ≤ Nat.find h ↔ ∀ m < n, ¬p m
· 使用定理 `Nat.count_iff_forall_not`：count_iff_forall_not {n : Nat} : count p n = 0
 ↔ forall m < n, ¬p m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem count_eq_zero (h : ∃ n, p n) {n : ℕ} : count p n = 0 ↔ n ≤ nth p 0 := by
  rw [nth_zero_of_exists h, le_find_iff h, Nat.count_iff_forall_not]

variable (p) in
/-
**Nat.nth_count_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_count_eq_sInf (n : Nat) : nth p (count p n) = sInf {i : Nat | p i ∧ n 
<= i}
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.nth_eq_sInf`：nth_eq_sInf (p : Nat -> Prop) (n : Nat) : nth p n = sIn
f {x | p x ∧ forall k < n, nth p k < x}
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.count_strict_mono`：count_strict_mono {m n : Nat} (hm : p m) (hmn : m
 < n) : count p m < count p n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_self_iff_false`：lt_self_iff_false (x : α) : x < x ↔ False
· 使用定理 `Nat.nth_count`：nth_count {n : Nat} (hpn : p n) : nth p (count p n) = n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.nth_lt_of_lt_count`：nth_lt_of_lt_count {n k : Nat} (h : k < count p 
n) : nth p k < n
-/
theorem nth_count_eq_sInf (n : ℕ) : nth p (count p n) = sInf {i : ℕ | p i ∧ n ≤ i} := by
  refine (nth_eq_sInf _ _).trans (congr_arg sInf ?_)
  refine Set.ext fun a => and_congr_right fun hpa => ?_
  refine ⟨fun h => not_lt.1 fun ha => ?_, fun hn k hk => lt_of_lt_of_le (nth_lt_of_lt_count hk) hn⟩
  have hn : nth p (count p a) < a := h _ (count_strict_mono hpa ha)
  rwa [nth_count hpa, lt_self_iff_false] at hn
/-
**Nat.le_nth_count'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_nth_count' {n : Nat} (hpn : exists k, p k ∧ n <= k) : n <= nth p (count
 p n)
参数：hpn : exists k, p k ∧ n <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Nat.nth_count_eq_sInf`：nth_count_eq_sInf (n : Nat) : nth p (count p n) =
 sInf {i : Nat | p i ∧ n <= i}
-/
theorem le_nth_count' {n : ℕ} (hpn : ∃ k, p k ∧ n ≤ k) : n ≤ nth p (count p n) :=
  (le_csInf hpn fun _ => And.right).trans (nth_count_eq_sInf p n).ge
/-
**Nat.le_nth_count** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_nth_count (hp : (Set.ofPred p).Infinite) (n : Nat) : n <= nth p (count 
p n)
参数：hp : (Set.ofPred p).Infinite；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.exists_gt`：∀ {α : Type u_2} [inst : LinearOrder α] [Locally
FiniteOrderBot α] {s : Set α}, s.Infinite → ∀ (a : α), ∃ b ∈ s, a < b
· 使用定理 `Nat.le_nth_count'`：le_nth_count' {n : Nat} (hpn : exists k, p k ∧ n <= k
) : n <= nth p (count p n)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem le_nth_count (hp : (Set.ofPred p).Infinite) (n : ℕ) : n ≤ nth p (count p n) :=
  let ⟨m, hp, hn⟩ := hp.exists_gt n
  le_nth_count' ⟨m, hp, hn.le⟩

/-- If a predicate `p : ℕ → Prop` is true for infinitely many numbers, then `Nat.count p` and
`Nat.nth p` form a Galois insertion. -/
/-
**Nat.giCountNth** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：giCountNth (hp : (Set.ofPred p).Infinite) : GaloisInsertion (count p) (nth
 p)
参数：hp : (Set.ofPred p).Infinite。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_monotone`：nth_monotone (hf : (Set.ofPred p).Infinite) : Monotone
 (nth p)
· 使用定理 `Nat.count_monotone`：count_monotone : Monotone (count p)
· 使用定理 `Nat.le_nth_count`：le_nth_count (hp : (Set.ofPred p).Infinite) (n : Nat) 
: n <= nth p (count p n)
· 使用定理 `Nat.count_nth_of_infinite`：count_nth_of_infinite (hp : (Set.ofPred p).In
finite) (n : Nat) : count p (nth p n) = n

--- 原说明 ---
If a predicate `p : ℕ → Prop` is true for infinitely many numbers, then `Nat.cou
nt p` and
`Nat.nth p` form a Galois insertion.
-/
noncomputable def giCountNth (hp : (Set.ofPred p).Infinite) : GaloisInsertion (count p) (nth p) :=
  GaloisInsertion.monotoneIntro (nth_monotone hp) (count_monotone p) (le_nth_count hp)
    (count_nth_of_infinite hp)
/-
**Nat.gc_count_nth** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：gc_count_nth (hp : (Set.ofPred p).Infinite) : GaloisConnection (count p) (
nth p)
参数：hp : (Set.ofPred p).Infinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem gc_count_nth (hp : (Set.ofPred p).Infinite) : GaloisConnection (count p) (nth p) :=
  (giCountNth hp).gc
/-
**Nat.count_le_iff_le_nth** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_le_iff_le_nth (hp : (Set.ofPred p).Infinite) {a b : Nat} : count p a
 <= b ↔ a <= nth p b
参数：hp : (Set.ofPred p).Infinite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.gc_count_nth`：gc_count_nth (hp : (Set.ofPred p).Infinite) : GaloisCo
nnection (count p) (nth p)
-/
theorem count_le_iff_le_nth (hp : (Set.ofPred p).Infinite) {a b : ℕ} :
    count p a ≤ b ↔ a ≤ nth p b :=
  gc_count_nth hp _ _
/-
**Nat.lt_nth_iff_count_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_nth_iff_count_lt (hp : (Set.ofPred p).Infinite) {a b : Nat} : a < count
 p b ↔ nth p a < b
参数：hp : (Set.ofPred p).Infinite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.lt_iff_lt`：lt_iff_lt (gc : GaloisConnection l u) {a : α
} {b : β} : b < l a ↔ u b < a
· 使用定理 `Nat.gc_count_nth`：gc_count_nth (hp : (Set.ofPred p).Infinite) : GaloisCo
nnection (count p) (nth p)
-/
theorem lt_nth_iff_count_lt (hp : (Set.ofPred p).Infinite) {a b : ℕ} :
    a < count p b ↔ nth p a < b :=
  (gc_count_nth hp).lt_iff_lt

end Count

/-
**Nat.nth_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_of_forall {n : Nat} (hp : forall n' <= n, p n') : nth p n = n
参数：hp : forall n' <= n, p n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.count_of_forall`：∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, 
(∀ n' < n, p n') → Nat.count p n = n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.nth_count`：nth_count {n : Nat} (hpn : p n) : nth p (count p n) = n
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem nth_of_forall {n : ℕ} (hp : ∀ n' ≤ n, p n') : nth p n = n := by
  classical nth_rw 1 [← count_of_forall (hp · ·.le), nth_count (hp n le_rfl)]
/-
**Nat.nth_true** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), Nat.nth (fun x => True) n = n
参数：n : ℕ；fun x => True。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_of_forall`：nth_of_forall {n : Nat} (hp : forall n' <= n, p n') :
 nth p n = n
· 使用定理 `trivial`：True
-/
@[simp] theorem nth_true (n : ℕ) : nth (fun _ ↦ True) n = n := nth_of_forall fun _ _ ↦ trivial
/-
**Nat.nth_of_forall_not** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_of_forall_not {n : Nat} (hp : forall n' >= n, ¬p n') : nth p n = 0
参数：hp : forall n' >= n, ¬p n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Nat.nth_of_card_le`：nth_of_card_le (hf : (Set.ofPred p).Finite) {n : Nat
} (hn : #hf.toFinset <= n) : nth p n = 0
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.toFinset_subset`：toFinset_subset {t : Finset α} : hs.toFinset
 subseteq t ↔ s subseteq t
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
-/
theorem nth_of_forall_not {n : ℕ} (hp : ∀ n' ≥ n, ¬p n') : nth p n = 0 := by
  have : Set.ofPred p ⊆ Finset.range n := by
    intro n' hn'
    contrapose! hp
    exact ⟨n', by simpa using hp, Set.mem_ofPred.mp hn'⟩
  rw [nth_of_card_le ((finite_toSet _).subset this)]
  · refine (Finset.card_le_card ?_).trans_eq (Finset.card_range n)
    exact Set.Finite.toFinset_subset.mpr this
/-
**Nat.nth_false** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), Nat.nth (fun x => False) n = 0
参数：n : ℕ；fun x => False。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_of_forall_not`：nth_of_forall_not {n : Nat} (hp : forall n' >= n,
 ¬p n') : nth p n = 0
-/
@[simp] theorem nth_false (n : ℕ) : nth (fun _ ↦ False) n = 0 := nth_of_forall_not fun _ _ ↦ id

end Nat

