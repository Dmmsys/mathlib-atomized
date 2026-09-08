/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Order.Interval.Finset.Gaps
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# Sum of gaps

This file proves that given a function `g` on `[a, b]`, `g b - g a` can be split according to a
given finite collection of pairwise disjoint closed subintervals of `[a, b]`. It is the sum of two
terms:
- the sum of `g y - g x` for `[x, y]` in the collection,
- the sum of `g y - g x` for `[x, y]` in the complement (modulo endpoints) of the union of the
  collection in `[a, b]`.

We use `Finset.intervalGapsWithin` to encode the complement.

We provide the multiplication versions in `Finset.prod_intervalGapsWithin_mul_prod_eq_div`,
`Finset.prod_intervalGapsWithin_eq_div_div_prod`, and the additive versions in
`Finset.sum_intervalGapsWithin_add_sum_eq_sub`, `Finset.sum_intervalGapsWithin_eq_sub_sub_sum`.

Technically, we don't require pairwise disjointness or endpoints to be within `[a, b]` or even
require that `a ≤ b`, but it makes the most sense if they are actually satisfied.
-/

public section

open Fin Fin.NatCast

variable {α β : Type*} [LinearOrder α] [CommGroup β]
  (F : Finset (α × α)) {k : ℕ} (h : F.card = k) {a b : α}
  (g : α → β)

@[to_additive]
/-
**Finset.prod_eq_prod_range_intervalGapsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.prod_eq_prod_range_intervalGapsWithin (f : α -> α -> β) : ∏ z in F,
 f z.1 z.2 = ∏ i in range k, f (F.intervalGapsWithin h a b i).2 (F.intervalGapsW
ithin h a b i.succ).1
参数：f : α -> α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_bij`：prod_bij (i : forall a in s, κ) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `Finset.intervalGapsWithin_mapsTo`：intervalGapsWithin_mapsTo : (Set.Iio k
).MapsTo (fun (j : Nat) => ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWit
hin h a b j.succ).1)) …
· 使用定理 `Finset.intervalGapsWithin_injOn`：intervalGapsWithin_injOn : (Set.Iio k).
InjOn (fun (j : Nat) => ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWithin
 h a b j.succ).1))
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Finset.intervalGapsWithin_surjOn`：intervalGapsWithin_surjOn : (Set.Iio k
).SurjOn (fun (j : Nat) => ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWit
hin h a b j.succ).1)) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Finset.prod_eq_prod_range_intervalGapsWithin (f : α → α → β) :
    ∏ z ∈ F, f z.1 z.2 = ∏ i ∈ range k,
      f (F.intervalGapsWithin h a b i).2 (F.intervalGapsWithin h a b i.succ).1 := by
  set p := F.intervalGapsWithin h a b
  symm
  apply prod_bij (fun (i : ℕ) hi ↦ ((p i).2, (p i.succ).1))
  · exact fun i _ ↦ F.intervalGapsWithin_mapsTo h a b (x := i) (by grind)
  · intro i hi j hj hij
    rw [mem_range] at hi hj
    apply F.intervalGapsWithin_injOn h a b <;> grind
  · intro z hz
    obtain ⟨i, hi₁, hi₂⟩ := F.intervalGapsWithin_surjOn h a b hz
    exact ⟨i, by grind, hi₂⟩
  · simp

@[to_additive]
/-
**Finset.prod_intervalGapsWithin_mul_prod_eq_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.prod_intervalGapsWithin_mul_prod_eq_div : (∏ i in Finset.range (k +
 1), g (F.intervalGapsWithin h a b i).2 / g (F.intervalGapsWithin h a b i).1) * 
∏ z in F, g z.2 / g z.1 = g b / g a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_prod_range_intervalGapsWithin`：Finset.prod_eq_prod_range_
intervalGapsWithin (f : α -> α -> β) : ∏ z in F, f z.1 z.2 = ∏ i in range k, f (
F.intervalGapsWithin h a b i).2 (F…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
· 使用引理 `Finset.prod_range_div`：prod_range_div (f : Nat -> G) (n : Nat) : (∏ i in
 range n, f (i + 1) / f i) = f n / f 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.intervalGapsWithin.congr_simp`：∀ {α : Type u_1} [inst : LinearOrd
er α] (F F_1 : Finset (α × α)) (e_F : F = F_1) {k : ℕ} (h : F.card = k) (a a_1 :
 α),   a = a_1 →     ∀ (b …
· 使用定理 `Fin.natCast_eq_last`：natCast_eq_last (n) : (n : Fin (n + 1)) = Fin.last 
n
· 使用定理 `Fin.natCast_zero`：∀ {n : ℕ} [inst : NeZero n], ↑0 = 0
· 使用定理 `Finset.intervalGapsWithin_zero_fst`：intervalGapsWithin_zero_fst : (F.int
ervalGapsWithin h a b 0).1 = a
· 使用定理 `Finset.intervalGapsWithin_last_snd`：intervalGapsWithin_last_snd : (F.int
ervalGapsWithin h a b (last k)).2 = b
· 使用定理 `div_mul_div_cancel'`：div_mul_div_cancel' (a b c : G) : a / b * (c / a) =
 c / b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.prod_intervalGapsWithin_mul_prod_eq_div :
    (∏ i ∈ Finset.range (k + 1),
      g (F.intervalGapsWithin h a b i).2 / g (F.intervalGapsWithin h a b i).1) *
      ∏ z ∈ F, g z.2 / g z.1 = g b / g a := by
  rw [F.prod_eq_prod_range_intervalGapsWithin h (fun x y ↦ g y / g x), mul_comm,
      prod_range_succ, ← mul_assoc,
      ← prod_mul_distrib,
      prod_congr rfl (fun _ _ ↦ div_mul_div_cancel _ _ _),
      prod_range_div (fun i ↦ g (F.intervalGapsWithin h a b i).1)]
  simp

@[to_additive]
/-
**Finset.prod_intervalGapsWithin_eq_div_div_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.prod_intervalGapsWithin_eq_div_div_prod : (∏ i in Finset.range (k +
 1), g (F.intervalGapsWithin h a b i).2 / g (F.intervalGapsWithin h a b i).1) = 
(g b / g a) / ∏ z in F, g z.2 / g z.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_div_iff_mul_eq'`：eq_div_iff_mul_eq' : a = b / c ↔ a * c = b
· 使用定理 `Finset.prod_intervalGapsWithin_mul_prod_eq_div`：Finset.prod_intervalGaps
Within_mul_prod_eq_div : (∏ i in Finset.range (k + 1), g (F.intervalGapsWithin h
 a b i).2 / g (F.intervalGapsWithin …
-/
theorem Finset.prod_intervalGapsWithin_eq_div_div_prod :
    (∏ i ∈ Finset.range (k + 1),
      g (F.intervalGapsWithin h a b i).2 / g (F.intervalGapsWithin h a b i).1) =
    (g b / g a) / ∏ z ∈ F, g z.2 / g z.1 :=
  eq_div_iff_mul_eq'.mpr (F.prod_intervalGapsWithin_mul_prod_eq_div h g)
