/-
Copyright (c) 2021 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
public import Mathlib.Algebra.Order.BigOperators.Ring.List

/-!
# Big operators on a multiset in ordered rings

This file contains the results concerning the interaction of multiset big operators with ordered
rings.
-/

public section

open Multiset

@[simp]
/-
**CanonicallyOrderedAdd.multiset_prod_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CanonicallyOrderedAdd.multiset_prod_pos {R : Type*} [CommSemiring R] [Part
ialOrder R] [CanonicallyOrderedAdd R] [NoZeroDivisors R] [Nontrivial R] {m : Mul
tiset R} : 0 < m.prod ↔ forall x in m, 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.quot_mk_to_coe''`：quot_mk_to_coe'' (l : List α) : @Eq (Multiset
 α) (Quot.mk Setoid.r l) l
· 使用定理 `Multiset.prod_coe`：prod_coe (l : List M) : prod ↑l = l.prod
· 使用定理 `CanonicallyOrderedAdd.list_prod_pos`：∀ {α : Type u_2} [inst : CommSemiri
ng α] [inst_1 : PartialOrder α] [CanonicallyOrderedAdd α] [NoZeroDivisors α]   [
Nontrivial α] {l : List α…
-/
lemma CanonicallyOrderedAdd.multiset_prod_pos {R : Type*}
    [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [NoZeroDivisors R] [Nontrivial R]
    {m : Multiset R} : 0 < m.prod ↔ ∀ x ∈ m, 0 < x := by
  rcases m with ⟨l⟩
  rw [Multiset.quot_mk_to_coe'', Multiset.prod_coe]
  exact CanonicallyOrderedAdd.list_prod_pos

section OrderedCommSemiring

variable {α β : Type*} [CommMonoid α] [CommMonoidWithZero β] [PartialOrder β] [PosMulMono β]

/-
**Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg (f : α -> β) (p : 
α -> Prop) (h0 : forall a, 0 <= f a) (h_one : f 1 <= 1) (h_mul : forall a b, p a
 -> p b -> f (a * b) <= f a * f b) (hp_mul : forall a b, p a -> p b -> p (a * b)
) (s : Multiset α) (hps : forall a, a in s -> p a) : f s.prod <= (s.map f).prod
参数：f : α -> β；p : α -> Prop；h0 : forall a, 0 <= f a；h_one : f 1 <= 1；h_mul : for
all a b, p a -> p b -> f (a * b) <= f a * f b；hp_mul : forall a b, p a -> p b ->
 p (a * b)；s : Multiset α；hps : forall a, a in s -> p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `Multiset.prod_induction_nonempty`：prod_induction_nonempty (p : M -> Prop
) (p_mul : forall a b, p a -> p b -> p (a * b)) (hs : s != ∅) (p_s : forall a in
 s, p a) : p s.prod
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
theorem Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg (f : α → β) (p : α → Prop)
    (h0 : ∀ a, 0 ≤ f a) (h_one : f 1 ≤ 1) (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b)
    (hp_mul : ∀ a b, p a → p b → p (a * b)) (s : Multiset α) (hps : ∀ a, a ∈ s → p a) :
    f s.prod ≤ (s.map f).prod := by
  revert s
  refine Multiset.induction (by simp [h_one]) ?_
  intro a s hs hpsa
  by_cases hs0 : s = ∅
  · simp [hs0]
  · have hps : ∀ x, x ∈ s → p x := fun x hx ↦ hpsa x (mem_cons_of_mem hx)
    have hp_prod : p s.prod := prod_induction_nonempty p hp_mul hs0 hps
    rw [prod_cons, map_cons, prod_cons]
    exact (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans
      (by gcongr; exacts [h0 _, hs hps])
/-
**Multiset.le_prod_of_submultiplicative_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.le_prod_of_submultiplicative_of_nonneg (f : α -> β) (h0 : forall 
a, 0 <= f a) (h_one : f 1 <= 1) (h_mul : forall a b, f (a * b) <= f a * f b) (s 
: Multiset α) : f s.prod <= (s.map f).prod
参数：f : α -> β；h0 : forall a, 0 <= f a；h_one : f 1 <= 1；h_mul : forall a b, f (a 
* b) <= f a * f b；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg`：Multiset.le_pro
d_of_submultiplicative_on_pred_of_nonneg (f : α -> β) (p : α -> Prop) (h0 : fora
ll a, 0 <= f a) (h_one : f 1 <= 1) (h_mul : f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem Multiset.le_prod_of_submultiplicative_of_nonneg (f : α → β) (h0 : ∀ a, 0 ≤ f a)
    (h_one : f 1 ≤ 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) :
    f s.prod ≤ (s.map f).prod :=
  le_prod_of_submultiplicative_on_pred_of_nonneg f (fun _ ↦ True) h0 h_one
    (fun x y _ _ ↦ h_mul x y) (by simp) s (by simp)

omit [CommMonoid α] in
/-
**Multiset.mem_le_prod_of_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multiset.mem_le_prod_of_one_le [ZeroLEOneClass β] {f : α -> β} (h1 : foral
l a : α, 1 <= f a) {s : Multiset α} {a : α} (ha : a in s) : f a <= (s.map f).pro
d
参数：h1 : forall a : α, 1 <= f a；ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
-/
lemma Multiset.mem_le_prod_of_one_le [ZeroLEOneClass β] {f : α → β} (h1 : ∀ a : α, 1 ≤ f a)
    {s : Multiset α} {a : α} (ha : a ∈ s) : f a ≤ (s.map f).prod := by
  obtain ⟨s', rfl⟩ := exists_cons_of_mem ha
  rw [map_cons, prod_cons]
  calc f a = f a * 1 := (mul_one (f a)).symm
    _ ≤ f a * (s'.map f).prod := by
      gcongr
      · exact le_trans (zero_le_one' β) (h1 a)
      · simp_all [one_le_prod]

end OrderedCommSemiring

