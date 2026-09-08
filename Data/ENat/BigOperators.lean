/-
Copyright (c) 2024 Joachim Breitner, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner, Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.WithTop
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ENat.Lattice

/-!
# Sum of suprema in `ENat`
-/

public section

assert_not_exists Field

namespace ENat

variable {a b c d : ℕ∞} {r p q : ℕ}

section OperationsAndInfty

variable {α : Type*}

@[simp]
/-
**ENat.toNat_prod** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toNat_prod {ι : Type*} {s : Finset ι} {f : ι -> Nat∞} : (∏ i in s, f i).to
Nat = ∏ i in s, (f i).toNat
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem toNat_prod {ι : Type*} {s : Finset ι} {f : ι → ℕ∞} :
    (∏ i ∈ s, f i).toNat = ∏ i ∈ s, (f i).toNat :=
  map_prod toNatHom _ _
/-
**ENat.iInf_sum** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：iInf_sum {ι α : Type*} {f : ι -> α -> Nat∞} {s : Finset α} [Nonempty ι] (h
 : forall (t : Finset α) (i j : ι), exists k, forall a in t, f k a <= f i a ∧ f 
k a <= f j a) : ⨅ i, ∑ a in s, f i a = ∑ a in s, ⨅ i, f i a
参数：h : forall (t : Finset α) (i j : ι), exists k, forall a in t, f k a <= f i a 
∧ f k a <= f j a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ciInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyComple
tePartialOrderInf α] [hι : Nonempty ι] {a : α}, ⨅ x, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.iInf_add_iInf`：iInf_add_iInf (h : forall i j, exists k, f k + g k <
= f i + g j) : iInf f + iInf g = ⨅ a, f a + g a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.forall_mem_cons`：forall_mem_cons (h : a ∉ s) (p : α -> Prop) : (f
orall x, x in cons a s h -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem iInf_sum {ι α : Type*} {f : ι → α → ℕ∞} {s : Finset α} [Nonempty ι]
    (h : ∀ (t : Finset α) (i j : ι), ∃ k, ∀ a ∈ t, f k a ≤ f i a ∧ f k a ≤ f j a) :
    ⨅ i, ∑ a ∈ s, f i a = ∑ a ∈ s, ⨅ i, f i a := by
  induction s using Finset.cons_induction_on with
  | empty => simp only [Finset.sum_empty, ciInf_const]
  | cons a s ha ih =>
    simp only [Finset.sum_cons, ← ih]
    refine (iInf_add_iInf fun i j => ?_).symm
    refine (h (Finset.cons a s ha) i j).imp fun k hk => ?_
    rw [Finset.forall_mem_cons] at hk
    exact add_le_add hk.1.1 (Finset.sum_le_sum fun a ha => (hk.2 a ha).2)

end OperationsAndInfty

section Sum

open Finset

variable {α : Type*} {s : Finset α} {f : α → ℕ∞}

/-- A product of finite numbers is still finite. -/
/-
**ENat.prod_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：prod_ne_top (h : forall a in s, f a != ⊤) : ∏ a in s, f a != ⊤
参数：h : forall a in s, f a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.prod_ne_top`：prod_ne_top (h : forall i in s, f i != ⊤) : ∏ i in 
s, f i != ⊤
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α

--- 原说明 ---
A product of finite numbers is still finite.
-/
lemma prod_ne_top (h : ∀ a ∈ s, f a ≠ ⊤) : ∏ a ∈ s, f a ≠ ⊤ := WithTop.prod_ne_top h

/-- A product of finite numbers is still finite. -/
/-
**ENat.prod_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：prod_lt_top (h : forall a in s, f a < ⊤) : ∏ a in s, f a < ⊤
参数：h : forall a in s, f a < ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.prod_lt_top`：prod_lt_top [LT M₀] (h : forall i in s, f i < ⊤) : 
∏ i in s, f i < ⊤
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α

--- 原说明 ---
A product of finite numbers is still finite.
-/
lemma prod_lt_top (h : ∀ a ∈ s, f a < ⊤) : ∏ a ∈ s, f a < ⊤ := WithTop.prod_lt_top h

/-- A sum is infinite iff one of the summands is infinite. -/
/-
**ENat.sum_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {f : α → ℕ∞}, ∑ x ∈ s, f x = ⊤ ↔ ∃ a ∈ s, 
f a = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.sum_eq_top`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoi
d M] {s : Finset ι} {f : ι → WithTop M},   ∑ i ∈ s, f i = ⊤ ↔ ∃ i ∈ s, f i = ⊤

--- 原说明 ---
A sum is infinite iff one of the summands is infinite.
-/
@[simp] lemma sum_eq_top : ∑ x ∈ s, f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤ := WithTop.sum_eq_top

/-- A sum is finite iff all summands are finite. -/
/-
**ENat.sum_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：sum_ne_top : ∑ a in s, f a != ⊤ ↔ forall a in s, f a != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.sum_ne_top`：sum_ne_top : ∑ i in s, f i != ⊤ ↔ forall i in s, f i
 != ⊤

--- 原说明 ---
A sum is finite iff all summands are finite.
-/
lemma sum_ne_top : ∑ a ∈ s, f a ≠ ⊤ ↔ ∀ a ∈ s, f a ≠ ⊤ := WithTop.sum_ne_top

/-- A sum is finite iff all summands are finite. -/
/-
**ENat.sum_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {f : α → ℕ∞}, ∑ a ∈ s, f a < ⊤ ↔ ∀ a ∈ s, 
f a < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.sum_lt_top`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoi
d M] {s : Finset ι} {f : ι → WithTop M} [inst_1 : LT M],   ∑ i ∈ s, f i < ⊤ ↔ ∀ 
i ∈ s, f…

--- 原说明 ---
A sum is finite iff all summands are finite.
-/
@[simp] lemma sum_lt_top : ∑ a ∈ s, f a < ⊤ ↔ ∀ a ∈ s, f a < ⊤ := WithTop.sum_lt_top
/-
**ENat.lt_top_of_sum_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：lt_top_of_sum_ne_top {s : Finset α} {f : α -> Nat∞} (h : ∑ x in s, f x != 
⊤) {a : α} (ha : a in s) : f a < ⊤
参数：h : ∑ x in s, f x != ⊤；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENat.sum_lt_top`：∀ {α : Type u_1} {s : Finset α} {f : α → ℕ∞}, ∑ a ∈ s, 
f a < ⊤ ↔ ∀ a ∈ s, f a < ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤

--- 原说明 ---
A sum is finite iff all summands are finite.
-/
theorem lt_top_of_sum_ne_top {s : Finset α} {f : α → ℕ∞} (h : ∑ x ∈ s, f x ≠ ⊤) {a : α}
    (ha : a ∈ s) : f a < ⊤ :=
  sum_lt_top.1 h.lt_top a ha

/-- Seeing `ℕ∞` as `ℕ` does not change their sum, unless one of the `ℕ∞` is
infinity -/
/-
**ENat.toNat_sum** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toNat_sum {s : Finset α} {f : α -> Nat∞} (hf : forall a in s, f a != ⊤) : 
ENat.toNat (∑ a in s, f a) = ∑ a in s, ENat.toNat (f a)
参数：hf : forall a in s, f a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_inj`：natCast_inj {a b : Nat} : (a : Nat∞) = b ↔ a = b
· 使用定理 `ENat.natCast_toNat`：∀ {n : ℕ∞}, n ≠ ⊤ → ↑n.toNat = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENat.sum_ne_top`：sum_ne_top : ∑ a in s, f a != ⊤ ↔ forall a in s, f a !=
 ⊤
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…

--- 原说明 ---
Seeing `ℕ∞` as `ℕ` does not change their sum, unless one of the `ℕ∞` is
infinity
-/
theorem toNat_sum {s : Finset α} {f : α → ℕ∞} (hf : ∀ a ∈ s, f a ≠ ⊤) :
    ENat.toNat (∑ a ∈ s, f a) = ∑ a ∈ s, ENat.toNat (f a) := by
  rw [← natCast_inj, natCast_toNat (sum_ne_top.2 hf), Nat.cast_sum]
  exact sum_congr rfl fun x hx => (natCast_toNat (hf x hx)).symm
/-
**ENat.sum_lt_sum_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α -> Nat∞} 
(Hlt : forall i in s, f i < g i) : ∑ i in s, f i < ∑ i in s, g i
参数：hs : s.Nonempty；Hlt : forall i in s, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `ENat.add_lt_add`：∀ {a b c d : ℕ∞}, a < c → b < d → a + b < c + d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α → ℕ∞}
    (Hlt : ∀ i ∈ s, f i < g i) : ∑ i ∈ s, f i < ∑ i ∈ s, g i := by
  induction hs using Nonempty.cons_induction with
  | singleton => simp [Hlt _ (mem_singleton_self _)]
  | cons _ _ _ _ ih =>
    simp only [sum_cons, forall_mem_cons] at Hlt ⊢
    exact ENat.add_lt_add Hlt.1 (ih Hlt.2)
/-
**ENat.exists_le_of_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α -> Nat∞} (Hl
e : ∑ i in s, f i <= ∑ i in s, g i) : exists i in s, f i <= g i
参数：hs : s.Nonempty；Hle : ∑ i in s, f i <= ∑ i in s, g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `ENat.sum_lt_sum_of_nonempty`：sum_lt_sum_of_nonempty {s : Finset α} (hs :
 s.Nonempty) {f g : α -> Nat∞} (Hlt : forall i in s, f i < g i) : ∑ i in s, f i 
< ∑ i in s, g i
-/
theorem exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α → ℕ∞}
    (Hle : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i) : ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle
  apply sum_lt_sum_of_nonempty hs Hle

end Sum

/-
**ENat.sum_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：sum_iSup {α ι : Type*} {s : Finset α} {f : α -> ι -> Nat∞} (hf : forall i 
j, exists k, forall a, f a i <= f a k ∧ f a j <= f a k) : ∑ a in s, ⨆ i, f a i =
 ⨆ i, ∑ a in s, f a i
参数：hf : forall i j, exists k, forall a, f a i <= f a k ∧ f a j <= f a k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ENat.iSup_add_iSup`：iSup_add_iSup (h : forall i j, exists k, f i + g j <
= f k + g k) : iSup f + iSup g = ⨆ i, f i + g i
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma sum_iSup {α ι : Type*} {s : Finset α} {f : α → ι → ℕ∞}
    (hf : ∀ i j, ∃ k, ∀ a, f a i ≤ f a k ∧ f a j ≤ f a k) :
    ∑ a ∈ s, ⨆ i, f a i = ⨆ i, ∑ a ∈ s, f a i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ihs =>
    simp_rw [Finset.sum_cons, ihs]
    refine iSup_add_iSup fun i j ↦ (hf i j).imp fun k hk ↦ ?_
    gcongr
    exacts [(hk a).1, (hk _).2]
/-
**ENat.sum_iSup_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：sum_iSup_of_monotone {α ι : Type*} [Preorder ι] [IsDirectedOrder ι] {s : F
inset α} {f : α -> ι -> Nat∞} (hf : forall a, Monotone (f a)) : (∑ a in s, iSup 
(f a)) = ⨆ n, ∑ a in s, f a n
参数：hf : forall a, Monotone (f a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.sum_iSup`：sum_iSup {α ι : Type*} {s : Finset α} {f : α -> ι -> Nat∞
} (hf : forall i j, exists k, forall a, f a i <= f a k ∧ f a j <= f a k) : ∑ a i
n s…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
-/
lemma sum_iSup_of_monotone {α ι : Type*} [Preorder ι] [IsDirectedOrder ι] {s : Finset α}
    {f : α → ι → ℕ∞} (hf : ∀ a, Monotone (f a)) : (∑ a ∈ s, iSup (f a)) = ⨆ n, ∑ a ∈ s, f a n :=
  sum_iSup fun i j ↦ (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ a ↦ ⟨hf a hi, hf a hj⟩

end ENat

