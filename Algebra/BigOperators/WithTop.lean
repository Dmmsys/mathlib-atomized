/-
Copyright (c) 2024 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Sums in `WithTop`

This file proves results about finite sums over monoids extended by a bottom or top element.
-/

public section

open Finset

variable {ι M M₀ : Type*}

namespace WithTop
section AddCommMonoid
variable [AddCommMonoid M] {s : Finset ι} {f : ι → WithTop M}

/-
**WithTop.coe_sum** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] (s : Finset ι) (f
 : ι → M), ↑(∑ i ∈ s, f i) = ∑ i ∈ s, ↑(f i)
参数：s : Finset ι；f : ι → M；∑ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
@[simp, norm_cast] lemma coe_sum (s : Finset ι) (f : ι → M) :
    ∑ i ∈ s, f i = ∑ i ∈ s, (f i : WithTop M) := map_sum addHom f s

/-- A sum is infinite iff one term is infinite. -/
/-
**WithTop.sum_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] {s : Finset ι} {f
 : ι → WithTop M},   ∑ i ∈ s, f i = ⊤ ↔ ∃ i ∈ s, f i = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
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
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …

--- 原说明 ---
A sum is infinite iff one term is infinite.
-/
@[simp] lemma sum_eq_top : ∑ i ∈ s, f i = ⊤ ↔ ∃ i ∈ s, f i = ⊤ := by
  induction s using Finset.cons_induction <;> simp [*]

/-- A sum is finite iff all terms are finite. -/
/-
**WithTop.sum_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：sum_ne_top : ∑ i in s, f i != ⊤ ↔ forall i in s, f i != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A sum is finite iff all terms are finite.
-/
lemma sum_ne_top : ∑ i ∈ s, f i ≠ ⊤ ↔ ∀ i ∈ s, f i ≠ ⊤ := by simp

variable [LT M]

/-- A sum is finite iff all terms are finite. -/
/-
**WithTop.sum_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] {s : Finset ι} {f
 : ι → WithTop M} [inst_1 : LT M],   ∑ i ∈ s, f i < ⊤ ↔ ∀ i ∈ s, f i < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A sum is finite iff all terms are finite.
-/
@[simp] lemma sum_lt_top : ∑ i ∈ s, f i < ⊤ ↔ ∀ i ∈ s, f i < ⊤ := by
  simp [WithTop.lt_top_iff_ne_top]

end AddCommMonoid

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι → WithTop M₀} {i : ι}

/-- A product of finite terms is finite. -/
/-
**WithTop.prod_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：prod_ne_top (h : forall i in s, f i != ⊤) : ∏ i in s, f i != ⊤
参数：h : forall i in s, f i != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `WithTop.mul_ne_top`：mul_ne_top {a b : WithTop α} (ha : a != ⊤) (hb : b !
= ⊤) : a * b != ⊤
· 使用定理 `WithTop.coe_ne_top`：∀ {α : Type u_1} {a : α}, ↑a ≠ ⊤

--- 原说明 ---
A product of finite terms is finite.
-/
lemma prod_ne_top (h : ∀ i ∈ s, f i ≠ ⊤) : ∏ i ∈ s, f i ≠ ⊤ :=
  prod_induction f (· ≠ ⊤) (fun _ _ ↦ mul_ne_top) coe_ne_top h

/-- A product of finite terms is finite. -/
/-
**WithTop.prod_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：prod_lt_top [LT M₀] (h : forall i in s, f i < ⊤) : ∏ i in s, f i < ⊤
参数：h : forall i in s, f i < ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `WithTop.mul_lt_top`：mul_lt_top [LT α] {a b : WithTop α} (ha : a < ⊤) (hb
 : b < ⊤) : a * b < ⊤
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤

--- 原说明 ---
A product of finite terms is finite.
-/
lemma prod_lt_top [LT M₀] (h : ∀ i ∈ s, f i < ⊤) : ∏ i ∈ s, f i < ⊤ :=
  prod_induction f (· < ⊤) (fun _ _ ↦ mul_lt_top) (coe_lt_top _) h
/-
**WithTop.prod_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：prod_eq_top (hi : i in s) (hi' : f i = ⊤) (h : forall j in s, f j != 0) : 
∏ j in s, f j = ⊤
参数：hi : i in s；hi' : f i = ⊤；h : forall j in s, f j != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_erase_mul`：prod_erase_mul [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (∏ x in s.erase a, f x) * f a = ∏ x in s, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithTop.mul_eq_top_iff`：mul_eq_top_iff : a * b = ⊤ ↔ a != 0 ∧ b = ⊤ ∨ a 
= ⊤ ∧ b != 0
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `WithTop.nontrivial`：∀ {α : Type u_1} [Nonempty α], Nontrivial (WithTop α
)
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma prod_eq_top (hi : i ∈ s) (hi' : f i = ⊤) (h : ∀ j ∈ s, f j ≠ 0) :
    ∏ j ∈ s, f j = ⊤ := by
  classical rw [← prod_erase_mul _ _ hi]
  refine WithTop.mul_eq_top_iff.mpr (Or.inl ⟨?_, hi'⟩)
  refine prod_ne_zero_iff.mpr ?_
  intros
  simp_all only [ne_eq, mem_erase, not_false_eq_true]
/-
**WithTop.prod_eq_top_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：prod_eq_top_ne_zero (hi : i in s) (h : ∏ j in s, f j = ⊤) : f i != 0
参数：hi : i in s；h : ∏ j in s, f j = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_ne_zero`：∀ {α : Type u} [inst : Zero α], ⊤ ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
-/
lemma prod_eq_top_ne_zero (hi : i ∈ s) (h : ∏ j ∈ s, f j = ⊤) : f i ≠ 0 := by
  by_contra! h0
  apply WithTop.top_ne_zero (α := M₀)
  calc
    ⊤ = ∏ j ∈ s, f j := Eq.symm h
    _ = 0 := prod_eq_zero hi h0
/-
**WithTop.prod_eq_top_ex_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：prod_eq_top_ex_top (h : ∏ j in s, f j = ⊤) : exists i in s, f i = ⊤
参数：h : ∏ j in s, f j = ⊤。
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
· 使用引理 `WithTop.prod_ne_top`：prod_ne_top (h : forall i in s, f i != ⊤) : ∏ i in 
s, f i != ⊤
-/
lemma prod_eq_top_ex_top (h : ∏ j ∈ s, f j = ⊤) : ∃ i ∈ s, f i = ⊤ := by
  contrapose! h
  exact WithTop.prod_ne_top h

/-- A product is infinite iff each factor is nonzero and some factor is infinite -/
/-
**WithTop.prod_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：prod_eq_top_iff : ∏ j in s, f j = ⊤ ↔ (exists i in s, f i = ⊤) ∧ (forall i
 in s, f i != 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.prod_eq_top_ex_top`：prod_eq_top_ex_top (h : ∏ j in s, f j = ⊤) :
 exists i in s, f i = ⊤
· 使用引理 `WithTop.prod_eq_top_ne_zero`：prod_eq_top_ne_zero (hi : i in s) (h : ∏ j 
in s, f j = ⊤) : f i != 0
· 使用引理 `WithTop.prod_eq_top`：prod_eq_top (hi : i in s) (hi' : f i = ⊤) (h : fora
ll j in s, f j != 0) : ∏ j in s, f j = ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A product is infinite iff each factor is nonzero and some factor is infinite
-/
lemma prod_eq_top_iff : ∏ j ∈ s, f j = ⊤ ↔ (∃ i ∈ s, f i = ⊤) ∧ (∀ i ∈ s, f i ≠ 0) := by
  constructor
  · exact fun h ↦ ⟨prod_eq_top_ex_top h, fun _ ih ↦ prod_eq_top_ne_zero ih h⟩
  · exact fun ⟨h, h'⟩ ↦ prod_eq_top (Exists.choose_spec h).1 (Exists.choose_spec h).2 h'

end CommMonoidWithZero
end WithTop

namespace WithBot
section AddCommMonoid
variable [AddCommMonoid M] {s : Finset ι} {f : ι → WithBot M}

/-
**WithBot.coe_sum** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] (s : Finset ι) (f
 : ι → M), ↑(∑ i ∈ s, f i) = ∑ i ∈ s, ↑(f i)
参数：s : Finset ι；f : ι → M；∑ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
@[simp, norm_cast] lemma coe_sum (s : Finset ι) (f : ι → M) :
    ∑ i ∈ s, f i = ∑ i ∈ s, (f i : WithBot M) := map_sum addHom f s

/-- A sum is infinite iff one term is infinite. -/
/-
**WithBot.sum_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：sum_eq_bot_iff : ∑ i in s, f i = ⊥ ↔ exists i in s, f i = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
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
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …

--- 原说明 ---
A sum is infinite iff one term is infinite.
-/
lemma sum_eq_bot_iff : ∑ i ∈ s, f i = ⊥ ↔ ∃ i ∈ s, f i = ⊥ := by
  induction s using Finset.cons_induction <;> simp [*]

variable [LT M]

/-- A sum is finite iff all terms are finite. -/
/-
**WithBot.bot_lt_sum_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：bot_lt_sum_iff : ⊥ < ∑ i in s, f i ↔ forall i in s, ⊥ < f i
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A sum is finite iff all terms are finite.
-/
lemma bot_lt_sum_iff : ⊥ < ∑ i ∈ s, f i ↔ ∀ i ∈ s, ⊥ < f i := by
  simp only [WithBot.bot_lt_iff_ne_bot, ne_eq, sum_eq_bot_iff, not_exists, not_and]

/-- A sum of finite terms is finite. -/
/-
**WithBot.sum_lt_bot** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：sum_lt_bot (h : forall i in s, f i != ⊥) : ⊥ < ∑ i in s, f i
参数：h : forall i in s, f i != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.bot_lt_sum_iff`：bot_lt_sum_iff : ⊥ < ∑ i in s, f i ↔ forall i in
 s, ⊥ < f i
· 使用定理 `WithBot.bot_lt_iff_ne_bot`：∀ {α : Type u_1} [inst : LT α] {x : WithBot α
}, ⊥ < x ↔ x ≠ ⊥

--- 原说明 ---
A sum of finite terms is finite.
-/
lemma sum_lt_bot (h : ∀ i ∈ s, f i ≠ ⊥) : ⊥ < ∑ i ∈ s, f i :=
  bot_lt_sum_iff.2 fun i hi ↦ WithBot.bot_lt_iff_ne_bot.2 (h i hi)

end AddCommMonoid

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι → WithBot M₀}

/-- A product of finite terms is finite. -/
/-
**WithBot.prod_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：prod_ne_bot (h : forall i in s, f i != ⊥) : ∏ i in s, f i != ⊥
参数：h : forall i in s, f i != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `WithBot.mul_ne_bot`：mul_ne_bot {a b : WithBot α} (ha : a != ⊥) (hb : b !
= ⊥) : a * b != ⊥
· 使用定理 `WithBot.coe_ne_bot`：coe_ne_bot : (a : WithBot α) != ⊥

--- 原说明 ---
A product of finite terms is finite.
-/
lemma prod_ne_bot (h : ∀ i ∈ s, f i ≠ ⊥) : ∏ i ∈ s, f i ≠ ⊥ :=
  prod_induction f (· ≠ ⊥) (fun _ _ ↦ mul_ne_bot) coe_ne_bot h

/-- A product of finite terms is finite. -/
/-
**WithBot.bot_lt_prod** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：bot_lt_prod [LT M₀] (h : forall i in s, ⊥ < f i) : ⊥ < ∏ i in s, f i
参数：h : forall i in s, ⊥ < f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `WithBot.bot_lt_mul`：bot_lt_mul [LT α] {a b : WithBot α} (ha : ⊥ < a) (hb
 : ⊥ < b) : ⊥ < a * b
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)

--- 原说明 ---
A product of finite terms is finite.
-/
lemma bot_lt_prod [LT M₀] (h : ∀ i ∈ s, ⊥ < f i) : ⊥ < ∏ i ∈ s, f i :=
  prod_induction f (⊥ < ·) (fun _ _ ↦ bot_lt_mul) (bot_lt_coe _) h

end CommMonoidWithZero

end WithBot

