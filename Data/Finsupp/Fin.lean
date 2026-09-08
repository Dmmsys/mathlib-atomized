/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
module

public import Mathlib.Data.Finsupp.Single

/-!
# `cons` and `tail` for maps `Fin n →₀ M`

We interpret maps `Fin n →₀ M` as `n`-tuples of elements of `M`,
We define the following operations:
* `Finsupp.tail` : the tail of a map `Fin (n + 1) →₀ M`, i.e., its last `n` entries;
* `Finsupp.cons` : adding an element at the beginning of an `n`-tuple, to get an `n + 1`-tuple;

In this context, we prove some usual properties of `tail` and `cons`, analogous to those of
`Data.Fin.Tuple.Basic`.
-/

@[expose] public section

open Function

noncomputable section

namespace Finsupp

variable {n : ℕ} (i : Fin n) {M : Type*} [Zero M] (y : M) (t : Fin (n + 1) →₀ M) (s : Fin n →₀ M)

/-- `tail` for maps `Fin (n + 1) →₀ M`. See `Fin.tail` for more details. -/
/-
**Finsupp.tail** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：tail (s : Fin (n + 1) ->₀ M) : Fin n ->₀ M
参数：s : Fin (n + 1) ->₀ M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`tail` for maps `Fin (n + 1) →₀ M`. See `Fin.tail` for more details.
-/
def tail (s : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.tail s)

/-- `cons` for maps `Fin n →₀ M`. See `Fin.cons` for more details. -/
/-
**Finsupp.cons** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：cons (y : M) (s : Fin n ->₀ M) : Fin (n + 1) ->₀ M
参数：y : M；s : Fin n ->₀ M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`cons` for maps `Fin n →₀ M`. See `Fin.cons` for more details.
-/
def cons (y : M) (s : Fin n →₀ M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.cons y s : Fin (n + 1) → M)
/-
**Finsupp.tail_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：tail_apply : tail t i = t i.succ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_apply : tail t i = t i.succ :=
  rfl

@[simp]
/-
**Finsupp.cons_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：cons_zero : cons y s 0 = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem cons_zero : cons y s 0 = y :=
  rfl

@[simp]
/-
**Finsupp.cons_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：cons_succ : cons y s i.succ = s i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_succ : cons y s i.succ = s i :=
  rfl

@[simp]
/-
**Finsupp.tail_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：tail_cons : tail (cons y s) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tail_cons : tail (cons y s) = s :=
  ext fun k => by simp only [tail_apply, cons_succ]

@[simp]
/-
**Finsupp.tail_update_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：tail_update_zero : tail (update t 0 y) = tail t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Fin.tail_update_zero`：tail_update_zero : tail (update q 0 z) = tail q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tail_update_zero : tail (update t 0 y) = tail t := by simp [tail]

@[simp]
/-
**Finsupp.tail_update_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：tail_update_succ : tail (update t i.succ y) = update (tail t) i y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Fin.tail_update_succ`：tail_update_succ : tail (update q i.succ y) = upda
te (tail q) i y
· 使用定理 `Finsupp.equivFunOnFinite_symm_apply_apply`：∀ {α : Type u_1} {M : Type u_
4} [inst : Zero M] [inst_1 : Finite α] (f : α → M) (a : α),   (Finsupp.equivFunO
nFinite.symm f) a = f a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tail_update_succ : tail (update t i.succ y) = update (tail t) i y := by ext; simp [tail]

@[simp]
/-
**Finsupp.cons_tail** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：cons_tail : cons (t 0) (tail t) = t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.cons_zero`：cons_zero : cons y s 0 = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `Finsupp.cons_succ`：cons_succ : cons y s i.succ = s i
· 使用定理 `Finsupp.tail_apply`：tail_apply : tail t i = t i.succ
-/
theorem cons_tail : cons (t 0) (tail t) = t := by
  ext a
  by_cases c_a : a = 0
  · rw [c_a, cons_zero]
  · rw [← Fin.succ_pred a c_a, cons_succ, ← tail_apply]
/-
**Finsupp.cons_zero_eq_single_zero** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：cons_zero_eq_single_zero : cons y (0 : Fin n ->₀ M) = single 0 y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma cons_zero_eq_single_zero : cons y (0 : Fin n →₀ M) = single 0 y := by
  ext j
  cases j using Fin.cases <;> simp
/-
**Finsupp.cons_zero_single_eq_single_succ** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：cons_zero_single_eq_single_succ : cons 0 (single i y) = single i.succ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
lemma cons_zero_single_eq_single_succ : cons 0 (single i y) = single i.succ y := by
  ext j
  cases j using Fin.cases <;> simp [single_apply]

@[simp]
/-
**Finsupp.cons_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：cons_zero_zero : cons 0 (0 : Fin n ->₀ M) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Finsupp.cons_zero_eq_single_zero`：cons_zero_eq_single_zero : cons y (0 :
 Fin n ->₀ M) = single 0 y
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_zero_zero : cons 0 (0 : Fin n →₀ M) = 0 := by simp [cons_zero_eq_single_zero]

variable {s} {y}
/-
**Finsupp.cons_ne_zero_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：cons_ne_zero_of_left (h : y != 0) : cons y s != 0
参数：h : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.cons_zero`：cons_zero : cons y s 0 = y
· 使用定理 `Finsupp.coe_zero`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M], ⇑0 = 
0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
-/
theorem cons_ne_zero_of_left (h : y ≠ 0) : cons y s ≠ 0 := by
  contrapose h with c
  rw [← cons_zero y s, c, Finsupp.coe_zero, Pi.zero_apply]
/-
**Finsupp.cons_ne_zero_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：cons_ne_zero_of_right (h : s != 0) : cons y s != 0
参数：h : s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_ne_zero_of_right (h : s ≠ 0) : cons y s ≠ 0 := by
  contrapose h with c
  ext a
  simp [← cons_succ a y s, c]
/-
**Finsupp.cons_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：cons_ne_zero_iff : cons y s != 0 ↔ y != 0 ∨ s != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `imp_iff_not_or`：imp_iff_not_or : a -> b ↔ ¬a ∨ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.cons_zero_zero`：cons_zero_zero : cons 0 (0 : Fin n ->₀ M) = 0
· 使用定理 `Finsupp.cons_ne_zero_of_left`：cons_ne_zero_of_left (h : y != 0) : cons y
 s != 0
· 使用定理 `Finsupp.cons_ne_zero_of_right`：cons_ne_zero_of_right (h : s != 0) : cons
 y s != 0
-/
theorem cons_ne_zero_iff : cons y s ≠ 0 ↔ y ≠ 0 ∨ s ≠ 0 := by
  refine ⟨fun h => ?_, fun h => h.casesOn cons_ne_zero_of_left cons_ne_zero_of_right⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h', c, Finsupp.cons_zero_zero]
/-
**Finsupp.cons_support** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：cons_support : (s.cons y).support subseteq insert 0 (s.support.map (Fin.su
ccEmb n))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.eq_zero_or_eq_succ`：∀ {n : ℕ} (i : Fin (n + 1)), i = 0 ∨ ∃ j, i = j.
succ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma cons_support : (s.cons y).support ⊆ insert 0 (s.support.map (Fin.succEmb n)) := by
  intro i hi
  suffices i = 0 ∨ ∃ a, ¬s a = 0 ∧ a.succ = i by simpa
  apply (Fin.eq_zero_or_eq_succ i).imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

variable (y) in
/-
**Finsupp.cons_right_injective** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：cons_right_injective : Injective (Finsupp.cons y : (Fin n ->₀ M) -> Fin (n
 + 1) ->₀ M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Fin.cons_right_injective`：cons_right_injective (x₀ : α 0) : Function.Inj
ective (cons x₀)
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
lemma cons_right_injective : Injective (Finsupp.cons y : (Fin n →₀ M) → Fin (n + 1) →₀ M) :=
  (equivFunOnFinite.symm.injective.comp ((Fin.cons_right_injective _).comp DFunLike.coe_injective))

/-- As a binary function, `Finsupp.cons` is injective. -/
/-
**Finsupp.cons_injective2** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：cons_injective2 : Function.Injective2 (cons (n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `Finsupp.cons_right_injective`：cons_right_injective : Injective (Finsupp.
cons y : (Fin n ->₀ M) -> Fin (n + 1) ->₀ M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
As a binary function, `Finsupp.cons` is injective.
-/
theorem cons_injective2 : Function.Injective2 (cons (n := n) (M := M)) := by
  refine fun x₀ y₀ x y h ↦ ?_
  have := DFunLike.congr_fun h 0
  simp only [cons_zero] at this
  exact ⟨this, cons_right_injective y₀ (this ▸ h)⟩
/-
**Finsupp.cons_eq_single_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：cons_eq_single_zero_iff {x : M} : s.cons x = single 0 y ↔ s = 0 ∧ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.cons_zero_eq_single_zero`：cons_zero_eq_single_zero : cons y (0 :
 Fin n ->₀ M) = single 0 y
· 使用定理 `Function.Injective2.eq_iff`：eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f
 a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂
· 使用定理 `Finsupp.cons_injective2`：cons_injective2 : Function.Injective2 (cons (n
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cons_eq_single_zero_iff {x : M} : s.cons x = single 0 y ↔ s = 0 ∧ x = y := by
  rw [← cons_zero_eq_single_zero, cons_injective2.eq_iff, and_comm]
/-
**Finsupp.cons_eq_single_succ_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：cons_eq_single_succ_iff {x : M} : s.cons x = single i.succ y ↔ s = single 
i y ∧ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.cons_zero_single_eq_single_succ`：cons_zero_single_eq_single_succ
 : cons 0 (single i y) = single i.succ y
· 使用定理 `Function.Injective2.eq_iff`：eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f
 a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂
· 使用定理 `Finsupp.cons_injective2`：cons_injective2 : Function.Injective2 (cons (n
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cons_eq_single_succ_iff {x : M} : s.cons x = single i.succ y ↔ s = single i y ∧ x = 0 := by
  rw [← cons_zero_single_eq_single_succ, cons_injective2.eq_iff, and_comm]

end Finsupp

