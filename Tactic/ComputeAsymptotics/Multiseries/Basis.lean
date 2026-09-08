/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs

/-!
# Well-formed bases

## Main definitions

* `WellFormedBasis basis`: a predicate meaning that all functions from `basis` tend to `atTop`,
  and `basis` is sorted such that if
  `g` goes after `f` in `basis`, then `log f =o[atTop] log g`.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Asymptotics Filter

/-- `WellFormedBasis basis` means that all functions from `basis` tend to `atTop`, and
`basis` is sorted such that if
`g` goes after `f` in `basis`, then `log f =o[atTop] log g`.

We use two types `Basis` and `WellFormedBasis` instead of a single bundled one because it
it lets us to use the `List` API for `Basis`. -/
/-
**Tactic.ComputeAsymptotics.WellFormedBasis** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.Co
mputeAsymptotics`。
形式化陈述：WellFormedBasis (basis : Basis) : Prop
参数：basis : Basis。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WellFormedBasis basis` means that all functions from `basis` tend to `atTop`, a
nd
`basis` is sorted such that if
`g` goes after `f` in `basis`, then `log f =o[atTop] log g`.

We use two types `Basis` and `WellFormedBasis` instead of a single bundled one b
ecause it
it lets us to use the `List` API for `Basis`.
-/
def WellFormedBasis (basis : Basis) : Prop :=
  basis.Pairwise (fun x y => (Real.log ∘ y) =o[atTop] (Real.log ∘ x)) ∧
  ∀ f ∈ basis, Tendsto f atTop atTop

namespace WellFormedBasis

/-
**Tactic.ComputeAsymptotics.WellFormedBasis.nil** 是 Mathlib 中的一个定理，位于命名空间 `Tacti
c.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：nil : WellFormedBasis []
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem nil : WellFormedBasis [] := by simp [WellFormedBasis]
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.single** 是 Mathlib 中的一个定理，位于命名空间 `Ta
ctic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：single (f : Real -> Real) (hf : Tendsto f atTop atTop) : WellFormedBasis [
f]
参数：f : Real -> Real；hf : Tendsto f atTop atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem single (f : ℝ → ℝ) (hf : Tendsto f atTop atTop) : WellFormedBasis [f] := by
  simpa [WellFormedBasis]
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.of_sublist** 是 Mathlib 中的一个定理，位于命名空间
 `Tactic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：of_sublist {basis basis' : Basis} (h : List.Sublist basis basis') (h_basis
 : WellFormedBasis basis') : WellFormedBasis basis
参数：h : List.Sublist basis basis'；h_basis : WellFormedBasis basis'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α} {R : α → α → Pr
op}, l₁.Sublist l₂ → List.Pairwise R l₂ → List.Pairwise R l₁
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
-/
theorem of_sublist {basis basis' : Basis} (h : List.Sublist basis basis')
    (h_basis : WellFormedBasis basis') : WellFormedBasis basis :=
  ⟨h_basis.left.sublist h, fun _ hf ↦ h_basis.right _ (h.subset hf)⟩

/-- The tail of a well-formed basis is well-formed. -/
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.tail** 是 Mathlib 中的一个定理，位于命名空间 `Tact
ic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：tail {basis_hd : Real -> Real} {basis_tl : Basis} (h : WellFormedBasis (ba
sis_hd :: basis_tl)) : WellFormedBasis basis_tl
参数：h : WellFormedBasis (basis_hd :: basis_tl)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.of_sublist`：of_sublist {basis 
basis' : Basis} (h : List.Sublist basis basis') (h_basis : WellFormedBasis basis
') : WellFormedBasis basis
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
The tail of a well-formed basis is well-formed.
-/
theorem tail {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : WellFormedBasis (basis_hd :: basis_tl)) : WellFormedBasis basis_tl :=
  h.of_sublist (by simp)
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.of_append_right** 是 Mathlib 中的一个定理，位
于命名空间 `Tactic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：of_append_right {left right : Basis} (h : WellFormedBasis (left ++ right))
 : WellFormedBasis right
参数：h : WellFormedBasis (left ++ right)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.of_sublist`：of_sublist {basis 
basis' : Basis} (h : List.Sublist basis basis') (h_basis : WellFormedBasis basis
') : WellFormedBasis basis
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem of_append_right {left right : Basis} (h : WellFormedBasis (left ++ right)) :
    WellFormedBasis right :=
  h.of_sublist (by simp)
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.compare_left_aux** 是 Mathlib 中的一个定理，
位于命名空间 `Tactic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：compare_left_aux {basis : Basis} {f : Real -> Real} (h : WellFormedBasis b
asis) (h_comp : forall g, basis.getLast? = .some g -> (Real.log ∘ f) =o[atTop] (
Real.log ∘ g)) : forall g in basis, (Real.log ∘ f) =o[atTop] (Real.log ∘ g)
参数：h : WellFormedBasis basis；h_comp : forall g, basis.getLast? = .some g -> (Rea
l.log ∘ f) =o[atTop] (Real.log ∘ g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.eq_nil_or_concat`：∀ {α : Type u_1} (l : List α), l = [] ∨ ∃ l' b, l
 = l'.concat b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Asymptotics.IsLittleO.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {l : Fi
lter α} {f : α → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.getLast?_append`：∀ {α : Type u_1} {l l' : List α}, (l ++ l').getLas
t? = l'.getLast?.or l.getLast?
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem compare_left_aux {basis : Basis} {f : ℝ → ℝ} (h : WellFormedBasis basis)
    (h_comp : ∀ g, basis.getLast? = .some g → (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) :
    ∀ g ∈ basis, (Real.log ∘ f) =o[atTop] (Real.log ∘ g) := by
  intro g hg
  rcases basis.eq_nil_or_concat with rfl | ⟨basis_begin, basis_end, rfl⟩
  · simp at hg
  simp only [List.concat_eq_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq,
    forall_eq'] at hg h_comp
  rcases hg with hg | hg
  · simp only [WellFormedBasis, List.concat_eq_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at h
    exact h_comp.trans (by grind)
  · grind
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.compare_right_aux** 是 Mathlib 中的一个定理
，位于命名空间 `Tactic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：compare_right_aux {basis : Basis} {f : Real -> Real} (h : WellFormedBasis 
basis) (h_comp : forall g, basis.head? = .some g -> (Real.log ∘ g) =o[atTop] (Re
al.log ∘ f)) : forall g in basis, (Real.log ∘ g) =o[atTop] (Real.log ∘ f)
参数：h : WellFormedBasis basis；h_comp : forall g, basis.head? = .some g -> (Real.l
og ∘ g) =o[atTop] (Real.log ∘ f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsLittleO.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {l : Fi
lter α} {f : α → …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem compare_right_aux {basis : Basis} {f : ℝ → ℝ} (h : WellFormedBasis basis)
    (h_comp : ∀ g, basis.head? = .some g → (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    ∀ g ∈ basis, (Real.log ∘ g) =o[atTop] (Real.log ∘ f) := by
  intro g hg
  cases basis with
  | nil => simp at hg
  | cons basis_hd basis_tl =>
    specialize h_comp basis_hd (by simp)
    simp only [List.mem_cons] at hg
    rcases hg with hg | hg
    · simpa [hg]
    · simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
      exact .trans (by grind) h_comp
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.append** 是 Mathlib 中的一个定理，位于命名空间 `Ta
ctic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：append {left right : Basis} (h_left : WellFormedBasis left) (h_right : Wel
lFormedBasis right) (h : forall f in left, forall g in right, (Real.log ∘ g) =o[
atTop] (Real.log ∘ f)) : WellFormedBasis (left ++ right)
参数：h_left : WellFormedBasis left；h_right : WellFormedBasis right；h : forall f in
 left, forall g in right, (Real.log ∘ g) =o[atTop] (Real.log ∘ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem append {left right : Basis}
    (h_left : WellFormedBasis left) (h_right : WellFormedBasis right)
    (h : ∀ f ∈ left, ∀ g ∈ right, (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    WellFormedBasis (left ++ right) := by
  simp only [WellFormedBasis] at *
  constructor
  · simpa [List.pairwise_append, h_left, h_right] using h
  · grind
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.cons** 是 Mathlib 中的一个定理，位于命名空间 `Tact
ic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：cons {basis : Basis} {f : Real -> Real} (h_basis : WellFormedBasis basis) 
(hf_tendsto : Tendsto f atTop atTop) (hf : forall g in basis, (Real.log ∘ g) =o[
atTop] (Real.log ∘ f)) : WellFormedBasis (f :: basis)
参数：h_basis : WellFormedBasis basis；hf_tendsto : Tendsto f atTop atTop；hf : foral
l g in basis, (Real.log ∘ g) =o[atTop] (Real.log ∘ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.append`：append {left right : B
asis} (h_left : WellFormedBasis left) (h_right : WellFormedBasis right) (h : for
all f in left, forall g in right, (Rea…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem cons {basis : Basis} {f : ℝ → ℝ} (h_basis : WellFormedBasis basis)
    (hf_tendsto : Tendsto f atTop atTop)
    (hf : ∀ g ∈ basis, (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    WellFormedBasis (f :: basis) := by
  change WellFormedBasis ([f] ++ basis)
  exact append (by simpa [WellFormedBasis]) h_basis (by simpa)
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.insert** 是 Mathlib 中的一个定理，位于命名空间 `Ta
ctic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：insert {left right : Basis} {f : Real -> Real} (h : WellFormedBasis (left 
++ right)) (hf_tendsto : Tendsto f atTop atTop) (hf_comp_left : forall g, left.g
etLast? = .some g -> (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) (hf_comp_right : f
orall g, right.head? = .some g -> (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) : Wel
lFormedBasis (left ++ f :: right)
参数：h : WellFormedBasis (left ++ right)；hf_tendsto : Tendsto f atTop atTop；hf_com
p_left : forall g, left.getLast? = .some g -> (Real.log ∘ f) =o[atTop] (Real.log
 ∘ g)；hf_comp_right : forall g, right.head? = .some g -> (Real.log ∘ g) =o[atTop
] (Real.log ∘ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.cons`：cons {basis : Basis} {f 
: Real -> Real} (h_basis : WellFormedBasis basis) (hf_tendsto : Tendsto f atTop 
atTop) (hf : forall g in basis, (Rea…
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.of_sublist`：of_sublist {basis 
basis' : Basis} (h : List.Sublist basis basis') (h_basis : WellFormedBasis basis
') : WellFormedBasis basis
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.compare_right_aux`：compare_rig
ht_aux {basis : Basis} {f : Real -> Real} (h : WellFormedBasis basis) (h_comp : 
forall g, basis.head? = .some g -> (Real.log ∘ g)…
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.append`：append {left right : B
asis} (h_left : WellFormedBasis left) (h_right : WellFormedBasis right) (h : for
all f in left, forall g in right, (Rea…
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.compare_left_aux`：compare_left
_aux {basis : Basis} {f : Real -> Real} (h : WellFormedBasis basis) (h_comp : fo
rall g, basis.getLast? = .some g -> (Real.log ∘ …
-/
theorem insert {left right : Basis} {f : ℝ → ℝ}
    (h : WellFormedBasis (left ++ right)) (hf_tendsto : Tendsto f atTop atTop)
    (hf_comp_left : ∀ g, left.getLast? = .some g → (Real.log ∘ f) =o[atTop] (Real.log ∘ g))
    (hf_comp_right : ∀ g, right.head? = .some g → (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    WellFormedBasis (left ++ f :: right) := by
  have : WellFormedBasis (f :: right) := cons (h.of_sublist (by simp)) hf_tendsto
    (compare_right_aux (h.of_sublist (by simp)) hf_comp_right)
  apply compare_left_aux (h.of_sublist (by simp)) at hf_comp_left
  apply append (h.of_sublist (by simp)) this
  exact fun g hg ↦ compare_right_aux this (by grind)
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.push** 是 Mathlib 中的一个定理，位于命名空间 `Tact
ic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：push {basis : Basis} {f : Real -> Real} (h : WellFormedBasis basis) (hf_te
ndsto : Tendsto f atTop atTop) (hf_comp : forall g, basis.getLast? = .some g -> 
(Real.log ∘ f) =o[atTop] (Real.log ∘ g)) : WellFormedBasis (basis ++ [f])
参数：h : WellFormedBasis basis；hf_tendsto : Tendsto f atTop atTop；hf_comp : forall
 g, basis.getLast? = .some g -> (Real.log ∘ f) =o[atTop] (Real.log ∘ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.insert`：insert {left right : B
asis} {f : Real -> Real} (h : WellFormedBasis (left ++ right)) (hf_tendsto : Ten
dsto f atTop atTop) (hf_comp_left : fo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem push {basis : Basis} {f : ℝ → ℝ} (h : WellFormedBasis basis)
    (hf_tendsto : Tendsto f atTop atTop)
    (hf_comp : ∀ g, basis.getLast? = .some g → (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) :
    WellFormedBasis (basis ++ [f]) :=
  insert (by simp [h]) hf_tendsto hf_comp (by simp)

/-- All functions from a well-formed basis tend to `atTop`. -/
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.tendsto_atTop** 是 Mathlib 中的一个定理，位于命
名空间 `Tactic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：tendsto_atTop {basis : Basis} (h : WellFormedBasis basis) {f : Real -> Rea
l} (hf : f in basis) : Tendsto f atTop atTop
参数：h : WellFormedBasis basis；hf : f in basis。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
All functions from a well-formed basis tend to `atTop`.
-/
theorem tendsto_atTop {basis : Basis} (h : WellFormedBasis basis) {f : ℝ → ℝ}
    (hf : f ∈ basis) :
    Tendsto f atTop atTop := h.right f hf

/-- Eventually all functions from a well-formed basis are positive. -/
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.eventually_pos** 是 Mathlib 中的一个定理，位于
命名空间 `Tactic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：eventually_pos {basis : Basis} (h : WellFormedBasis basis) : forallᶠ x in 
atTop, forall f in basis, 0 < f x
参数：h : WellFormedBasis basis。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b

--- 原说明 ---
Eventually all functions from a well-formed basis are positive.
-/
theorem eventually_pos {basis : Basis} (h : WellFormedBasis basis) :
    ∀ᶠ x in atTop, ∀ f ∈ basis, 0 < f x := by
  induction basis with
  | nil => simp
  | cons hd tl ih =>
    simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
    simp only [List.mem_cons, forall_eq_or_imp]
    exact (h.right.left.eventually <| eventually_gt_atTop 0).and (ih (by tauto))

/-- The first function in a well-formed basis is eventually positive. -/
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.head_eventually_pos** 是 Mathlib 中的一个
定理，位于命名空间 `Tactic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：head_eventually_pos {basis_hd : Real -> Real} {basis_tl : Basis} (h : Well
FormedBasis (basis_hd :: basis_tl)) : forallᶠ x in atTop, 0 < basis_hd x
参数：h : WellFormedBasis (basis_hd :: basis_tl)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.forall_eventually_of_eventually_forall`：forall_eventually_of_even
tually_forall {f : Filter α} {p : α -> β -> Prop} (h : forallᶠ x in f, forall y,
 p x y) : forall y, forallᶠ x in f,…
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.eventually_pos`：eventually_pos
 {basis : Basis} (h : WellFormedBasis basis) : forallᶠ x in atTop, forall f in b
asis, 0 < f x

--- 原说明 ---
The first function in a well-formed basis is eventually positive.
-/
theorem head_eventually_pos {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : WellFormedBasis (basis_hd :: basis_tl)) : ∀ᶠ x in atTop, 0 < basis_hd x :=
  (forall_eventually_of_eventually_forall h.eventually_pos basis_hd).mono (by grind)

/-- All functions in the tail of a well-formed basis are little-o of the basis' head. -/
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.tail_isLittleO_head** 是 Mathlib 中的一个
定理，位于命名空间 `Tactic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：tail_isLittleO_head {hd : Real -> Real} {tl : Basis} (h : WellFormedBasis 
(hd :: tl)) {f : Real -> Real} (hf : f in tl) : (Real.log ∘ f) =o[atTop] (Real.l
og ∘ hd)
参数：h : WellFormedBasis (hd :: tl)；hf : f in tl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.eq_1`：∀ (basis : Tactic.Comput
eAsymptotics.Basis),   Tactic.ComputeAsymptotics.WellFormedBasis basis =     (Li
st.Pairwise (fun x y => (Real.log ∘ …

--- 原说明 ---
All functions in the tail of a well-formed basis are little-o of the basis' head
.
-/
theorem tail_isLittleO_head {hd : ℝ → ℝ} {tl : Basis}
    (h : WellFormedBasis (hd :: tl)) {f : ℝ → ℝ} (hf : f ∈ tl) :
    (Real.log ∘ f) =o[atTop] (Real.log ∘ hd) := by
  rw [WellFormedBasis, List.pairwise_cons] at h
  exact h.left.left _ hf
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.push_log_last** 是 Mathlib 中的一个定理，位于命
名空间 `Tactic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：push_log_last {basis_hd : Real -> Real} {basis_tl : Basis} (h_basis : Well
FormedBasis (basis_hd :: basis_tl)) : WellFormedBasis ((basis_hd :: basis_tl) ++
 [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)])
参数：h_basis : WellFormedBasis (basis_hd :: basis_tl)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.push`：push {basis : Basis} {f 
: Real -> Real} (h : WellFormedBasis basis) (hf_tendsto : Tendsto f atTop atTop)
 (hf_comp : forall g, basis.getLast?…
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getLast_of_getLast?_eq_some`：∀ {α : Type u_1} {x : α} {l : List α} 
(hx : l.getLast? = some x), l.getLast ⋯ = x
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `Real.isLittleO_log_id_atTop`：isLittleO_log_id_atTop : log =o[atTop] id
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tendsto_atTop`：tendsto_atTop {
basis : Basis} (h : WellFormedBasis basis) {f : Real -> Real} (hf : f in basis) 
: Tendsto f atTop atTop
· 使用定理 `List.mem_of_getLast?`：∀ {α : Type u_1} {l : List α} {a : α}, l.getLast? 
= some a → a ∈ l
-/
theorem push_log_last {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    WellFormedBasis ((basis_hd :: basis_tl) ++
      [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) := by
  apply h_basis.push
  · simp [Real.tendsto_log_atTop.comp, h_basis.right]
  · intro g hg
    simpa [List.getLast_of_getLast?_eq_some hg] using Real.isLittleO_log_id_atTop.comp_tendsto <|
      Real.tendsto_log_atTop.comp <| h_basis.tendsto_atTop <| List.mem_of_getLast? hg

/-- Auxiliary lemma. If function `f` is eventually positive, `g` tends to `atTop`, and
`log f =o[atTop] log g` then for any `a` and `b > 0`, then `f^a =o[atTop] g^b`. -/
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.pow_isLittleO_pow_of_log** 是 Mathlib
 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：pow_isLittleO_pow_of_log {f g : Real -> Real} (a b : Real) (hf : forallᶠ x
 in atTop, 0 < f x) (hg : Tendsto g atTop atTop) (h : (Real.log ∘ f) =o[atTop] (
Real.log ∘ g)) (hb : 0 < b) : (f ^ a) =o[atTop] (g ^ b)
参数：a b : Real；hf : forallᶠ x in atTop, 0 < f x；hg : Tendsto g atTop atTop；h : (R
eal.log ∘ f) =o[atTop] (Real.log ∘ g)；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_tendsto_div_atTop`：∀ {α : Type u_1} {𝕜 : Type u
_17} [inst : NormedField 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [
OrderTopology 𝕜] {l : Filter α} …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Tendsto.eventually_gt_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用定理 `Real.exp_mul`：exp_mul (x y : Real) : exp (x * y) = exp x ^ y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_exp_atTop`：tendsto_exp_atTop : Tendsto exp atTop atTop
· 使用定理 `Asymptotics.IsLittleO.const_mul_right`：∀ {α : Type u_1} {E : Type u_3} [
inst : Norm E] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S] {f : α →
 E}   {l : Filter α} {g : α…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Asymptotics.IsLittleO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R
 : Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filte
r α}   {f : α → R}, f =o[l…
· 使用定理 `Asymptotics.IsEquivalent.tendsto_atTop_iff`：∀ {α : Type u_1} {β : Type u
_2} [inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v
 : α → β}   {l : Filter α} [Orde…
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop

--- 原说明 ---
Auxiliary lemma. If function `f` is eventually positive, `g` tends to `atTop`, a
nd
`log f =o[atTop] log g` then for any `a` and `b > 0`, then `f^a =o[atTop] g^b`.
-/
theorem pow_isLittleO_pow_of_log {f g : ℝ → ℝ} (a b : ℝ) (hf : ∀ᶠ x in atTop, 0 < f x)
    (hg : Tendsto g atTop atTop) (h : (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) (hb : 0 < b) :
    (f ^ a) =o[atTop] (g ^ b) := by
  apply IsLittleO.of_tendsto_div_atTop
  apply Tendsto.congr' (f₁ := Real.exp ∘ (b • Real.log ∘ g - a • Real.log ∘ f))
  · refine (hf.and (hg.eventually_gt_atTop 0)).mono (fun x ⟨hf, hg⟩ ↦ ?_)
    simp [Real.exp_sub, mul_comm a, mul_comm b, Real.exp_mul, Real.exp_log hg, Real.exp_log hf]
  apply Real.tendsto_exp_atTop.comp
  have h' : (b • Real.log ∘ g - a • Real.log ∘ f) ~[atTop] b • Real.log ∘ g := by
    replace h : (a • Real.log ∘ f) =o[atTop] (b • Real.log ∘ g) :=
      (h.const_mul_left a).const_mul_right (hb.ne')
    grind only [IsEquivalent.sub_isLittleO, IsEquivalent.refl]
  rw [h'.tendsto_atTop_iff]
  apply Filter.Tendsto.const_mul_atTop hb
  apply Real.tendsto_log_atTop.comp hg

/-- Any power of function from a well-formed basis' tail is Majorized by
basis' head with zero exponent. -/
/-
**Tactic.ComputeAsymptotics.WellFormedBasis.tail_pow_majorized_head** 是 Mathlib 
中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.WellFormedBasis`。
形式化陈述：tail_pow_majorized_head {hd f : Real -> Real} {tl : Basis} (h_basis : Well
FormedBasis (hd :: tl)) (hf : f in tl) (r : Real) : Majorized (f ^ r) hd 0
参数：h_basis : WellFormedBasis (hd :: tl)；hf : f in tl；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.pow_isLittleO_pow_of_log`：pow_
isLittleO_pow_of_log {f g : Real -> Real} (a b : Real) (hf : forallᶠ x in atTop,
 0 < f x) (hg : Tendsto g atTop atTop) (h : (Real.log ∘ …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.eventually_pos`：eventually_pos
 {basis : Basis} (h : WellFormedBasis basis) : forallᶠ x in atTop, forall f in b
asis, 0 < f x
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tail`：tail {basis_hd : Real ->
 Real} {basis_tl : Basis} (h : WellFormedBasis (basis_hd :: basis_tl)) : WellFor
medBasis basis_tl
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tendsto_atTop`：tendsto_atTop {
basis : Basis} (h : WellFormedBasis basis) {f : Real -> Real} (hf : f in basis) 
: Tendsto f atTop atTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True

--- 原说明 ---
Any power of function from a well-formed basis' tail is Majorized by
basis' head with zero exponent.
-/
theorem tail_pow_majorized_head {hd f : ℝ → ℝ} {tl : Basis}
    (h_basis : WellFormedBasis (hd :: tl)) (hf : f ∈ tl) (r : ℝ) :
    Majorized (f ^ r) hd 0 := by
  intro exp h_exp
  apply pow_isLittleO_pow_of_log
  · exact h_basis.tail.eventually_pos.mono fun _ h ↦ h _ hf
  · exact h_basis.tendsto_atTop (by simp)
  · grind [WellFormedBasis, List.pairwise_cons]
  · exact h_exp

end WellFormedBasis

/-! ### Basis extensions -/

/-- The type of extensions of a given basis, defined as an inductive type.
Given a `basis : Basis` and `ex : BasisExtension basis` of it, one can use `getBasis` to produce a
basis `basis'` for which `basis <+ basis'`. Moreover, all such bases for which `basis` is a sublist
can be obtained in this manner. In this sense `BasisExtension` is a `Type`-valued analogue
of `List.Sublist`. -/
/-
**Tactic.ComputeAsymptotics.BasisExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 `Tactic.C
omputeAsymptotics`。
形式化陈述：Tactic.ComputeAsymptotics.Basis → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of extensions of a given basis, defined as an inductive type.
Given a `basis : Basis` and `ex : BasisExtension basis` of it, one can use `getB
asis` to produce a
basis `basis'` for which `basis <+ basis'`. Moreover, all such bases for which `
basis` is a sublist
can be obtained in this manner. In this sense `BasisExtension` is a `Type`-value
d analogue
of `List.Sublist`.
-/
inductive BasisExtension : Basis → Type
| nil : BasisExtension []
| keep (basis_hd : ℝ → ℝ) {basis_tl : Basis} (ex : BasisExtension basis_tl) :
  BasisExtension (basis_hd :: basis_tl)
| insert {basis : Basis} (f : ℝ → ℝ) (ex : BasisExtension basis) : BasisExtension basis

namespace BasisExtension

/-- The basis after applying a basis extension. -/
/-
**Tactic.ComputeAsymptotics.BasisExtension.getBasis** 是 Mathlib 中的一个定义，位于命名空间 `T
actic.ComputeAsymptotics.BasisExtension`。
形式化陈述：getBasis {basis : Basis} (ex : BasisExtension basis) : Basis
参数：ex : BasisExtension basis。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis after applying a basis extension.
-/
def getBasis {basis : Basis} (ex : BasisExtension basis) : Basis :=
  match ex with
  | nil => []
  | keep basis_hd ex => basis_hd :: ex.getBasis
  | insert f ex => f :: ex.getBasis
/-
**Tactic.ComputeAsymptotics.BasisExtension.sublist_getBasis** 是 Mathlib 中的一个定理，位
于命名空间 `Tactic.ComputeAsymptotics.BasisExtension`。
形式化陈述：sublist_getBasis {basis : Basis} {ex : BasisExtension basis} : List.Sublis
t basis ex.getBasis
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem sublist_getBasis {basis : Basis} {ex : BasisExtension basis} :
    List.Sublist basis ex.getBasis := by
  induction ex with
  | nil => simp
  | keep _ ex ih => simpa [getBasis] using ih
  | insert _ ex ih => exact List.Sublist.cons _ ih
/-
**Tactic.ComputeAsymptotics.BasisExtension.insert_tail_wellFormedBasis** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.BasisExtension`。
形式化陈述：insert_tail_wellFormedBasis {basis : Basis} {f : Real -> Real} {ex_tl : Ba
sisExtension basis} (h_basis : WellFormedBasis <| BasisExtension.getBasis (.inse
rt f ex_tl)) : WellFormedBasis ex_tl.getBasis
参数：h_basis : WellFormedBasis <| BasisExtension.getBasis (.insert f ex_tl)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.of_sublist`：of_sublist {basis 
basis' : Basis} (h : List.Sublist basis basis') (h_basis : WellFormedBasis basis
') : WellFormedBasis basis
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem insert_tail_wellFormedBasis {basis : Basis} {f : ℝ → ℝ}
    {ex_tl : BasisExtension basis}
    (h_basis : WellFormedBasis <| BasisExtension.getBasis (.insert f ex_tl)) :
    WellFormedBasis ex_tl.getBasis :=
  h_basis.of_sublist (by simp [getBasis])

end BasisExtension

end Tactic.ComputeAsymptotics

