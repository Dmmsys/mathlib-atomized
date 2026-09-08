/-
Copyright (c) 2024 Google. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/
module

public import Mathlib.Computability.DFA
public import Mathlib.Data.Set.Finite.Basic

/-!
# Myhill–Nerode theorem

This file proves the Myhill–Nerode theorem using left quotients.

Given a language `L` and a word `x`, the *left quotient* of `L` by `x` is the set of suffixes `y`
such that `x ++ y` is in `L`. The *Myhill–Nerode theorem* shows that each left quotient, in fact,
corresponds to the state of an automaton that matches `L`, and that `L` is regular if and only if
there are finitely many such states.

## References

* <https://en.wikipedia.org/wiki/Syntactic_monoid#Myhill%E2%80%93Nerode_theorem>
-/

@[expose] public section

universe u v
variable {α : Type u} {σ : Type v} {L : Language α}

namespace Language

variable (L) in
/-- The *left quotient* of `x` is the set of suffixes `y` such that `x ++ y` is in `L`. -/
/-
**Language.leftQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Language`。
形式化陈述：leftQuotient (x : List α) : Language α
参数：x : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *left quotient* of `x` is the set of suffixes `y` such that `x ++ y` is in `
L`.
-/
def leftQuotient (x : List α) : Language α := { y | x ++ y ∈ L }

variable (L) in
@[simp]
/-
**Language.leftQuotient_nil** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：leftQuotient_nil : L.leftQuotient [] = L
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftQuotient_nil : L.leftQuotient [] = L := rfl

set_option backward.isDefEq.respectTransparency false in
variable (L) in
/-
**Language.leftQuotient_append** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：leftQuotient_append (x y : List α) : L.leftQuotient (x ++ y) = (L.leftQuot
ient x).leftQuotient y
参数：x y : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftQuotient_append (x y : List α) :
    L.leftQuotient (x ++ y) = (L.leftQuotient x).leftQuotient y := by
  simp [leftQuotient, Language]

@[simp]
/-
**Language.mem_leftQuotient** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：mem_leftQuotient (x y : List α) : y in L.leftQuotient x ↔ x ++ y in L
参数：x y : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_leftQuotient (x y : List α) : y ∈ L.leftQuotient x ↔ x ++ y ∈ L := Iff.rfl
/-
**Language.leftQuotient_accepts_apply** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：leftQuotient_accepts_apply (M : DFA α σ) (x : List α) : leftQuotient M.acc
epts x = M.acceptsFrom (M.eval x)
参数：M : DFA α σ；x : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFA.evalFrom_of_append`：evalFrom_of_append (start : σ) (x y : List α) : 
M.evalFrom start (x ++ y) = M.evalFrom (M.evalFrom start x) y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem leftQuotient_accepts_apply (M : DFA α σ) (x : List α) :
    leftQuotient M.accepts x = M.acceptsFrom (M.eval x) := by
  ext y
  simp [DFA.mem_accepts, DFA.mem_acceptsFrom, DFA.eval, DFA.evalFrom_of_append]
/-
**Language.leftQuotient_accepts** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：leftQuotient_accepts (M : DFA α σ) : leftQuotient M.accepts = M.acceptsFro
m ∘ M.eval
参数：M : DFA α σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Language.leftQuotient_accepts_apply`：leftQuotient_accepts_apply (M : DFA
 α σ) (x : List α) : leftQuotient M.accepts x = M.acceptsFrom (M.eval x)
-/
theorem leftQuotient_accepts (M : DFA α σ) : leftQuotient M.accepts = M.acceptsFrom ∘ M.eval :=
  funext <| leftQuotient_accepts_apply M
/-
**Language.IsRegular.finite_range_leftQuotient** 是 Mathlib 中的一个定理，位于命名空间 `Langua
ge.IsRegular`。
形式化陈述：∀ {α : Type u} {L : Language α}, L.IsRegular → (Set.range L.leftQuotient).
Finite
参数：Set.range L.leftQuotient。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Language.leftQuotient_accepts`：leftQuotient_accepts (M : DFA α σ) : left
Quotient M.accepts = M.acceptsFrom ∘ M.eval
· 使用定理 `Set.finite_of_finite_preimage`：finite_of_finite_preimage (h : (f ⁻¹' s).
Finite) (hs : s subseteq range f) : s.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
theorem IsRegular.finite_range_leftQuotient (h : L.IsRegular) :
    (Set.range L.leftQuotient).Finite := by
  have ⟨σ, x, M, hM⟩ := h
  rw [← hM, leftQuotient_accepts]
  exact Set.finite_of_finite_preimage (Set.toFinite _)
    (Set.range_comp_subset_range M.eval M.acceptsFrom)

variable (L) in
/-- The left quotients of a language are the states of an automaton that accepts the language. -/
/-
**Language.toDFA** 是 Mathlib 中的一个定义，位于命名空间 `Language`。
形式化陈述：toDFA : DFA α (Set.range L.leftQuotient) where step s a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left quotients of a language are the states of an automaton that accepts the
 language.
-/
def toDFA : DFA α (Set.range L.leftQuotient) where
  step s a := by
    refine ⟨s.val.leftQuotient [a], ?_⟩
    obtain ⟨y, hy⟩ := s.prop
    exists y ++ [a]
    rw [← hy, leftQuotient_append]
  start := ⟨L, by exists []⟩
  accept := { s | [] ∈ s.val }

@[simp]
/-
**Language.mem_accept_toDFA** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：mem_accept_toDFA (s : Set.range L.leftQuotient) : s in L.toDFA.accept ↔ []
 in s.val
参数：s : Set.range L.leftQuotient。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_accept_toDFA (s : Set.range L.leftQuotient) : s ∈ L.toDFA.accept ↔ [] ∈ s.val := Iff.rfl

@[simp]
/-
**Language.step_toDFA** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：step_toDFA (s : Set.range L.leftQuotient) (a : α) : (L.toDFA.step s a).val
 = s.val.leftQuotient [a]
参数：s : Set.range L.leftQuotient；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem step_toDFA (s : Set.range L.leftQuotient) (a : α) :
    (L.toDFA.step s a).val = s.val.leftQuotient [a] := rfl

variable (L) in
@[simp]
/-
**Language.start_toDFA** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：start_toDFA : L.toDFA.start.val = L
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem start_toDFA : L.toDFA.start.val = L := rfl

variable (L) in
@[simp]
/-
**Language.accepts_toDFA** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：accepts_toDFA : L.toDFA.accepts = L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFA.mem_accepts`：mem_accepts {x : List α} : x in M.accepts ↔ M.eval x in
 M.accept
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DFA.eval_append_singleton`：eval_append_singleton (x : List α) (a : α) : 
M.eval (x ++ [a]) = M.step (M.eval x) a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Language.leftQuotient_append`：leftQuotient_append (x y : List α) : L.lef
tQuotient (x ++ y) = (L.leftQuotient x).leftQuotient y
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem accepts_toDFA : L.toDFA.accepts = L := by
  ext x
  rw [DFA.mem_accepts]
  suffices L.toDFA.eval x = L.leftQuotient x by simp [this]
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih, leftQuotient_append]
/-
**Language.IsRegular.of_finite_range_leftQuotient** 是 Mathlib 中的一个定理，位于命名空间 `Lan
guage.IsRegular`。
形式化陈述：∀ {α : Type u} {L : Language α}, (Set.range L.leftQuotient).Finite → L.IsR
egular
参数：Set.range L.leftQuotient。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Language.isRegular_iff`：isRegular_iff {T : Type u} {L : Language T} : L.
IsRegular ↔ exists σ : Type v, exists _ : Fintype σ, exists M : DFA T σ, M.accep
ts = L
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Language.accepts_toDFA`：accepts_toDFA : L.toDFA.accepts = L
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsRegular.of_finite_range_leftQuotient (h : Set.Finite (Set.range L.leftQuotient)) :
    L.IsRegular :=
  Language.isRegular_iff.mpr ⟨_, h.fintype, L.toDFA, by simp⟩

/--
**Myhill–Nerode theorem**. A language is regular if and only if the set of left quotients is finite.
-/
/-
**Language.isRegular_iff_finite_range_leftQuotient** 是 Mathlib 中的一个定理，位于命名空间 `La
nguage`。
形式化陈述：isRegular_iff_finite_range_leftQuotient : L.IsRegular ↔ (Set.range L.leftQ
uotient).Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.IsRegular.finite_range_leftQuotient`：∀ {α : Type u} {L : Langua
ge α}, L.IsRegular → (Set.range L.leftQuotient).Finite
· 使用定理 `Language.IsRegular.of_finite_range_leftQuotient`：∀ {α : Type u} {L : Lan
guage α}, (Set.range L.leftQuotient).Finite → L.IsRegular

--- 原说明 ---
**Myhill–Nerode theorem**. A language is regular if and only if the set of left 
quotients is finite.
-/
theorem isRegular_iff_finite_range_leftQuotient :
    L.IsRegular ↔ (Set.range L.leftQuotient).Finite :=
  ⟨IsRegular.finite_range_leftQuotient, .of_finite_range_leftQuotient⟩

end Language

