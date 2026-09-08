/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Chris Wong, Rudy Peterson
-/
module

public import Mathlib.Computability.Language
public import Mathlib.Data.Countable.Small
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.NormNum

/-!
# Deterministic Finite Automata

A Deterministic Finite Automaton (DFA) is a state machine which
decides membership in a particular `Language`, by following a path
uniquely determined by an input string.

We define regular languages to be ones for which a DFA exists, other formulations
are later proved equivalent.

Note that this definition allows for automata with infinite states,
a `Fintype` instance must be supplied for true DFAs.

## Main definitions

- `DFA α σ`: automaton over alphabet `α` and set of states `σ`
- `M.accepts`: the language accepted by the DFA `M`
- `Language.IsRegular L`: a predicate stating that `L` is a regular language, i.e. there exists
  a DFA that recognizes the language

## Main theorems

- `DFA.pumping_lemma` : every sufficiently long string accepted by the DFA has a substring that can
  be repeated arbitrarily many times (and have the overall string still be accepted)

## Implementation notes

Currently, there are two disjoint sets of simp lemmas: one for `DFA.eval`, and another for
`DFA.evalFrom`. You can switch from the former to the latter using `simp [eval]`.

## TODO

- Should we unify these simp sets, such that `eval` is rewritten to `evalFrom` automatically?
- Should `mem_accepts` and `mem_acceptsFrom` be marked `@[simp]`?
-/

@[expose] public section

universe u v

open Computability

/-- A DFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`). -/
/-
**DFA** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type v → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A DFA is a set of states (`σ`), a transition function from state to state labell
ed by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (
`accept`).
-/
structure DFA (α : Type u) (σ : Type v) where
  /-- A transition function from state to state labelled by the alphabet. -/
  step : σ → α → σ
  /-- Starting state. -/
  start : σ
  /-- Set of acceptance states. -/
  accept : Set σ

namespace DFA

variable {α : Type u} {σ : Type v} (M : DFA α σ)

/-
**DFA.** 是 Mathlib 中的一个实例，位于命名空间 `DFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited σ] : Inhabited (DFA α σ) :=
  ⟨DFA.mk (fun _ _ => default) default ∅⟩

/-- `M.evalFrom s x` evaluates `M` with input `x` starting from the state `s`. -/
/-
**DFA.evalFrom** 是 Mathlib 中的一个定义，位于命名空间 `DFA`。
形式化陈述：evalFrom (s : σ) : List α -> σ
参数：s : σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.evalFrom s x` evaluates `M` with input `x` starting from the state `s`.
-/
def evalFrom (s : σ) : List α → σ :=
  List.foldl M.step s

@[simp]
/-
**DFA.evalFrom_nil** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：evalFrom_nil (s : σ) : M.evalFrom s [] = s
参数：s : σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalFrom_nil (s : σ) : M.evalFrom s [] = s :=
  rfl

@[simp]
/-
**DFA.evalFrom_cons** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：evalFrom_cons (s : σ) (a : α) (x : List α) : M.evalFrom s (a :: x) = M.eva
lFrom (M.step s a) x
参数：s : σ；a : α；x : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalFrom_cons (s : σ) (a : α) (x : List α) :
    M.evalFrom s (a :: x) = M.evalFrom (M.step s a) x :=
  rfl

@[simp]
/-
**DFA.evalFrom_singleton** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：evalFrom_singleton (s : σ) (a : α) : M.evalFrom s [a] = M.step s a
参数：s : σ；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalFrom_singleton (s : σ) (a : α) : M.evalFrom s [a] = M.step s a :=
  rfl

@[simp]
/-
**DFA.evalFrom_append_singleton** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：evalFrom_append_singleton (s : σ) (x : List α) (a : α) : M.evalFrom s (x +
+ [a]) = M.step (M.evalFrom s x) a
参数：s : σ；x : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldl_append`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {b : 
β} {l l' : List α},   List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l)
 l'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalFrom_append_singleton (s : σ) (x : List α) (a : α) :
    M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
/-
**DFA.eval** 是 Mathlib 中的一个定义，位于命名空间 `DFA`。
形式化陈述：eval : List α -> σ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.eval x` evaluates `M` with input `x` starting from the state `M.start`.
-/
def eval : List α → σ :=
  M.evalFrom M.start

@[simp]
/-
**DFA.eval_nil** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：eval_nil : M.eval [] = M.start
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_nil : M.eval [] = M.start :=
  rfl

@[simp]
/-
**DFA.eval_singleton** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：eval_singleton (a : α) : M.eval [a] = M.step M.start a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_singleton (a : α) : M.eval [a] = M.step M.start a :=
  rfl

@[simp]
/-
**DFA.eval_append_singleton** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.step (M
.eval x) a
参数：x : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFA.evalFrom_append_singleton`：evalFrom_append_singleton (s : σ) (x : Li
st α) (a : α) : M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a
-/
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.step (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _
/-
**DFA.evalFrom_of_append** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：evalFrom_of_append (start : σ) (x y : List α) : M.evalFrom start (x ++ y) 
= M.evalFrom (M.evalFrom start x) y
参数：start : σ；x y : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.foldl_append`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {b : 
β} {l l' : List α},   List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l)
 l'
-/
theorem evalFrom_of_append (start : σ) (x y : List α) :
    M.evalFrom start (x ++ y) = M.evalFrom (M.evalFrom start x) y :=
  List.foldl_append

/--
`M.acceptsFrom s` is the language of `x` such that `M.evalFrom s x` is an accept state.
-/
/-
**DFA.acceptsFrom** 是 Mathlib 中的一个定义，位于命名空间 `DFA`。
形式化陈述：acceptsFrom (s : σ) : Language α
参数：s : σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.acceptsFrom s` is the language of `x` such that `M.evalFrom s x` is an accept
 state.
-/
def acceptsFrom (s : σ) : Language α := {x | M.evalFrom s x ∈ M.accept}
/-
**DFA.mem_acceptsFrom** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：mem_acceptsFrom {s : σ} {x : List α} : x in M.acceptsFrom s ↔ M.evalFrom s
 x in M.accept
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_acceptsFrom {s : σ} {x : List α} :
    x ∈ M.acceptsFrom s ↔ M.evalFrom s x ∈ M.accept := by rfl

/-- `M.accepts` is the language of `x` such that `M.eval x` is an accept state. -/
/-
**DFA.accepts** 是 Mathlib 中的一个定义，位于命名空间 `DFA`。
形式化陈述：accepts : Language α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.accepts` is the language of `x` such that `M.eval x` is an accept state.
-/
def accepts : Language α := M.acceptsFrom M.start
/-
**DFA.mem_accepts** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：mem_accepts {x : List α} : x in M.accepts ↔ M.eval x in M.accept
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ M.eval x ∈ M.accept := by rfl
/-
**DFA.evalFrom_split** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：evalFrom_split [Fintype σ] {x : List α} {s t : σ} (hlen : Fintype.card σ <
= x.length) (hx : M.evalFrom s x = t) : exists q a b c, x = a ++ b ++ c ∧ a.leng
th + b.length <= Fintype.card σ ∧ b != [] ∧ M.evalFrom s a = q ∧ M.evalFrom q b 
= q ∧ M.evalFrom q c = t
参数：hlen : Fintype.card σ <= x.length；hx : M.evalFrom s x = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.exists_ne_map_eq_of_card_lt`：exists_ne_map_eq_of_card_lt (f : α 
-> β) (h : Fintype.card β < Fintype.card α) : exists x y, x != y ∧ f x = f y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
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
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_take`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.take i l)
.length = min i l.length
· 使用定理 `List.length_drop`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.drop i l)
.length = l.length - i
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.take_take`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.take i (Li
st.take j l) = List.take (min i j) l
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFA.evalFrom_of_append`：evalFrom_of_append (start : σ) (x y : List α) : 
M.evalFrom start (x ++ y) = M.evalFrom (M.evalFrom start x) y
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem evalFrom_split [Fintype σ] {x : List α} {s t : σ} (hlen : Fintype.card σ ≤ x.length)
    (hx : M.evalFrom s x = t) :
    ∃ q a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card σ ∧
          b ≠ [] ∧ M.evalFrom s a = q ∧ M.evalFrom q b = q ∧ M.evalFrom q c = t := by
  obtain ⟨n, m, hneq, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card σ + 1) => M.evalFrom s (x.take n)) (by simp)
  wlog hle : (n : ℕ) ≤ m generalizing n m
  · exact this m n hneq.symm heq.symm (le_of_not_ge hle)
  refine
    ⟨M.evalFrom s ((x.take m).take n), (x.take m).take n, (x.take m).drop n,
                    x.drop m, ?_, ?_, ?_, by rfl, ?_⟩
  · rw [List.take_append_drop, List.take_append_drop]
  · simp only [List.length_drop, List.length_take]
    omega
  · intro h
    have hlen' := congr_arg List.length h
    simp only [List.length_drop, List.length, List.length_take] at hlen'
    omega
  have hq : M.evalFrom (M.evalFrom s ((x.take m).take n)) ((x.take m).drop n) =
      M.evalFrom s ((x.take m).take n) := by
    rw [List.take_take, min_eq_left hle, ← evalFrom_of_append, heq, ← min_eq_left hle, ←
      List.take_take, min_eq_left hle, List.take_append_drop]
  use hq
  rwa [← hq, ← evalFrom_of_append, ← evalFrom_of_append, ← List.append_assoc,
    List.take_append_drop, List.take_append_drop]

set_option backward.isDefEq.respectTransparency false in
/-
**DFA.evalFrom_of_pow** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：evalFrom_of_pow {x y : List α} {s : σ} (hx : M.evalFrom s x = s) (hy : y i
n ({x} : Language α)∗) : M.evalFrom s y = s
参数：hx : M.evalFrom s x = s；hy : y in ({x} : Language α)∗。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Language.mem_kstar`：mem_kstar : x in l∗ ↔ exists L : List (List α), x = 
L.flatten ∧ forall y in L, y in l
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.flatten_cons`：∀ {α : Type u_1} {l : List α} {L : List (List α)}, (l
 :: L).flatten = l ++ L.flatten
· 使用定理 `DFA.evalFrom_of_append`：evalFrom_of_append (start : σ) (x y : List α) : 
M.evalFrom start (x ++ y) = M.evalFrom (M.evalFrom start x) y
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem evalFrom_of_pow {x y : List α} {s : σ} (hx : M.evalFrom s x = s)
    (hy : y ∈ ({x} : Language α)∗) : M.evalFrom s y = s := by
  rw [Language.mem_kstar] at hy
  rcases hy with ⟨S, rfl, hS⟩
  induction S with
  | nil => rfl
  | cons a S ih =>
    have ha := hS a List.mem_cons_self
    rw [Set.mem_singleton_iff] at ha
    rw [List.flatten_cons, evalFrom_of_append, ha, hx]
    apply ih
    intro z hz
    exact hS z (List.mem_cons_of_mem a hz)

set_option backward.isDefEq.respectTransparency false in
/-
**DFA.pumping_lemma** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：pumping_lemma [Fintype σ] {x : List α} (hx : x in M.accepts) (hlen : Finty
pe.card σ <= List.length x) : exists a b c, x = a ++ b ++ c ∧ a.length + b.lengt
h <= Fintype.card σ ∧ b != [] ∧ {a} * {b}∗ * {c} <= M.accepts
参数：hx : x in M.accepts；hlen : Fintype.card σ <= List.length x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFA.evalFrom_split`：evalFrom_split [Fintype σ] {x : List α} {s t : σ} (h
len : Fintype.card σ <= x.length) (hx : M.evalFrom s x = t) : exists q a b c, x 
= a ++ b…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Language.mem_mul`：mem_mul : x in l * m ↔ exists a in l, exists b in m, a
 ++ b = x
· 使用定理 `DFA.evalFrom_of_pow`：evalFrom_of_pow {x y : List α} {s : σ} (hx : M.eval
From s x = s) (hy : y in ({x} : Language α)∗) : M.evalFrom s y = s
· 使用定理 `DFA.mem_accepts`：mem_accepts {x : List α} : x in M.accepts ↔ M.eval x in
 M.accept
· 使用定理 `DFA.eval.eq_1`：∀ {α : Type u} {σ : Type v} (M : DFA α σ), M.eval = M.eva
lFrom M.start
· 使用定理 `DFA.evalFrom_of_append`：evalFrom_of_append (start : σ) (x y : List α) : 
M.evalFrom start (x ++ y) = M.evalFrom (M.evalFrom start x) y
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card σ ≤ List.length x) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card σ ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts := by
  obtain ⟨_, a, b, c, hx, hlen, hnil, rfl, hb, hc⟩ := M.evalFrom_split (s := M.start) hlen rfl
  use a, b, c, hx, hlen, hnil
  intro y hy
  rw [Language.mem_mul] at hy
  rcases hy with ⟨ab, hab, c', hc', rfl⟩
  rw [Language.mem_mul] at hab
  rcases hab with ⟨a', ha', b', hb', rfl⟩
  rw [Set.mem_singleton_iff] at ha' hc'
  subst ha' hc'
  have h := M.evalFrom_of_pow hb hb'
  rwa [mem_accepts, eval, evalFrom_of_append, evalFrom_of_append, h, hc]

section Maps

variable {α' σ' : Type*}

/--
`M.comap f` pulls back the alphabet of `M` along `f`. In other words, it applies `f` to the input
before passing it to `M`.
-/
@[simps]
/-
**DFA.comap** 是 Mathlib 中的一个定义，位于命名空间 `DFA`。
形式化陈述：comap (f : α' -> α) (M : DFA α σ) : DFA α' σ where step s a
参数：f : α' -> α；M : DFA α σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.comap f` pulls back the alphabet of `M` along `f`. In other words, it applies
 `f` to the input
before passing it to `M`.
-/
def comap (f : α' → α) (M : DFA α σ) : DFA α' σ where
  step s a := M.step s (f a)
  start := M.start
  accept := M.accept

@[simp]
/-
**DFA.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：comap_id : M.comap id = M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_id : M.comap id = M := rfl

@[simp]
/-
**DFA.evalFrom_comap** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：evalFrom_comap (f : α' -> α) (s : σ) (x : List α') : (M.comap f).evalFrom 
s x = M.evalFrom s (x.map f)
参数：f : α' -> α；s : σ；x : List α'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DFA.evalFrom_append_singleton`：evalFrom_append_singleton (s : σ) (x : Li
st α) (a : α) : M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFA.comap_step`：∀ {α : Type u} {σ : Type v} {α' : Type u_1} (f : α' → α)
 (M : DFA α σ) (s : σ) (a : α'),   (DFA.comap f M).step s a = M.step s (f a)
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
theorem evalFrom_comap (f : α' → α) (s : σ) (x : List α') :
    (M.comap f).evalFrom s x = M.evalFrom s (x.map f) := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih]

@[simp]
/-
**DFA.eval_comap** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：eval_comap (f : α' -> α) (x : List α') : (M.comap f).eval x = M.eval (x.ma
p f)
参数：f : α' -> α；x : List α'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFA.comap_start`：∀ {α : Type u} {σ : Type v} {α' : Type u_1} (f : α' → α
) (M : DFA α σ), (DFA.comap f M).start = M.start
· 使用定理 `DFA.evalFrom_comap`：evalFrom_comap (f : α' -> α) (s : σ) (x : List α') :
 (M.comap f).evalFrom s x = M.evalFrom s (x.map f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_comap (f : α' → α) (x : List α') : (M.comap f).eval x = M.eval (x.map f) := by
  simp [eval]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**DFA.accepts_comap** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：accepts_comap (f : α' -> α) : (M.comap f).accepts = List.map f ⁻¹' M.accep
ts
参数：f : α' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `DFA.mem_accepts`：mem_accepts {x : List α} : x in M.accepts ↔ M.eval x in
 M.accept
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DFA.comap_accept`：∀ {α : Type u} {σ : Type v} {α' : Type u_1} (f : α' → 
α) (M : DFA α σ), (DFA.comap f M).accept = M.accept
· 使用定理 `DFA.eval_comap`：eval_comap (f : α' -> α) (x : List α') : (M.comap f).eva
l x = M.eval (x.map f)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem accepts_comap (f : α' → α) : (M.comap f).accepts = List.map f ⁻¹' M.accepts := by
  ext x
  conv =>
    rhs
    rw [Set.mem_preimage, mem_accepts]
  simp [mem_accepts]

/-- Lifts an equivalence on states to an equivalence on DFAs. -/
@[simps apply_step apply_start apply_accept]
/-
**DFA.reindex** 是 Mathlib 中的一个定义，位于命名空间 `DFA`。
形式化陈述：reindex (g : σ ≃ σ') : DFA α σ ≃ DFA α σ' where toFun M
参数：g : σ ≃ σ'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Lifts an equivalence on states to an equivalence on DFAs.
-/
def reindex (g : σ ≃ σ') : DFA α σ ≃ DFA α σ' where
  toFun M := {
    step := fun s a => g (M.step (g.symm s) a)
    start := g M.start
    accept := g.symm ⁻¹' M.accept
  }
  invFun M := {
    step := fun s a => g.symm (M.step (g s) a)
    start := g.symm M.start
    accept := g ⁻¹' M.accept
  }
  left_inv M := by simp
  right_inv M := by simp

@[simp]
/-
**DFA.reindex_refl** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：reindex_refl : reindex (Equiv.refl σ) M = M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem reindex_refl : reindex (Equiv.refl σ) M = M := rfl

@[simp]
/-
**DFA.symm_reindex** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：symm_reindex (g : σ ≃ σ') : (reindex (α
参数：g : σ ≃ σ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_reindex (g : σ ≃ σ') : (reindex (α := α) g).symm = reindex g.symm := rfl

@[simp]
/-
**DFA.evalFrom_reindex** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：evalFrom_reindex (g : σ ≃ σ') (s : σ') (x : List α) : (reindex g M).evalFr
om s x = g (M.evalFrom (g.symm s) x)
参数：g : σ ≃ σ'；s : σ'；x : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DFA.evalFrom_append_singleton`：evalFrom_append_singleton (s : σ) (x : Li
st α) (a : α) : M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFA.reindex_apply_step`：∀ {α : Type u} {σ : Type v} {σ' : Type u_2} (g :
 σ ≃ σ') (M : DFA α σ) (s : σ') (a : α),   ((DFA.reindex g) M).step s a = g (M.s
tep (g.symm …
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem evalFrom_reindex (g : σ ≃ σ') (s : σ') (x : List α) :
    (reindex g M).evalFrom s x = g (M.evalFrom (g.symm s) x) := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih]

@[simp]
/-
**DFA.eval_reindex** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：eval_reindex (g : σ ≃ σ') (x : List α) : (reindex g M).eval x = g (M.eval 
x)
参数：g : σ ≃ σ'；x : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DFA.reindex_apply_start`：∀ {α : Type u} {σ : Type v} {σ' : Type u_2} (g 
: σ ≃ σ') (M : DFA α σ), ((DFA.reindex g) M).start = g M.start
· 使用定理 `DFA.evalFrom_reindex`：evalFrom_reindex (g : σ ≃ σ') (s : σ') (x : List α
) : (reindex g M).evalFrom s x = g (M.evalFrom (g.symm s) x)
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_reindex (g : σ ≃ σ') (x : List α) : (reindex g M).eval x = g (M.eval x) := by
  simp [eval]

@[simp]
/-
**DFA.accepts_reindex** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：accepts_reindex (g : σ ≃ σ') : (reindex g M).accepts = M.accepts
参数：g : σ ≃ σ'。
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
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DFA.reindex_apply_accept`：∀ {α : Type u} {σ : Type v} {σ' : Type u_2} (g
 : σ ≃ σ') (M : DFA α σ),   ((DFA.reindex g) M).accept = ⇑g.symm ⁻¹' M.accept
· 使用定理 `DFA.eval_reindex`：eval_reindex (g : σ ≃ σ') (x : List α) : (reindex g M)
.eval x = g (M.eval x)
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem accepts_reindex (g : σ ≃ σ') : (reindex g M).accepts = M.accepts := by
  ext x
  simp [mem_accepts]

set_option backward.isDefEq.respectTransparency false in
/-
**DFA.comap_reindex** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：comap_reindex (f : α' -> α) (g : σ ≃ σ') : (reindex g M).comap f = reindex
 g (M.comap f)
参数：f : α' -> α；g : σ ≃ σ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_reindex (f : α' → α) (g : σ ≃ σ') :
    (reindex g M).comap f = reindex g (M.comap f) := by
  simp [comap, reindex]

end Maps

section compl

/-- DFAs are closed under complement:
Given a DFA `M`, `Mᶜ` is also a DFA such that `L(Mᶜ) = {x ∣ x ∉ L(M)}`. -/
/-
**DFA.** 是 Mathlib 中的一个实例，位于命名空间 `DFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
DFAs are closed under complement:
Given a DFA `M`, `Mᶜ` is also a DFA such that `L(Mᶜ) = {x ∣ x ∉ L(M)}`.
-/
instance : Compl (DFA α σ) where
  compl M := ⟨M.step, M.start, M.acceptᶜ⟩
/-
**DFA.compl_def** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：compl_def : Mᶜ = ⟨M.step, M.start, M.acceptᶜ⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl_def : Mᶜ = ⟨M.step, M.start, M.acceptᶜ⟩ :=
  rfl

@[simp]
/-
**DFA.acceptsFrom_compl** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：acceptsFrom_compl (s : σ) : (Mᶜ).acceptsFrom s = (M.acceptsFrom s)ᶜ
参数：s : σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem acceptsFrom_compl (s : σ) : (Mᶜ).acceptsFrom s = (M.acceptsFrom s)ᶜ :=
  rfl

@[simp]
/-
**DFA.accepts_compl** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：accepts_compl : (Mᶜ).accepts = (M.accepts)ᶜ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem accepts_compl : (Mᶜ).accepts = (M.accepts)ᶜ :=
  rfl

end compl

section union

variable {σ1 σ2 : Type v}

/-- DFAs are closed under union. -/
@[simps]
/-
**DFA.union** 是 Mathlib 中的一个定义，位于命名空间 `DFA`。
形式化陈述：union (M1 : DFA α σ1) (M2 : DFA α σ2) : DFA α (σ1 × σ2) where step (s : σ1
 × σ2) (a : α) : σ1 × σ2
参数：M1 : DFA α σ1；M2 : DFA α σ2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
DFAs are closed under union.
-/
def union (M1 : DFA α σ1) (M2 : DFA α σ2) : DFA α (σ1 × σ2) where
  step (s : σ1 × σ2) (a : α) : σ1 × σ2 := (M1.step s.1 a, M2.step s.2 a)
  start := (M1.start, M2.start)
  accept := {s : σ1 × σ2 | s.1 ∈ M1.accept ∨ s.2 ∈ M2.accept}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**DFA.acceptsFrom_union** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：acceptsFrom_union (M1 : DFA α σ1) (M2 : DFA α σ2) (s1 : σ1) (s2 : σ2) : (M
1.union M2).acceptsFrom (s1, s2) = M1.acceptsFrom s1 + M2.acceptsFrom s2
参数：M1 : DFA α σ1；M2 : DFA α σ2；s1 : σ1；s2 : σ2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Language.add_def`：add_def (l m : Language α) : l + m = (l union m : Set 
(List α))
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFA.union_accept`：∀ {α : Type u} {σ1 σ2 : Type v} (M1 : DFA α σ1) (M2 : 
DFA α σ2),   (M1.union M2).accept = {s | s.1 ∈ M1.accept ∨ s.2 ∈ M2.accept}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `DFA.union_step`：∀ {α : Type u} {σ1 σ2 : Type v} (M1 : DFA α σ1) (M2 : DF
A α σ2) (s : σ1 × σ2) (a : α),   (M1.union M2).step s a = (M1.step s.1 a, M2.ste
p s.…
-/
theorem acceptsFrom_union (M1 : DFA α σ1) (M2 : DFA α σ2) (s1 : σ1) (s2 : σ2) :
    (M1.union M2).acceptsFrom (s1, s2) = M1.acceptsFrom s1 + M2.acceptsFrom s2 := by
  ext x
  simp only [acceptsFrom]
  rw [Language.add_def, Set.mem_union]
  simp_rw [↑Set.mem_ofPred]
  induction x generalizing s1 s2 with
  | nil => simp
  | cons a x ih => simp only [evalFrom_cons, union_step, ih]

@[simp]
/-
**DFA.accepts_union** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：accepts_union (M1 : DFA α σ1) (M2 : DFA α σ2) : (M1.union M2).accepts = M1
.accepts + M2.accepts
参数：M1 : DFA α σ1；M2 : DFA α σ2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFA.union_start`：∀ {α : Type u} {σ1 σ2 : Type v} (M1 : DFA α σ1) (M2 : D
FA α σ2), (M1.union M2).start = (M1.start, M2.start)
· 使用定理 `DFA.acceptsFrom_union`：acceptsFrom_union (M1 : DFA α σ1) (M2 : DFA α σ2)
 (s1 : σ1) (s2 : σ2) : (M1.union M2).acceptsFrom (s1, s2) = M1.acceptsFrom s1 + 
M2.acceptsF…
· 使用定理 `add_eq_sup`：add_eq_sup (a b : α) : a + b = a ⊔ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem accepts_union (M1 : DFA α σ1) (M2 : DFA α σ2) :
    (M1.union M2).accepts = M1.accepts + M2.accepts := by
  simp [accepts]

end union

section inter

variable {σ1 σ2 : Type v} (M1 : DFA α σ1) (M2 : DFA α σ2)

/-- DFAs are closed under intersection. -/
@[simps]
/-
**DFA.inter** 是 Mathlib 中的一个定义，位于命名空间 `DFA`。
形式化陈述：inter : DFA α (σ1 × σ2) where step (s : σ1 × σ2) (a : α) : σ1 × σ2
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
DFAs are closed under intersection.
-/
def inter : DFA α (σ1 × σ2) where
  step (s : σ1 × σ2) (a : α) : σ1 × σ2 := (M1.step s.1 a, M2.step s.2 a)
  start := (M1.start, M2.start)
  accept := {s : σ1 × σ2 | s.1 ∈ M1.accept ∧ s.2 ∈ M2.accept}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**DFA.acceptsFrom_inter** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：acceptsFrom_inter (s1 : σ1) (s2 : σ2) : (M1.inter M2).acceptsFrom (s1, s2)
 = M1.acceptsFrom s1 ⊓ M2.acceptsFrom s2
参数：s1 : σ1；s2 : σ2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFA.inter_accept`：∀ {α : Type u} {σ1 σ2 : Type v} (M1 : DFA α σ1) (M2 : 
DFA α σ2),   (M1.inter M2).accept = {s | s.1 ∈ M1.accept ∧ s.2 ∈ M2.accept}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `DFA.inter_step`：∀ {α : Type u} {σ1 σ2 : Type v} (M1 : DFA α σ1) (M2 : DF
A α σ2) (s : σ1 × σ2) (a : α),   (M1.inter M2).step s a = (M1.step s.1 a, M2.ste
p s.…
-/
theorem acceptsFrom_inter (s1 : σ1) (s2 : σ2) :
    (M1.inter M2).acceptsFrom (s1, s2) = M1.acceptsFrom s1 ⊓ M2.acceptsFrom s2 := by
  ext x
  simp only [acceptsFrom, Language.mem_inf]
  simp_rw [↑Set.mem_ofPred]
  induction x generalizing s1 s2 with
  | nil => simp
  | cons a x ih => simp only [evalFrom_cons, inter_step, ih]

@[simp]
/-
**DFA.accepts_inter** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：accepts_inter : (M1.inter M2).accepts = M1.accepts ⊓ M2.accepts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFA.inter_start`：∀ {α : Type u} {σ1 σ2 : Type v} (M1 : DFA α σ1) (M2 : D
FA α σ2), (M1.inter M2).start = (M1.start, M2.start)
· 使用定理 `DFA.acceptsFrom_inter`：acceptsFrom_inter (s1 : σ1) (s2 : σ2) : (M1.inter
 M2).acceptsFrom (s1, s2) = M1.acceptsFrom s1 ⊓ M2.acceptsFrom s2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem accepts_inter : (M1.inter M2).accepts = M1.accepts ⊓ M2.accepts := by
  simp [accepts]

end inter

end DFA

namespace Language

/-- A regular language is a language that is defined by a DFA with finite states. -/
/-
**Language.IsRegular** 是 Mathlib 中的一个定义，位于命名空间 `Language`。
形式化陈述：IsRegular {T : Type u} (L : Language T) : Prop
参数：L : Language T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular language is a language that is defined by a DFA with finite states.
-/
def IsRegular {T : Type u} (L : Language T) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L

/-- Lifts the state type `σ` inside `Language.IsRegular` to a different universe. -/
/-
**Language.isRegular_iff.helper.** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts the state type `σ` inside `Language.IsRegular` to a different universe.
-/
private lemma isRegular_iff.helper.{v'} {T : Type u} {L : Language T}
    (hL : ∃ σ : Type v, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L) :
    ∃ σ' : Type v', ∃ _ : Fintype σ', ∃ M : DFA T σ', M.accepts = L :=
  have ⟨σ, _, M, hM⟩ := hL
  have ⟨σ', ⟨f⟩⟩ := Small.equiv_small.{v', v} (α := σ)
  ⟨σ', Fintype.ofEquiv σ f, M.reindex f, hM ▸ DFA.accepts_reindex M f⟩

/--
A language is regular if and only if it is defined by a DFA with finite states.

This is more general than using the definition of `Language.IsRegular` directly, as the state type
`σ` is universe-polymorphic.
-/
/-
**Language.isRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：isRegular_iff {T : Type u} {L : Language T} : L.IsRegular ↔ exists σ : Typ
e v, exists _ : Fintype σ, exists M : DFA T σ, M.accepts = L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Computability.DFA.0.Language.isRegular_iff.helper`：∀ {T
 : Type u} {L : Language T}, (∃ σ x M, M.accepts = L) → ∃ σ' x M, M.accepts = L

--- 原说明 ---
A language is regular if and only if it is defined by a DFA with finite states.

This is more general than using the definition of `Language.IsRegular` directly,
 as the state type
`σ` is universe-polymorphic.
-/
theorem isRegular_iff {T : Type u} {L : Language T} :
    L.IsRegular ↔ ∃ σ : Type v, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L :=
  ⟨Language.isRegular_iff.helper, Language.isRegular_iff.helper⟩
/-
**Language.IsRegular.compl** 是 Mathlib 中的一个定理，位于命名空间 `Language.IsRegular`。
形式化陈述：∀ {T : Type u} {L : Language T}, L.IsRegular → Lᶜ.IsRegular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem IsRegular.compl {T : Type u} {L : Language T} (h : L.IsRegular) : Lᶜ.IsRegular :=
  have ⟨σ, _, M, hM⟩ := h
  ⟨σ, inferInstance, Mᶜ, by simp [hM]⟩
/-
**Language.IsRegular.of_compl** 是 Mathlib 中的一个定理，位于命名空间 `Language.IsRegular`。
形式化陈述：∀ {T : Type u} {L : Language T}, Lᶜ.IsRegular → L.IsRegular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.IsRegular.compl`：∀ {T : Type u} {L : Language T}, L.IsRegular →
 Lᶜ.IsRegular
· 使用引理 `Language.compl_compl`：compl_compl (l : Language α) : lᶜᶜ = l
-/
protected theorem IsRegular.of_compl {T : Type u} {L : Language T} (h : Lᶜ.IsRegular) :
  L.IsRegular :=
  L.compl_compl ▸ h.compl

/-- Regular languages are closed under complement. -/
@[simp]
/-
**Language.IsRegular_compl** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：IsRegular_compl {T : Type u} {L : Language T} : Lᶜ.IsRegular ↔ L.IsRegular
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.IsRegular.of_compl`：∀ {T : Type u} {L : Language T}, Lᶜ.IsRegul
ar → L.IsRegular
· 使用定理 `Language.IsRegular.compl`：∀ {T : Type u} {L : Language T}, L.IsRegular →
 Lᶜ.IsRegular

--- 原说明 ---
Regular languages are closed under complement.
-/
theorem IsRegular_compl {T : Type u} {L : Language T} : Lᶜ.IsRegular ↔ L.IsRegular :=
  ⟨.of_compl, .compl⟩

/-- Regular languages are closed under union. -/
/-
**Language.IsRegular.add** 是 Mathlib 中的一个定理，位于命名空间 `Language.IsRegular`。
形式化陈述：∀ {T : Type u} {L1 L2 : Language T}, L1.IsRegular → L2.IsRegular → (L1 + L
2).IsRegular
参数：L1 + L2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFA.accepts_union`：accepts_union (M1 : DFA α σ1) (M2 : DFA α σ2) : (M1.u
nion M2).accepts = M1.accepts + M2.accepts
· 使用定理 `add_eq_sup`：add_eq_sup (a b : α) : a + b = a ⊔ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Regular languages are closed under union.
-/
theorem IsRegular.add {T : Type u} {L1 L2 : Language T} (h1 : L1.IsRegular) (h2 : L2.IsRegular) :
    (L1 + L2).IsRegular :=
  have ⟨σ1, _, M1, hM1⟩ := h1
  have ⟨σ2, _, M2, hM2⟩ := h2
  ⟨σ1 × σ2, inferInstance, M1.union M2, by simp [hM1, hM2]⟩

/-- Regular languages are closed under intersection. -/
/-
**Language.IsRegular.inf** 是 Mathlib 中的一个定理，位于命名空间 `Language.IsRegular`。
形式化陈述：∀ {T : Type u} {L1 L2 : Language T}, L1.IsRegular → L2.IsRegular → (L1 ⊓ L
2).IsRegular
参数：L1 ⊓ L2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFA.accepts_inter`：accepts_inter : (M1.inter M2).accepts = M1.accepts ⊓ 
M2.accepts
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Regular languages are closed under intersection.
-/
theorem IsRegular.inf {T : Type u} {L1 L2 : Language T} (h1 : L1.IsRegular) (h2 : L2.IsRegular) :
    (L1 ⊓ L2).IsRegular :=
  have ⟨σ1, _, M1, hM1⟩ := h1
  have ⟨σ2, _, M2, hM2⟩ := h2
  ⟨σ1 × σ2, inferInstance, M1.inter M2, by simp [hM1, hM2]⟩

end Language

