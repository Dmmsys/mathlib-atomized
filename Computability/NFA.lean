/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Maja Kądziołka, Chris Wong, Rudy Peterson
-/
module

public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Powerset

/-!
# Nondeterministic Finite Automata

A Nondeterministic Finite Automaton (NFA) is a state machine which
decides membership in a particular `Language`, by following every
possible path that describes an input string.

We show that DFAs and NFAs can decide the same languages, by constructing
an equivalent DFA for every NFA, and vice versa.

As constructing a DFA from an NFA uses an exponential number of states,
we re-prove the pumping lemma instead of lifting `DFA.pumping_lemma`,
in order to obtain the optimal bound on the minimal length of the string.

Like `DFA`, this definition allows for automata with infinite states;
a `Fintype` instance must be supplied for true NFAs.

## Main definitions

* `NFA α σ`: automaton over alphabet `α` and set of states `σ`
* `NFA.evalFrom M S x`: set of possible ending states for an input word `x`
  and set of initial states `S`
* `NFA.accepts M`: the language accepted by the NFA `M`
* `NFA.Path M s t x`: a specific path from `s` to `t` for an input word `x`
* `NFA.Path.supp p`: set of states visited by the path `p`

## Main theorems

* `NFA.pumping_lemma`: every sufficiently long string accepted by the NFA has a substring that can
  be repeated arbitrarily many times (and have the overall string still be accepted)
-/

@[expose] public section

open Set

open Computability

universe u v

/-- An NFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a set of starting states (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `Set` of states. These are the states that it
  may be sent to. -/
/-
**NFA** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type v → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An NFA is a set of states (`σ`), a transition function from state to state label
led by the
  alphabet (`step`), a set of starting states (`start`) and a set of acceptance 
states (`accept`).
  Note the transition function sends a state to a `Set` of states. These are the
 states that it
  may be sent to.
-/
structure NFA (α : Type u) (σ : Type v) where
  /-- The NFA's transition function -/
  step : σ → α → Set σ
  /-- Set of starting states -/
  start : Set σ
  /-- Set of accepting states -/
  accept : Set σ

variable {α : Type u} {σ : Type v} {M : NFA α σ}

namespace NFA

/-
**NFA.** 是 Mathlib 中的一个实例，位于命名空间 `NFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (NFA α σ) :=
  ⟨NFA.mk (fun _ _ => ∅) ∅ ∅⟩

variable (M) in
/-- `M.stepSet S a` is the union of `M.step s a` for all `s ∈ S`. -/
/-
**NFA.stepSet** 是 Mathlib 中的一个定义，位于命名空间 `NFA`。
形式化陈述：stepSet (S : Set σ) (a : α) : Set σ
参数：S : Set σ；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.stepSet S a` is the union of `M.step s a` for all `s ∈ S`.
-/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.step s a
/-
**NFA.mem_stepSet** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：mem_stepSet {s : σ} {S : Set σ} {a : α} : s in M.stepSet S a ↔ exists t in
 S, s in M.step t a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_stepSet {s : σ} {S : Set σ} {a : α} : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.step t a := by
  simp [stepSet]

variable (M) in
@[simp]
/-
**NFA.stepSet_empty** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：stepSet_empty (a : α) : M.stepSet ∅ a = ∅
参数：a : α。
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
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by simp [stepSet]

variable (M) in
@[simp]
/-
**NFA.stepSet_singleton** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：stepSet_singleton (s : σ) (a : α) : M.stepSet {s} a = M.step s a
参数：s : σ；a : α。
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
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stepSet_singleton (s : σ) (a : α) : M.stepSet {s} a = M.step s a := by
  simp [stepSet]

variable (M) in
@[simp]
/-
**NFA.stepSet_union** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：stepSet_union {S T : Set σ} {a : α} : M.stepSet (S union T) a = M.stepSet 
S a union M.stepSet T a
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem stepSet_union {S T : Set σ} {a : α} :
    M.stepSet (S ∪ T) a = M.stepSet S a ∪ M.stepSet T a := by
  ext s
  simp [mem_stepSet, or_and_right, exists_or]

variable (M) in
/-- `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element
  of `S`. -/
/-
**NFA.evalFrom** 是 Mathlib 中的一个定义，位于命名空间 `NFA`。
形式化陈述：evalFrom (S : Set σ) : List α -> Set σ
参数：S : Set σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.evalFrom S x` computes all possible paths through `M` with input `x` starting
 at an element
  of `S`.
-/
def evalFrom (S : Set σ) : List α → Set σ :=
  List.foldl M.stepSet S

variable (M) in
@[simp]
/-
**NFA.evalFrom_nil** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：evalFrom_nil (S : Set σ) : M.evalFrom S [] = S
参数：S : Set σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = S :=
  rfl

variable (M) in
@[simp]
/-
**NFA.evalFrom_singleton** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet S a
参数：S : Set σ；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet S a :=
  rfl

variable (M) in
@[simp]
/-
**NFA.evalFrom_cons** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：evalFrom_cons (S : Set σ) (a : α) (x : List α) : M.evalFrom S (a :: x) = M
.evalFrom (M.stepSet S a) x
参数：S : Set σ；a : α；x : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalFrom_cons (S : Set σ) (a : α) (x : List α) :
    M.evalFrom S (a :: x) = M.evalFrom (M.stepSet S a) x :=
  rfl

variable (M) in
@[simp]
/-
**NFA.evalFrom_append** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：evalFrom_append (S : Set σ) (x y : List α) : M.evalFrom S (x ++ y) = M.eva
lFrom (M.evalFrom S x) y
参数：S : Set σ；x y : List α。
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
theorem evalFrom_append (S : Set σ) (x y : List α) :
    M.evalFrom S (x ++ y) = M.evalFrom (M.evalFrom S x) y := by
  simp only [evalFrom, List.foldl_append]

variable (M) in
@[simp]
/-
**NFA.evalFrom_union** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：evalFrom_union (S T : Set σ) (x : List α) : M.evalFrom (S union T) x = M.e
valFrom S x union M.evalFrom T x
参数：S T : Set σ；x : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NFA.stepSet_union`：stepSet_union {S T : Set σ} {a : α} : M.stepSet (S un
ion T) a = M.stepSet S a union M.stepSet T a
-/
theorem evalFrom_union (S T : Set σ) (x : List α) :
    M.evalFrom (S ∪ T) x = M.evalFrom S x ∪ M.evalFrom T x := by
  induction x generalizing S T with
  | nil => simp
  | cons a x ih => simp [ih]

variable (M) in
@[simp]
/-
**NFA.evalFrom_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：evalFrom_iUnion {ι : Sort*} (s : ι -> Set σ) (x : List α) : M.evalFrom (⋃ 
i, s i) x = ⋃ i, M.evalFrom (s i) x
参数：s : ι -> Set σ；x : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_comm`：iUnion_comm (s : ι -> ι' -> Set α) : ⋃ (i) (i'), s i i'
 = ⋃ (i') (i), s i i'
-/
theorem evalFrom_iUnion {ι : Sort*} (s : ι → Set σ) (x : List α) :
    M.evalFrom (⋃ i, s i) x = ⋃ i, M.evalFrom (s i) x := by
  induction x generalizing s with
  | nil => simp
  | cons a x ih => simp [stepSet, Set.iUnion_comm (ι := σ) (ι' := ι), ih]

variable (M) in
/-
**NFA.evalFrom_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：evalFrom_iUnion {ι : Sort*} (s : ι -> Set σ) (x : List α) : M.evalFrom (⋃ 
i, s i) x = ⋃ i, M.evalFrom (s i) x
参数：s : ι -> Set σ；x : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_comm`：iUnion_comm (s : ι -> ι' -> Set α) : ⋃ (i) (i'), s i i'
 = ⋃ (i') (i), s i i'
-/
theorem evalFrom_iUnion₂ {ι : Sort*} {κ : ι → Sort*} (f : ∀ i, κ i → Set σ) (x : List α) :
    M.evalFrom (⋃ (i) (j), f i j) x = ⋃ (i) (j), M.evalFrom (f i j) x := by
  simp

variable (M) in
/-
**NFA.evalFrom_eq_biUnion_singleton** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：evalFrom_eq_biUnion_singleton (S : Set σ) (x : List α) : M.evalFrom S x = 
⋃ s in S, M.evalFrom {s} x
参数：S : Set σ；x : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalFrom_eq_biUnion_singleton (S : Set σ) (x : List α) :
    M.evalFrom S x = ⋃ s ∈ S, M.evalFrom {s} x := by
  simp [← evalFrom_iUnion₂]
/-
**NFA.mem_evalFrom_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：mem_evalFrom_iff_exists {s : σ} {S : Set σ} {x : List α} : s in M.evalFrom
 S x ↔ exists t in S, s in M.evalFrom {t} x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NFA.evalFrom_eq_biUnion_singleton`：evalFrom_eq_biUnion_singleton (S : Se
t σ) (x : List α) : M.evalFrom S x = ⋃ s in S, M.evalFrom {s} x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_evalFrom_iff_exists {s : σ} {S : Set σ} {x : List α} :
    s ∈ M.evalFrom S x ↔ ∃ t ∈ S, s ∈ M.evalFrom {t} x := by
  rw [evalFrom_eq_biUnion_singleton]
  simp

variable (M) in
/-- `M.acceptsFrom S` is the language of `x` such that there is an accept state
in `M.evalFrom S x`. -/
/-
**NFA.acceptsFrom** 是 Mathlib 中的一个定义，位于命名空间 `NFA`。
形式化陈述：acceptsFrom (S : Set σ) : Language α
参数：S : Set σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.acceptsFrom S` is the language of `x` such that there is an accept state
in `M.evalFrom S x`.
-/
def acceptsFrom (S : Set σ) : Language α := {x | ∃ s ∈ M.accept, s ∈ M.evalFrom S x}
/-
**NFA.mem_acceptsFrom** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：mem_acceptsFrom {S : Set σ} {x : List α} : x in M.acceptsFrom S ↔ exists s
 in M.accept, s in M.evalFrom S x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_acceptsFrom {S : Set σ} {x : List α} :
    x ∈ M.acceptsFrom S ↔ ∃ s ∈ M.accept, s ∈ M.evalFrom S x := by
  rfl

variable (M) in
@[simp]
/-
**NFA.nil_mem_acceptsFrom** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：nil_mem_acceptsFrom {S : Set σ} : [] in M.acceptsFrom S ↔ exists s in S, s
 in M.accept
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem nil_mem_acceptsFrom {S : Set σ} : [] ∈ M.acceptsFrom S ↔ ∃ s ∈ S, s ∈ M.accept := by
  simp only [mem_acceptsFrom, evalFrom_nil]; tauto

variable (M) in
@[simp]
/-
**NFA.cons_mem_acceptsFrom** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：cons_mem_acceptsFrom {S : Set σ} {a : α} {x : List α} : a :: x in M.accept
sFrom S ↔ x in M.acceptsFrom (M.stepSet S a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cons_mem_acceptsFrom {S : Set σ} {a : α} {x : List α} :
    a :: x ∈ M.acceptsFrom S ↔ x ∈ M.acceptsFrom (M.stepSet S a) := by
  simp [mem_acceptsFrom]

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/-
**NFA.cons_preimage_acceptsFrom** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：cons_preimage_acceptsFrom {S : Set σ} {a : α} : (a :: ·) ⁻¹' M.acceptsFrom
 S = M.acceptsFrom (M.stepSet S a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NFA.cons_mem_acceptsFrom`：cons_mem_acceptsFrom {S : Set σ} {a : α} {x : 
List α} : a :: x in M.acceptsFrom S ↔ x in M.acceptsFrom (M.stepSet S a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cons_preimage_acceptsFrom {S : Set σ} {a : α} :
    (a :: ·) ⁻¹' M.acceptsFrom S = M.acceptsFrom (M.stepSet S a) := by
  ext x; simp [cons_mem_acceptsFrom M]

variable (M) in
@[simp]
/-
**NFA.append_mem_acceptsFrom** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：append_mem_acceptsFrom {S : Set σ} {x y : List α} : x ++ y in M.acceptsFro
m S ↔ y in M.acceptsFrom (M.evalFrom S x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `NFA.evalFrom_append`：evalFrom_append (S : Set σ) (x y : List α) : M.eval
From S (x ++ y) = M.evalFrom (M.evalFrom S x) y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem append_mem_acceptsFrom {S : Set σ} {x y : List α} :
    x ++ y ∈ M.acceptsFrom S ↔ y ∈ M.acceptsFrom (M.evalFrom S x) := by
  simp [mem_acceptsFrom]

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/-
**NFA.append_preimage_acceptsFrom** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：append_preimage_acceptsFrom {S : Set σ} {x : List α} : (x ++ ·) ⁻¹' M.acce
ptsFrom S = M.acceptsFrom (M.evalFrom S x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NFA.append_mem_acceptsFrom`：append_mem_acceptsFrom {S : Set σ} {x y : Li
st α} : x ++ y in M.acceptsFrom S ↔ y in M.acceptsFrom (M.evalFrom S x)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem append_preimage_acceptsFrom {S : Set σ} {x : List α} :
    (x ++ ·) ⁻¹' M.acceptsFrom S = M.acceptsFrom (M.evalFrom S x) := by
  ext y; simp [append_mem_acceptsFrom M]

variable (M) in
@[simp]
/-
**NFA.acceptsFrom_union** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：acceptsFrom_union {S T : Set σ} : M.acceptsFrom (S union T) = M.acceptsFro
m S + M.acceptsFrom T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Language.add_def`：add_def (l m : Language α) : l + m = (l union m : Set 
(List α))
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NFA.evalFrom_union`：evalFrom_union (S T : Set σ) (x : List α) : M.evalFr
om (S union T) x = M.evalFrom S x union M.evalFrom T x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
theorem acceptsFrom_union {S T : Set σ} :
    M.acceptsFrom (S ∪ T) = M.acceptsFrom S + M.acceptsFrom T := by
  rw [Language.add_def]; ext x
  simp only [mem_acceptsFrom, evalFrom_union, mem_union]
  constructor
  · rintro ⟨s, hs, h | h⟩
    · left; tauto
    · right; tauto
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩) <;> exists s <;> tauto

set_option backward.isDefEq.respectTransparency false in
variable (M) in
@[simp]
/-
**NFA.acceptsFrom_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：acceptsFrom_iUnion {ι : Sort*} (s : ι -> Set σ) : M.acceptsFrom (⋃ i, s i)
 = ⋃ i, M.acceptsFrom (s i)
参数：s : ι -> Set σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NFA.evalFrom_iUnion`：evalFrom_iUnion {ι : Sort*} (s : ι -> Set σ) (x : L
ist α) : M.evalFrom (⋃ i, s i) x = ⋃ i, M.evalFrom (s i) x
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
-/
theorem acceptsFrom_iUnion {ι : Sort*} (s : ι → Set σ) :
    M.acceptsFrom (⋃ i, s i) = ⋃ i, M.acceptsFrom (s i) := by
  ext x
  simp only [acceptsFrom, evalFrom_iUnion, mem_iUnion]
  simp_rw [↑mem_iUnion, ↑mem_ofPred_eq]; tauto

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/-
**NFA.acceptsFrom_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：acceptsFrom_iUnion {ι : Sort*} (s : ι -> Set σ) : M.acceptsFrom (⋃ i, s i)
 = ⋃ i, M.acceptsFrom (s i)
参数：s : ι -> Set σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NFA.evalFrom_iUnion`：evalFrom_iUnion {ι : Sort*} (s : ι -> Set σ) (x : L
ist α) : M.evalFrom (⋃ i, s i) x = ⋃ i, M.evalFrom (s i) x
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
-/
theorem acceptsFrom_iUnion₂ {ι : Sort*} {κ : ι → Sort*} (f : ∀ i, κ i → Set σ) :
    M.acceptsFrom (⋃ (i) (j), f i j) = ⋃ (i) (j), M.acceptsFrom (f i j) := by
  simp

variable (M) in
@[simp]
/-
**NFA.mem_acceptsFrom_sep_fact** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mem_acceptsFrom_sep_fact {S : Set σ} {p : Prop} {x : List α} :
    x ∈ M.acceptsFrom {s ∈ S | p} ↔ x ∈ M.acceptsFrom S ∧ p := by
  induction x generalizing S with
  | nil => simp only [nil_mem_acceptsFrom, mem_ofPred_eq]; tauto
  | cons a x ih =>
    have h : M.stepSet {s ∈ S | p} a = {s ∈ M.stepSet S a | p} := by
      ext s; simp only [stepSet, mem_ofPred_eq, mem_iUnion, exists_prop]; tauto
    simp [h, ih]

variable (M) in
/-- `M.eval x` computes all possible paths though `M` with input `x` starting at an element of
  `M.start`. -/
/-
**NFA.eval** 是 Mathlib 中的一个定义，位于命名空间 `NFA`。
形式化陈述：eval : List α -> Set σ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.eval x` computes all possible paths though `M` with input `x` starting at an 
element of
  `M.start`.
-/
def eval : List α → Set σ :=
  M.evalFrom M.start

variable (M) in
@[simp]
/-
**NFA.eval_nil** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：eval_nil : M.eval [] = M.start
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_nil : M.eval [] = M.start :=
  rfl

variable (M) in
@[simp]
/-
**NFA.eval_singleton** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：eval_singleton (a : α) : M.eval [a] = M.stepSet M.start a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet M.start a :=
  rfl

variable (M) in
@[simp]
/-
**NFA.eval_append_singleton** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet
 (M.eval x) a
参数：x : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NFA.evalFrom_append`：evalFrom_append (S : Set σ) (x y : List α) : M.eval
From S (x ++ y) = M.evalFrom (M.evalFrom S x) y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_append_singleton (x : List α) (a : α) :
    M.eval (x ++ [a]) = M.stepSet (M.eval x) a := by
  simp [eval]

variable (M) in
/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
/-
**NFA.accepts** 是 Mathlib 中的一个定义，位于命名空间 `NFA`。
形式化陈述：accepts : Language α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.accepts` is the language of `x` such that there is an accept state in `M.eval
 x`.
-/
def accepts : Language α := {x | ∃ S ∈ M.accept, S ∈ M.eval x}
/-
**NFA.mem_accepts** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：mem_accepts {x : List α} : x in M.accepts ↔ exists S in M.accept, S in M.e
valFrom M.start x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ ∃ S ∈ M.accept, S ∈ M.evalFrom M.start x := by
  rfl
/-
**NFA.accepts_eq_acceptsFrom_start** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：accepts_eq_acceptsFrom_start : M.accepts = M.acceptsFrom M.start
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem accepts_eq_acceptsFrom_start : M.accepts = M.acceptsFrom M.start := rfl

variable (M) in
/-- `M.Path` represents a concrete path through the NFA from a start state to an end state
for a particular word.

Note that due to the non-deterministic nature of the automata, there can be more than one `Path`
for a given word.

Also note that this is `Type` and not a `Prop`, so that we can speak about the properties
of a particular `Path`, such as the set of states visited along the way (defined as `Path.supp`). -/
/-
**NFA.Path** 是 Mathlib 中的一个归纳类型，位于命名空间 `NFA`。
形式化陈述：{α : Type u} → {σ : Type v} → NFA α σ → σ → σ → List α → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.Path` represents a concrete path through the NFA from a start state to an end
 state
for a particular word.

Note that due to the non-deterministic nature of the automata, there can be more
 than one `Path`
for a given word.

Also note that this is `Type` and not a `Prop`, so that we can speak about the p
roperties
of a particular `Path`, such as the set of states visited along the way (defined
 as `Path.supp`).
-/
inductive Path : σ → σ → List α → Type (max u v)
  | nil (s : σ) : Path s s []
  | cons (t s u : σ) (a : α) (x : List α) :
      t ∈ M.step s a → Path t u x → Path s u (a :: x)

/-- Set of states visited by a path. -/
@[simp]
/-
**NFA.Path.supp** 是 Mathlib 中的一个定义，位于命名空间 `NFA.Path`。
形式化陈述：{α : Type u} → {σ : Type v} → {M : NFA α σ} → [DecidableEq σ] → {s t : σ} 
→ {x : List α} → M.Path s t x → Finset σ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Set of states visited by a path.
-/
def Path.supp [DecidableEq σ] {s t : σ} {x : List α} : M.Path s t x → Finset σ
  | nil s => {s}
  | cons _ _ _ _ _ _ p => {s} ∪ p.supp
/-
**NFA.mem_evalFrom_iff_nonempty_path** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：mem_evalFrom_iff_nonempty_path {s t : σ} {x : List α} : t in M.evalFrom {s
} x ↔ Nonempty (M.Path s t x) where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_evalFrom_iff_nonempty_path {s t : σ} {x : List α} :
    t ∈ M.evalFrom {s} x ↔ Nonempty (M.Path s t x) where
  mp h := match x with
    | [] =>
      have h : s = t := by simp at h; tauto
      ⟨h ▸ Path.nil s⟩
    | a :: x =>
      have h : ∃ s' ∈ M.step s a, t ∈ M.evalFrom {s'} x := by
        rw [evalFrom_cons, mem_evalFrom_iff_exists, stepSet_singleton] at h; exact h
      let ⟨s', h₁, h₂⟩ := h
      let ⟨p'⟩ := mem_evalFrom_iff_nonempty_path.1 h₂
      ⟨Path.cons s' _ _ _ _ h₁ p'⟩
  mpr p := match p with
    | ⟨Path.nil s⟩ => by simp
    | ⟨Path.cons s' s t a x h₁ h₂⟩ => by
      rw [evalFrom_cons, stepSet_singleton, mem_evalFrom_iff_exists]
      exact ⟨s', h₁, mem_evalFrom_iff_nonempty_path.2 ⟨h₂⟩⟩
/-
**NFA.accepts_iff_exists_path** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：accepts_iff_exists_path {x : List α} : x in M.accepts ↔ exists s in M.star
t, exists t in M.accept, Nonempty (M.Path s t x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NFA.mem_evalFrom_iff_exists`：mem_evalFrom_iff_exists {s : σ} {S : Set σ}
 {x : List α} : s in M.evalFrom S x ↔ exists t in S, s in M.evalFrom {t} x
-/
theorem accepts_iff_exists_path {x : List α} :
    x ∈ M.accepts ↔ ∃ s ∈ M.start, ∃ t ∈ M.accept, Nonempty (M.Path s t x) := by
  simp only [← mem_evalFrom_iff_nonempty_path, mem_accepts, mem_evalFrom_iff_exists (S := M.start)]
  tauto

variable (M) in
/-- `M.toDFA` is a `DFA` constructed from an `NFA` `M` using the subset construction. The
  states is the type of `Set`s of `M.state` and the step function is `M.stepSet`. -/
/-
**NFA.toDFA** 是 Mathlib 中的一个定义，位于命名空间 `NFA`。
形式化陈述：toDFA : DFA α (Set σ) where step
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.toDFA` is a `DFA` constructed from an `NFA` `M` using the subset construction
. The
  states is the type of `Set`s of `M.state` and the step function is `M.stepSet`
.
-/
def toDFA : DFA α (Set σ) where
  step := M.stepSet
  start := M.start
  accept := { S | ∃ s ∈ S, s ∈ M.accept }

@[simp]
/-
**NFA.toDFA_correct** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：toDFA_correct : M.toDFA.accepts = M.accepts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NFA.mem_accepts`：mem_accepts {x : List α} : x in M.accepts ↔ exists S in
 M.accept, S in M.evalFrom M.start x
· 使用定理 `DFA.mem_accepts`：mem_accepts {x : List α} : x in M.accepts ↔ M.eval x in
 M.accept
-/
theorem toDFA_correct : M.toDFA.accepts = M.accepts := by
  ext x
  rw [mem_accepts, DFA.mem_accepts]
  constructor <;> · exact fun ⟨w, h2, h3⟩ => ⟨w, h3, h2⟩
/-
**NFA.pumping_lemma** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：pumping_lemma [Fintype σ] {x : List α} (hx : x in M.accepts) (hlen : Finty
pe.card (Set σ) <= List.length x) : exists a b c, x = a ++ b ++ c ∧ a.length + b
.length <= Fintype.card (Set σ) ∧ b != [] ∧ {a} * {b}∗ * {c} <= M.accepts
参数：hx : x in M.accepts；hlen : Fintype.card (Set σ) <= List.length x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NFA.toDFA_correct`：toDFA_correct : M.toDFA.accepts = M.accepts
· 使用定理 `DFA.pumping_lemma`：pumping_lemma [Fintype σ] {x : List α} (hx : x in M.a
ccepts) (hlen : Fintype.card σ <= List.length x) : exists a b c, x = a ++ b ++ c
 ∧ a.le…
-/
theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card (Set σ) ≤ List.length x) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts := by
  rw [← toDFA_correct] at hx ⊢
  exact M.toDFA.pumping_lemma hx hlen

end NFA

namespace DFA

/-- `M.toNFA` is an `NFA` constructed from a `DFA` `M` by using the same start and accept
  states and a transition function which sends `s` with input `a` to the singleton `M.step s a`. -/
/-
**DFA.toNFA** 是 Mathlib 中的一个定义，位于命名空间 `DFA`。
形式化陈述：{α : Type u} → {σ : Type v} → DFA α σ → NFA α σ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.toNFA` is an `NFA` constructed from a `DFA` `M` by using the same start and a
ccept
  states and a transition function which sends `s` with input `a` to the singlet
on `M.step s a`.
-/
@[simps] def toNFA (M : DFA α σ) : NFA α σ where
  step s a := {M.step s a}
  start := {M.start}
  accept := M.accept

@[simp]
/-
**DFA.toNFA_evalFrom_match** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：toNFA_evalFrom_match (M : DFA α σ) (start : σ) (s : List α) : M.toNFA.eval
From {start} s = {M.evalFrom start s}
参数：M : DFA α σ；start : σ；s : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldl.eq_2`：∀ {α : Type u} {β : Type v} (f : α → β → α) (x : α) (b 
: β) (l : List β),   List.foldl f x (b :: l) = List.foldl f (f x b) l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `DFA.toNFA_step`：∀ {α : Type u} {σ : Type v} (M : DFA α σ) (s : σ) (a : α
), M.toNFA.step s a = {M.step s a}
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNFA_evalFrom_match (M : DFA α σ) (start : σ) (s : List α) :
    M.toNFA.evalFrom {start} s = {M.evalFrom start s} := by
  change List.foldl M.toNFA.stepSet {start} s = {List.foldl M.step start s}
  induction s generalizing start with
  | nil => tauto
  | cons a s ih =>
    rw [List.foldl, List.foldl,
      show M.toNFA.stepSet {start} a = {M.step start a} by simp [NFA.stepSet]]
    tauto

@[simp]
/-
**DFA.toNFA_correct** 是 Mathlib 中的一个定理，位于命名空间 `DFA`。
形式化陈述：toNFA_correct (M : DFA α σ) : M.toNFA.accepts = M.accepts
参数：M : DFA α σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NFA.mem_accepts`：mem_accepts {x : List α} : x in M.accepts ↔ exists S in
 M.accept, S in M.evalFrom M.start x
· 使用定理 `DFA.toNFA_start`：∀ {α : Type u} {σ : Type v} (M : DFA α σ), M.toNFA.star
t = {M.start}
· 使用定理 `DFA.toNFA_evalFrom_match`：toNFA_evalFrom_match (M : DFA α σ) (start : σ)
 (s : List α) : M.toNFA.evalFrom {start} s = {M.evalFrom start s}
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem toNFA_correct (M : DFA α σ) : M.toNFA.accepts = M.accepts := by
  ext x
  rw [NFA.mem_accepts, toNFA_start, toNFA_evalFrom_match]
  constructor
  · rintro ⟨S, hS₁, hS₂⟩
    rwa [Set.mem_singleton_iff.mp hS₂] at hS₁
  · exact fun h => ⟨M.eval x, h, rfl⟩

end DFA

namespace NFA

variable (M) in
/-- `M.reverse` constructs an NFA with the same states as `M`, but all the transitions reversed. The
resulting automaton accepts a word `x` if and only if `M` accepts `List.reverse x`. -/
@[simps]
/-
**NFA.reverse** 是 Mathlib 中的一个定义，位于命名空间 `NFA`。
形式化陈述：reverse : NFA α σ where step s a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.reverse` constructs an NFA with the same states as `M`, but all the transitio
ns reversed. The
resulting automaton accepts a word `x` if and only if `M` accepts `List.reverse 
x`.
-/
def reverse : NFA α σ where
  step s a := { s' | s ∈ M.step s' a }
  start := M.accept
  accept := M.start

variable (M) in
@[simp]
/-
**NFA.reverse_reverse** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：reverse_reverse : M.reverse.reverse = M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reverse_reverse : M.reverse.reverse = M := by
  simp [reverse]
/-
**NFA.disjoint_stepSet_reverse** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：disjoint_stepSet_reverse {a : α} {S S' : Set σ} : Disjoint S (M.reverse.st
epSet S' a) ↔ Disjoint S' (M.stepSet S a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NFA.reverse_step`：∀ {α : Type u} {σ : Type v} (M : NFA α σ) (s : σ) (a :
 α), M.reverse.step s a = {s' | s ∈ M.step s' a}
-/
theorem disjoint_stepSet_reverse {a : α} {S S' : Set σ} :
    Disjoint S (M.reverse.stepSet S' a) ↔ Disjoint S' (M.stepSet S a) := by
  rw [← not_iff_not]
  simp only [Set.not_disjoint_iff, mem_stepSet, reverse_step, Set.mem_ofPred_eq]
  tauto
/-
**NFA.disjoint_evalFrom_reverse** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：disjoint_evalFrom_reverse {x : List α} {S S' : Set σ} (h : Disjoint S (M.r
everse.evalFrom S' x)) : Disjoint S' (M.evalFrom S x.reverse)
参数：h : Disjoint S (M.reverse.evalFrom S' x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldl_reverse`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {f : β 
→ α → β} {b : β},   List.foldl f b l.reverse = List.foldr (fun x y => f y x) b l
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `List.foldr_cons`：∀ {α : Type u} {β : Type v} {a : α} {l : List α} {f : α
 → β → β} {b : β},   List.foldr f b (a :: l) = f a (List.foldr f b l)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NFA.disjoint_stepSet_reverse`：disjoint_stepSet_reverse {a : α} {S S' : S
et σ} : Disjoint S (M.reverse.stepSet S' a) ↔ Disjoint S' (M.stepSet S a)
· 使用定理 `List.foldl_cons`：∀ {α : Type u} {β : Type v} {a : α} {l : List α} {f : β
 → α → β} {b : β},   List.foldl f b (a :: l) = List.foldl f (f b a) l
-/
theorem disjoint_evalFrom_reverse {x : List α} {S S' : Set σ}
    (h : Disjoint S (M.reverse.evalFrom S' x)) : Disjoint S' (M.evalFrom S x.reverse) := by
  simp only [evalFrom, List.foldl_reverse] at h ⊢
  induction x generalizing S S' with
  | nil =>
    rw [disjoint_comm]
    exact h
  | cons x xs ih =>
    rw [List.foldl_cons] at h
    rw [List.foldr_cons, ← NFA.disjoint_stepSet_reverse, disjoint_comm]
    exact ih h
/-
**NFA.disjoint_evalFrom_reverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：disjoint_evalFrom_reverse_iff {x : List α} {S S' : Set σ} : Disjoint S (M.
reverse.evalFrom S' x) ↔ Disjoint S' (M.evalFrom S x.reverse)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NFA.disjoint_evalFrom_reverse`：disjoint_evalFrom_reverse {x : List α} {S
 S' : Set σ} (h : Disjoint S (M.reverse.evalFrom S' x)) : Disjoint S' (M.evalFro
m S x.reverse)
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
-/
theorem disjoint_evalFrom_reverse_iff {x : List α} {S S' : Set σ} :
    Disjoint S (M.reverse.evalFrom S' x) ↔ Disjoint S' (M.evalFrom S x.reverse) :=
  ⟨disjoint_evalFrom_reverse, fun h ↦ List.reverse_reverse x ▸ disjoint_evalFrom_reverse h⟩

@[simp]
/-
**NFA.mem_accepts_reverse** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
形式化陈述：mem_accepts_reverse {x : List α} : x in M.reverse.accepts ↔ x.reverse in M
.accepts
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `NFA.reverse_accept`：∀ {α : Type u} {σ : Type v} (M : NFA α σ), M.reverse
.accept = M.start
· 使用定理 `NFA.reverse_start`：∀ {α : Type u} {σ : Type v} (M : NFA α σ), M.reverse.
start = M.accept
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_accepts_reverse {x : List α} : x ∈ M.reverse.accepts ↔ x.reverse ∈ M.accepts := by
  simp [mem_accepts, ← Set.not_disjoint_iff, disjoint_evalFrom_reverse_iff]

end NFA

namespace Language

/-
**Language.IsRegular.reverse** 是 Mathlib 中的一个定理，位于命名空间 `Language.IsRegular`。
形式化陈述：∀ {α : Type u} {L : Language α}, L.IsRegular → L.reverse.IsRegular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NFA.toDFA_correct`：toDFA_correct : M.toDFA.accepts = M.accepts
· 使用定理 `DFA.toNFA_correct`：toNFA_correct (M : DFA α σ) : M.toNFA.accepts = M.acc
epts
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem IsRegular.reverse {L : Language α} (h : L.IsRegular) : L.reverse.IsRegular :=
  have ⟨σ, _, M, hM⟩ := h
  ⟨_, inferInstance, M.toNFA.reverse.toDFA, by ext; simp [hM]⟩
/-
**Language.IsRegular.of_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Language.IsRegular`。
形式化陈述：∀ {α : Type u} {L : Language α}, L.reverse.IsRegular → L.IsRegular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.IsRegular.reverse`：∀ {α : Type u} {L : Language α}, L.IsRegular
 → L.reverse.IsRegular
· 使用引理 `Language.reverse_reverse`：reverse_reverse (l : Language α) : l.reverse.r
everse = l
-/
protected theorem IsRegular.of_reverse {L : Language α} (h : L.reverse.IsRegular) : L.IsRegular :=
  L.reverse_reverse ▸ h.reverse

/-- Regular languages are closed under reversal. -/
@[simp]
/-
**Language.isRegular_reverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：isRegular_reverse_iff {L : Language α} : L.reverse.IsRegular ↔ L.IsRegular
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.IsRegular.of_reverse`：∀ {α : Type u} {L : Language α}, L.revers
e.IsRegular → L.IsRegular
· 使用定理 `Language.IsRegular.reverse`：∀ {α : Type u} {L : Language α}, L.IsRegular
 → L.reverse.IsRegular

--- 原说明 ---
Regular languages are closed under reversal.
-/
theorem isRegular_reverse_iff {L : Language α} : L.reverse.IsRegular ↔ L.IsRegular :=
  ⟨.of_reverse, .reverse⟩

end Language

