/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Pim Spelier, Daan van Gent
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.PFun
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Defs

/-!
# State Transition Systems

This file contains simple definitions and lemmas for reasoning about state transition systems
defined by a function `σ → Option σ`, where `σ` is the type of states.
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Relation

namespace StateTransition

/-- Run a state transition function `σ → Option σ` "to completion". The return value is the last
state returned before a `none` result. If the state transition function always returns `some`,
then the computation diverges, returning `Part.none`. -/
/-
**StateTransition.eval** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：eval {σ} (f : σ -> Option σ) : σ -> Part σ
参数：f : σ -> Option σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Run a state transition function `σ → Option σ` "to completion". The return value
 is the last
state returned before a `none` result. If the state transition function always r
eturns `some`,
then the computation diverges, returning `Part.none`.
-/
def eval {σ} (f : σ → Option σ) : σ → Part σ :=
  PFun.fix fun s ↦ Part.some <| (f s).elim (Sum.inl s) Sum.inr

/-- The reflexive transitive closure of a state transition function. `Reaches f a b` means
there is a finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`.
This relation permits zero steps of the state transition function. -/
/-
**StateTransition.Reaches** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：Reaches {σ} (f : σ -> Option σ) : σ -> σ -> Prop
参数：f : σ -> Option σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reflexive transitive closure of a state transition function. `Reaches f a b`
 means
there is a finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such 
that `aₙ = b`.
This relation permits zero steps of the state transition function.
-/
def Reaches {σ} (f : σ → Option σ) : σ → σ → Prop :=
  ReflTransGen fun a b ↦ b ∈ f a

/-- The transitive closure of a state transition function. `Reaches₁ f a b` means there is a
nonempty finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`.
This relation does not permit zero steps of the state transition function. -/
/-
**StateTransition.Reaches** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：Reaches {σ} (f : σ -> Option σ) : σ -> σ -> Prop
参数：f : σ -> Option σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transitive closure of a state transition function. `Reaches₁ f a b` means th
ere is a
nonempty finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such th
at `aₙ = b`.
This relation does not permit zero steps of the state transition function.
-/
def Reaches₁ {σ} (f : σ → Option σ) : σ → σ → Prop :=
  TransGen fun a b ↦ b ∈ f a
/-
**StateTransition.reaches** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reaches₁_eq {σ} {f : σ → Option σ} {a b c} (h : f a = f b) :
    Reaches₁ f a c ↔ Reaches₁ f b c :=
  TransGen.head'_iff.trans (TransGen.head'_iff.trans <| by rw [h]).symm
/-
**StateTransition.reaches_total** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：reaches_total {σ} {f : σ -> Option σ} {a b c} (hab : Reaches f a b) (hac :
 Reaches f a c) : Reaches f b c ∨ Reaches f c b
参数：hab : Reaches f a b；hac : Reaches f a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.total_of_right_unique`：total_of_right_unique (U : 
Relator.RightUnique r) (ab : ReflTransGen r a b) (ac : ReflTransGen r a c) : Ref
lTransGen r b c ∨ ReflTransGen r …
· 使用定理 `Option.mem_unique`：∀ {α : Type u_1} {o : Option α} {a b : α}, a ∈ o → b 
∈ o → a = b
-/
theorem reaches_total {σ} {f : σ → Option σ} {a b c} (hab : Reaches f a b) (hac : Reaches f a c) :
    Reaches f b c ∨ Reaches f c b :=
  ReflTransGen.total_of_right_unique (fun _ _ _ ↦ Option.mem_unique) hab hac
/-
**StateTransition.reaches** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reaches₁_fwd {σ} {f : σ → Option σ} {a b c} (h₁ : Reaches₁ f a c) (h₂ : b ∈ f a) :
    Reaches f b c := by
  rcases TransGen.head'_iff.1 h₁ with ⟨b', hab, hbc⟩
  cases Option.mem_unique hab h₂; exact hbc

/-- A variation on `Reaches`. `Reaches₀ f a b` holds if whenever `Reaches₁ f b c` then
`Reaches₁ f a c`. This is a weaker property than `Reaches` and is useful for replacing states with
equivalent states without taking a step. -/
/-
**StateTransition.Reaches** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：Reaches {σ} (f : σ -> Option σ) : σ -> σ -> Prop
参数：f : σ -> Option σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variation on `Reaches`. `Reaches₀ f a b` holds if whenever `Reaches₁ f b c` th
en
`Reaches₁ f a c`. This is a weaker property than `Reaches` and is useful for rep
lacing states with
equivalent states without taking a step.
-/
def Reaches₀ {σ} (f : σ → Option σ) (a b : σ) : Prop :=
  ∀ c, Reaches₁ f b c → Reaches₁ f a c
/-
**StateTransition.Reaches** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：Reaches {σ} (f : σ -> Option σ) : σ -> σ -> Prop
参数：f : σ -> Option σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Reaches₀.trans {σ} {f : σ → Option σ} {a b c : σ} (h₁ : Reaches₀ f a b)
    (h₂ : Reaches₀ f b c) : Reaches₀ f a c
  | _, h₃ => h₁ _ (h₂ _ h₃)

@[refl]
/-
**StateTransition.Reaches** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：Reaches {σ} (f : σ -> Option σ) : σ -> σ -> Prop
参数：f : σ -> Option σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Reaches₀.refl {σ} {f : σ → Option σ} (a : σ) : Reaches₀ f a a
  | _, h => h
/-
**StateTransition.Reaches** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：Reaches {σ} (f : σ -> Option σ) : σ -> σ -> Prop
参数：f : σ -> Option σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Reaches₀.single {σ} {f : σ → Option σ} {a b : σ} (h : b ∈ f a) : Reaches₀ f a b
  | _, h₂ => h₂.head h
/-
**StateTransition.Reaches** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：Reaches {σ} (f : σ -> Option σ) : σ -> σ -> Prop
参数：f : σ -> Option σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Reaches₀.head {σ} {f : σ → Option σ} {a b c : σ} (h : b ∈ f a) (h₂ : Reaches₀ f b c) :
    Reaches₀ f a c :=
  (Reaches₀.single h).trans h₂
/-
**StateTransition.Reaches** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：Reaches {σ} (f : σ -> Option σ) : σ -> σ -> Prop
参数：f : σ -> Option σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Reaches₀.tail {σ} {f : σ → Option σ} {a b c : σ} (h₁ : Reaches₀ f a b) (h : c ∈ f b) :
    Reaches₀ f a c :=
  h₁.trans (Reaches₀.single h)
/-
**StateTransition.reaches** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reaches₀_eq {σ} {f : σ → Option σ} {a b} (e : f a = f b) : Reaches₀ f a b
  | _, h => (reaches₁_eq e).2 h
/-
**StateTransition.Reaches** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：Reaches {σ} (f : σ -> Option σ) : σ -> σ -> Prop
参数：f : σ -> Option σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Reaches₁.to₀ {σ} {f : σ → Option σ} {a b : σ} (h : Reaches₁ f a b) : Reaches₀ f a b
  | _, h₂ => h.trans h₂
/-
**StateTransition.Reaches.to** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Reaches.to₀ {σ} {f : σ → Option σ} {a b : σ} (h : Reaches f a b) : Reaches₀ f a b
  | _, h₂ => h₂.trans_right h
/-
**StateTransition.Reaches** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：Reaches {σ} (f : σ -> Option σ) : σ -> σ -> Prop
参数：f : σ -> Option σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Reaches₀.tail' {σ} {f : σ → Option σ} {a b c : σ} (h : Reaches₀ f a b) (h₂ : c ∈ f b) :
    Reaches₁ f a c :=
  h _ (TransGen.single h₂)

/-- (co-)Induction principle for `eval`. If a property `C` holds of any point `a` evaluating to `b`
which is either terminal (meaning `a = b`) or where the next point also satisfies `C`, then it
holds of any point where `eval f a` evaluates to `b`. This formalizes the notion that if
`eval f a` evaluates to `b` then it reaches terminal state `b` in finitely many steps. -/
@[elab_as_elim]
/-
**StateTransition.evalInduction** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：evalInduction {σ} {f : σ -> Option σ} {b : σ} {C : σ -> Sort*} {a : σ} (h 
: b in eval f a) (H : forall a, b in eval f a -> (forall a', f a = some a' -> C 
a') -> C a) : C a
参数：h : b in eval f a；H : forall a, b in eval f a -> (forall a', f a = some a' ->
 C a') -> C a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(co-)Induction principle for `eval`. If a property `C` holds of any point `a` ev
aluating to `b`
which is either terminal (meaning `a = b`) or where the next point also satisfie
s `C`, then it
holds of any point where `eval f a` evaluates to `b`. This formalizes the notion
 that if
`eval f a` evaluates to `b` then it reaches terminal state `b` in finitely many 
steps.
-/
def evalInduction {σ} {f : σ → Option σ} {b : σ} {C : σ → Sort*} {a : σ}
    (h : b ∈ eval f a) (H : ∀ a, b ∈ eval f a → (∀ a', f a = some a' → C a') → C a) : C a :=
  PFun.fixInduction h fun a' ha' h' ↦
    H _ ha' fun b' e ↦ h' _ <| Part.mem_some_iff.2 <| by rw [e]; rfl
/-
**StateTransition.mem_eval** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：mem_eval {σ} {f : σ -> Option σ} {a b} : b in eval f a ↔ Reaches f a b ∧ f
 b = none
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PFun.mem_fix_iff`：mem_fix_iff {f : α ->. β oplus α} {a : α} {b : β} : b 
in f.fix a ↔ Sum.inl b in f a ∨ exists a', Sum.inr a' in f a ∧ b in f.fix a'
· 使用定理 `Part.mem_some_iff`：mem_some_iff {a b} : b in (some a : Part α) ↔ b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Relation.ReflTransGen.head`：head (hab : r a b) (hbc : ReflTransGen r b c
) : ReflTransGen r a c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Relation.ReflTransGen.head_induction_on`：head_induction_on {motive : for
all a : α, ReflTransGen r a b -> Prop} {a : α} (h : ReflTransGen r a b) (refl : 
motive b refl) (head : forall…
· 使用定理 `Part.mem_some`：mem_some (a : α) : a in some a
-/
theorem mem_eval {σ} {f : σ → Option σ} {a b} : b ∈ eval f a ↔ Reaches f a b ∧ f b = none := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · refine evalInduction h fun a h IH ↦ ?_
    rcases e : f a with - | a'
    · rw [Part.mem_unique h
          (PFun.mem_fix_iff.2 <| Or.inl <| Part.mem_some_iff.2 <| by rw [e]; rfl)]
      exact ⟨ReflTransGen.refl, e⟩
    · rcases PFun.mem_fix_iff.1 h with (h | ⟨_, h, _⟩) <;> rw [e] at h <;>
        cases Part.mem_some_iff.1 h
      obtain ⟨h₁, h₂⟩ := IH a' e
      exact ⟨ReflTransGen.head e h₁, h₂⟩
  · refine ReflTransGen.head_induction_on h₁ ?_ fun h _ IH ↦ ?_
    · refine PFun.mem_fix_iff.2 (Or.inl ?_)
      rw [h₂]
      apply Part.mem_some
    · refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, IH⟩)
      rw [h]
      apply Part.mem_some
/-
**StateTransition.eval_maximal** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：eval_maximal {σ} {f : σ -> Option σ} {a b} (h : b in eval f a) {c} : Reach
es f b c ↔ c = b
参数：h : b in eval f a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StateTransition.mem_eval`：mem_eval {σ} {f : σ -> Option σ} {a b} : b in 
eval f a ↔ Reaches f a b ∧ f b = none
· 使用定理 `Relation.reflTransGen_iff_eq`：reflTransGen_iff_eq (h : forall b, ¬r a b)
 : ReflTransGen r a b ↔ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem eval_maximal₁ {σ} {f : σ → Option σ} {a b} (h : b ∈ eval f a) (c) : ¬Reaches₁ f b c
  | bc => by
    let ⟨_, b0⟩ := mem_eval.1 h
    let ⟨b', h', _⟩ := TransGen.head'_iff.1 bc
    cases b0.symm.trans h'
/-
**StateTransition.eval_maximal** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：eval_maximal {σ} {f : σ -> Option σ} {a b} (h : b in eval f a) {c} : Reach
es f b c ↔ c = b
参数：h : b in eval f a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StateTransition.mem_eval`：mem_eval {σ} {f : σ -> Option σ} {a b} : b in 
eval f a ↔ Reaches f a b ∧ f b = none
· 使用定理 `Relation.reflTransGen_iff_eq`：reflTransGen_iff_eq (h : forall b, ¬r a b)
 : ReflTransGen r a b ↔ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem eval_maximal {σ} {f : σ → Option σ} {a b} (h : b ∈ eval f a) {c} : Reaches f b c ↔ c = b :=
  let ⟨_, b0⟩ := mem_eval.1 h
  reflTransGen_iff_eq fun b' h' ↦ by cases b0.symm.trans h'
/-
**StateTransition.reaches_eval** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：reaches_eval {σ} {f : σ -> Option σ} {a b} (ab : Reaches f a b) : eval f a
 = eval f b
参数：ab : Reaches f a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StateTransition.mem_eval`：mem_eval {σ} {f : σ -> Option σ} {a b} : b in 
eval f a ↔ Reaches f a b ∧ f b = none
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `or_iff_left_of_imp`：∀ {b a : Prop}, (b → a) → (a ∨ b ↔ a)
· 使用定理 `StateTransition.eval_maximal`：eval_maximal {σ} {f : σ -> Option σ} {a b}
 (h : b in eval f a) {c} : Reaches f b c ↔ c = b
· 使用定理 `StateTransition.reaches_total`：reaches_total {σ} {f : σ -> Option σ} {a 
b c} (hab : Reaches f a b) (hac : Reaches f a c) : Reaches f b c ∨ Reaches f c b
· 使用定理 `Relation.ReflTransGen.trans`：trans (hab : ReflTransGen r a b) (hbc : Ref
lTransGen r b c) : ReflTransGen r a c
-/
theorem reaches_eval {σ} {f : σ → Option σ} {a b} (ab : Reaches f a b) : eval f a = eval f b := by
  refine Part.ext fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have ⟨ac, c0⟩ := mem_eval.1 h
    exact mem_eval.2 ⟨(or_iff_left_of_imp fun cb ↦ (eval_maximal h).1 cb ▸ ReflTransGen.refl).1
      (reaches_total ab ac), c0⟩
  · have ⟨bc, c0⟩ := mem_eval.1 h
    exact mem_eval.2 ⟨ab.trans bc, c0⟩

/-- Given a relation `tr : σ₁ → σ₂ → Prop` between state spaces, and state transition functions
`f₁ : σ₁ → Option σ₁` and `f₂ : σ₂ → Option σ₂`, `Respects f₁ f₂ tr` means that if `tr a₁ a₂` holds
initially and `f₁` takes a step to `a₂` then `f₂` will take one or more steps before reaching a
state `b₂` satisfying `tr a₂ b₂`, and if `f₁ a₁` terminates then `f₂ a₂` also terminates.
Such a relation `tr` is also known as a refinement. -/
/-
**StateTransition.Respects** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：Respects {σ₁ σ₂} (f₁ : σ₁ -> Option σ₁) (f₂ : σ₂ -> Option σ₂) (tr : σ₁ ->
 σ₂ -> Prop)
参数：f₁ : σ₁ -> Option σ₁；f₂ : σ₂ -> Option σ₂；tr : σ₁ -> σ₂ -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a relation `tr : σ₁ → σ₂ → Prop` between state spaces, and state transitio
n functions
`f₁ : σ₁ → Option σ₁` and `f₂ : σ₂ → Option σ₂`, `Respects f₁ f₂ tr` means that 
if `tr a₁ a₂` holds
initially and `f₁` takes a step to `a₂` then `f₂` will take one or more steps be
fore reaching a
state `b₂` satisfying `tr a₂ b₂`, and if `f₁ a₁` terminates then `f₂ a₂` also te
rminates.
Such a relation `tr` is also known as a refinement.
-/
def Respects {σ₁ σ₂} (f₁ : σ₁ → Option σ₁) (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂ → Prop) :=
  ∀ ⦃a₁ a₂⦄, tr a₁ a₂ → (match f₁ a₁ with
    | some b₁ => ∃ b₂, tr b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
    | none => f₂ a₂ = none : Prop)
/-
**StateTransition.tr_reaches** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：tr_reaches {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {
a₁ a₂} (aa : tr a₁ a₂) {b₁} (ab : Reaches f₁ a₁ b₁) : exists b₂, tr b₁ b₂ ∧ Reac
hes f₂ a₂ b₂
参数：H : Respects f₁ f₂ tr；aa : tr a₁ a₂；ab : Reaches f₁ a₁ b₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Relation.reflTransGen_iff_eq_or_transGen`：reflTransGen_iff_eq_or_transGe
n : ReflTransGen r a b ↔ b = a ∨ TransGen r a b
· 使用定理 `StateTransition.tr_reaches₁`：tr_reaches₁ {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ ->
 Prop} (H : Respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₁} (ab : Reaches₁ f₁ a₁
 b₁) : exists b₂,…
· 使用定理 `Relation.TransGen.to_reflTransGen`：to_reflTransGen {a b} : TransGen r a 
b -> ReflTransGen r a b
-/
theorem tr_reaches₁ {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₁} (ab : Reaches₁ f₁ a₁ b₁) : ∃ b₂, tr b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂ := by
  induction ab with
  | single ac =>
    have := H aa
    rwa [show f₁ a₁ = _ from ac] at this
  | @tail c₁ d₁ _ cd IH =>
    rcases IH with ⟨c₂, cc, ac₂⟩
    have := H cc
    rw [show f₁ c₁ = _ from cd] at this
    rcases this with ⟨d₂, dd, cd₂⟩
    exact ⟨_, dd, ac₂.trans cd₂⟩
/-
**StateTransition.tr_reaches** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：tr_reaches {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {
a₁ a₂} (aa : tr a₁ a₂) {b₁} (ab : Reaches f₁ a₁ b₁) : exists b₂, tr b₁ b₂ ∧ Reac
hes f₂ a₂ b₂
参数：H : Respects f₁ f₂ tr；aa : tr a₁ a₂；ab : Reaches f₁ a₁ b₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Relation.reflTransGen_iff_eq_or_transGen`：reflTransGen_iff_eq_or_transGe
n : ReflTransGen r a b ↔ b = a ∨ TransGen r a b
· 使用定理 `StateTransition.tr_reaches₁`：tr_reaches₁ {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ ->
 Prop} (H : Respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₁} (ab : Reaches₁ f₁ a₁
 b₁) : exists b₂,…
· 使用定理 `Relation.TransGen.to_reflTransGen`：to_reflTransGen {a b} : TransGen r a 
b -> ReflTransGen r a b
-/
theorem tr_reaches {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₁} (ab : Reaches f₁ a₁ b₁) : ∃ b₂, tr b₁ b₂ ∧ Reaches f₂ a₂ b₂ := by
  rcases reflTransGen_iff_eq_or_transGen.1 ab with (rfl | ab)
  · exact ⟨_, aa, ReflTransGen.refl⟩
  · have ⟨b₂, bb, h⟩ := tr_reaches₁ H aa ab
    exact ⟨b₂, bb, h.to_reflTransGen⟩
/-
**StateTransition.tr_reaches_rev** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：tr_reaches_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ t
r) {a₁ a₂} (aa : tr a₁ a₂) {b₂} (ab : Reaches f₂ a₂ b₂) : exists c₁ c₂, Reaches 
f₂ b₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁
参数：H : Respects f₁ f₂ tr；aa : tr a₁ a₂；ab : Reaches f₂ a₂ b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.cases_head`：cases_head (h : ReflTransGen r a b) : 
a = b ∨ exists c, r a c ∧ ReflTransGen r c b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Relation.TransGen.head'_iff`：∀ {α : Type u_1} {r : α → α → Prop} {a c : 
α}, Relation.TransGen r a c ↔ ∃ b, r a b ∧ Relation.ReflTransGen r b c
· 使用定理 `Option.mem_unique`：∀ {α : Type u_1} {o : Option α} {a b : α}, a ∈ o → b 
∈ o → a = b
-/
theorem tr_reaches_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₂} (ab : Reaches f₂ a₂ b₂) :
    ∃ c₁ c₂, Reaches f₂ b₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁ := by
  induction ab with
  | refl => exact ⟨_, _, ReflTransGen.refl, aa, ReflTransGen.refl⟩
  | tail _ cd IH =>
    rcases IH with ⟨e₁, e₂, ce, ee, ae⟩
    rcases ReflTransGen.cases_head ce with (rfl | ⟨d', cd', de⟩)
    · have := H ee
      revert this
      rcases eg : f₁ e₁ with - | g₁ <;> simp only [and_imp, exists_imp]
      · intro c0
        cases cd.symm.trans c0
      · intro g₂ gg cg
        rcases TransGen.head'_iff.1 cg with ⟨d', cd', dg⟩
        cases Option.mem_unique cd cd'
        exact ⟨_, _, dg, gg, ae.tail eg⟩
    · cases Option.mem_unique cd cd'
      exact ⟨_, _, de, ee, ae⟩
/-
**StateTransition.tr_eval** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ 
b₁ a₂} (aa : tr a₁ a₂) (ab : b₁ in eval f₁ a₁) : exists b₂, tr b₁ b₂ ∧ b₂ in eva
l f₂ a₂
参数：H : Respects f₁ f₂ tr；aa : tr a₁ a₂；ab : b₁ in eval f₁ a₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StateTransition.mem_eval`：mem_eval {σ} {f : σ -> Option σ} {a b} : b in 
eval f a ↔ Reaches f a b ∧ f b = none
· 使用定理 `StateTransition.tr_reaches`：tr_reaches {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> P
rop} (H : Respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₁} (ab : Reaches f₁ a₁ b₁
) : exists b₂, t…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ b₁ a₂}
    (aa : tr a₁ a₂) (ab : b₁ ∈ eval f₁ a₁) : ∃ b₂, tr b₁ b₂ ∧ b₂ ∈ eval f₂ a₂ := by
  obtain ⟨ab, b0⟩ := mem_eval.1 ab
  rcases tr_reaches H aa ab with ⟨b₂, bb, ab⟩
  refine ⟨_, bb, mem_eval.2 ⟨ab, ?_⟩⟩
  have := H bb; rwa [b0] at this
/-
**StateTransition.tr_eval_rev** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：tr_eval_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) 
{a₁ b₂ a₂} (aa : tr a₁ a₂) (ab : b₂ in eval f₂ a₂) : exists b₁, tr b₁ b₂ ∧ b₁ in
 eval f₁ a₁
参数：H : Respects f₁ f₂ tr；aa : tr a₁ a₂；ab : b₂ in eval f₂ a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StateTransition.mem_eval`：mem_eval {σ} {f : σ -> Option σ} {a b} : b in 
eval f a ↔ Reaches f a b ∧ f b = none
· 使用定理 `StateTransition.tr_reaches_rev`：tr_reaches_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ ->
 σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₂} (ab : Reaches 
f₂ a₂ b₂) : exists c…
· 使用定理 `Relation.reflTransGen_iff_eq`：reflTransGen_iff_eq (h : forall b, ¬r a b)
 : ReflTransGen r a b ↔ b = a
· 使用定理 `Option.eq_none_iff_forall_not_mem`：∀ {α : Type u_1} {o : Option α}, o = 
none ↔ ∀ (a : α), a ∉ o
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.TransGen.head'_iff`：∀ {α : Type u_1} {r : α → α → Prop} {a c : 
α}, Relation.TransGen r a c ↔ ∃ b, r a b ∧ Relation.ReflTransGen r b c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem tr_eval_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ b₂ a₂}
    (aa : tr a₁ a₂) (ab : b₂ ∈ eval f₂ a₂) : ∃ b₁, tr b₁ b₂ ∧ b₁ ∈ eval f₁ a₁ := by
  obtain ⟨ab, b0⟩ := mem_eval.1 ab
  rcases tr_reaches_rev H aa ab with ⟨c₁, c₂, bc, cc, ac⟩
  cases (reflTransGen_iff_eq (Option.eq_none_iff_forall_not_mem.1 b0)).1 bc
  refine ⟨_, cc, mem_eval.2 ⟨ac, ?_⟩⟩
  have := H cc
  rcases hfc : f₁ c₁ with - | d₁
  · rfl
  rw [hfc] at this
  rcases this with ⟨d₂, _, bd⟩
  rcases TransGen.head'_iff.1 bd with ⟨e, h, _⟩
  cases b0.symm.trans h
/-
**StateTransition.tr_eval_dom** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：tr_eval_dom {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) 
{a₁ a₂} (aa : tr a₁ a₂) : (eval f₂ a₂).Dom ↔ (eval f₁ a₁).Dom
参数：H : Respects f₁ f₂ tr；aa : tr a₁ a₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StateTransition.tr_eval_rev`：tr_eval_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ ->
 Prop} (H : Respects f₁ f₂ tr) {a₁ b₂ a₂} (aa : tr a₁ a₂) (ab : b₂ in eval f₂ a₂
) : exists b₁, tr…
· 使用定理 `StateTransition.tr_eval`：tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (
H : Respects f₁ f₂ tr) {a₁ b₁ a₂} (aa : tr a₁ a₂) (ab : b₁ in eval f₁ a₁) : exis
ts b₂, tr b₁ …
-/
theorem tr_eval_dom {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) : (eval f₂ a₂).Dom ↔ (eval f₁ a₁).Dom :=
  ⟨fun h ↦
    let ⟨_, _, h, _⟩ := tr_eval_rev H aa ⟨h, rfl⟩
    h,
    fun h ↦
    let ⟨_, _, h, _⟩ := tr_eval H aa ⟨h, rfl⟩
    h⟩

/-- A simpler version of `Respects` when the state transition relation `tr` is a function. -/
/-
**StateTransition.FRespects** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition`。
形式化陈述：{σ₁ : Type u_1} → {σ₂ : Type u_2} → (σ₂ → Option σ₂) → (σ₁ → σ₂) → σ₂ → Op
tion σ₁ → Prop
参数：σ₂ → Option σ₂；σ₁ → σ₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simpler version of `Respects` when the state transition relation `tr` is a fun
ction.
-/
def FRespects {σ₁ σ₂} (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂) (a₂ : σ₂) : Option σ₁ → Prop
  | some b₁ => Reaches₁ f₂ a₂ (tr b₁)
  | none => f₂ a₂ = none
/-
**StateTransition.frespects_eq** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：∀ {σ₁ : Type u_1} {σ₂ : Type u_2} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂} {a₂
 b₂ : σ₂},   f₂ a₂ = f₂ b₂ → ∀ {b₁ : Option σ₁}, StateTransition.FRespects f₂ tr
 a₂ b₁ ↔ StateTransition.FRespects f₂ tr b₂ b₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StateTransition.reaches₁_eq`：reaches₁_eq {σ} {f : σ -> Option σ} {a b c}
 (h : f a = f b) : Reaches₁ f a c ↔ Reaches₁ f b c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem frespects_eq {σ₁ σ₂} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂} {a₂ b₂} (h : f₂ a₂ = f₂ b₂) :
    ∀ {b₁}, FRespects f₂ tr a₂ b₁ ↔ FRespects f₂ tr b₂ b₁
  | some _ => reaches₁_eq h
  | none => by unfold FRespects; rw [h]
/-
**StateTransition.fun_respects** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：fun_respects {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂} : (Respects f₁ f₂ fun a b => tr
 a = b) ↔ forall ⦃a₁⦄, FRespects f₂ tr (tr a₁) (f₁ a₁)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem fun_respects {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂} :
    (Respects f₁ f₂ fun a b ↦ tr a = b) ↔ ∀ ⦃a₁⦄, FRespects f₂ tr (tr a₁) (f₁ a₁) :=
  forall_congr' fun a₁ ↦ by
    cases f₁ a₁ <;> simp only [FRespects, exists_eq_left', forall_eq']
/-
**StateTransition.tr_eval'** 是 Mathlib 中的一个定理，位于命名空间 `StateTransition`。
形式化陈述：tr_eval' {σ₁ σ₂} (f₁ : σ₁ -> Option σ₁) (f₂ : σ₂ -> Option σ₂) (tr : σ₁ ->
 σ₂) (H : Respects f₁ f₂ fun a b => tr a = b) (a₁) : eval f₂ (tr a₁) = tr < > ev
al f₁ a₁
参数：f₁ : σ₁ -> Option σ₁；f₂ : σ₂ -> Option σ₂；tr : σ₁ -> σ₂；H : Respects f₁ f₂ fu
n a b => tr a = b；a₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `StateTransition.tr_eval_rev`：tr_eval_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ ->
 Prop} (H : Respects f₁ f₂ tr) {a₁ b₂ a₂} (aa : tr a₁ a₂) (ab : b₂ in eval f₂ a₂
) : exists b₁, tr…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.mem_map_iff`：mem_map_iff (f : α -> β) {o : Part α} {b} : b in map f
 o ↔ exists a in o, f a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StateTransition.tr_eval`：tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (
H : Respects f₁ f₂ tr) {a₁ b₁ a₂} (aa : tr a₁ a₂) (ab : b₁ in eval f₁ a₁) : exis
ts b₂, tr b₁ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem tr_eval' {σ₁ σ₂} (f₁ : σ₁ → Option σ₁) (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂)
    (H : Respects f₁ f₂ fun a b ↦ tr a = b) (a₁) : eval f₂ (tr a₁) = tr <$> eval f₁ a₁ :=
  Part.ext fun b₂ ↦
    ⟨fun h ↦
      let ⟨b₁, bb, hb⟩ := tr_eval_rev H rfl h
      (Part.mem_map_iff _).2 ⟨b₁, hb, bb⟩,
      fun h ↦ by
      rcases (Part.mem_map_iff _).1 h with ⟨b₁, ab, bb⟩
      rcases tr_eval H rfl ab with ⟨_, rfl, h⟩
      rwa [bb] at h⟩

section EvalsTo

/-- A "proof" of the fact that `f` eventually reaches `b` when repeatedly evaluated on `a`,
remembering the number of steps it takes. -/
/-
**StateTransition.EvalsTo** 是 Mathlib 中的一个归纳类型，位于命名空间 `StateTransition`。
形式化陈述：{σ : Type u_1} → (σ → Option σ) → σ → Option σ → Type
参数：σ → Option σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A "proof" of the fact that `f` eventually reaches `b` when repeatedly evaluated 
on `a`,
remembering the number of steps it takes.
-/
structure EvalsTo {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) where
  /-- number of steps taken -/
  steps : ℕ
  evals_in_steps : (flip bind f)^[steps] a = b

-- note: this cannot currently be used in `calc`, as the last two arguments must be `a` and `b`.
-- If this is desired, this argument order can be changed, but this spelling is I think the most
-- natural, so there is a trade-off that needs to be made here. A notation can get around this.
/-- A "proof" of the fact that `f` eventually reaches `b` in at most `m` steps when repeatedly
evaluated on `a`, remembering the number of steps it takes. -/
/-
**StateTransition.EvalsToInTime** 是 Mathlib 中的一个归纳类型，位于命名空间 `StateTransition`。
形式化陈述：{σ : Type u_1} → (σ → Option σ) → σ → Option σ → ℕ → Type
参数：σ → Option σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A "proof" of the fact that `f` eventually reaches `b` in at most `m` steps when 
repeatedly
evaluated on `a`, remembering the number of steps it takes.
-/
structure EvalsToInTime {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) extends
  EvalsTo f a b where
  steps_le_m : steps ≤ m

/-- Reflexivity of `EvalsTo` in 0 steps. -/
/-
**StateTransition.EvalsTo.refl** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition.EvalsT
o`。
形式化陈述：{σ : Type u_1} → (f : σ → Option σ) → (a : σ) → StateTransition.EvalsTo f 
a (some a)
参数：f : σ → Option σ；a : σ；some a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reflexivity of `EvalsTo` in 0 steps.
-/
def EvalsTo.refl {σ : Type*} (f : σ → Option σ) (a : σ) : EvalsTo f a (some a) :=
  ⟨0, rfl⟩

/-- Transitivity of `EvalsTo` in the sum of the numbers of steps. -/
@[trans]
/-
**StateTransition.EvalsTo.trans** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition.Evals
To`。
形式化陈述：{σ : Type u_1} →   (f : σ → Option σ) →     (a b : σ) →       (c : Option 
σ) →         StateTransition.EvalsTo f a (some b) → StateTransition.EvalsTo f b 
c → StateTransition.EvalsTo f a c
参数：f : σ → Option σ；a b : σ；c : Option σ；some b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transitivity of `EvalsTo` in the sum of the numbers of steps.
-/
def EvalsTo.trans {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ)
    (h₁ : EvalsTo f a b) (h₂ : EvalsTo f b c) : EvalsTo f a c :=
  ⟨h₂.steps + h₁.steps, by rw [Function.iterate_add_apply, h₁.evals_in_steps, h₂.evals_in_steps]⟩

/-- Reflexivity of `EvalsToInTime` in 0 steps. -/
/-
**StateTransition.EvalsToInTime.refl** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition.
EvalsToInTime`。
形式化陈述：{σ : Type u_1} → (f : σ → Option σ) → (a : σ) → StateTransition.EvalsToInT
ime f a (some a) 0
参数：f : σ → Option σ；a : σ；some a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reflexivity of `EvalsToInTime` in 0 steps.
-/
def EvalsToInTime.refl {σ : Type*} (f : σ → Option σ) (a : σ) : EvalsToInTime f a (some a) 0 :=
  ⟨EvalsTo.refl f a, le_refl 0⟩

/-- Transitivity of `EvalsToInTime` in the sum of the numbers of steps. -/
@[trans]
/-
**StateTransition.EvalsToInTime.trans** 是 Mathlib 中的一个定义，位于命名空间 `StateTransition
.EvalsToInTime`。
形式化陈述：{σ : Type u_1} →   (f : σ → Option σ) →     (m₁ m₂ : ℕ) →       (a b : σ) 
→         (c : Option σ) →           StateTransition.EvalsToInTime f a (some b) 
m₁ →             StateTransition.EvalsToInTime f b c m₂ → StateTransition.EvalsT
oInTime f a c (m₂ + m₁)
参数：f : σ → Option σ；m₁ m₂ : ℕ；a b : σ；c : Option σ；some b；m₂ + m₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transitivity of `EvalsToInTime` in the sum of the numbers of steps.
-/
def EvalsToInTime.trans {σ : Type*} (f : σ → Option σ) (m₁ : ℕ) (m₂ : ℕ) (a : σ) (b : σ)
    (c : Option σ) (h₁ : EvalsToInTime f a b m₁) (h₂ : EvalsToInTime f b c m₂) :
    EvalsToInTime f a c (m₂ + m₁) :=
  ⟨EvalsTo.trans f a b c h₁.toEvalsTo h₂.toEvalsTo, add_le_add h₂.steps_le_m h₁.steps_le_m⟩

end EvalsTo

end StateTransition

