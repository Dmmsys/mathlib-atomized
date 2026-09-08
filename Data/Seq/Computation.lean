/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Stream.Init
public import Mathlib.Logic.Relator
public import Mathlib.Tactic.Common
public import Batteries.Tactic.Lint.Simp

/-!
# Coinductive formalization of unbounded computations.

This file provides a `Computation` type where `Computation α` is the type of
unbounded computations returning `α`.
-/

@[expose] public section

open Function

universe u v w

/-
coinductive Computation (α : Type u) : Type u
| pure : α → Computation α
| think : Computation α → Computation α
-/
/-- `Computation α` is the type of unbounded computations returning `α`.
  An element of `Computation α` is an infinite sequence of `Option α` such
  that if `f n = some a` for some `n` then it is constantly `some a` after that. -/
/-
**Computation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Computation (α : Type u) : Type u
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Computation α` is the type of unbounded computations returning `α`.
  An element of `Computation α` is an infinite sequence of `Option α` such
  that if `f n = some a` for some `n` then it is constantly `some a` after that.
-/
def Computation (α : Type u) : Type u :=
  { f : Stream' (Option α) // ∀ ⦃n a⦄, f n = some a → f (n + 1) = some a }

namespace Computation

variable {α : Type u} {β : Type v} {γ : Type w}

-- constructors
/-- `pure a` is the computation that immediately terminates with result `a`. -/
/-
**Computation.pure** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：pure (a : α) : Computation α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pure a` is the computation that immediately terminates with result `a`.
-/
def pure (a : α) : Computation α :=
  ⟨Stream'.const (some a), fun _ _ => id⟩
/-
**Computation.** 是 Mathlib 中的一个实例，位于命名空间 `Computation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC α (Computation α) :=
  ⟨pure⟩

-- note [use has_coe_t]
/-- `think c` is the computation that delays for one "tick" and then performs
  computation `c`. -/
/-
**Computation.think** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：think (c : Computation α) : Computation α
参数：c : Computation α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`think c` is the computation that delays for one "tick" and then performs
  computation `c`.
-/
def think (c : Computation α) : Computation α :=
  ⟨Stream'.cons none c.1, fun n a h => by
    rcases n with - | n
    · contradiction
    · exact c.2 h⟩

/-- `thinkN c n` is the computation that delays for `n` ticks and then performs
  computation `c`. -/
/-
**Computation.thinkN** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：{α : Type u} → Computation α → ℕ → Computation α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`thinkN c n` is the computation that delays for `n` ticks and then performs
  computation `c`.
-/
def thinkN (c : Computation α) : ℕ → Computation α
  | 0 => c
  | n + 1 => think (thinkN c n)

-- check for immediate result
/-- `head c` is the first step of computation, either `some a` if `c = pure a`
  or `none` if `c = think c'`. -/
/-
**Computation.head** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：head (c : Computation α) : Option α
参数：c : Computation α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`head c` is the first step of computation, either `some a` if `c = pure a`
  or `none` if `c = think c'`.
-/
def head (c : Computation α) : Option α :=
  c.1.head

-- one step of computation
/-- `tail c` is the remainder of computation, either `c` if `c = pure a`
  or `c'` if `c = think c'`. -/
/-
**Computation.tail** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：tail (c : Computation α) : Computation α
参数：c : Computation α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`tail c` is the remainder of computation, either `c` if `c = pure a`
  or `c'` if `c = think c'`.
-/
def tail (c : Computation α) : Computation α :=
  ⟨c.1.tail, fun _ _ h => c.2 h⟩

/-- `empty α` is the computation that never returns, an infinite sequence of
  `think`s. -/
/-
**Computation.empty** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：empty (α) : Computation α
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`empty α` is the computation that never returns, an infinite sequence of
  `think`s.
-/
def empty (α) : Computation α :=
  ⟨Stream'.const none, fun _ _ => id⟩
/-
**Computation.** 是 Mathlib 中的一个实例，位于命名空间 `Computation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Computation α) :=
  ⟨empty _⟩

/-- `runFor c n` evaluates `c` for `n` steps and returns the result, or `none`
  if it did not terminate after `n` steps. -/
/-
**Computation.runFor** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：runFor : Computation α -> Nat -> Option α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`runFor c n` evaluates `c` for `n` steps and returns the result, or `none`
  if it did not terminate after `n` steps.
-/
def runFor : Computation α → ℕ → Option α :=
  Subtype.val

/-- `destruct c` is the destructor for `Computation α` as a coinductive type.
  It returns `inl a` if `c = pure a` and `inr c'` if `c = think c'`. -/
/-
**Computation.destruct** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：destruct (c : Computation α) : α oplus (Computation α)
参数：c : Computation α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`destruct c` is the destructor for `Computation α` as a coinductive type.
  It returns `inl a` if `c = pure a` and `inr c'` if `c = think c'`.
-/
def destruct (c : Computation α) : α ⊕ (Computation α) :=
  match c.1 0 with
  | none => Sum.inr (tail c)
  | some a => Sum.inl a

/-- `run c` is an unsound meta function that runs `c` to completion, possibly
  resulting in an infinite loop in the VM. -/
/-
**Computation.run** 是 Mathlib 中的一个unsafe-def，位于命名空间 `Computation`。
形式化陈述：{α : Type u} → Computation α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`run c` is an unsound meta function that runs `c` to completion, possibly
  resulting in an infinite loop in the VM.
-/
unsafe def run : Computation α → α
  | c =>
    match destruct c with
    | Sum.inl a => a
    | Sum.inr ca => run ca
/-
**Computation.destruct_eq_pure** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：destruct_eq_pure {s : Computation α} {a : α} : destruct s = Sum.inl a -> s
 = pure a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem destruct_eq_pure {s : Computation α} {a : α} : destruct s = Sum.inl a → s = pure a := by
  dsimp [destruct]
  cases f0 : s.1 0 <;> intro h
  · contradiction
  · apply Subtype.ext
    funext n
    induction n with
    | zero => injection h with h'; rwa [h'] at f0
    | succ n IH => exact s.2 IH
/-
**Computation.destruct_eq_think** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：destruct_eq_think {s : Computation α} {s'} : destruct s = Sum.inr s' -> s 
= think s'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Stream'.eta`：∀ {α : Type u} (s : Stream' α), Stream'.cons s.head s.tail 
= s
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem destruct_eq_think {s : Computation α} {s'} : destruct s = Sum.inr s' → s = think s' := by
  dsimp [destruct]
  rcases f0 : s.1 0 with - | a' <;> intro h
  · injection h with h'
    rw [← h']
    obtain ⟨f, al⟩ := s
    apply Subtype.ext
    dsimp [think, tail]
    rw [← f0]
    exact (Stream'.eta f).symm
  · contradiction

@[simp]
/-
**Computation.destruct_pure** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：destruct_pure (a : α) : destruct (pure a) = Sum.inl a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem destruct_pure (a : α) : destruct (pure a) = Sum.inl a :=
  rfl

@[simp]
/-
**Computation.destruct_think** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} (s : Computation α), s.think.destruct = Sum.inr s
参数：s : Computation α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem destruct_think : ∀ s : Computation α, destruct (think s) = Sum.inr s
  | ⟨_, _⟩ => rfl

@[simp]
/-
**Computation.destruct_empty** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：destruct_empty : destruct (empty α) = Sum.inr (empty α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem destruct_empty : destruct (empty α) = Sum.inr (empty α) :=
  rfl

@[simp]
/-
**Computation.head_pure** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：head_pure (a : α) : head (pure a) = some a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_pure (a : α) : head (pure a) = some a :=
  rfl

@[simp]
/-
**Computation.head_think** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：head_think (s : Computation α) : head (think s) = none
参数：s : Computation α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_think (s : Computation α) : head (think s) = none :=
  rfl

@[simp]
/-
**Computation.head_empty** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：head_empty : head (empty α) = none
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_empty : head (empty α) = none :=
  rfl

@[simp]
/-
**Computation.tail_pure** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：tail_pure (a : α) : tail (pure a) = pure a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_pure (a : α) : tail (pure a) = pure a :=
  rfl

@[simp]
/-
**Computation.tail_think** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：tail_think (s : Computation α) : tail (think s) = s
参数：s : Computation α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_think (s : Computation α) : tail (think s) = s := rfl

@[simp]
/-
**Computation.tail_empty** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：tail_empty : tail (empty α) = empty α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_empty : tail (empty α) = empty α :=
  rfl
/-
**Computation.think_empty** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：think_empty : empty α = think (empty α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.destruct_eq_think`：destruct_eq_think {s : Computation α} {s'
} : destruct s = Sum.inr s' -> s = think s'
· 使用定理 `Computation.destruct_empty`：destruct_empty : destruct (empty α) = Sum.in
r (empty α)
-/
theorem think_empty : empty α = think (empty α) :=
  destruct_eq_think destruct_empty

/-- Recursion principle for computations, compare with `List.recOn`. -/
@[elab_as_elim]
/-
**Computation.recOn** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：recOn {motive : Computation α -> Sort v} (s : Computation α) (pure : foral
l a, motive (pure a)) (think : forall s, motive (think s)) : motive s
参数：s : Computation α；pure : forall a, motive (pure a)；think : forall s, motive (
think s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle for computations, compare with `List.recOn`.
-/
def recOn {motive : Computation α → Sort v} (s : Computation α) (pure : ∀ a, motive (pure a))
    (think : ∀ s, motive (think s)) : motive s :=
  match H : destruct s with
  | Sum.inl v => by
    rw [destruct_eq_pure H]
    apply pure
  | Sum.inr v => match v with
    | ⟨a, s'⟩ => by
      rw [destruct_eq_think H]
      apply think

/-- Corecursor constructor for `corec` -/
/-
**Computation.Corec.f** 是 Mathlib 中的一个定义，位于命名空间 `Computation.Corec`。
形式化陈述：{α : Type u} → {β : Type v} → (β → α ⊕ β) → α ⊕ β → Option α × (α ⊕ β)
参数：β → α ⊕ β；α ⊕ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Corecursor constructor for `corec`
-/
def Corec.f (f : β → α ⊕ β) : α ⊕ β → Option α × (α ⊕ β)
  | Sum.inl a => (some a, Sum.inl a)
  | Sum.inr b =>
    (match f b with
      | Sum.inl a => some a
      | Sum.inr _ => none,
      f b)

/-- `corec f b` is the corecursor for `Computation α` as a coinductive type.
  If `f b = inl a` then `corec f b = pure a`, and if `f b = inl b'` then
  `corec f b = think (corec f b')`. -/
/-
**Computation.corec** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：corec (f : β -> α oplus β) (b : β) : Computation α
参数：f : β -> α oplus β；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`corec f b` is the corecursor for `Computation α` as a coinductive type.
  If `f b = inl a` then `corec f b = pure a`, and if `f b = inl b'` then
  `corec f b = think (corec f b')`.
-/
def corec (f : β → α ⊕ β) (b : β) : Computation α := by
  refine ⟨Stream'.corec' (Corec.f f) (Sum.inr b), fun n a' h => ?_⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (Corec.f f) (Corec.f f (Sum.inr b)).2 n = some a'
  revert h; generalize Sum.inr b = o
  induction n generalizing o with
  | zero =>
    change (Corec.f f o).1 = some a' → (Corec.f f (Corec.f f o).2).1 = some a'
    rcases o with _ | b <;> intro h
    · exact h
    unfold Corec.f at *; split <;> simp_all
  | succ n IH =>
    rw [Stream'.corec'_eq (Corec.f f) (Corec.f f o).2, Stream'.corec'_eq (Corec.f f) o]
    exact IH (Corec.f f o).2

/-- left map of `⊕` -/
/-
**Computation.lmap** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：{α : Type u} → {β : Type v} → {γ : Type w} → (α → β) → α ⊕ γ → β ⊕ γ
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
left map of `⊕`
-/
def lmap (f : α → β) : α ⊕ γ → β ⊕ γ
  | Sum.inl a => Sum.inl (f a)
  | Sum.inr b => Sum.inr b

/-- right map of `⊕` -/
/-
**Computation.rmap** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：{α : Type u} → {β : Type v} → {γ : Type w} → (β → γ) → α ⊕ β → α ⊕ γ
参数：β → γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
right map of `⊕`
-/
def rmap (f : β → γ) : α ⊕ β → α ⊕ γ
  | Sum.inl a => Sum.inl a
  | Sum.inr b => Sum.inr (f b)

attribute [simp] lmap rmap

@[simp]
/-
**Computation.corec_eq** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：corec_eq (f : β -> α oplus β) (b : β) : destruct (corec f b) = rmap (corec
 f) (f b)
参数：f : β -> α oplus β；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Stream'.corec'_eq`：∀ {α : Type u} {β : Type v} (f : α → β × α) (a : α), 
  Stream'.corec' f a = Stream'.cons (f a).1 (Stream'.corec' f (f a).2)
· 使用定理 `Stream'.tail_cons`：tail_cons (a : α) (s : Stream' α) : tail (a::s) = s
-/
theorem corec_eq (f : β → α ⊕ β) (b : β) : destruct (corec f b) = rmap (corec f) (f b) := by
  dsimp [corec, destruct]
  rw [show Stream'.corec' (Corec.f f) (Sum.inr b) 0 =
    Sum.rec Option.some (fun _ ↦ none) (f b) by
    dsimp [Corec.f, Stream'.corec', Stream'.corec, Stream'.map, Stream'.get, Stream'.iterate]
    match (f b) with
    | Sum.inl x => rfl
    | Sum.inr x => rfl]
  rcases h : f b with a | b'; · rfl
  dsimp [Corec.f, destruct]
  apply congr_arg; apply Subtype.ext
  dsimp [corec, tail]
  rw [Stream'.corec'_eq, Stream'.tail_cons]
  dsimp [Corec.f]; rw [h]

section Bisim

variable (R : Computation α → Computation α → Prop)

/-- bisimilarity relation -/
local infixl:50 " ~ " => R

/-- Bisimilarity over a sum of `Computation`s -/
/-
**Computation.BisimO** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：{α : Type u} → (Computation α → Computation α → Prop) → α ⊕ Computation α 
→ α ⊕ Computation α → Prop
参数：Computation α → Computation α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bisimilarity over a sum of `Computation`s
-/
def BisimO : α ⊕ (Computation α) → α ⊕ (Computation α) → Prop
  | Sum.inl a, Sum.inl a' => a = a'
  | Sum.inr s, Sum.inr s' => R s s'
  | _, _ => False

attribute [simp] BisimO
attribute [nolint simpNF] BisimO.eq_3

/-- Attribute expressing bisimilarity over two `Computation`s -/
/-
**Computation.IsBisimulation** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：IsBisimulation
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Attribute expressing bisimilarity over two `Computation`s
-/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → BisimO R (destruct s₁) (destruct s₂)

-- If two computations are bisimilar, then they are equal
/-
**Computation.eq_of_bisim** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂
参数：bisim : IsBisimulation R；r : s₁ ~ s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Stream'.eq_of_bisim`：eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} : s₁
 ~ s₂ -> s₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.tail_pure`：tail_pure (a : α) : tail (pure a) = pure a
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
· 使用定理 `Computation.destruct_pure`：destruct_pure (a : α) : destruct (pure a) = S
um.inl a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ := by
  apply Subtype.ext
  apply Stream'.eq_of_bisim fun x y => ∃ s s' : Computation α, s.1 = x ∧ s'.1 = y ∧ R s s'
  · dsimp [Stream'.IsBisimulation]
    intro t₁ t₂ e
    match t₁, t₂, e with
    | _, _, ⟨s, s', rfl, rfl, r⟩ =>
      suffices head s = head s' ∧ R (tail s) (tail s') from
        And.imp id (fun r => ⟨tail s, tail s', by cases s; rfl, by cases s'; rfl, r⟩) this
      have h := bisim r; revert r h
      refine recOn s ?_ ?_ <;> intro r' <;> refine recOn s' ?_ ?_ <;> intro a' r h
      · constructor <;> dsimp at h
        · rw [h]
        · rw [h] at r
          rw [tail_pure, tail_pure, h]
          assumption
      · rw [destruct_pure, destruct_think] at h
        exact False.elim h
      · rw [destruct_pure, destruct_think] at h
        exact False.elim h
      · simp_all
  · exact ⟨s₁, s₂, rfl, rfl, r⟩

end Bisim

-- It's more of a stretch to use ∈ for this relation, but it
-- asserts that the computation limits to the given value.
/-- Assertion that a `Computation` limits to a given value -/
/-
**Computation.Mem** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：{α : Type u} → Computation α → α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assertion that a `Computation` limits to a given value
-/
protected def Mem (s : Computation α) (a : α) :=
  some a ∈ s.1
/-
**Computation.** 是 Mathlib 中的一个实例，位于命名空间 `Computation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership α (Computation α) :=
  ⟨Computation.Mem⟩
/-
**Computation.le_stable** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：le_stable (s : Computation α) {a m n} (h : m <= n) : s.1 m = some a -> s.1
 n = some a
参数：s : Computation α；h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_stable (s : Computation α) {a m n} (h : m ≤ n) : s.1 m = some a → s.1 n = some a := by
  obtain ⟨f, al⟩ := s
  induction h with
  | refl => exact id
  | step _ IH => exact fun h2 ↦ al (IH h2)
/-
**Computation.mem_unique** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} {s : Computation α} {a b : α}, a ∈ s → b ∈ s → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.le_stable`：le_stable (s : Computation α) {a m n} (h : m <= n
) : s.1 m = some a -> s.1 n = some a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem mem_unique {s : Computation α} {a b : α} : a ∈ s → b ∈ s → a = b
  | ⟨m, ha⟩, ⟨n, hb⟩ => by
    injection
      (le_stable s (le_max_left m n) ha.symm).symm.trans (le_stable s (le_max_right m n) hb.symm)
/-
**Computation.Mem.left_unique** 是 Mathlib 中的一个定理，位于命名空间 `Computation.Mem`。
形式化陈述：∀ {α : Type u}, Relator.LeftUnique fun x1 x2 => x1 ∈ x2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.mem_unique`：∀ {α : Type u} {s : Computation α} {a b : α}, a 
∈ s → b ∈ s → a = b
-/
theorem Mem.left_unique : Relator.LeftUnique ((· ∈ ·) : α → Computation α → Prop) := fun _ _ _ =>
  mem_unique

/-- `Terminates s` asserts that the computation `s` eventually terminates with some value. -/
/-
**Computation.Terminates** 是 Mathlib 中的一个归纳类型，位于命名空间 `Computation`。
形式化陈述：{α : Type u} → Computation α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Terminates s` asserts that the computation `s` eventually terminates with some 
value.
-/
class Terminates (s : Computation α) : Prop where
  /-- assertion that there is some term `a` such that the `Computation` terminates -/
  term : ∃ a, a ∈ s
/-
**Computation.terminates_iff** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：terminates_iff (s : Computation α) : Terminates s ↔ exists a, a in s
参数：s : Computation α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.Terminates.term`：∀ {α : Type u} {s : Computation α} [self : 
s.Terminates], ∃ a, a ∈ s
-/
theorem terminates_iff (s : Computation α) : Terminates s ↔ ∃ a, a ∈ s :=
  ⟨fun h => h.1, Terminates.mk⟩
/-
**Computation.terminates_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：terminates_of_mem {s : Computation α} {a : α} (h : a in s) : Terminates s
参数：h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem terminates_of_mem {s : Computation α} {a : α} (h : a ∈ s) : Terminates s :=
  ⟨⟨a, h⟩⟩
/-
**Computation.terminates_def** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：terminates_def (s : Computation α) : Terminates s ↔ exists n, (s.1 n).isSo
me
参数：s : Computation α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.eq_some_of_isSome`：∀ {α : Type u_1} {o : Option α} (h : o.isSome 
= true), o = some (o.get h)
-/
theorem terminates_def (s : Computation α) : Terminates s ↔ ∃ n, (s.1 n).isSome :=
  ⟨fun ⟨⟨a, n, h⟩⟩ =>
    ⟨n, by
      dsimp [Stream'.get] at h
      rw [← h]
      exact rfl⟩,
    fun ⟨n, h⟩ => ⟨⟨Option.get _ h, n, (Option.eq_some_of_isSome h).symm⟩⟩⟩
/-
**Computation.ret_mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：ret_mem (a : α) : a in pure a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ret_mem (a : α) : a ∈ pure a :=
  Exists.intro 0 rfl
/-
**Computation.eq_of_pure_mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：eq_of_pure_mem {a a' : α} (h : a' in pure a) : a' = a
参数：h : a' in pure a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.mem_unique`：∀ {α : Type u} {s : Computation α} {a b : α}, a 
∈ s → b ∈ s → a = b
· 使用定理 `Computation.ret_mem`：ret_mem (a : α) : a in pure a
-/
theorem eq_of_pure_mem {a a' : α} (h : a' ∈ pure a) : a' = a :=
  mem_unique h (ret_mem _)

@[simp]
/-
**Computation.mem_pure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：mem_pure_iff (a b : α) : a in pure b ↔ a = b
参数：a b : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.eq_of_pure_mem`：eq_of_pure_mem {a a' : α} (h : a' in pure a)
 : a' = a
· 使用定理 `Computation.ret_mem`：ret_mem (a : α) : a in pure a
-/
theorem mem_pure_iff (a b : α) : a ∈ pure b ↔ a = b :=
  ⟨eq_of_pure_mem, fun h => h ▸ ret_mem _⟩
/-
**Computation.ret_terminates** 是 Mathlib 中的一个实例，位于命名空间 `Computation`。
形式化陈述：ret_terminates (a : α) : Terminates (pure a)
参数：a : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s
· 使用定理 `Computation.ret_mem`：ret_mem (a : α) : a in pure a
-/
instance ret_terminates (a : α) : Terminates (pure a) :=
  terminates_of_mem (ret_mem _)
/-
**Computation.think_mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} {s : Computation α} {a : α}, a ∈ s → a ∈ s.think
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem think_mem {s : Computation α} {a} : a ∈ s → a ∈ think s
  | ⟨n, h⟩ => ⟨n + 1, h⟩
/-
**Computation.think_terminates** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} (s : Computation α) [s.Terminates], s.think.Terminates
参数：s : Computation α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance think_terminates (s : Computation α) : ∀ [Terminates s], Terminates (think s)
  | ⟨⟨a, n, h⟩⟩ => ⟨⟨a, n + 1, h⟩⟩
/-
**Computation.of_think_mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} {s : Computation α} {a : α}, a ∈ s.think → a ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem of_think_mem {s : Computation α} {a} : a ∈ think s → a ∈ s
  | ⟨n, h⟩ => by
    rcases n with - | n'
    · contradiction
    · exact ⟨n', h⟩
/-
**Computation.of_think_terminates** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} {s : Computation α}, s.think.Terminates → s.Terminates
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.of_think_mem`：∀ {α : Type u} {s : Computation α} {a : α}, a 
∈ s.think → a ∈ s
-/
theorem of_think_terminates {s : Computation α} : Terminates (think s) → Terminates s
  | ⟨⟨a, h⟩⟩ => ⟨⟨a, of_think_mem h⟩⟩
/-
**Computation.notMem_empty** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：notMem_empty (a : α) : a ∉ empty α
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem notMem_empty (a : α) : a ∉ empty α := fun ⟨n, h⟩ => by contradiction
/-
**Computation.not_terminates_empty** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：not_terminates_empty : ¬Terminates (empty α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.notMem_empty`：notMem_empty (a : α) : a ∉ empty α
-/
theorem not_terminates_empty : ¬Terminates (empty α) := fun ⟨⟨a, h⟩⟩ => notMem_empty a h
/-
**Computation.eq_empty_of_not_terminates** 是 Mathlib 中的一个定理，位于命名空间 `Computation`
。
形式化陈述：eq_empty_of_not_terminates {s} (H : ¬Terminates s) : s = empty α
参数：H : ¬Terminates s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_empty_of_not_terminates {s} (H : ¬Terminates s) : s = empty α := by
  apply Subtype.ext; funext n
  rcases h : s.val n; · rfl
  refine absurd ?_ H; exact ⟨⟨_, _, h.symm⟩⟩
/-
**Computation.thinkN_mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} {s : Computation α} {a : α} (n : ℕ), a ∈ s.thinkN n ↔ a ∈ s
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem thinkN_mem {s : Computation α} {a} : ∀ n, a ∈ thinkN s n ↔ a ∈ s
  | 0 => Iff.rfl
  | n + 1 => Iff.trans ⟨of_think_mem, think_mem⟩ (thinkN_mem n)
/-
**Computation.thinkN_terminates** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} (s : Computation α) [s.Terminates] (n : ℕ), (s.thinkN n).Te
rminates
参数：s : Computation α；n : ℕ；s.thinkN n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Computation.thinkN_mem`：∀ {α : Type u} {s : Computation α} {a : α} (n : 
ℕ), a ∈ s.thinkN n ↔ a ∈ s
-/
instance thinkN_terminates (s : Computation α) : ∀ [Terminates s] (n), Terminates (thinkN s n)
  | ⟨⟨a, h⟩⟩, n => ⟨⟨a, (thinkN_mem n).2 h⟩⟩
/-
**Computation.of_thinkN_terminates** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} (s : Computation α) (n : ℕ), (s.thinkN n).Terminates → s.Te
rminates
参数：s : Computation α；n : ℕ；s.thinkN n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Computation.thinkN_mem`：∀ {α : Type u} {s : Computation α} {a : α} (n : 
ℕ), a ∈ s.thinkN n ↔ a ∈ s
-/
theorem of_thinkN_terminates (s : Computation α) (n) : Terminates (thinkN s n) → Terminates s
  | ⟨⟨a, h⟩⟩ => ⟨⟨a, (thinkN_mem _).1 h⟩⟩

/-- `Promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`. -/
/-
**Computation.Promises** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：Promises (s : Computation α) (a : α) : Prop
参数：s : Computation α；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`.
-/
def Promises (s : Computation α) (a : α) : Prop :=
  ∀ ⦃a'⦄, a' ∈ s → a = a'

/-- `Promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`. -/
scoped infixl:50 " ~> " => Promises

/-
**Computation.mem_promises** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：mem_promises {s : Computation α} {a : α} : a in s -> s ~> a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.mem_unique`：∀ {α : Type u} {s : Computation α} {a b : α}, a 
∈ s → b ∈ s → a = b
-/
theorem mem_promises {s : Computation α} {a : α} : a ∈ s → s ~> a := fun h _ => mem_unique h
/-
**Computation.empty_promises** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：empty_promises (a : α) : empty α ~> a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.notMem_empty`：notMem_empty (a : α) : a ∉ empty α
-/
theorem empty_promises (a : α) : empty α ~> a := fun _ h => absurd h (notMem_empty _)

section get

variable (s : Computation α) [h : Terminates s]

/-- `length s` gets the number of steps of a terminating computation -/
/-
**Computation.length** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：length : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`length s` gets the number of steps of a terminating computation
-/
def length : ℕ :=
  Nat.find ((terminates_def _).1 h)

/-- `get s` returns the result of a terminating computation -/
/-
**Computation.get** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：get : α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`get s` returns the result of a terminating computation
-/
def get : α :=
  Option.get _ (Nat.find_spec <| (terminates_def _).1 h)
/-
**Computation.get_mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：get_mem : get s in s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.eq_some_of_isSome`：∀ {α : Type u_1} {o : Option α} (h : o.isSome 
= true), o = some (o.get h)
-/
theorem get_mem : get s ∈ s :=
  Exists.intro (length s) (Option.eq_some_of_isSome _).symm
/-
**Computation.get_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：get_eq_of_mem {a} : a in s -> get s = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.mem_unique`：∀ {α : Type u} {s : Computation α} {a b : α}, a 
∈ s → b ∈ s → a = b
· 使用定理 `Computation.get_mem`：get_mem : get s in s
-/
theorem get_eq_of_mem {a} : a ∈ s → get s = a :=
  mem_unique (get_mem _)
/-
**Computation.mem_of_get_eq** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：mem_of_get_eq {a} : get s = a -> a in s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.get_mem`：get_mem : get s in s
-/
theorem mem_of_get_eq {a} : get s = a → a ∈ s := by intro h; rw [← h]; apply get_mem

@[simp]
/-
**Computation.get_think** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：get_think : get (think s) = get s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.get_eq_of_mem`：get_eq_of_mem {a} : a in s -> get s = a
· 使用定理 `Computation.think_terminates`：∀ {α : Type u} (s : Computation α) [s.Term
inates], s.think.Terminates
· 使用定理 `Computation.get_mem`：get_mem : get s in s
-/
theorem get_think : get (think s) = get s :=
  get_eq_of_mem _ <|
    let ⟨n, h⟩ := get_mem s
    ⟨n + 1, h⟩

@[simp]
/-
**Computation.get_thinkN** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：get_thinkN (n) : get (thinkN s n) = get s
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.get_eq_of_mem`：get_eq_of_mem {a} : a in s -> get s = a
· 使用定理 `Computation.thinkN_terminates`：∀ {α : Type u} (s : Computation α) [s.Ter
minates] (n : ℕ), (s.thinkN n).Terminates
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Computation.thinkN_mem`：∀ {α : Type u} {s : Computation α} {a : α} (n : 
ℕ), a ∈ s.thinkN n ↔ a ∈ s
· 使用定理 `Computation.get_mem`：get_mem : get s in s
-/
theorem get_thinkN (n) : get (thinkN s n) = get s :=
  get_eq_of_mem _ <| (thinkN_mem _).2 (get_mem _)
/-
**Computation.get_promises** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：get_promises : s ~> get s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.get_eq_of_mem`：get_eq_of_mem {a} : a in s -> get s = a
-/
theorem get_promises : s ~> get s := fun _ => get_eq_of_mem _
/-
**Computation.mem_of_promises** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：mem_of_promises {a} (p : s ~> a) : a in s
参数：p : s ~> a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mem_of_promises {a} (p : s ~> a) : a ∈ s := by
  obtain ⟨a', h⟩ := h
  rw [p h]
  exact h
/-
**Computation.get_eq_of_promises** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：get_eq_of_promises {a} : s ~> a -> get s = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.get_eq_of_mem`：get_eq_of_mem {a} : a in s -> get s = a
· 使用定理 `Computation.mem_of_promises`：mem_of_promises {a} (p : s ~> a) : a in s
-/
theorem get_eq_of_promises {a} : s ~> a → get s = a :=
  get_eq_of_mem _ ∘ mem_of_promises _

end get

/-- `Results s a n` completely characterizes a terminating computation:
  it asserts that `s` terminates after exactly `n` steps, with result `a`. -/
/-
**Computation.Results** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：Results (s : Computation α) (a : α) (n : Nat)
参数：s : Computation α；a : α；n : Nat。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s

--- 原说明 ---
`Results s a n` completely characterizes a terminating computation:
  it asserts that `s` terminates after exactly `n` steps, with result `a`.
-/
def Results (s : Computation α) (a : α) (n : ℕ) :=
  ∃ h : a ∈ s, @length _ s (terminates_of_mem h) = n
/-
**Computation.results_of_terminates** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：results_of_terminates (s : Computation α) [_T : Terminates s] : Results s 
(get s) (length s)
参数：s : Computation α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s
· 使用定理 `Computation.get_mem`：get_mem : get s in s
-/
theorem results_of_terminates (s : Computation α) [_T : Terminates s] :
    Results s (get s) (length s) :=
  ⟨get_mem _, rfl⟩
/-
**Computation.results_of_terminates'** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：results_of_terminates' (s : Computation α) [T : Terminates s] {a} (h : a i
n s) : Results s a (length s)
参数：s : Computation α；h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.get_eq_of_mem`：get_eq_of_mem {a} : a in s -> get s = a
· 使用定理 `Computation.results_of_terminates`：results_of_terminates (s : Computatio
n α) [_T : Terminates s] : Results s (get s) (length s)
-/
theorem results_of_terminates' (s : Computation α) [T : Terminates s] {a} (h : a ∈ s) :
    Results s a (length s) := by rw [← get_eq_of_mem _ h]; apply results_of_terminates
/-
**Computation.Results.mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation.Results`。
形式化陈述：∀ {α : Type u} {s : Computation α} {a : α} {n : ℕ}, s.Results a n → a ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s
-/
theorem Results.mem {s : Computation α} {a n} : Results s a n → a ∈ s
  | ⟨m, _⟩ => m
/-
**Computation.Results.terminates** 是 Mathlib 中的一个定理，位于命名空间 `Computation.Results`
。
形式化陈述：∀ {α : Type u} {s : Computation α} {a : α} {n : ℕ}, s.Results a n → s.Term
inates
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s
· 使用定理 `Computation.Results.mem`：∀ {α : Type u} {s : Computation α} {a : α} {n :
 ℕ}, s.Results a n → a ∈ s
-/
theorem Results.terminates {s : Computation α} {a n} (h : Results s a n) : Terminates s :=
  terminates_of_mem h.mem
/-
**Computation.Results.length** 是 Mathlib 中的一个定理，位于命名空间 `Computation.Results`。
形式化陈述：∀ {α : Type u} {s : Computation α} {a : α} {n : ℕ} [_T : s.Terminates], s.
Results a n → s.length = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s
-/
theorem Results.length {s : Computation α} {a n} [_T : Terminates s] : Results s a n → length s = n
  | ⟨_, h⟩ => h
/-
**Computation.Results.val_unique** 是 Mathlib 中的一个定理，位于命名空间 `Computation.Results`
。
形式化陈述：∀ {α : Type u} {s : Computation α} {a b : α} {m n : ℕ}, s.Results a m → s.
Results b n → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.mem_unique`：∀ {α : Type u} {s : Computation α} {a b : α}, a 
∈ s → b ∈ s → a = b
· 使用定理 `Computation.Results.mem`：∀ {α : Type u} {s : Computation α} {a : α} {n :
 ℕ}, s.Results a n → a ∈ s
-/
theorem Results.val_unique {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n) :
    a = b :=
  mem_unique h1.mem h2.mem
/-
**Computation.Results.len_unique** 是 Mathlib 中的一个定理，位于命名空间 `Computation.Results`
。
形式化陈述：∀ {α : Type u} {s : Computation α} {a b : α} {m n : ℕ}, s.Results a m → s.
Results b n → m = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.Results.terminates`：∀ {α : Type u} {s : Computation α} {a : 
α} {n : ℕ}, s.Results a n → s.Terminates
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.Results.length`：∀ {α : Type u} {s : Computation α} {a : α} {
n : ℕ} [_T : s.Terminates], s.Results a n → s.length = n
-/
theorem Results.len_unique {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n) :
    m = n := by have := h1.terminates; have := h2.terminates; rw [← h1.length, h2.length]
/-
**Computation.exists_results_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：exists_results_of_mem {s : Computation α} {a} (h : a in s) : exists n, Res
ults s a n
参数：h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s
· 使用定理 `Computation.results_of_terminates'`：results_of_terminates' (s : Computat
ion α) [T : Terminates s] {a} (h : a in s) : Results s a (length s)
-/
theorem exists_results_of_mem {s : Computation α} {a} (h : a ∈ s) : ∃ n, Results s a n :=
  haveI := terminates_of_mem h
  ⟨_, results_of_terminates' s h⟩

@[simp]
/-
**Computation.get_pure** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：get_pure (a : α) : get (pure a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.get_eq_of_mem`：get_eq_of_mem {a} : a in s -> get s = a
-/
theorem get_pure (a : α) : get (pure a) = a :=
  get_eq_of_mem _ ⟨0, rfl⟩

@[simp]
/-
**Computation.length_pure** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：length_pure (a : α) : length (pure a) = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Computation.terminates_def`：terminates_def (s : Computation α) : Termina
tes s ↔ exists n, (s.1 n).isSome
-/
theorem length_pure (a : α) : length (pure a) = 0 :=
  let h := Computation.ret_terminates a
  Nat.eq_zero_of_le_zero <| Nat.find_min' ((terminates_def (pure a)).1 h) rfl
/-
**Computation.results_pure** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：results_pure (a : α) : Results (pure a) a 0
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s
· 使用定理 `Computation.ret_mem`：ret_mem (a : α) : a in pure a
· 使用定理 `Computation.length_pure`：length_pure (a : α) : length (pure a) = 0
-/
theorem results_pure (a : α) : Results (pure a) a 0 :=
  ⟨ret_mem a, length_pure _⟩

@[simp]
/-
**Computation.length_think** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：length_think (s : Computation α) [h : Terminates s] : length (think s) = l
ength s + 1
参数：s : Computation α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Computation.think_terminates`：∀ {α : Type u} (s : Computation α) [s.Term
inates], s.think.Terminates
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Computation.terminates_def`：terminates_def (s : Computation α) : Termina
tes s ↔ exists n, (s.1 n).isSome
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
-/
theorem length_think (s : Computation α) [h : Terminates s] : length (think s) = length s + 1 := by
  apply le_antisymm
  · exact Nat.find_min' _ (Nat.find_spec ((terminates_def _).1 h))
  · have : (Option.isSome ((think s).val (length (think s))) : Prop) :=
      Nat.find_spec ((terminates_def _).1 s.think_terminates)
    revert this; rcases length (think s) with - | n <;> intro this
    · simp [think, Stream'.cons] at this
    · apply Nat.succ_le_succ
      apply Nat.find_min'
      apply this
/-
**Computation.results_think** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：results_think {s : Computation α} {a n} (h : Results s a n) : Results (thi
nk s) a (n + 1)
参数：h : Results s a n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s
· 使用定理 `Computation.think_mem`：∀ {α : Type u} {s : Computation α} {a : α}, a ∈ s
 → a ∈ s.think
· 使用定理 `Computation.Results.mem`：∀ {α : Type u} {s : Computation α} {a : α} {n :
 ℕ}, s.Results a n → a ∈ s
· 使用定理 `Computation.Results.terminates`：∀ {α : Type u} {s : Computation α} {a : 
α} {n : ℕ}, s.Results a n → s.Terminates
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.think_terminates`：∀ {α : Type u} (s : Computation α) [s.Term
inates], s.think.Terminates
· 使用定理 `Computation.length_think`：length_think (s : Computation α) [h : Terminat
es s] : length (think s) = length s + 1
· 使用定理 `Computation.Results.length`：∀ {α : Type u} {s : Computation α} {a : α} {
n : ℕ} [_T : s.Terminates], s.Results a n → s.length = n
-/
theorem results_think {s : Computation α} {a n} (h : Results s a n) : Results (think s) a (n + 1) :=
  haveI := h.terminates
  ⟨think_mem h.mem, by rw [length_think, h.length]⟩
/-
**Computation.of_results_think** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：of_results_think {s : Computation α} {a n} (h : Results (think s) a n) : e
xists m, Results s a m ∧ n = m + 1
参数：h : Results (think s) a n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.of_think_terminates`：∀ {α : Type u} {s : Computation α}, s.t
hink.Terminates → s.Terminates
· 使用定理 `Computation.Results.terminates`：∀ {α : Type u} {s : Computation α} {a : 
α} {n : ℕ}, s.Results a n → s.Terminates
· 使用定理 `Computation.results_of_terminates'`：results_of_terminates' (s : Computat
ion α) [T : Terminates s] {a} (h : a in s) : Results s a (length s)
· 使用定理 `Computation.of_think_mem`：∀ {α : Type u} {s : Computation α} {a : α}, a 
∈ s.think → a ∈ s
· 使用定理 `Computation.Results.mem`：∀ {α : Type u} {s : Computation α} {a : α} {n :
 ℕ}, s.Results a n → a ∈ s
· 使用定理 `Computation.Results.len_unique`：∀ {α : Type u} {s : Computation α} {a b 
: α} {m n : ℕ}, s.Results a m → s.Results b n → m = n
· 使用定理 `Computation.results_think`：results_think {s : Computation α} {a n} (h : 
Results s a n) : Results (think s) a (n + 1)
-/
theorem of_results_think {s : Computation α} {a n} (h : Results (think s) a n) :
    ∃ m, Results s a m ∧ n = m + 1 := by
  have := of_think_terminates h.terminates
  have := results_of_terminates' _ (of_think_mem h.mem)
  exact ⟨_, this, Results.len_unique h (results_think this)⟩

@[simp]
/-
**Computation.results_think_iff** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：results_think_iff {s : Computation α} {a n} : Results (think s) a (n + 1) 
↔ Results s a n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.of_results_think`：of_results_think {s : Computation α} {a n}
 (h : Results (think s) a n) : exists m, Results s a m ∧ n = m + 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.results_think`：results_think {s : Computation α} {a n} (h : 
Results s a n) : Results (think s) a (n + 1)
-/
theorem results_think_iff {s : Computation α} {a n} : Results (think s) a (n + 1) ↔ Results s a n :=
  ⟨fun h => by
    let ⟨n', r, e⟩ := of_results_think h
    injection e with h'; rwa [h'], results_think⟩
/-
**Computation.results_thinkN** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} {s : Computation α} {a : α} {m : ℕ} (n : ℕ), s.Results a m 
→ (s.thinkN n).Results a (m + n)
参数：n : ℕ；s.thinkN n；m + n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem results_thinkN {s : Computation α} {a m} :
    ∀ n, Results s a m → Results (thinkN s n) a (m + n)
  | 0, h => h
  | n + 1, h => results_think (results_thinkN n h)
/-
**Computation.results_thinkN_pure** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：results_thinkN_pure (a : α) (n) : Results (thinkN (pure a) n) a n
参数：a : α；n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.results_thinkN`：∀ {α : Type u} {s : Computation α} {a : α} {
m : ℕ} (n : ℕ), s.Results a m → (s.thinkN n).Results a (m + n)
· 使用定理 `Computation.results_pure`：results_pure (a : α) : Results (pure a) a 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
-/
theorem results_thinkN_pure (a : α) (n) : Results (thinkN (pure a) n) a n := by
  have := results_thinkN n (results_pure a); rwa [Nat.zero_add] at this

@[simp]
/-
**Computation.length_thinkN** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：length_thinkN (s : Computation α) [_h : Terminates s] (n) : length (thinkN
 s n) = length s + n
参数：s : Computation α；n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.Results.length`：∀ {α : Type u} {s : Computation α} {a : α} {
n : ℕ} [_T : s.Terminates], s.Results a n → s.length = n
· 使用定理 `Computation.thinkN_terminates`：∀ {α : Type u} (s : Computation α) [s.Ter
minates] (n : ℕ), (s.thinkN n).Terminates
· 使用定理 `Computation.results_thinkN`：∀ {α : Type u} {s : Computation α} {a : α} {
m : ℕ} (n : ℕ), s.Results a m → (s.thinkN n).Results a (m + n)
· 使用定理 `Computation.results_of_terminates`：results_of_terminates (s : Computatio
n α) [_T : Terminates s] : Results s (get s) (length s)
-/
theorem length_thinkN (s : Computation α) [_h : Terminates s] (n) :
    length (thinkN s n) = length s + n :=
  (results_thinkN n (results_of_terminates _)).length
/-
**Computation.eq_thinkN** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：eq_thinkN {s : Computation α} {a n} (h : Results s a n) : s = thinkN (pure
 a) n
参数：h : Results s a n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.eq_of_pure_mem`：eq_of_pure_mem {a a' : α} (h : a' in pure a)
 : a' = a
· 使用定理 `Computation.Results.mem`：∀ {α : Type u} {s : Computation α} {a : α} {n :
 ℕ}, s.Results a n → a ∈ s
· 使用定理 `Computation.of_results_think`：of_results_think {s : Computation α} {a n}
 (h : Results (think s) a n) : exists m, Results s a m ∧ n = m + 1
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Computation.Results.len_unique`：∀ {α : Type u} {s : Computation α} {a b 
: α} {m n : ℕ}, s.Results a m → s.Results b n → m = n
· 使用定理 `Computation.results_pure`：results_pure (a : α) : Results (pure a) a 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Computation.results_think_iff`：results_think_iff {s : Computation α} {a 
n} : Results (think s) a (n + 1) ↔ Results s a n
-/
theorem eq_thinkN {s : Computation α} {a n} (h : Results s a n) : s = thinkN (pure a) n := by
  induction n generalizing s with | zero | succ n IH <;>
  induction s using recOn with | pure a' | think s
  · rw [← eq_of_pure_mem h.mem]
    rfl
  · obtain ⟨n, h⟩ := of_results_think h
    cases h
    contradiction
  · have := h.len_unique (results_pure _)
    contradiction
  · rw [IH (results_think_iff.1 h)]
    rfl
/-
**Computation.eq_thinkN'** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：eq_thinkN' (s : Computation α) [_h : Terminates s] : s = thinkN (pure (get
 s)) (length s)
参数：s : Computation α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.eq_thinkN`：eq_thinkN {s : Computation α} {a n} (h : Results 
s a n) : s = thinkN (pure a) n
· 使用定理 `Computation.results_of_terminates`：results_of_terminates (s : Computatio
n α) [_T : Terminates s] : Results s (get s) (length s)
-/
theorem eq_thinkN' (s : Computation α) [_h : Terminates s] :
    s = thinkN (pure (get s)) (length s) :=
  eq_thinkN (results_of_terminates _)

/-- Recursor based on membership -/
/-
**Computation.memRecOn** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：memRecOn {C : Computation α -> Sort v} {a s} (M : a in s) (h1 : C (pure a)
) (h2 : forall s, C s -> C (think s)) : C s
参数：M : a in s；h1 : C (pure a)；h2 : forall s, C s -> C (think s)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s

--- 原说明 ---
Recursor based on membership
-/
def memRecOn {C : Computation α → Sort v} {a s} (M : a ∈ s) (h1 : C (pure a))
    (h2 : ∀ s, C s → C (think s)) : C s := by
  haveI T := terminates_of_mem M
  rw [eq_thinkN' s, get_eq_of_mem s M]
  generalize length s = n
  induction n with | zero => exact h1 | succ n IH => exact h2 _ IH

/-- Recursor based on assertion of `Terminates` -/
/-
**Computation.terminatesRecOn** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：terminatesRecOn {C : Computation α -> Sort v} (s) [Terminates s] (h1 : for
all a, C (pure a)) (h2 : forall s, C s -> C (think s)) : C s
参数：s；h1 : forall a, C (pure a)；h2 : forall s, C s -> C (think s)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.get_mem`：get_mem : get s in s

--- 原说明 ---
Recursor based on assertion of `Terminates`
-/
def terminatesRecOn
    {C : Computation α → Sort v}
    (s) [Terminates s]
    (h1 : ∀ a, C (pure a))
    (h2 : ∀ s, C s → C (think s)) : C s :=
  memRecOn (get_mem s) (h1 _) h2

/-- Map a function on the result of a computation. -/
/-
**Computation.map** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：{α : Type u} → {β : Type v} → (α → β) → Computation α → Computation β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a function on the result of a computation.
-/
def map (f : α → β) : Computation α → Computation β
  | ⟨s, al⟩ =>
    ⟨s.map fun o => Option.casesOn o none (some ∘ f), fun n b => by
      dsimp [Stream'.map, Stream'.get]
      rcases e : s n with - | a <;> intro h
      · contradiction
      · rw [al e]; exact h⟩

/-- bind over a `Sum` of `Computation` -/
/-
**Computation.Bind.g** 是 Mathlib 中的一个定义，位于命名空间 `Computation.Bind`。
形式化陈述：{α : Type u} → {β : Type v} → β ⊕ Computation β → β ⊕ Computation α ⊕ Comp
utation β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
bind over a `Sum` of `Computation`
-/
def Bind.g : β ⊕ Computation β → β ⊕ (Computation α ⊕ Computation β)
  | Sum.inl b => Sum.inl b
  | Sum.inr cb' => Sum.inr <| Sum.inr cb'

/-- bind over a function mapping `α` to a `Computation` -/
/-
**Computation.Bind.f** 是 Mathlib 中的一个定义，位于命名空间 `Computation.Bind`。
形式化陈述：{α : Type u} → {β : Type v} → (α → Computation β) → Computation α ⊕ Comput
ation β → β ⊕ Computation α ⊕ Computation β
参数：α → Computation β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
bind over a function mapping `α` to a `Computation`
-/
def Bind.f (f : α → Computation β) :
    Computation α ⊕ Computation β → β ⊕ (Computation α ⊕ Computation β)
  | Sum.inl ca =>
    match destruct ca with
    | Sum.inl a => Bind.g <| destruct (f a)
    | Sum.inr ca' => Sum.inr <| Sum.inl ca'
  | Sum.inr cb => Bind.g <| destruct cb

/-- Compose two computations into a monadic `bind` operation. -/
/-
**Computation.bind** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：bind (c : Computation α) (f : α -> Computation β) : Computation β
参数：c : Computation α；f : α -> Computation β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose two computations into a monadic `bind` operation.
-/
def bind (c : Computation α) (f : α → Computation β) : Computation β :=
  corec (Bind.f f) (Sum.inl c)
/-
**Computation.** 是 Mathlib 中的一个实例，位于命名空间 `Computation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bind Computation :=
  ⟨@bind⟩
/-
**Computation.has_bind_eq_bind** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：has_bind_eq_bind {β} (c : Computation α) (f : α -> Computation β) : c >>= 
f = bind c f
参数：c : Computation α；f : α -> Computation β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem has_bind_eq_bind {β} (c : Computation α) (f : α → Computation β) : c >>= f = bind c f :=
  rfl

/-- Flatten a computation of computations into a single computation. -/
/-
**Computation.join** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：join (c : Computation (Computation α)) : Computation α
参数：c : Computation (Computation α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Flatten a computation of computations into a single computation.
-/
def join (c : Computation (Computation α)) : Computation α :=
  c >>= id

@[simp]
/-
**Computation.map_pure** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：map_pure (f : α -> β) (a) : map f (pure a) = pure (f a)
参数：f : α -> β；a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_pure (f : α → β) (a) : map f (pure a) = pure (f a) :=
  rfl

@[simp]
/-
**Computation.map_think** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} {β : Type v} (f : α → β) (s : Computation α), Computation.m
ap f s.think = (Computation.map f s).think
参数：f : α → β；s : Computation α；Computation.map f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.map_cons`：map_cons (a : α) (s : Stream' α) : map f (a::s) = f a:
:map f s
-/
theorem map_think (f : α → β) : ∀ s, map f (think s) = think (map f s)
  | ⟨s, al⟩ => by apply Subtype.ext; dsimp [think, map]; rw [Stream'.map_cons]

@[simp]
/-
**Computation.destruct_map** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：destruct_map (f : α -> β) (s) : destruct (map f s) = lmap f (rmap (map f) 
(destruct s))
参数：f : α -> β；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.map_think`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Comp
utation α), Computation.map f s.think = (Computation.map f s).think
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
-/
theorem destruct_map (f : α → β) (s) : destruct (map f s) = lmap f (rmap (map f) (destruct s)) := by
  induction s using recOn <;> simp

@[simp]
/-
**Computation.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：map_id : forall s : Computation α, map id s = s | ⟨f, al⟩ => by apply Subt
ype.ext; simp only [map, comp_apply, id_eq] have e : @Option.rec α (fun _ => Opt
ion α) none some = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_id : ∀ s : Computation α, map id s = s
  | ⟨f, al⟩ => by
    apply Subtype.ext; simp only [map, comp_apply, id_eq]
    have e : @Option.rec α (fun _ => Option α) none some = id := by ext ⟨⟩ <;> rfl
    have h : ((fun x : Option α => x) = id) := rfl
    simp [e, h, Stream'.map_id]
/-
**Computation.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : β → γ) (s : Comp
utation α),   Computation.map (g ∘ f) s = Computation.map g (Computation.map f s
)
参数：f : α → β；g : β → γ；s : Computation α；g ∘ f；Computation.map f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_comp (f : α → β) (g : β → γ) : ∀ s : Computation α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.ext; dsimp [map]
    apply congr_arg fun f : _ → Option γ => Stream'.map f s
    ext ⟨⟩ <;> rfl

@[simp]
/-
**Computation.ret_bind** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：ret_bind (a) (f : α -> Computation β) : bind (pure a) f = f a
参数：a；f : α -> Computation β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.eq_of_bisim`：eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} 
(r : s₁ ~ s₂) : s₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.corec_eq`：corec_eq (f : β -> α oplus β) (b : β) : destruct (
corec f b) = rmap (corec f) (f b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem ret_bind (a) (f : α → Computation β) : bind (pure a) f = f a := by
  apply
    eq_of_bisim fun c₁ c₂ => c₁ = bind (pure a) f ∧ c₂ = f a ∨ c₁ = corec (Bind.f f) (Sum.inr c₂)
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, _, Or.inl ⟨rfl, rfl⟩ =>
      simp only [BisimO, bind, Bind.f, corec_eq, rmap, destruct_pure]
      rcases destruct (f a) with b | cb <;> simp [Bind.g]
    | _, c, Or.inr rfl =>
      simp only [BisimO, Bind.f, corec_eq, rmap]
      rcases destruct c with b | cb <;> simp [Bind.g]
  · simp

@[simp]
/-
**Computation.think_bind** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：think_bind (c) (f : α -> Computation β) : bind (think c) f = think (bind c
 f)
参数：c；f : α -> Computation β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.destruct_eq_think`：destruct_eq_think {s : Computation α} {s'
} : destruct s = Sum.inr s' -> s = think s'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.corec_eq`：corec_eq (f : β -> α oplus β) (b : β) : destruct (
corec f b) = rmap (corec f) (f b)
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem think_bind (c) (f : α → Computation β) : bind (think c) f = think (bind c f) :=
  destruct_eq_think <| by simp [bind, Bind.f]

@[simp]
/-
**Computation.bind_pure** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：bind_pure (f : α -> β) (s) : bind s (pure ∘ f) = map f s
参数：f : α -> β；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.eq_of_bisim`：eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} 
(r : s₁ ~ s₂) : s₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Computation.ret_bind`：ret_bind (a) (f : α -> Computation β) : bind (pure
 a) f = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Computation.think_bind`：think_bind (c) (f : α -> Computation β) : bind (
think c) f = think (bind c f)
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
· 使用定理 `Computation.map_think`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Comp
utation α), Computation.map f s.think = (Computation.map f s).think
-/
theorem bind_pure (f : α → β) (s) : bind s (pure ∘ f) = map f s := by
  apply eq_of_bisim fun c₁ c₂ => c₁ = c₂ ∨ ∃ s, c₁ = bind s (pure ∘ f) ∧ c₂ = map f s
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => rcases destruct c₂ with b | cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      induction s using recOn with
      | pure s => simp
      | think s => simpa using Or.inr ⟨s, rfl, rfl⟩
  · exact Or.inr ⟨s, rfl, rfl⟩

@[simp]
/-
**Computation.bind_pure'** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：bind_pure' (s : Computation α) : bind s pure = s
参数：s : Computation α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.map_id`：map_id : forall s : Computation α, map id s = s | ⟨f
, al⟩ => by apply Subtype.ext; simp only [map, comp_apply, id_eq] have e : @Opti
on.rec α…
· 使用定理 `Computation.bind_pure`：bind_pure (f : α -> β) (s) : bind s (pure ∘ f) = 
map f s
-/
theorem bind_pure' (s : Computation α) : bind s pure = s := by
  simpa using bind_pure id s

@[simp]
/-
**Computation.bind_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：bind_assoc (s : Computation α) (f : α -> Computation β) (g : β -> Computat
ion γ) : bind (bind s f) g = bind s fun x : α => bind (f x) g
参数：s : Computation α；f : α -> Computation β；g : β -> Computation γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.eq_of_bisim`：eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} 
(r : s₁ ~ s₂) : s₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Computation.ret_bind`：ret_bind (a) (f : α -> Computation β) : bind (pure
 a) f = f a
· 使用定理 `Computation.think_bind`：think_bind (c) (f : α -> Computation β) : bind (
think c) f = think (bind c f)
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
-/
theorem bind_assoc (s : Computation α) (f : α → Computation β) (g : β → Computation γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  apply
    eq_of_bisim fun c₁ c₂ =>
      c₁ = c₂ ∨ ∃ s, c₁ = bind (bind s f) g ∧ c₂ = bind s fun x : α => bind (f x) g
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => rcases destruct c₂ with b | cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      induction s using recOn with
      | pure s =>
        simp only [BisimO, ret_bind]; generalize f s = fs
        induction fs using recOn with
        | pure t => rw [ret_bind]; rcases destruct (g t) with b | cb <;> simp
        | think => simp
      | think s => simpa [BisimO] using Or.inr ⟨s, rfl, rfl⟩
  · exact Or.inr ⟨s, rfl, rfl⟩
/-
**Computation.results_bind** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：results_bind {s : Computation α} {f : α -> Computation β} {a b m n} (h1 : 
Results s a m) (h2 : Results (f a) b n) : Results (bind s f) b (n + m)
参数：h1 : Results s a m；h2 : Results (f a) b n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.Results.mem`：∀ {α : Type u} {s : Computation α} {a : α} {n :
 ℕ}, s.Results a n → a ∈ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.ret_bind`：ret_bind (a) (f : α -> Computation β) : bind (pure
 a) f = f a
· 使用定理 `Computation.Results.len_unique`：∀ {α : Type u} {s : Computation α} {a b 
: α} {m n : ℕ}, s.Results a m → s.Results b n → m = n
· 使用定理 `Computation.results_pure`：results_pure (a : α) : Results (pure a) a 0
· 使用定理 `Computation.think_bind`：think_bind (c) (f : α -> Computation β) : bind (
think c) f = think (bind c f)
· 使用定理 `Computation.of_results_think`：of_results_think {s : Computation α} {a n}
 (h : Results (think s) a n) : exists m, Results s a m ∧ n = m + 1
· 使用定理 `Computation.results_think`：results_think {s : Computation α} {a n} (h : 
Results s a n) : Results (think s) a (n + 1)
-/
theorem results_bind {s : Computation α} {f : α → Computation β} {a b m n} (h1 : Results s a m)
    (h2 : Results (f a) b n) : Results (bind s f) b (n + m) := by
  have := h1.mem; revert m
  apply memRecOn this _ fun s IH => _
  · intro _ h1
    rw [ret_bind]
    rw [h1.len_unique (results_pure _)]
    exact h2
  · intro _ h3 _ h1
    rw [think_bind]
    obtain ⟨m', h⟩ := of_results_think h1
    obtain ⟨h1, e⟩ := h
    rw [e]
    exact results_think (h3 h1)
/-
**Computation.mem_bind** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：mem_bind {s : Computation α} {f : α -> Computation β} {a b} (h1 : a in s) 
(h2 : b in f a) : b in bind s f
参数：h1 : a in s；h2 : b in f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.exists_results_of_mem`：exists_results_of_mem {s : Computatio
n α} {a} (h : a in s) : exists n, Results s a n
· 使用定理 `Computation.Results.mem`：∀ {α : Type u} {s : Computation α} {a : α} {n :
 ℕ}, s.Results a n → a ∈ s
· 使用定理 `Computation.results_bind`：results_bind {s : Computation α} {f : α -> Com
putation β} {a b m n} (h1 : Results s a m) (h2 : Results (f a) b n) : Results (b
ind s f) b (n …
-/
theorem mem_bind {s : Computation α} {f : α → Computation β} {a b} (h1 : a ∈ s) (h2 : b ∈ f a) :
    b ∈ bind s f :=
  let ⟨_, h1⟩ := exists_results_of_mem h1
  let ⟨_, h2⟩ := exists_results_of_mem h2
  (results_bind h1 h2).mem
/-
**Computation.terminates_bind** 是 Mathlib 中的一个实例，位于命名空间 `Computation`。
形式化陈述：terminates_bind (s : Computation α) (f : α -> Computation β) [Terminates s
] [Terminates (f (get s))] : Terminates (bind s f)
参数：s : Computation α；f : α -> Computation β；f (get s)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s
· 使用定理 `Computation.mem_bind`：mem_bind {s : Computation α} {f : α -> Computation
 β} {a b} (h1 : a in s) (h2 : b in f a) : b in bind s f
· 使用定理 `Computation.get_mem`：get_mem : get s in s
-/
instance terminates_bind (s : Computation α) (f : α → Computation β) [Terminates s]
    [Terminates (f (get s))] : Terminates (bind s f) :=
  terminates_of_mem (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp]
/-
**Computation.get_bind** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：get_bind (s : Computation α) (f : α -> Computation β) [Terminates s] [Term
inates (f (get s))] : get (bind s f) = get (f (get s))
参数：s : Computation α；f : α -> Computation β；f (get s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.get_eq_of_mem`：get_eq_of_mem {a} : a in s -> get s = a
· 使用定理 `Computation.mem_bind`：mem_bind {s : Computation α} {f : α -> Computation
 β} {a b} (h1 : a in s) (h2 : b in f a) : b in bind s f
· 使用定理 `Computation.get_mem`：get_mem : get s in s
-/
theorem get_bind (s : Computation α) (f : α → Computation β) [Terminates s]
    [Terminates (f (get s))] : get (bind s f) = get (f (get s)) :=
  get_eq_of_mem _ (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp]
/-
**Computation.length_bind** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：length_bind (s : Computation α) (f : α -> Computation β) [_T1 : Terminates
 s] [_T2 : Terminates (f (get s))] : length (bind s f) = length (f (get s)) + le
ngth s
参数：s : Computation α；f : α -> Computation β；f (get s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.Results.len_unique`：∀ {α : Type u} {s : Computation α} {a b 
: α} {m n : ℕ}, s.Results a m → s.Results b n → m = n
· 使用定理 `Computation.results_of_terminates`：results_of_terminates (s : Computatio
n α) [_T : Terminates s] : Results s (get s) (length s)
· 使用定理 `Computation.results_bind`：results_bind {s : Computation α} {f : α -> Com
putation β} {a b m n} (h1 : Results s a m) (h2 : Results (f a) b n) : Results (b
ind s f) b (n …
-/
theorem length_bind (s : Computation α) (f : α → Computation β) [_T1 : Terminates s]
    [_T2 : Terminates (f (get s))] : length (bind s f) = length (f (get s)) + length s :=
  (results_of_terminates _).len_unique <|
    results_bind (results_of_terminates _) (results_of_terminates _)
/-
**Computation.of_results_bind** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：of_results_bind {s : Computation α} {f : α -> Computation β} {b k} : Resul
ts (bind s f) b k -> exists a m n, Results s a m ∧ Results (f a) b n ∧ k = n + m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.results_pure`：results_pure (a : α) : Results (pure a) a 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.ret_bind`：ret_bind (a) (f : α -> Computation β) : bind (pure
 a) f = f a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Computation.eq_thinkN`：eq_thinkN {s : Computation α} {a n} (h : Results 
s a n) : s = thinkN (pure a) n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Computation.think_bind`：think_bind (c) (f : α -> Computation β) : bind (
think c) f = think (bind c f)
· 使用定理 `Computation.results_think`：results_think {s : Computation α} {a n} (h : 
Results s a n) : Results (think s) a (n + 1)
-/
theorem of_results_bind {s : Computation α} {f : α → Computation β} {b k} :
    Results (bind s f) b k → ∃ a m n, Results s a m ∧ Results (f a) b n ∧ k = n + m := by
  induction k generalizing s with | zero | succ n IH <;>
  induction s using recOn with intro h | pure a | think s'
  · simp only [ret_bind] at h
    exact ⟨_, _, _, results_pure _, h, rfl⟩
  · have := congr_arg head (eq_thinkN h)
    contradiction
  · simp only [ret_bind] at h
    exact ⟨_, _, n + 1, results_pure _, h, rfl⟩
  · simp only [think_bind, results_think_iff] at h
    let ⟨a, m, n', h1, h2, e'⟩ := IH h
    rw [e']
    exact ⟨a, m.succ, n', results_think h1, h2, rfl⟩
/-
**Computation.exists_of_mem_bind** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：exists_of_mem_bind {s : Computation α} {f : α -> Computation β} {b} (h : b
 in bind s f) : exists a in s, b in f a
参数：h : b in bind s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.exists_results_of_mem`：exists_results_of_mem {s : Computatio
n α} {a} (h : a in s) : exists n, Results s a n
· 使用定理 `Computation.of_results_bind`：of_results_bind {s : Computation α} {f : α 
-> Computation β} {b k} : Results (bind s f) b k -> exists a m n, Results s a m 
∧ Results (f a) b…
· 使用定理 `Computation.Results.mem`：∀ {α : Type u} {s : Computation α} {a : α} {n :
 ℕ}, s.Results a n → a ∈ s
-/
theorem exists_of_mem_bind {s : Computation α} {f : α → Computation β} {b} (h : b ∈ bind s f) :
    ∃ a ∈ s, b ∈ f a :=
  let ⟨_, h⟩ := exists_results_of_mem h
  let ⟨a, _, _, h1, h2, _⟩ := of_results_bind h
  ⟨a, h1.mem, h2.mem⟩
/-
**Computation.bind_promises** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：bind_promises {s : Computation α} {f : α -> Computation β} {a b} (h1 : s ~
> a) (h2 : f a ~> b) : bind s f ~> b
参数：h1 : s ~> a；h2 : f a ~> b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.exists_of_mem_bind`：exists_of_mem_bind {s : Computation α} {
f : α -> Computation β} {b} (h : b in bind s f) : exists a in s, b in f a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bind_promises {s : Computation α} {f : α → Computation β} {a b} (h1 : s ~> a)
    (h2 : f a ~> b) : bind s f ~> b := fun b' bB => by
  rcases exists_of_mem_bind bB with ⟨a', a's, ba'⟩
  rw [← h1 a's] at ba'; exact h2 ba'
/-
**Computation.monad** 是 Mathlib 中的一个实例，位于命名空间 `Computation`。
形式化陈述：monad : Monad Computation where map
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monad : Monad Computation where
  map := @map
  pure := @pure
  bind := @bind
/-
**Computation.** 是 Mathlib 中的一个实例，位于命名空间 `Computation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad Computation := LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_pure)
  (pure_bind := @ret_bind)
  (bind_assoc := @bind_assoc)
/-
**Computation.has_map_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：has_map_eq_map {β} (f : α -> β) (c : Computation α) : f < > c = map f c
参数：f : α -> β；c : Computation α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem has_map_eq_map {β} (f : α → β) (c : Computation α) : f <$> c = map f c :=
  rfl

@[simp]
/-
**Computation.pure_def** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：pure_def (a) : (return a : Computation α) = pure a
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_def (a) : (return a : Computation α) = pure a :=
  rfl

@[simp]
/-
**Computation.map_pure'** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：map_pure' {α β} : forall (f : α -> β) (a), f < > pure a = pure (f a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.map_pure`：map_pure (f : α -> β) (a) : map f (pure a) = pure 
(f a)
-/
theorem map_pure' {α β} : ∀ (f : α → β) (a), f <$> pure a = pure (f a) :=
  map_pure

@[simp]
/-
**Computation.map_think'** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：map_think' {α β} : forall (f : α -> β) (s), f < > think s = think (f <$> s
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.map_think`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Comp
utation α), Computation.map f s.think = (Computation.map f s).think
-/
theorem map_think' {α β} : ∀ (f : α → β) (s), f <$> think s = think (f <$> s) :=
  map_think
/-
**Computation.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：mem_map (f : α -> β) {a} {s : Computation α} (m : a in s) : f a in map f s
参数：f : α -> β；m : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.bind_pure`：bind_pure (f : α -> β) (s) : bind s (pure ∘ f) = 
map f s
· 使用定理 `Computation.mem_bind`：mem_bind {s : Computation α} {f : α -> Computation
 β} {a b} (h1 : a in s) (h2 : b in f a) : b in bind s f
· 使用定理 `Computation.ret_mem`：ret_mem (a : α) : a in pure a
-/
theorem mem_map (f : α → β) {a} {s : Computation α} (m : a ∈ s) : f a ∈ map f s := by
  rw [← bind_pure]; apply mem_bind m; apply ret_mem
/-
**Computation.exists_of_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：exists_of_mem_map {f : α -> β} {b : β} {s : Computation α} (h : b in map f
 s) : exists a, a in s ∧ f a = b
参数：h : b in map f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.exists_of_mem_bind`：exists_of_mem_bind {s : Computation α} {
f : α -> Computation β} {b} (h : b in bind s f) : exists a in s, b in f a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.bind_pure`：bind_pure (f : α -> β) (s) : bind s (pure ∘ f) = 
map f s
· 使用定理 `Computation.mem_unique`：∀ {α : Type u} {s : Computation α} {a b : α}, a 
∈ s → b ∈ s → a = b
· 使用定理 `Computation.ret_mem`：ret_mem (a : α) : a in pure a
-/
theorem exists_of_mem_map {f : α → β} {b : β} {s : Computation α} (h : b ∈ map f s) :
    ∃ a, a ∈ s ∧ f a = b := by
  rw [← bind_pure] at h
  let ⟨a, as, fb⟩ := exists_of_mem_bind h
  exact ⟨a, as, mem_unique (ret_mem _) fb⟩
/-
**Computation.terminates_map** 是 Mathlib 中的一个实例，位于命名空间 `Computation`。
形式化陈述：terminates_map (f : α -> β) (s : Computation α) [Terminates s] : Terminate
s (map f s)
参数：f : α -> β；s : Computation α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.bind_pure`：bind_pure (f : α -> β) (s) : bind s (pure ∘ f) = 
map f s
· 使用定理 `Computation.terminates_of_mem`：terminates_of_mem {s : Computation α} {a 
: α} (h : a in s) : Terminates s
· 使用定理 `Computation.mem_bind`：mem_bind {s : Computation α} {f : α -> Computation
 β} {a b} (h1 : a in s) (h2 : b in f a) : b in bind s f
· 使用定理 `Computation.get_mem`：get_mem : get s in s
-/
instance terminates_map (f : α → β) (s : Computation α) [Terminates s] : Terminates (map f s) := by
  rw [← bind_pure]; exact terminates_of_mem (mem_bind (get_mem s) (get_mem (α := β) (f (get s))))
/-
**Computation.terminates_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：terminates_map_iff (f : α -> β) (s : Computation α) : Terminates (map f s)
 ↔ Terminates s
参数：f : α -> β；s : Computation α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.exists_of_mem_map`：exists_of_mem_map {f : α -> β} {b : β} {s
 : Computation α} (h : b in map f s) : exists a, a in s ∧ f a = b
-/
theorem terminates_map_iff (f : α → β) (s : Computation α) : Terminates (map f s) ↔ Terminates s :=
  ⟨fun ⟨⟨_, h⟩⟩ =>
    let ⟨_, h1, _⟩ := exists_of_mem_map h
    ⟨⟨_, h1⟩⟩,
    @Computation.terminates_map _ _ _ _⟩

-- Parallel computation
/-- `c₁ <|> c₂` calculates `c₁` and `c₂` simultaneously, returning
  the first one that gives a result. -/
/-
**Computation.orElse** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：orElse (c₁ : Computation α) (c₂ : Unit -> Computation α) : Computation α
参数：c₁ : Computation α；c₂ : Unit -> Computation α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`c₁ <|> c₂` calculates `c₁` and `c₂` simultaneously, returning
  the first one that gives a result.
-/
def orElse (c₁ : Computation α) (c₂ : Unit → Computation α) : Computation α :=
  @Computation.corec α (Computation α × Computation α)
    (fun ⟨c₁, c₂⟩ =>
      match destruct c₁ with
      | Sum.inl a => Sum.inl a
      | Sum.inr c₁' =>
        match destruct c₂ with
        | Sum.inl a => Sum.inl a
        | Sum.inr c₂' => Sum.inr (c₁', c₂'))
    (c₁, c₂ ())
/-
**Computation.instAlternativeComputation** 是 Mathlib 中的一个实例，位于命名空间 `Computation`
。
形式化陈述：instAlternativeComputation : Alternative Computation
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlternativeComputation : Alternative Computation :=
  { Computation.monad with
    orElse := @orElse
    failure := @empty }

@[simp]
/-
**Computation.ret_orElse** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：ret_orElse (a : α) (c₂ : Computation α) : (pure a <|> c₂) = pure a
参数：a : α；c₂ : Computation α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.destruct_eq_pure`：destruct_eq_pure {s : Computation α} {a : 
α} : destruct s = Sum.inl a -> s = pure a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.corec_eq`：corec_eq (f : β -> α oplus β) (b : β) : destruct (
corec f b) = rmap (corec f) (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ret_orElse (a : α) (c₂ : Computation α) : (pure a <|> c₂) = pure a :=
  destruct_eq_pure <| by
    unfold_projs
    simp [orElse]

@[simp]
/-
**Computation.orElse_pure** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：orElse_pure (c₁ : Computation α) (a : α) : (think c₁ <|> pure a) = pure a
参数：c₁ : Computation α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.destruct_eq_pure`：destruct_eq_pure {s : Computation α} {a : 
α} : destruct s = Sum.inl a -> s = pure a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.corec_eq`：corec_eq (f : β -> α oplus β) (b : β) : destruct (
corec f b) = rmap (corec f) (f b)
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orElse_pure (c₁ : Computation α) (a : α) : (think c₁ <|> pure a) = pure a :=
  destruct_eq_pure <| by
    unfold_projs
    simp [orElse]

@[simp]
/-
**Computation.orElse_think** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：orElse_think (c₁ c₂ : Computation α) : (think c₁ <|> think c₂) = think (c₁
 <|> c₂)
参数：c₁ c₂ : Computation α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.destruct_eq_think`：destruct_eq_think {s : Computation α} {s'
} : destruct s = Sum.inr s' -> s = think s'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.corec_eq`：corec_eq (f : β -> α oplus β) (b : β) : destruct (
corec f b) = rmap (corec f) (f b)
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orElse_think (c₁ c₂ : Computation α) : (think c₁ <|> think c₂) = think (c₁ <|> c₂) :=
  destruct_eq_think <| by
    unfold_projs
    simp [orElse]

@[simp]
/-
**Computation.empty_orElse** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：empty_orElse (c) : (empty α <|> c) = c
参数：c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.eq_of_bisim`：eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} 
(r : s₁ ~ s₂) : s₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.think_empty`：think_empty : empty α = think (empty α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Computation.orElse_pure`：orElse_pure (c₁ : Computation α) (a : α) : (thi
nk c₁ <|> pure a) = pure a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Computation.orElse_think`：orElse_think (c₁ c₂ : Computation α) : (think 
c₁ <|> think c₂) = think (c₁ <|> c₂)
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
-/
theorem empty_orElse (c) : (empty α <|> c) = c := by
  apply eq_of_bisim (fun c₁ c₂ => (empty α <|> c₂) = c₁) _ rfl
  intro s' s h; rw [← h]
  induction s using recOn with rw [think_empty]
  | pure s => simp
  | think s => simp only [BisimO, orElse_think, destruct_think]; rw [← think_empty]

@[simp]
/-
**Computation.orElse_empty** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：orElse_empty (c : Computation α) : (c <|> empty α) = c
参数：c : Computation α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.eq_of_bisim`：eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} 
(r : s₁ ~ s₂) : s₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.think_empty`：think_empty : empty α = think (empty α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Computation.ret_orElse`：ret_orElse (a : α) (c₂ : Computation α) : (pure 
a <|> c₂) = pure a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Computation.orElse_think`：orElse_think (c₁ c₂ : Computation α) : (think 
c₁ <|> think c₂) = think (c₁ <|> c₂)
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
-/
theorem orElse_empty (c : Computation α) : (c <|> empty α) = c := by
  apply eq_of_bisim (fun c₁ c₂ => (c₂ <|> empty α) = c₁) _ rfl
  intro s' s h; rw [← h]
  induction s using recOn with rw [think_empty]
  | pure s => simp
  | think s => simp only [BisimO, orElse_think, destruct_think]; rw [← think_empty]

/-- `c₁ ~ c₂` asserts that `c₁` and `c₂` either both terminate with the same result,
  or both loop forever. -/
/-
**Computation.Equiv** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：Equiv (c₁ c₂ : Computation α) : Prop
参数：c₁ c₂ : Computation α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`c₁ ~ c₂` asserts that `c₁` and `c₂` either both terminate with the same result,
  or both loop forever.
-/
def Equiv (c₁ c₂ : Computation α) : Prop :=
  ∀ a, a ∈ c₁ ↔ a ∈ c₂

/-- equivalence relation for computations -/
scoped infixl:50 " ~ " => Equiv

@[refl]
/-
**Computation.Equiv.refl** 是 Mathlib 中的一个定理，位于命名空间 `Computation.Equiv`。
形式化陈述：∀ {α : Type u} (s : Computation α), s.Equiv s
参数：s : Computation α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Equiv.refl (s : Computation α) : s ~ s := fun _ => Iff.rfl

@[symm]
/-
**Computation.Equiv.symm** 是 Mathlib 中的一个定理，位于命名空间 `Computation.Equiv`。
形式化陈述：∀ {α : Type u} {s t : Computation α}, s.Equiv t → t.Equiv s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem Equiv.symm {s t : Computation α} : s ~ t → t ~ s := fun h a => (h a).symm

@[trans]
/-
**Computation.Equiv.trans** 是 Mathlib 中的一个定理，位于命名空间 `Computation.Equiv`。
形式化陈述：∀ {α : Type u} {s t u : Computation α}, s.Equiv t → t.Equiv u → s.Equiv u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
-/
theorem Equiv.trans {s t u : Computation α} : s ~ t → t ~ u → s ~ u := fun h1 h2 a =>
  (h1 a).trans (h2 a)
/-
**Computation.Equiv.equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Computation.Equiv`。
形式化陈述：∀ {α : Type u}, Equivalence Computation.Equiv
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.Equiv.refl`：∀ {α : Type u} (s : Computation α), s.Equiv s
· 使用定理 `Computation.Equiv.symm`：∀ {α : Type u} {s t : Computation α}, s.Equiv t 
→ t.Equiv s
· 使用定理 `Computation.Equiv.trans`：∀ {α : Type u} {s t u : Computation α}, s.Equiv
 t → t.Equiv u → s.Equiv u
-/
theorem Equiv.equivalence : Equivalence (@Equiv α) :=
  ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩
/-
**Computation.equiv_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：equiv_of_mem {s t : Computation α} {a} (h1 : a in s) (h2 : a in t) : s ~ t
参数：h1 : a in s；h2 : a in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.mem_unique`：∀ {α : Type u} {s : Computation α} {a b : α}, a 
∈ s → b ∈ s → a = b
-/
theorem equiv_of_mem {s t : Computation α} {a} (h1 : a ∈ s) (h2 : a ∈ t) : s ~ t := fun a' =>
  ⟨fun ma => by rw [mem_unique ma h1]; exact h2, fun ma => by rw [mem_unique ma h2]; exact h1⟩
/-
**Computation.terminates_congr** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：terminates_congr {c₁ c₂ : Computation α} (h : c₁ ~ c₂) : Terminates c₁ ↔ T
erminates c₂
参数：h : c₁ ~ c₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem terminates_congr {c₁ c₂ : Computation α} (h : c₁ ~ c₂) : Terminates c₁ ↔ Terminates c₂ := by
  simp only [terminates_iff, exists_congr h]
/-
**Computation.promises_congr** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：promises_congr {c₁ c₂ : Computation α} (h : c₁ ~ c₂) (a) : c₁ ~> a ↔ c₂ ~>
 a
参数：h : c₁ ~ c₂；a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr`：∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a → b ↔ c → d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem promises_congr {c₁ c₂ : Computation α} (h : c₁ ~ c₂) (a) : c₁ ~> a ↔ c₂ ~> a :=
  forall_congr' fun a' => imp_congr (h a') Iff.rfl
/-
**Computation.get_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：get_equiv {c₁ c₂ : Computation α} (h : c₁ ~ c₂) [Terminates c₁] [Terminate
s c₂] : get c₁ = get c₂
参数：h : c₁ ~ c₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.get_eq_of_mem`：get_eq_of_mem {a} : a in s -> get s = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Computation.get_mem`：get_mem : get s in s
-/
theorem get_equiv {c₁ c₂ : Computation α} (h : c₁ ~ c₂) [Terminates c₁] [Terminates c₂] :
    get c₁ = get c₂ :=
  get_eq_of_mem _ <| (h _).2 <| get_mem _
/-
**Computation.think_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：think_equiv (s : Computation α) : think s ~ s
参数：s : Computation α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.of_think_mem`：∀ {α : Type u} {s : Computation α} {a : α}, a 
∈ s.think → a ∈ s
· 使用定理 `Computation.think_mem`：∀ {α : Type u} {s : Computation α} {a : α}, a ∈ s
 → a ∈ s.think
-/
theorem think_equiv (s : Computation α) : think s ~ s := fun _ => ⟨of_think_mem, think_mem⟩
/-
**Computation.thinkN_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：thinkN_equiv (s : Computation α) (n) : thinkN s n ~ s
参数：s : Computation α；n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.thinkN_mem`：∀ {α : Type u} {s : Computation α} {a : α} (n : 
ℕ), a ∈ s.thinkN n ↔ a ∈ s
-/
theorem thinkN_equiv (s : Computation α) (n) : thinkN s n ~ s := fun _ => thinkN_mem n
/-
**Computation.bind_congr** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：bind_congr {s1 s2 : Computation α} {f1 f2 : α -> Computation β} (h1 : s1 ~
 s2) (h2 : forall a, f1 a ~ f2 a) : bind s1 f1 ~ bind s2 f2
参数：h1 : s1 ~ s2；h2 : forall a, f1 a ~ f2 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.exists_of_mem_bind`：exists_of_mem_bind {s : Computation α} {
f : α -> Computation β} {b} (h : b in bind s f) : exists a in s, b in f a
· 使用定理 `Computation.mem_bind`：mem_bind {s : Computation α} {f : α -> Computation
 β} {a b} (h1 : a in s) (h2 : b in f a) : b in bind s f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem bind_congr {s1 s2 : Computation α} {f1 f2 : α → Computation β} (h1 : s1 ~ s2)
    (h2 : ∀ a, f1 a ~ f2 a) : bind s1 f1 ~ bind s2 f2 := fun b =>
  ⟨fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).1 ha) ((h2 a b).1 hb),
    fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).2 ha) ((h2 a b).2 hb)⟩
/-
**Computation.equiv_pure_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：equiv_pure_of_mem {s : Computation α} {a} (h : a in s) : s ~ pure a
参数：h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.equiv_of_mem`：equiv_of_mem {s t : Computation α} {a} (h1 : a
 in s) (h2 : a in t) : s ~ t
· 使用定理 `Computation.ret_mem`：ret_mem (a : α) : a in pure a
-/
theorem equiv_pure_of_mem {s : Computation α} {a} (h : a ∈ s) : s ~ pure a :=
  equiv_of_mem h (ret_mem _)

/-- `LiftRel R ca cb` is a generalization of `Equiv` to relations other than
  equality. It asserts that if `ca` terminates with `a`, then `cb` terminates with
  some `b` such that `R a b`, and if `cb` terminates with `b` then `ca` terminates
  with some `a` such that `R a b`. -/
/-
**Computation.LiftRel** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：LiftRel (R : α -> β -> Prop) (ca : Computation α) (cb : Computation β) : P
rop
参数：R : α -> β -> Prop；ca : Computation α；cb : Computation β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LiftRel R ca cb` is a generalization of `Equiv` to relations other than
  equality. It asserts that if `ca` terminates with `a`, then `cb` terminates wi
th
  some `b` such that `R a b`, and if `cb` terminates with `b` then `ca` terminat
es
  with some `a` such that `R a b`.
-/
def LiftRel (R : α → β → Prop) (ca : Computation α) (cb : Computation β) : Prop :=
  (∀ {a}, a ∈ ca → ∃ b, b ∈ cb ∧ R a b) ∧ ∀ {b}, b ∈ cb → ∃ a, a ∈ ca ∧ R a b
/-
**Computation.LiftRel.swap** 是 Mathlib 中的一个定理，位于命名空间 `Computation.LiftRel`。
形式化陈述：∀ {α : Type u} {β : Type v} (R : α → β → Prop) (ca : Computation α) (cb : 
Computation β),   Computation.LiftRel (Function.swap R) cb ca ↔ Computation.Lift
Rel R ca cb
参数：R : α → β → Prop；ca : Computation α；cb : Computation β；Function.swap R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem LiftRel.swap (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel (swap R) cb ca ↔ LiftRel R ca cb :=
  @and_comm _ _
/-
**Computation.lift_eq_iff_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：lift_eq_iff_equiv (c₁ c₂ : Computation α) : LiftRel (· = ·) c₁ c₂ ↔ c₁ ~ c
₂
参数：c₁ c₂ : Computation α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem lift_eq_iff_equiv (c₁ c₂ : Computation α) : LiftRel (· = ·) c₁ c₂ ↔ c₁ ~ c₂ :=
  ⟨fun ⟨h1, h2⟩ a =>
    ⟨fun a1 => by let ⟨b, b2, ab⟩ := h1 a1; rwa [ab],
     fun a2 => by let ⟨b, b1, ab⟩ := h2 a2; rwa [← ab]⟩,
    fun e => ⟨fun {a} a1 => ⟨a, (e _).1 a1, rfl⟩, fun {a} a2 => ⟨a, (e _).2 a2, rfl⟩⟩⟩
/-
**Computation.LiftRel.refl** 是 Mathlib 中的一个定理，位于命名空间 `Computation.LiftRel`。
形式化陈述：∀ {α : Type u} (R : α → α → Prop) [Std.Refl R], Std.Refl (Computation.Lift
Rel R)
参数：R : α → α → Prop；Computation.LiftRel R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `refl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Refl r] (a : α), r a a
-/
instance LiftRel.refl (R : α → α → Prop) [Std.Refl R] : Std.Refl (LiftRel R) where
  refl _ := ⟨fun {a} as => ⟨a, as, refl_of R a⟩, fun {b} bs => ⟨b, bs, refl_of R b⟩⟩
/-
**Computation.LiftRel.symm** 是 Mathlib 中的一个定理，位于命名空间 `Computation.LiftRel`。
形式化陈述：∀ {α : Type u} (R : α → α → Prop) [Std.Symm R], Std.Symm (Computation.Lift
Rel R)
参数：R : α → α → Prop；Computation.LiftRel R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
-/
instance LiftRel.symm (R : α → α → Prop) [Std.Symm R] : Std.Symm (LiftRel R) where
  symm _ _ := fun ⟨l, r⟩ ↦ {
    left a2 :=
      let ⟨b, b1, ab⟩ := r a2
      ⟨b, b1, symm_of R ab⟩
    right a1 :=
      let ⟨b, b2, ab⟩ := l a1
      ⟨b, b2, symm_of R ab⟩
  }
/-
**Computation.LiftRel.trans** 是 Mathlib 中的一个定理，位于命名空间 `Computation.LiftRel`。
形式化陈述：∀ {α : Type u} (R : α → α → Prop) [IsTrans α R], IsTrans (Computation α) (
Computation.LiftRel R)
参数：R : α → α → Prop；Computation α；Computation.LiftRel R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
-/
instance LiftRel.trans (R : α → α → Prop) [IsTrans α R] : IsTrans _ (LiftRel R) :=
  ⟨fun _ _ _ ⟨l1, r1⟩ ⟨l2, r2⟩ =>
  ⟨fun {_a} a1 =>
    let ⟨_b, b2, ab⟩ := l1 a1
    let ⟨c, c3, bc⟩ := l2 b2
    ⟨c, c3, trans_of R ab bc⟩,
    fun {_c} c3 =>
    let ⟨_b, b2, bc⟩ := r2 c3
    let ⟨a, a1, ab⟩ := r1 b2
    ⟨a, a1, trans_of R ab bc⟩⟩⟩
/-
**Computation.LiftRel.equiv** 是 Mathlib 中的一个定理，位于命名空间 `Computation.LiftRel`。
形式化陈述：∀ {α : Type u} (R : α → α → Prop), Equivalence R → Equivalence (Computatio
n.LiftRel R)
参数：R : α → α → Prop；Computation.LiftRel R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a
· 使用定理 `Computation.LiftRel.refl`：∀ {α : Type u} (R : α → α → Prop) [Std.Refl R]
, Std.Refl (Computation.LiftRel R)
· 使用定理 `Equivalence.stdRefl`：Equivalence.stdRefl (h : Equivalence r) : Std.Refl 
r where refl
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
· 使用定理 `Computation.LiftRel.symm`：∀ {α : Type u} (R : α → α → Prop) [Std.Symm R]
, Std.Symm (Computation.LiftRel R)
· 使用定理 `Equivalence.stdSymm`：Equivalence.stdSymm (h : Equivalence r) : Std.Symm 
r where symm _ _
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
· 使用定理 `Computation.LiftRel.trans`：∀ {α : Type u} (R : α → α → Prop) [IsTrans α 
R], IsTrans (Computation α) (Computation.LiftRel R)
· 使用定理 `Equivalence.isTrans`：Equivalence.isTrans (h : Equivalence r) : IsTrans α
 r
-/
theorem LiftRel.equiv (R : α → α → Prop) (H : Equivalence R) : Equivalence (LiftRel R) where
  refl := @LiftRel.refl α R H.stdRefl |>.refl
  symm := @LiftRel.symm α R H.stdSymm |>.symm _ _
  trans := @LiftRel.trans α R H.isTrans |>.trans _ _ _
/-
**Computation.LiftRel.imp** 是 Mathlib 中的一个定理，位于命名空间 `Computation.LiftRel`。
形式化陈述：∀ {α : Type u} {β : Type v} {R S : α → β → Prop},   (∀ {a : α} {b : β}, R 
a b → S a b) →     ∀ (s : Computation α) (t : Computation β), Computation.LiftRe
l R s t → Computation.LiftRel S s t
参数：∀ {a : α} {b : β}, R a b → S a b；s : Computation α；t : Computation β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LiftRel.imp {R S : α → β → Prop} (H : ∀ {a b}, R a b → S a b) (s t) :
    LiftRel R s t → LiftRel S s t
  | ⟨l, r⟩ =>
    ⟨fun {_} as =>
      let ⟨b, bt, ab⟩ := l as
      ⟨b, bt, H ab⟩,
      fun {_} bt =>
      let ⟨a, as, ab⟩ := r bt
      ⟨a, as, H ab⟩⟩
/-
**Computation.terminates_of_liftRel** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：terminates_of_liftRel {R : α -> β -> Prop} {s t} : LiftRel R s t -> (Termi
nates s ↔ Terminates t) | ⟨l, r⟩ => ⟨fun ⟨⟨_, as⟩⟩ => let ⟨b, bt, _⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem terminates_of_liftRel {R : α → β → Prop} {s t} :
    LiftRel R s t → (Terminates s ↔ Terminates t)
  | ⟨l, r⟩ =>
    ⟨fun ⟨⟨_, as⟩⟩ =>
      let ⟨b, bt, _⟩ := l as
      ⟨⟨b, bt⟩⟩,
      fun ⟨⟨_, bt⟩⟩ =>
      let ⟨a, as, _⟩ := r bt
      ⟨⟨a, as⟩⟩⟩
/-
**Computation.rel_of_liftRel** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：rel_of_liftRel {R : α -> β -> Prop} {ca cb} : LiftRel R ca cb -> forall {a
 b}, a in ca -> b in cb -> R a b | ⟨l, _⟩, a, b, ma, mb => by let ⟨b', mb', ab'⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.mem_unique`：∀ {α : Type u} {s : Computation α} {a b : α}, a 
∈ s → b ∈ s → a = b
-/
theorem rel_of_liftRel {R : α → β → Prop} {ca cb} :
    LiftRel R ca cb → ∀ {a b}, a ∈ ca → b ∈ cb → R a b
  | ⟨l, _⟩, a, b, ma, mb => by
    let ⟨b', mb', ab'⟩ := l ma
    rw [mem_unique mb mb']; exact ab'
/-
**Computation.liftRel_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：liftRel_of_mem {R : α -> β -> Prop} {a b ca cb} (ma : a in ca) (mb : b in 
cb) (ab : R a b) : LiftRel R ca cb
参数：ma : a in ca；mb : b in cb；ab : R a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.mem_unique`：∀ {α : Type u} {s : Computation α} {a b : α}, a 
∈ s → b ∈ s → a = b
-/
theorem liftRel_of_mem {R : α → β → Prop} {a b ca cb} (ma : a ∈ ca) (mb : b ∈ cb) (ab : R a b) :
    LiftRel R ca cb :=
  ⟨fun {a'} ma' => by rw [mem_unique ma' ma]; exact ⟨b, mb, ab⟩, fun {b'} mb' => by
    rw [mem_unique mb' mb]; exact ⟨a, ma, ab⟩⟩
/-
**Computation.exists_of_liftRel_left** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：exists_of_liftRel_left {R : α -> β -> Prop} {ca cb} (H : LiftRel R ca cb) 
{a} (h : a in ca) : exists b, b in cb ∧ R a b
参数：H : LiftRel R ca cb；h : a in ca。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem exists_of_liftRel_left {R : α → β → Prop} {ca cb} (H : LiftRel R ca cb) {a} (h : a ∈ ca) :
    ∃ b, b ∈ cb ∧ R a b :=
  H.left h
/-
**Computation.exists_of_liftRel_right** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：exists_of_liftRel_right {R : α -> β -> Prop} {ca cb} (H : LiftRel R ca cb)
 {b} (h : b in cb) : exists a, a in ca ∧ R a b
参数：H : LiftRel R ca cb；h : b in cb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem exists_of_liftRel_right {R : α → β → Prop} {ca cb} (H : LiftRel R ca cb) {b} (h : b ∈ cb) :
    ∃ a, a ∈ ca ∧ R a b :=
  H.right h
/-
**Computation.liftRel_def** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：liftRel_def {R : α -> β -> Prop} {ca cb} : LiftRel R ca cb ↔ (Terminates c
a ↔ Terminates cb) ∧ forall {a b}, a in ca -> b in cb -> R a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.terminates_of_liftRel`：terminates_of_liftRel {R : α -> β -> 
Prop} {s t} : LiftRel R s t -> (Terminates s ↔ Terminates t) | ⟨l, r⟩ => ⟨fun ⟨⟨
_, as⟩⟩ => let ⟨b, bt, …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.mem_unique`：∀ {α : Type u} {s : Computation α} {a b : α}, a 
∈ s → b ∈ s → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem liftRel_def {R : α → β → Prop} {ca cb} :
    LiftRel R ca cb ↔ (Terminates ca ↔ Terminates cb) ∧ ∀ {a b}, a ∈ ca → b ∈ cb → R a b :=
  ⟨fun h =>
    ⟨terminates_of_liftRel h, fun {a b} ma mb => by
      let ⟨b', mb', ab⟩ := h.left ma
      rwa [mem_unique mb mb']⟩,
    fun ⟨l, r⟩ =>
    ⟨fun {_} ma =>
      let ⟨⟨b, mb⟩⟩ := l.1 ⟨⟨_, ma⟩⟩
      ⟨b, mb, r ma mb⟩,
      fun {_} mb =>
      let ⟨⟨a, ma⟩⟩ := l.2 ⟨⟨_, mb⟩⟩
      ⟨a, ma, r ma mb⟩⟩⟩
/-
**Computation.liftRel_bind** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：liftRel_bind {δ} (R : α -> β -> Prop) (S : γ -> δ -> Prop) {s1 : Computati
on α} {s2 : Computation β} {f1 : α -> Computation γ} {f2 : β -> Computation δ} (
h1 : LiftRel R s1 s2) (h2 : forall {a b}, R a b -> LiftRel S (f1 a) (f2 b)) : Li
ftRel S (bind s1 f1) (bind s2 f2)
参数：R : α -> β -> Prop；S : γ -> δ -> Prop；h1 : LiftRel R s1 s2；h2 : forall {a b},
 R a b -> LiftRel S (f1 a) (f2 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.exists_of_mem_bind`：exists_of_mem_bind {s : Computation α} {
f : α -> Computation β} {b} (h : b in bind s f) : exists a in s, b in f a
· 使用定理 `Computation.mem_bind`：mem_bind {s : Computation α} {f : α -> Computation
 β} {a b} (h1 : a in s) (h2 : b in f a) : b in bind s f
-/
theorem liftRel_bind {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : Computation α}
    {s2 : Computation β} {f1 : α → Computation γ} {f2 : β → Computation δ} (h1 : LiftRel R s1 s2)
    (h2 : ∀ {a b}, R a b → LiftRel S (f1 a) (f2 b)) : LiftRel S (bind s1 f1) (bind s2 f2) :=
  let ⟨l1, r1⟩ := h1
  ⟨fun {_} cB =>
    let ⟨_, a1, c₁⟩ := exists_of_mem_bind cB
    let ⟨_, b2, ab⟩ := l1 a1
    let ⟨l2, _⟩ := h2 ab
    let ⟨_, d2, cd⟩ := l2 c₁
    ⟨_, mem_bind b2 d2, cd⟩,
    fun {_} dB =>
    let ⟨_, b1, d1⟩ := exists_of_mem_bind dB
    let ⟨_, a2, ab⟩ := r1 b1
    let ⟨_, r2⟩ := h2 ab
    let ⟨_, c₂, cd⟩ := r2 d1
    ⟨_, mem_bind a2 c₂, cd⟩⟩

@[simp]
/-
**Computation.liftRel_pure_left** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：liftRel_pure_left (R : α -> β -> Prop) (a : α) (cb : Computation β) : Lift
Rel R (pure a) cb ↔ exists b, b in cb ∧ R a b
参数：R : α -> β -> Prop；a : α；cb : Computation β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.ret_mem`：ret_mem (a : α) : a in pure a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.eq_of_pure_mem`：eq_of_pure_mem {a a' : α} (h : a' in pure a)
 : a' = a
· 使用定理 `Computation.mem_unique`：∀ {α : Type u} {s : Computation α} {a b : α}, a 
∈ s → b ∈ s → a = b
-/
theorem liftRel_pure_left (R : α → β → Prop) (a : α) (cb : Computation β) :
    LiftRel R (pure a) cb ↔ ∃ b, b ∈ cb ∧ R a b :=
  ⟨fun ⟨l, _⟩ => l (ret_mem _), fun ⟨b, mb, ab⟩ =>
    ⟨fun {a'} ma' => by rw [eq_of_pure_mem ma']; exact ⟨b, mb, ab⟩, fun {b'} mb' =>
      ⟨_, ret_mem _, by rw [mem_unique mb' mb]; exact ab⟩⟩⟩

@[simp]
/-
**Computation.liftRel_pure_right** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：liftRel_pure_right (R : α -> β -> Prop) (ca : Computation α) (b : β) : Lif
tRel R ca (pure b) ↔ exists a, a in ca ∧ R a b
参数：R : α -> β -> Prop；ca : Computation α；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.LiftRel.swap`：∀ {α : Type u} {β : Type v} (R : α → β → Prop)
 (ca : Computation α) (cb : Computation β),   Computation.LiftRel (Function.swap
 R) cb ca ↔ Co…
· 使用定理 `Computation.liftRel_pure_left`：liftRel_pure_left (R : α -> β -> Prop) (a
 : α) (cb : Computation β) : LiftRel R (pure a) cb ↔ exists b, b in cb ∧ R a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem liftRel_pure_right (R : α → β → Prop) (ca : Computation α) (b : β) :
    LiftRel R ca (pure b) ↔ ∃ a, a ∈ ca ∧ R a b := by rw [LiftRel.swap, liftRel_pure_left]
/-
**Computation.liftRel_pure** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：liftRel_pure (R : α -> β -> Prop) (a : α) (b : β) : LiftRel R (pure a) (pu
re b) ↔ R a b
参数：R : α -> β -> Prop；a : α；b : β。
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
theorem liftRel_pure (R : α → β → Prop) (a : α) (b : β) :
    LiftRel R (pure a) (pure b) ↔ R a b := by
  simp

@[simp]
/-
**Computation.liftRel_think_left** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：liftRel_think_left (R : α -> β -> Prop) (ca : Computation α) (cb : Computa
tion β) : LiftRel R (think ca) cb ↔ LiftRel R ca cb
参数：R : α -> β -> Prop；ca : Computation α；cb : Computation β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr`：∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a → b ↔ c → d)
· 使用定理 `Computation.of_think_mem`：∀ {α : Type u} {s : Computation α} {a : α}, a 
∈ s.think → a ∈ s
· 使用定理 `Computation.think_mem`：∀ {α : Type u} {s : Computation α} {a : α}, a ∈ s
 → a ∈ s.think
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
-/
theorem liftRel_think_left (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel R (think ca) cb ↔ LiftRel R ca cb :=
  and_congr (forall_congr' fun _ => imp_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)
    (forall_congr' fun _ =>
      imp_congr Iff.rfl <| exists_congr fun _ => and_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)

@[simp]
/-
**Computation.liftRel_think_right** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：liftRel_think_right (R : α -> β -> Prop) (ca : Computation α) (cb : Comput
ation β) : LiftRel R ca (think cb) ↔ LiftRel R ca cb
参数：R : α -> β -> Prop；ca : Computation α；cb : Computation β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.LiftRel.swap`：∀ {α : Type u} {β : Type v} (R : α → β → Prop)
 (ca : Computation α) (cb : Computation β),   Computation.LiftRel (Function.swap
 R) cb ca ↔ Co…
· 使用定理 `Computation.liftRel_think_left`：liftRel_think_left (R : α -> β -> Prop) 
(ca : Computation α) (cb : Computation β) : LiftRel R (think ca) cb ↔ LiftRel R 
ca cb
-/
theorem liftRel_think_right (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel R ca (think cb) ↔ LiftRel R ca cb := by
  rw [← LiftRel.swap R, ← LiftRel.swap R]; apply liftRel_think_left
/-
**Computation.liftRel_mem_cases** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：liftRel_mem_cases {R : α -> β -> Prop} {ca cb} (Ha : forall a in ca, LiftR
el R ca cb) (Hb : forall b in cb, LiftRel R ca cb) : LiftRel R ca cb
参数：Ha : forall a in ca, LiftRel R ca cb；Hb : forall b in cb, LiftRel R ca cb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem liftRel_mem_cases {R : α → β → Prop} {ca cb} (Ha : ∀ a ∈ ca, LiftRel R ca cb)
    (Hb : ∀ b ∈ cb, LiftRel R ca cb) : LiftRel R ca cb :=
  ⟨fun {_} ma => (Ha _ ma).left ma, fun {_} mb => (Hb _ mb).right mb⟩
/-
**Computation.liftRel_congr** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：liftRel_congr {R : α -> β -> Prop} {ca ca' : Computation α} {cb cb' : Comp
utation β} (ha : ca ~ ca') (hb : cb ~ cb') : LiftRel R ca cb ↔ LiftRel R ca' cb'
参数：ha : ca ~ ca'；hb : cb ~ cb'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr`：∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a → b ↔ c → d)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem liftRel_congr {R : α → β → Prop} {ca ca' : Computation α} {cb cb' : Computation β}
    (ha : ca ~ ca') (hb : cb ~ cb') : LiftRel R ca cb ↔ LiftRel R ca' cb' :=
  and_congr
    (forall_congr' fun _ => imp_congr (ha _) <| exists_congr fun _ => and_congr (hb _) Iff.rfl)
    (forall_congr' fun _ => imp_congr (hb _) <| exists_congr fun _ => and_congr (ha _) Iff.rfl)
/-
**Computation.liftRel_map** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：liftRel_map {δ} (R : α -> β -> Prop) (S : γ -> δ -> Prop) {s1 : Computatio
n α} {s2 : Computation β} {f1 : α -> γ} {f2 : β -> δ} (h1 : LiftRel R s1 s2) (h2
 : forall {a b}, R a b -> S (f1 a) (f2 b)) : LiftRel S (map f1 s1) (map f2 s2)
参数：R : α -> β -> Prop；S : γ -> δ -> Prop；h1 : LiftRel R s1 s2；h2 : forall {a b},
 R a b -> S (f1 a) (f2 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.bind_pure`：bind_pure (f : α -> β) (s) : bind s (pure ∘ f) = 
map f s
· 使用定理 `Computation.liftRel_bind`：liftRel_bind {δ} (R : α -> β -> Prop) (S : γ -
> δ -> Prop) {s1 : Computation α} {s2 : Computation β} {f1 : α -> Computation γ}
 {f2 : β -> Co…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem liftRel_map {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : Computation α}
    {s2 : Computation β} {f1 : α → γ} {f2 : β → δ} (h1 : LiftRel R s1 s2)
    (h2 : ∀ {a b}, R a b → S (f1 a) (f2 b)) : LiftRel S (map f1 s1) (map f2 s2) := by
  rw [← bind_pure, ← bind_pure]; apply liftRel_bind _ _ h1; simpa
/-
**Computation.map_congr** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：map_congr {s1 s2 : Computation α} {f : α -> β} (h1 : s1 ~ s2) : map f s1 ~
 map f s2
参数：h1 : s1 ~ s2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.lift_eq_iff_equiv`：lift_eq_iff_equiv (c₁ c₂ : Computation α)
 : LiftRel (· = ·) c₁ c₂ ↔ c₁ ~ c₂
· 使用定理 `Computation.liftRel_map`：liftRel_map {δ} (R : α -> β -> Prop) (S : γ -> 
δ -> Prop) {s1 : Computation α} {s2 : Computation β} {f1 : α -> γ} {f2 : β -> δ}
 (h1 : LiftRe…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem map_congr {s1 s2 : Computation α} {f : α → β}
    (h1 : s1 ~ s2) : map f s1 ~ map f s2 := by
  rw [← lift_eq_iff_equiv]
  exact liftRel_map Eq _ ((lift_eq_iff_equiv _ _).2 h1) fun {a} b => congr_arg _

/-- Alternate definition of `LiftRel` over relations between `Computation`s -/
/-
**Computation.LiftRelAux** 是 Mathlib 中的一个定义，位于命名空间 `Computation`。
形式化陈述：{α : Type u} →   {β : Type v} → (α → β → Prop) → (Computation α → Computat
ion β → Prop) → α ⊕ Computation α → β ⊕ Computation β → Prop
参数：α → β → Prop；Computation α → Computation β → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternate definition of `LiftRel` over relations between `Computation`s
-/
def LiftRelAux (R : α → β → Prop) (C : Computation α → Computation β → Prop) :
    α ⊕ (Computation α) → β ⊕ (Computation β) → Prop
  | Sum.inl a, Sum.inl b => R a b
  | Sum.inl a, Sum.inr cb => ∃ b, b ∈ cb ∧ R a b
  | Sum.inr ca, Sum.inl b => ∃ a, a ∈ ca ∧ R a b
  | Sum.inr ca, Sum.inr cb => C ca cb

variable {R : α → β → Prop} {C : Computation α → Computation β → Prop}
/-
**Computation.liftRelAux_inl_inl** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} {β : Type v} {R : α → β → Prop} {C : Computation α → Comput
ation β → Prop} {a : α} {b : β},   Computation.LiftRelAux R C (Sum.inl a) (Sum.i
nl b) = R a b
参数：Sum.inl a；Sum.inl b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma liftRelAux_inl_inl {a : α} {b : β} : LiftRelAux R C (Sum.inl a) (Sum.inl b) = R a b :=
  rfl
/-
**Computation.liftRelAux_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} {β : Type v} {R : α → β → Prop} {C : Computation α → Comput
ation β → Prop} {a : α} {cb : Computation β},   Computation.LiftRelAux R C (Sum.
inl a) (Sum.inr cb) = ∃ b ∈ cb, R a b
参数：Sum.inl a；Sum.inr cb。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma liftRelAux_inl_inr {a : α} {cb} :
    LiftRelAux R C (Sum.inl a) (Sum.inr cb) = ∃ b, b ∈ cb ∧ R a b :=
  rfl
/-
**Computation.liftRelAux_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} {β : Type v} {R : α → β → Prop} {C : Computation α → Comput
ation β → Prop} {b : β} {ca : Computation α},   Computation.LiftRelAux R C (Sum.
inr ca) (Sum.inl b) = ∃ a ∈ ca, R a b
参数：Sum.inr ca；Sum.inl b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma liftRelAux_inr_inl {b : β} {ca} :
    LiftRelAux R C (Sum.inr ca) (Sum.inl b) = ∃ a, a ∈ ca ∧ R a b :=
  rfl
/-
**Computation.liftRelAux_inr_inr** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：∀ {α : Type u} {β : Type v} {R : α → β → Prop} {C : Computation α → Comput
ation β → Prop} {ca : Computation α}   {cb : Computation β}, Computation.LiftRel
Aux R C (Sum.inr ca) (Sum.inr cb) = C ca cb
参数：Sum.inr ca；Sum.inr cb。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma liftRelAux_inr_inr {ca cb} :
    LiftRelAux R C (Sum.inr ca) (Sum.inr cb) = C ca cb :=
  rfl

@[simp]
/-
**Computation.LiftRelAux.ret_left** 是 Mathlib 中的一个定理，位于命名空间 `Computation.LiftRel
Aux`。
形式化陈述：∀ {α : Type u} {β : Type v} (R : α → β → Prop) (C : Computation α → Comput
ation β → Prop) (a : α) (cb : Computation β),   Computation.LiftRelAux R C (Sum.
inl a) cb.destruct ↔ ∃ b ∈ cb, R a b
参数：R : α → β → Prop；C : Computation α → Computation β → Prop；a : α；cb : Computat
ion β；Sum.inl a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.ret_mem`：ret_mem (a : α) : a in pure a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.mem_unique`：∀ {α : Type u} {s : Computation α} {a b : α}, a 
∈ s → b ∈ s → a = b
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
· 使用定理 `Computation.think_mem`：∀ {α : Type u} {s : Computation α} {a : α}, a ∈ s
 → a ∈ s.think
· 使用定理 `Computation.of_think_mem`：∀ {α : Type u} {s : Computation α} {a : α}, a 
∈ s.think → a ∈ s
-/
theorem LiftRelAux.ret_left (R : α → β → Prop) (C : Computation α → Computation β → Prop) (a cb) :
    LiftRelAux R C (Sum.inl a) (destruct cb) ↔ ∃ b, b ∈ cb ∧ R a b := by
  induction cb using recOn with
  | pure b =>
    exact
      ⟨fun h => ⟨_, ret_mem _, h⟩, fun ⟨b', mb, h⟩ => by rw [mem_unique (ret_mem _) mb]; exact h⟩
  | think cb =>
    rw [destruct_think]
    exact ⟨fun ⟨b, h, r⟩ => ⟨b, think_mem h, r⟩, fun ⟨b, h, r⟩ => ⟨b, of_think_mem h, r⟩⟩
/-
**Computation.LiftRelAux.swap** 是 Mathlib 中的一个定理，位于命名空间 `Computation.LiftRelAux`
。
形式化陈述：∀ {α : Type u} {β : Type v} (R : α → β → Prop) (C : Computation α → Comput
ation β → Prop) (a : α ⊕ Computation α)   (b : β ⊕ Computation β),   Computation
.LiftRelAux (Function.swap R) (Function.swap C) b a = Computation.LiftRelAux R C
 a b
参数：R : α → β → Prop；C : Computation α → Computation β → Prop；a : α ⊕ Computation
 α；b : β ⊕ Computation β；Function.swap R；Function.swap C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LiftRelAux.swap (R : α → β → Prop) (C) (a b) :
    LiftRelAux (swap R) (swap C) b a = LiftRelAux R C a b := by
  rcases a with a | ca <;> rcases b with b | cb <;> simp only [LiftRelAux]

@[simp]
/-
**Computation.LiftRelAux.ret_right** 是 Mathlib 中的一个定理，位于命名空间 `Computation.LiftRe
lAux`。
形式化陈述：∀ {α : Type u} {β : Type v} (R : α → β → Prop) (C : Computation α → Comput
ation β → Prop) (b : β) (ca : Computation α),   Computation.LiftRelAux R C ca.de
struct (Sum.inl b) ↔ ∃ a ∈ ca, R a b
参数：R : α → β → Prop；C : Computation α → Computation β → Prop；b : β；ca : Computat
ion α；Sum.inl b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.LiftRelAux.swap`：∀ {α : Type u} {β : Type v} (R : α → β → Pr
op) (C : Computation α → Computation β → Prop) (a : α ⊕ Computation α)   (b : β 
⊕ Computation β),…
· 使用定理 `Computation.LiftRelAux.ret_left`：∀ {α : Type u} {β : Type v} (R : α → β 
→ Prop) (C : Computation α → Computation β → Prop) (a : α) (cb : Computation β),
   Computation.LiftRe…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem LiftRelAux.ret_right (R : α → β → Prop) (C : Computation α → Computation β → Prop) (b ca) :
    LiftRelAux R C (destruct ca) (Sum.inl b) ↔ ∃ a, a ∈ ca ∧ R a b := by
  rw [← LiftRelAux.swap, LiftRelAux.ret_left]
/-
**Computation.LiftRelRec.lem** 是 Mathlib 中的一个定理，位于命名空间 `Computation.LiftRelRec`。
形式化陈述：∀ {α : Type u} {β : Type v} {R : α → β → Prop} (C : Computation α → Comput
ation β → Prop),   (∀ {ca : Computation α} {cb : Computation β}, C ca cb → Compu
tation.LiftRelAux R C ca.destruct cb.destruct) →     ∀ (ca : Computation α) (cb 
: Computation β), C ca cb → ∀ a ∈ ca, Computation.LiftRel R ca cb
参数：C : Computation α → Computation β → Prop；∀ {ca : Computation α} {cb : Computa
tion β}, C ca cb → Computation.LiftRelAux R C ca.destruct cb.destruct；ca : Compu
tation α；cb : Computation β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Computation.destruct_think`：∀ {α : Type u} (s : Computation α), s.think.
destruct = Sum.inr s
-/
theorem LiftRelRec.lem {R : α → β → Prop} (C : Computation α → Computation β → Prop)
    (H : ∀ {ca cb}, C ca cb → LiftRelAux R C (destruct ca) (destruct cb)) (ca cb) (Hc : C ca cb) (a)
    (ha : a ∈ ca) : LiftRel R ca cb := by
  revert cb
  refine memRecOn (C := (fun ca ↦ ∀ (cb : Computation β), C ca cb → LiftRel R ca cb))
    ha ?_ (fun ca' IH => ?_) <;> intro cb Hc <;> have h := H Hc
  · simp only [destruct_pure, LiftRelAux.ret_left] at h
    simp [h]
  · simp only [liftRel_think_left]
    induction cb using recOn with
    | pure b => simpa using h
    | think cb => simpa [h] using IH _ h
/-
**Computation.liftRel_rec** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：liftRel_rec {R : α -> β -> Prop} (C : Computation α -> Computation β -> Pr
op) (H : forall {ca cb}, C ca cb -> LiftRelAux R C (destruct ca) (destruct cb)) 
(ca cb) (Hc : C ca cb) : LiftRel R ca cb
参数：C : Computation α -> Computation β -> Prop；H : forall {ca cb}, C ca cb -> Lif
tRelAux R C (destruct ca) (destruct cb)；ca cb；Hc : C ca cb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computation.liftRel_mem_cases`：liftRel_mem_cases {R : α -> β -> Prop} {c
a cb} (Ha : forall a in ca, LiftRel R ca cb) (Hb : forall b in cb, LiftRel R ca 
cb) : LiftRel R ca …
· 使用定理 `Computation.LiftRelRec.lem`：∀ {α : Type u} {β : Type v} {R : α → β → Pro
p} (C : Computation α → Computation β → Prop),   (∀ {ca : Computation α} {cb : C
omputation β}, C…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Computation.LiftRel.swap`：∀ {α : Type u} {β : Type v} (R : α → β → Prop)
 (ca : Computation α) (cb : Computation β),   Computation.LiftRel (Function.swap
 R) cb ca ↔ Co…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Computation.LiftRelAux.swap`：∀ {α : Type u} {β : Type v} (R : α → β → Pr
op) (C : Computation α → Computation β → Prop) (a : α ⊕ Computation α)   (b : β 
⊕ Computation β),…
-/
theorem liftRel_rec {R : α → β → Prop} (C : Computation α → Computation β → Prop)
    (H : ∀ {ca cb}, C ca cb → LiftRelAux R C (destruct ca) (destruct cb)) (ca cb) (Hc : C ca cb) :
    LiftRel R ca cb :=
  liftRel_mem_cases (LiftRelRec.lem C (@H) ca cb Hc) fun b hb =>
    (LiftRel.swap _ _ _).2 <|
      LiftRelRec.lem (swap C) (fun {_ _} h => cast (LiftRelAux.swap _ _ _ _).symm <| H h) cb ca Hc b
        hb

end Computation

