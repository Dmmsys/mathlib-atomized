/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Control.Combinators
public import Mathlib.Tactic.CasesM
public import Mathlib.Tactic.Attr.Core

import Mathlib.Tactic.Attr.Register

/-!
# Basic control operations

Extends the theory on functors, applicatives and monads.
-/

@[expose] public section

universe u v w

variable {α β γ : Type u}

section Functor

attribute [functor_norm] Functor.map_map

end Functor

section Applicative

variable {F : Type u → Type v} [Applicative F]

/-- A generalization of `List.zipWith` which combines list elements with an `Applicative`. -/
/-
**zipWithM** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{F : Type u → Type v} → [Applicative F] → {α₁ α₂ φ : Type u} → (α₁ → α₂ → 
F φ) → List α₁ → List α₂ → F (List φ)
参数：α₁ → α₂ → F φ；List φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A generalization of `List.zipWith` which combines list elements with an `Applica
tive`.
-/
def zipWithM {α₁ α₂ φ : Type u} (f : α₁ → α₂ → F φ) : ∀ (_ : List α₁) (_ : List α₂), F (List φ)
  | x :: xs, y :: ys => (· :: ·) <$> f x y <*> zipWithM f xs ys
  | _, _ => pure []

/-- Like `zipWithM` but evaluates the result as it traverses the lists using `*>`. -/
/-
**zipWithM'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α β γ : Type u} → {F : Type u → Type v} → [Applicative F] → (α → β → F γ)
 → List α → List β → F PUnit.{u + 1}
参数：α → β → F γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Like `zipWithM` but evaluates the result as it traverses the lists using `*>`.
-/
def zipWithM' (f : α → β → F γ) : List α → List β → F PUnit
  | x :: xs, y :: ys => f x y *> zipWithM' f xs ys
  | [], _ => pure PUnit.unit
  | _, [] => pure PUnit.unit

variable [LawfulApplicative F]

@[simp]
/-
**pure_id'_seq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {F : Type u → Type v} [inst : Applicative F] [LawfulApplica
tive F] (x : F α), (pure fun x => x) <*> x = x
参数：x : F α；pure fun x => x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pure_id_seq`：∀ {f : Type u_1 → Type u_2} {α : Type u_1} [inst : Applicat
ive f] [LawfulApplicative f] (x : f α), pure id <*> x = x
-/
theorem pure_id'_seq (x : F α) : (pure fun x => x) <*> x = x :=
  pure_id_seq x

@[functor_norm]
/-
**seq_map_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seq_map_assoc (x : F (α -> β)) (f : γ -> α) (y : F γ) : x <*> f < > y = (·
 ∘ f) < > x <*> y
参数：x : F (α -> β)；f : γ -> α；y : F γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LawfulApplicative.seq_assoc`：∀ {f : Type u → Type v} {inst : Applicative
 f} [self : LawfulApplicative f] {α β γ : Type u} (x : f α) (g : f (α → β))   (h
 : f (β → γ)), h …
· 使用定理 `LawfulApplicative.seq_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : f (α → β)) (x : α),   g <*> 
pure x = (fun h …
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `LawfulApplicative.pure_seq`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : f α),   pure g <
*> x = g <$> x
-/
theorem seq_map_assoc (x : F (α → β)) (f : γ → α) (y : F γ) :
    x <*> f <$> y = (· ∘ f) <$> x <*> y := by
  simp only [← pure_seq]
  simp only [seq_assoc, seq_pure, ← comp_map]
  simp [pure_seq]
  rfl

@[functor_norm]
/-
**map_seq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_seq (f : β -> γ) (x : F (α -> β)) (y : F α) : f < > (x <*> y) = (f ∘ ·
) < > x <*> y
参数：f : β -> γ；x : F (α -> β)；y : F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LawfulApplicative.seq_assoc`：∀ {f : Type u → Type v} {inst : Applicative
 f} [self : LawfulApplicative f] {α β γ : Type u} (x : f α) (g : f (α → β))   (h
 : f (β → γ)), h …
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_seq (f : β → γ) (x : F (α → β)) (y : F α) :
    f <$> (x <*> y) = (f ∘ ·) <$> x <*> y := by
  simp only [← pure_seq]; simp [seq_assoc]

end Applicative

section Monad

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-
**seq_bind_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seq_bind_eq (x : m α) {g : β -> m γ} {f : α -> β} : f < > x >>= g = x >>= 
g ∘ f
参数：x : m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bind_map_left`：∀ {m : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : Mo
nad m] [LawfulMonad m] (f : α → β) (x : m α) (g : β → m γ),   (do       let b ← 
f <…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem seq_bind_eq (x : m α) {g : β → m γ} {f : α → β} :
    f <$> x >>= g = x >>= g ∘ f :=
  show bind (f <$> x) g = bind x (g ∘ f) by
    simp [Function.comp_def]
-- order of implicits and `Seq.seq` has a lazily evaluated second argument using `Unit`

@[functor_norm]
/-
**fish_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fish_pure {α β} (f : α -> m β) : f >=> pure = f
参数：f : α -> m β。
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
· 使用定理 `bind_pure`：∀ {m : Type u_1 → Type u_2} {α : Type u_1} [inst : Monad m] [
LawfulMonad m] (x : m α), x >>= pure = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fish_pure {α β} (f : α → m β) : f >=> pure = f := by
  simp +unfoldPartialApp only [(· >=> ·), functor_norm]

@[functor_norm]
/-
**fish_pipe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fish_pipe {α β} (f : α -> m β) : pure >=> f = f
参数：f : α -> m β。
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
· 使用定理 `LawfulMonad.pure_bind`：∀ {m : Type u → Type v} {inst : Monad m} [self : 
LawfulMonad m] {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fish_pipe {α β} (f : α → m β) : pure >=> f = f := by
  simp +unfoldPartialApp only [(· >=> ·), functor_norm]

-- note: in Lean 3 `>=>` is left-associative, but in Lean 4 it is right-associative.
@[functor_norm]
/-
**fish_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fish_assoc {α β γ φ} (f : α -> m β) (g : β -> m γ) (h : γ -> m φ) : (f >=>
 g) >=> h = f >=> g >=> h
参数：f : α -> m β；g : β -> m γ；h : γ -> m φ。
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
· 使用定理 `LawfulMonad.bind_assoc`：∀ {m : Type u → Type v} {inst : Monad m} [self :
 LawfulMonad m] {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),   x >>= 
f >>= g = x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fish_assoc {α β γ φ} (f : α → m β) (g : β → m γ) (h : γ → m φ) :
    (f >=> g) >=> h = f >=> g >=> h := by
  simp +unfoldPartialApp only [(· >=> ·), functor_norm]

variable {β' γ' : Type v}
variable {m' : Type v → Type w} [Monad m']

/-- Takes a value `β` and `List α` and accumulates pairs according to a monadic function `f`.
Accumulation occurs from the right (i.e., starting from the tail of the list). -/
/-
**List.mapAccumRM** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u} →   {β' γ' : Type v} → {m' : Type v → Type w} → [Monad m'] → 
(α → β' → m' (β' × γ')) → β' → List α → m' (β' × List γ')
参数：α → β' → m' (β' × γ')；β' × List γ'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Takes a value `β` and `List α` and accumulates pairs according to a monadic func
tion `f`.
Accumulation occurs from the right (i.e., starting from the tail of the list).
-/
def List.mapAccumRM (f : α → β' → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', ys) ← List.mapAccumRM f a xs
    let (a'', y) ← f x a'
    pure (a'', y :: ys)

/-- Takes a value `β` and `List α` and accumulates pairs according to a monadic function `f`.
Accumulation occurs from the left (i.e., starting from the head of the list). -/
/-
**List.mapAccumLM** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u} →   {β' γ' : Type v} → {m' : Type v → Type w} → [Monad m'] → 
(β' → α → m' (β' × γ')) → β' → List α → m' (β' × List γ')
参数：β' → α → m' (β' × γ')；β' × List γ'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Takes a value `β` and `List α` and accumulates pairs according to a monadic func
tion `f`.
Accumulation occurs from the left (i.e., starting from the head of the list).
-/
def List.mapAccumLM (f : β' → α → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', y) ← f a x
    let (a'', ys) ← List.mapAccumLM f a' xs
    pure (a'', y :: ys)

end Monad

section

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]

/-
**joinM_map_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：joinM_map_map {α β : Type u} (f : α -> β) (a : m (m α)) : joinM (Functor.m
ap f <$> a) = f < > joinM a
参数：f : α -> β；a : m (m α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulMonad.bind_assoc`：∀ {m : Type u → Type v} {inst : Monad m} [self :
 LawfulMonad m] {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),   x >>= 
f >>= g = x …
· 使用定理 `LawfulMonad.pure_bind`：∀ {m : Type u → Type v} {inst : Monad m} [self : 
LawfulMonad m] {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem joinM_map_map {α β : Type u} (f : α → β) (a : m (m α)) :
    joinM (Functor.map f <$> a) = f <$> joinM a := by
  simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind]
/-
**joinM_map_joinM** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：joinM_map_joinM {α : Type u} (a : m (m (m α))) : joinM (joinM <$> a) = joi
nM (joinM a)
参数：a : m (m (m α))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LawfulMonad.bind_assoc`：∀ {m : Type u → Type v} {inst : Monad m} [self :
 LawfulMonad m] {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),   x >>= 
f >>= g = x …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulMonad.pure_bind`：∀ {m : Type u → Type v} {inst : Monad m} [self : 
LawfulMonad m] {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem joinM_map_joinM {α : Type u} (a : m (m (m α))) : joinM (joinM <$> a) = joinM (joinM a) := by
  simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind]

@[simp]
/-
**joinM_map_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：joinM_map_pure {α : Type u} (a : m α) : joinM (pure <$> a) = a
参数：a : m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulMonad.bind_assoc`：∀ {m : Type u → Type v} {inst : Monad m} [self :
 LawfulMonad m] {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),   x >>= 
f >>= g = x …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulMonad.pure_bind`：∀ {m : Type u → Type v} {inst : Monad m} [self : 
LawfulMonad m] {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x
· 使用定理 `bind_pure`：∀ {m : Type u_1 → Type u_2} {α : Type u_1} [inst : Monad m] [
LawfulMonad m] (x : m α), x >>= pure = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem joinM_map_pure {α : Type u} (a : m α) : joinM (pure <$> a) = a := by
  simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind, bind_pure]

@[simp]
/-
**joinM_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：joinM_pure {α : Type u} (a : m α) : joinM (pure a) = a
参数：a : m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulMonad.pure_bind`：∀ {m : Type u → Type v} {inst : Monad m} [self : 
LawfulMonad m] {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x
-/
theorem joinM_pure {α : Type u} (a : m α) : joinM (pure a) = a :=
  LawfulMonad.pure_bind a id

end

section Alternative

variable {F : Type → Type v} [Alternative F]

-- [todo] add notation for `Functor.mapConst` and port `Functor.mapConstRev`
/-- Returns `pure true` if the computation succeeds and `pure false` otherwise. -/
/-
**succeeds** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：succeeds {α} (x : F α) : F Bool
参数：x : F α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns `pure true` if the computation succeeds and `pure false` otherwise.
-/
def succeeds {α} (x : F α) : F Bool :=
  Functor.mapConst true x <|> pure false

/-- Attempts to perform the computation, but fails silently if it doesn't succeed. -/
/-
**tryM** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：tryM {α} (x : F α) : F Unit
参数：x : F α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Attempts to perform the computation, but fails silently if it doesn't succeed.
-/
def tryM {α} (x : F α) : F Unit :=
  Functor.mapConst () x <|> pure ()

/-- Attempts to perform the computation, and returns `none` if it doesn't succeed. -/
/-
**try** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：try? {α} (x : F α) : F (Option α)
参数：x : F α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Attempts to perform the computation, and returns `none` if it doesn't succeed.
-/
def try? {α} (x : F α) : F (Option α) :=
  some <$> x <|> pure none

@[simp]
/-
**guard_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：guard_true {h : Decidable True} : @guard F _ True h = pure ()
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem guard_true {h : Decidable True} : @guard F _ True h = pure () := by simp [guard]

@[simp]
/-
**guard_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：guard_false {h : Decidable False} : @guard F _ False h = failure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem guard_false {h : Decidable False} : @guard F _ False h = failure := by
  simp [guard]

end Alternative

namespace Sum

variable {e : Type v}

/-- The monadic `bind` operation for `Sum`. -/
/-
**Sum.bind** 是 Mathlib 中的一个定义，位于命名空间 `Sum`。
形式化陈述：{e : Type v} → {α : Type u_1} → {β : Type u_2} → e ⊕ α → (α → e ⊕ β) → e ⊕
 β
参数：α → e ⊕ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monadic `bind` operation for `Sum`.
-/
protected def bind {α β} : e ⊕ α → (α → e ⊕ β) → e ⊕ β
  | inl x, _ => inl x
  | inr x, f => f x
-- incorrectly marked as a bad translation by mathport, so we do not mark with `ₓ`.
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monad (Sum.{v, u} e) where
  pure := @Sum.inr e
  bind := @Sum.bind e
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulFunctor (Sum.{v, u} e) := by
  constructor <;> intros <;> (try casesm Sum _ _) <;> rfl
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad (Sum.{v, u} e) where
  seqRight_eq := by
    intros
    casesm Sum _ _ <;> casesm Sum _ _ <;> rfl
  seqLeft_eq := by
    intros
    casesm Sum _ _ <;> rfl
  pure_seq := by
    intros
    rfl
  bind_assoc := by
    intros
    casesm Sum _ _ <;> rfl
  pure_bind := by
    intros
    rfl
  bind_pure_comp := by
    intros
    casesm Sum _ _ <;> rfl
  bind_map := by
    intros
    casesm Sum _ _ <;> rfl

end Sum

/-- A `CommApplicative` functor `m` is a (lawful) applicative functor which behaves identically on
`α × β` and `β × α`, so computations can occur in either order. -/
/-
**CommApplicative** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(m : Type u → Type v) → [Applicative m] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `CommApplicative` functor `m` is a (lawful) applicative functor which behaves 
identically on
`α × β` and `β × α`, so computations can occur in either order.
-/
class CommApplicative (m : Type u → Type v) [Applicative m] : Prop extends LawfulApplicative m where
  /-- Computations performed first on `a : α` and then on `b : β` are equal to those performed in
  the reverse order. -/
  commutative_prod : ∀ {α β} (a : m α) (b : m β),
    Prod.mk <$> a <*> b = (fun (b : β) a => (a, b)) <$> b <*> a

open Functor
/-
**CommApplicative.commutative_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommApplicative.commutative_map {m : Type u -> Type v} [h : Applicative m]
 [CommApplicative m] {α β γ} (a : m α) (b : m β) {f : α -> β -> γ} : f < > a <*>
 b = flip f < > b <*> a
参数：a : m α；b : m β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_seq`：map_seq (f : β -> γ) (x : F (α -> β)) (y : F α) : f < > (x <*> 
y) = (f ∘ ·) < > x <*> y
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CommApplicative.commutative_prod`：∀ {m : Type u → Type v} {inst : Applic
ative m} [self : CommApplicative m] {α β : Type u} (a : m α) (b : m β),   Prod.m
k <$> a <*> b = (fun b…
-/
theorem CommApplicative.commutative_map {m : Type u → Type v} [h : Applicative m]
    [CommApplicative m] {α β γ} (a : m α) (b : m β) {f : α → β → γ} :
    f <$> a <*> b = flip f <$> b <*> a :=
  calc
    f <$> a <*> b = (fun p : α × β => f p.1 p.2) <$> (Prod.mk <$> a <*> b) := by
      simp only [map_seq, map_map, Function.comp_def]
    _ = (fun b a => f a b) <$> b <*> a := by
      rw [@CommApplicative.commutative_prod m h]
      simp [map_seq, map_map]
      rfl
