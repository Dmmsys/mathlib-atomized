/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Part
public import Mathlib.Order.Hom.Basic
public import Mathlib.Tactic.Common

/-!
# Monotonicity of monadic operations on `Part`
-/

@[expose] public section

open Part

variable {α β γ : Type*} [Preorder α]

section bind
variable {f : α → Part β} {g : α → β → Part γ}

/-
**Monotone.partBind** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.partBind (hf : Monotone f) (hg : Monotone g) : Monotone fun x => 
(f x).bind (g x)
参数：hf : Monotone f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma Monotone.partBind (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x ↦ (f x).bind (g x) := by
  rintro x y h a
  simp only [and_imp, Part.mem_bind_iff, exists_imp]
  exact fun b hb ha ↦ ⟨b, hf h _ hb, hg h _ _ ha⟩
/-
**Antitone.partBind** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.partBind (hf : Antitone f) (hg : Antitone g) : Antitone fun x => 
(f x).bind (g x)
参数：hf : Antitone f；hg : Antitone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma Antitone.partBind (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x ↦ (f x).bind (g x) := by
  rintro x y h a
  simp only [and_imp, Part.mem_bind_iff, exists_imp]
  exact fun b hb ha ↦ ⟨b, hf h _ hb, hg h _ _ ha⟩

end bind

section map
variable {f : β → γ} {g : α → Part β}

/-
**Monotone.partMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.partMap (hg : Monotone g) : Monotone fun x => (g x).map f
参数：hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Monotone.partBind`：Monotone.partBind (hf : Monotone f) (hg : Monotone g)
 : Monotone fun x => (f x).bind (g x)
· 使用定理 `monotone_const`：monotone_const [Preorder α] [Preorder β] {c : β} : Monot
one fun _ : α => c
-/
lemma Monotone.partMap (hg : Monotone g) : Monotone fun x ↦ (g x).map f := by
  simpa only [← bind_some_eq_map] using hg.partBind monotone_const
/-
**Antitone.partMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.partMap (hg : Antitone g) : Antitone fun x => (g x).map f
参数：hg : Antitone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Antitone.partBind`：Antitone.partBind (hf : Antitone f) (hg : Antitone g)
 : Antitone fun x => (f x).bind (g x)
· 使用定理 `antitone_const`：antitone_const [Preorder α] [Preorder β] {c : β} : Antit
one fun _ : α => c
-/
lemma Antitone.partMap (hg : Antitone g) : Antitone fun x ↦ (g x).map f := by
  simpa only [← bind_some_eq_map] using hg.partBind antitone_const

end map

section seq
variable {β γ : Type _} {f : α → Part (β → γ)} {g : α → Part β}

/-
**Monotone.partSeq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.partSeq (hf : Monotone f) (hg : Monotone g) : Monotone fun x => f
 x <*> g x
参数：hf : Monotone f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `seq_eq_bind_map`：∀ {m : Type u → Type u_1} {α β : Type u} [inst : Monad 
m] [LawfulMonad m] (f : m (α → β)) (x : m α),   f <*> x = do     let x_1 ← f    
 x_1 …
· 使用定理 `Part.instLawfulMonad`：LawfulMonad Part
· 使用引理 `Monotone.partBind`：Monotone.partBind (hf : Monotone f) (hg : Monotone g)
 : Monotone fun x => (f x).bind (g x)
· 使用定理 `Monotone.of_apply₂`：∀ {ι : Type u_1} {α : Type u} {β : ι → Type u_4} [in
st : (i : ι) → Preorder (β i)] [inst_1 : Preorder α]   {f : α → (i : ι) → β i}, 
(∀ (i : …
· 使用引理 `Monotone.partMap`：Monotone.partMap (hg : Monotone g) : Monotone fun x =>
 (g x).map f
-/
lemma Monotone.partSeq (hf : Monotone f) (hg : Monotone g) : Monotone fun x ↦ f x <*> g x := by
  simpa only [seq_eq_bind_map] using! hf.partBind <| Monotone.of_apply₂ fun _ ↦ hg.partMap
/-
**Antitone.partSeq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.partSeq (hf : Antitone f) (hg : Antitone g) : Antitone fun x => f
 x <*> g x
参数：hf : Antitone f；hg : Antitone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `seq_eq_bind_map`：∀ {m : Type u → Type u_1} {α β : Type u} [inst : Monad 
m] [LawfulMonad m] (f : m (α → β)) (x : m α),   f <*> x = do     let x_1 ← f    
 x_1 …
· 使用定理 `Part.instLawfulMonad`：LawfulMonad Part
· 使用引理 `Antitone.partBind`：Antitone.partBind (hf : Antitone f) (hg : Antitone g)
 : Antitone fun x => (f x).bind (g x)
· 使用定理 `Antitone.of_apply₂`：∀ {ι : Type u_1} {α : Type u} {β : ι → Type u_4} [in
st : (i : ι) → Preorder (β i)] [inst_1 : Preorder α]   {f : α → (i : ι) → β i}, 
(∀ (i : …
· 使用引理 `Antitone.partMap`：Antitone.partMap (hg : Antitone g) : Antitone fun x =>
 (g x).map f
-/
lemma Antitone.partSeq (hf : Antitone f) (hg : Antitone g) : Antitone fun x ↦ f x <*> g x := by
  simpa only [seq_eq_bind_map] using! hf.partBind <| Antitone.of_apply₂ fun _ ↦ hg.partMap

end seq

namespace OrderHom

/-- `Part.bind` as a monotone function -/
@[simps]
/-
**OrderHom.partBind** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：partBind (f : α ->o Part β) (g : α ->o β -> Part γ) : α ->o Part γ where t
oFun x
参数：f : α ->o Part β；g : α ->o β -> Part γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Part.bind` as a monotone function
-/
def partBind (f : α →o Part β) (g : α →o β → Part γ) : α →o Part γ where
  toFun x := (f x).bind (g x)
  monotone' := f.2.partBind g.2

end OrderHom

