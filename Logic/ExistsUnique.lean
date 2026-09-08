/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
module

public import Mathlib.Init

/-!
# `ExistsUnique`

This file defines the `ExistsUnique` predicate, notated as `∃!`, and proves some of its
basic properties.
-/

@[expose] public section

variable {α : Sort*}

/-- For `p : α → Prop`, `ExistsUnique p` means that there exists a unique `x : α` with `p x`. -/
/-
**ExistsUnique** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ExistsUnique (p : α -> Prop)
参数：p : α -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `p : α → Prop`, `ExistsUnique p` means that there exists a unique `x : α` wi
th `p x`.
-/
def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

namespace Mathlib.Notation
open Lean

/-- Checks to see that `xs` has only one binder. -/
meta def isExplicitBinderSingular (xs : TSyntax ``explicitBinders) : Bool :=
  match xs with
  | `(explicitBinders| $_:binderIdent $[: $_]?) => true
  | `(explicitBinders| ($_:binderIdent : $_)) => true
  | _ => false

open TSyntax.Compat in
/--
`∃! x : α, p x` means that there exists a unique `x` in `α` such that `p x`.
This is notation for `ExistsUnique (fun (x : α) ↦ p x)`.

This notation does not allow multiple binders like `∃! (x : α) (y : β), p x y`
as a shorthand for `∃! (x : α), ∃! (y : β), p x y` since it is liable to be misunderstood.
Often, the intended meaning is instead `∃! q : α × β, p q.1 q.2`.
-/
macro "∃!" xs:explicitBinders ", " b:term : term => do
  if !isExplicitBinderSingular xs then
    Macro.throwErrorAt xs "\
      The `ExistsUnique` notation should not be used with more than one binder.\n\
      \n\
      The reason for this is that `∃! (x : α), ∃! (y : β), p x y` has a completely different \
      meaning from `∃! q : α × β, p q.1 q.2`. \
      To prevent confusion, this notation requires that you be explicit \
      and use one with the correct interpretation."
  expandExplicitBinders ``ExistsUnique xs b

/--
Pretty-printing for `ExistsUnique`, following the same pattern as pretty printing for `Exists`.
However, it does *not* merge binders.
-/
@[app_unexpander ExistsUnique] meta def unexpandExistsUnique : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident ↦ $b)                      => `(∃! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) ↦ $b)               => `(∃! $x:ident : $t, $b)
  | _                                               => throw ()

/--
`∃! x ∈ s, p x` means `∃! x, x ∈ s ∧ p x`, which is to say that there exists a unique `x ∈ s`
such that `p x`.
Similarly, notations such as `∃! x ≤ n, p n` are supported,
using any relation defined using the `binder_predicate` command.
-/
syntax "∃! " binderIdent binderPred ", " term : term

macro_rules
  | `(∃! $x:ident $p:binderPred, $b) => `(∃! $x:ident, satisfies_binder_pred% $x $p ∧ $b)
  | `(∃! _ $p:binderPred, $b) => `(∃! x, satisfies_binder_pred% x $p ∧ $b)

end Mathlib.Notation

-- @[intro] -- TODO
/-
**ExistsUnique.intro** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ExistsUnique.intro {p : α -> Prop} (w : α) (h₁ : p w) (h₂ : forall y, p y 
-> y = w) : exists! x, p x
参数：w : α；h₁ : p w；h₂ : forall y, p y -> y = w。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ExistsUnique.intro {p : α → Prop} (w : α)
    (h₁ : p w) (h₂ : ∀ y, p y → y = w) : ∃! x, p x := ⟨w, h₁, h₂⟩
/-
**ExistsUnique.elim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ExistsUnique.elim {p : α -> Prop} {b : Prop} (h₂ : exists! x, p x) (h₁ : f
orall x, p x -> (forall y, p y -> y = x) -> b) : b
参数：h₂ : exists! x, p x；h₁ : forall x, p x -> (forall y, p y -> y = x) -> b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ExistsUnique.elim {p : α → Prop} {b : Prop}
    (h₂ : ∃! x, p x) (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
  Exists.elim h₂ (fun w hw ↦ h₁ w (And.left hw) (And.right hw))
/-
**existsUnique_of_exists_of_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：existsUnique_of_exists_of_unique {p : α -> Prop} (hex : exists x, p x) (hu
nique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y₂) : exists! x, p x
参数：hex : exists x, p x；hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `ExistsUnique.intro`：ExistsUnique.intro {p : α -> Prop} (w : α) (h₁ : p w
) (h₂ : forall y, p y -> y = w) : exists! x, p x
-/
theorem existsUnique_of_exists_of_unique {p : α → Prop}
    (hex : ∃ x, p x) (hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) : ∃! x, p x :=
  Exists.elim hex (fun x px ↦ ExistsUnique.intro x px (fun y (h : p y) ↦ hunique y x h px))
/-
**ExistsUnique.exists** 是 Mathlib 中的一个定理，位于命名空间 `ExistsUnique`。
形式化陈述：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x, p x
参数：∃! x, p x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ExistsUnique.exists {p : α → Prop} : (∃! x, p x) → ∃ x, p x | ⟨x, h, _⟩ => ⟨x, h⟩
/-
**ExistsUnique.unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ExistsUnique.unique {p : α -> Prop} (h : exists! x, p x) {y₁ y₂ : α} (py₁ 
: p y₁) (py₂ : p y₂) : y₁ = y₂
参数：h : exists! x, p x；py₁ : p y₁；py₂ : p y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ExistsUnique.unique {p : α → Prop}
    (h : ∃! x, p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
  let ⟨_, _, hy⟩ := h; (hy _ py₁).trans (hy _ py₂).symm
/-
**ExistsUnique.choose_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ExistsUnique.choose_eq_iff {p : α -> Prop} {a : α} (h : exists! x, p x) : 
h.choose = a ↔ p a
参数：h : exists! x, p x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
-/
theorem ExistsUnique.choose_eq_iff {p : α → Prop} {a : α} (h : ∃! x, p x) :
    h.choose = a ↔ p a :=
  ⟨fun ha ↦ ha ▸ h.choose_spec.left, h.unique h.choose_spec.left⟩

-- TODO
-- attribute [congr] forall_congr'
-- attribute [congr] exists_congr'

-- @[congr]
/-
**existsUnique_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：existsUnique_congr {p q : α -> Prop} (h : forall a, p a ↔ q a) : (exists! 
a, p a) ↔ exists! a, q a
参数：h : forall a, p a ↔ q a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr_left`：∀ {a b c : Prop}, (a ↔ b) → (a → c ↔ b → c)
-/
theorem existsUnique_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃! a, p a) ↔ ∃! a, q a :=
  exists_congr fun _ ↦ and_congr (h _) <| forall_congr' fun _ ↦ imp_congr_left (h _)
/-
**existsUnique_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} [Subsingleton α] {p : α → Prop}, (∃! x, p x) ↔ ∃ x, p x
参数：∃! x, p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
@[simp] theorem existsUnique_iff_exists [Subsingleton α] {p : α → Prop} :
    (∃! x, p x) ↔ ∃ x, p x :=
  ⟨fun h ↦ h.exists, Exists.imp fun x hx ↦ ⟨hx, fun y _ ↦ Subsingleton.elim y x⟩⟩
/-
**existsUnique_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：existsUnique_const {b : Prop} (α : Sort*) [i : Nonempty α] [Subsingleton α
] : (exists! _ : α, b) ↔ b
参数：α : Sort*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem existsUnique_const {b : Prop} (α : Sort*) [i : Nonempty α] [Subsingleton α] :
    (∃! _ : α, b) ↔ b := by simp
/-
**existsUnique_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {a' : α}, ∃! a, a = a'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] theorem existsUnique_eq {a' : α} : ∃! a, a = a' := by
  simp only [eq_comm, ExistsUnique, and_self, forall_eq', exists_eq']

/-- The difference with `existsUnique_eq` is that the equality is reversed. -/
/-
**existsUnique_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {a' : α}, ∃! a, a' = a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The difference with `existsUnique_eq` is that the equality is reversed.
-/
@[simp] theorem existsUnique_eq' {a' : α} : ∃! a, a' = a := by
  simp only [ExistsUnique, and_self, forall_eq', exists_eq']
/-
**existsUnique_prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：existsUnique_prop {p q : Prop} : (exists! _ : p, q) ↔ p ∧ q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem existsUnique_prop {p q : Prop} : (∃! _ : p, q) ↔ p ∧ q := by simp
/-
**existsUnique_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1}, ¬∃! x, False
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem existsUnique_false : ¬∃! _ : α, False := fun ⟨_, h, _⟩ ↦ h
/-
**existsUnique_prop_of_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：existsUnique_prop_of_true {p : Prop} {q : p -> Prop} (h : p) : (exists! h'
 : p, q h') ↔ q h
参数：h : p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_const`：existsUnique_const {b : Prop} (α : Sort*) [i : Nonem
pty α] [Subsingleton α] : (exists! _ : α, b) ↔ b
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
-/
theorem existsUnique_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∃! h' : p, q h') ↔ q h :=
  @existsUnique_const (q h) p ⟨h⟩ _
/-
**ExistsUnique.elim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ExistsUnique.elim {p : α -> Prop} {b : Prop} (h₂ : exists! x, p x) (h₁ : f
orall x, p x -> (forall y, p y -> y = x) -> b) : b
参数：h₂ : exists! x, p x；h₁ : forall x, p x -> (forall y, p y -> y = x) -> b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ExistsUnique.elim₂ {p : α → Sort*} [∀ x, Subsingleton (p x)]
    {q : ∀ (x) (_ : p x), Prop} {b : Prop} (h₂ : ∃! x, ∃! h : p x, q x h)
    (h₁ : ∀ (x) (h : p x), q x h → (∀ (y) (hy : p y), q y hy → y = x) → b) : b := by
  simp only [existsUnique_iff_exists] at h₂
  apply h₂.elim
  exact fun x ⟨hxp, hxq⟩ H ↦ h₁ x hxp hxq fun y hyp hyq ↦ H y ⟨hyp, hyq⟩
/-
**ExistsUnique.intro** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ExistsUnique.intro {p : α -> Prop} (w : α) (h₁ : p w) (h₂ : forall y, p y 
-> y = w) : exists! x, p x
参数：w : α；h₁ : p w；h₂ : forall y, p y -> y = w。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ExistsUnique.intro₂ {p : α → Sort*} [∀ x, Subsingleton (p x)]
    {q : ∀ (x : α) (_ : p x), Prop} (w : α) (hp : p w) (hq : q w hp)
    (H : ∀ (y) (hy : p y), q y hy → y = w) : ∃! x, ∃! hx : p x, q x hx := by
  simp only [existsUnique_iff_exists]
  exact ExistsUnique.intro w ⟨hp, hq⟩ fun y ⟨hyp, hyq⟩ ↦ H y hyp hyq
/-
**ExistsUnique.exists** 是 Mathlib 中的一个定理，位于命名空间 `ExistsUnique`。
形式化陈述：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x, p x
参数：∃! x, p x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ExistsUnique.exists₂ {p : α → Sort*} {q : ∀ (x : α) (_ : p x), Prop}
    (h : ∃! x, ∃! hx : p x, q x hx) : ∃ (x : _) (hx : p x), q x hx :=
  h.exists.imp fun _ hx ↦ hx.exists
/-
**ExistsUnique.unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ExistsUnique.unique {p : α -> Prop} (h : exists! x, p x) {y₁ y₂ : α} (py₁ 
: p y₁) (py₂ : p y₂) : y₁ = y₂
参数：h : exists! x, p x；py₁ : p y₁；py₂ : p y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ExistsUnique.unique₂ {p : α → Sort*} [∀ x, Subsingleton (p x)]
    {q : ∀ (x : α) (_ : p x), Prop} (h : ∃! x, ∃! hx : p x, q x hx) {y₁ y₂ : α}
    (hpy₁ : p y₁) (hqy₁ : q y₁ hpy₁) (hpy₂ : p y₂) (hqy₂ : q y₂ hpy₂) : y₁ = y₂ := by
  simp only [existsUnique_iff_exists] at h
  exact h.unique ⟨hpy₁, hqy₁⟩ ⟨hpy₂, hqy₂⟩

/-- This invokes the two `Decidable` arguments $O(n)$ times. -/
/-
**List.decidableBExistsUnique** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：List.decidableBExistsUnique {α : Type*} [DecidableEq α] (p : α -> Prop) [D
ecidablePred p] : (l : List α) -> Decidable (exists! x, x in l ∧ p x) | [] => .i
sFalse by simp | x :: xs => if hx : p x then decidable_of_iff (forall y in xs, p
 y -> x = y) (⟨fun h => ⟨x, by grind⟩, fun ⟨z, h⟩ y hy hp => (h.2 x ⟨mem_cons_se
lf, hx⟩).trans (by grind)⟩) else have
参数：p : α -> Prop。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This invokes the two `Decidable` arguments $O(n)$ times.
-/
instance List.decidableBExistsUnique {α : Type*} [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    (l : List α) → Decidable (∃! x, x ∈ l ∧ p x)
  | [] => .isFalse <| by simp
  | x :: xs =>
    if hx : p x then
      decidable_of_iff (∀ y ∈ xs, p y → x = y) (⟨fun h ↦ ⟨x, by grind⟩,
        fun ⟨z, h⟩ y hy hp ↦ (h.2 x ⟨mem_cons_self, hx⟩).trans (by grind)⟩)
    else
      have := List.decidableBExistsUnique p xs
      decidable_of_iff (∃! x, x ∈ xs ∧ p x) (by grind)
