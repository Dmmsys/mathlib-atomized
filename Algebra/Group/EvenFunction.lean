/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Module.Defs

/-!
# Even and odd functions

We define even functions `α → β` assuming `α` has a negation, and odd functions assuming both `α`
and `β` have negation.

These definitions are `Function.Even` and `Function.Odd`; and they are `protected`, to avoid
conflicting with the root-level definitions `Even` and `Odd` (which, for functions, mean that the
function takes even resp. odd _values_, a wholly different concept).
-/

@[expose] public section

assert_not_exists Module.IsTorsionFree NoZeroSMulDivisors

namespace Function

variable {α β : Type*} [Neg α]

/-- A function `f` is _even_ if it satisfies `f (-x) = f x` for all `x`. -/
/-
**Function.Even** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [Neg α] → (α → β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is _even_ if it satisfies `f (-x) = f x` for all `x`.
-/
protected def Even (f : α → β) : Prop := ∀ a, f (-a) = f a

/-- A function `f` is _odd_ if it satisfies `f (-x) = -f x` for all `x`. -/
/-
**Function.Odd** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [Neg α] → [Neg β] → (α → β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is _odd_ if it satisfies `f (-x) = -f x` for all `x`.
-/
protected def Odd [Neg β] (f : α → β) : Prop := ∀ a, f (-a) = -(f a)

/-- An even function `f` satisfies `f (-x) = f x`. -/
/-
**Function.Even.eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Even`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] {f : α → β}, Function.Even 
f → ∀ (x : α), f (-x) = f x
参数：x : α；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An even function `f` satisfies `f (-x) = f x`.
-/
lemma Even.eq {f : α → β} (hf : f.Even) (x : α) : f (-x) = f x := hf x

/-- Any constant function is even. -/
/-
**Function.Even.const** 是 Mathlib 中的一个定理，位于命名空间 `Function.Even`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] (b : β), Function.Even fun 
x => b
参数：b : β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any constant function is even.
-/
lemma Even.const (b : β) : Function.Even (fun _ : α ↦ b) := fun _ ↦ rfl

/-- The zero function is even. -/
/-
**Function.Even.zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.Even`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] [inst_1 : Zero β], Function
.Even fun x => 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Even.const`：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] (b :
 β), Function.Even fun x => b

--- 原说明 ---
The zero function is even.
-/
lemma Even.zero [Zero β] : Function.Even (fun (_ : α) ↦ (0 : β)) := Even.const 0

/-- An odd function `f` satisfies `f (-x) = -f x`. -/
/-
**Function.Odd.eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Odd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] [inst_1 : Neg β] {f : α → β
}, Function.Odd f → ∀ (x : α), f (-x) = -f x
参数：x : α；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An odd function `f` satisfies `f (-x) = -f x`.
-/
lemma Odd.eq [Neg β] {f : α → β} (hf : f.Odd) (x : α) : f (-x) = -f x := hf x

/-- The zero function is odd. -/
/-
**Function.Odd.zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.Odd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] [inst_1 : NegZeroClass β], 
Function.Odd fun x => 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0

--- 原说明 ---
The zero function is odd.
-/
lemma Odd.zero [NegZeroClass β] : Function.Odd (fun (_ : α) ↦ (0 : β)) := fun _ ↦ neg_zero.symm

section composition

variable {γ : Type*}

/-- If `f` is arbitrary and `g` is even, then `f ∘ g` is even. -/
/-
**Function.Even.left_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Even`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] {γ : Type u_3} {g : α → β},
   Function.Even g → ∀ (f : β → γ), Function.Even (f ∘ g)
参数：f : β → γ；f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If `f` is arbitrary and `g` is even, then `f ∘ g` is even.
-/
lemma Even.left_comp {g : α → β} (hg : g.Even) (f : β → γ) : (f ∘ g).Even :=
  (congr_arg f <| hg ·)

/-- If `f` is even and `g` is odd, then `f ∘ g` is even. -/
/-
**Function.Even.comp_odd** 是 Mathlib 中的一个定理，位于命名空间 `Function.Even`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] {γ : Type u_3} [inst_1 : Ne
g β] {f : β → γ},   Function.Even f → ∀ {g : α → β}, Function.Odd g → Function.E
ven (f ∘ g)
参数：f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` is even and `g` is odd, then `f ∘ g` is even.
-/
lemma Even.comp_odd [Neg β] {f : β → γ} (hf : f.Even) {g : α → β} (hg : g.Odd) :
    (f ∘ g).Even := by
  intro a
  simp only [comp_apply, hg a, hf _]

/-- If `f` and `g` are odd, then `f ∘ g` is odd. -/
/-
**Function.Odd.comp_odd** 是 Mathlib 中的一个定理，位于命名空间 `Function.Odd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] {γ : Type u_3} [inst_1 : Ne
g β] [inst_2 : Neg γ] {f : β → γ},   Function.Odd f → ∀ {g : α → β}, Function.Od
d g → Function.Odd (f ∘ g)
参数：f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` and `g` are odd, then `f ∘ g` is odd.
-/
lemma Odd.comp_odd [Neg β] [Neg γ] {f : β → γ} (hf : f.Odd) {g : α → β} (hg : g.Odd) :
    (f ∘ g).Odd := by
  intro a
  simp only [comp_apply, hg a, hf _]

end composition

/-
**Function.Even.add** 是 Mathlib 中的一个定理，位于命名空间 `Function.Even`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] [inst_1 : Add β] {f g : α →
 β},   Function.Even f → Function.Even g → Function.Even (f + g)
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Even.add [Add β] {f g : α → β} (hf : f.Even) (hg : g.Even) : (f + g).Even := by
  intro a
  simp only [hf a, hg a, Pi.add_apply]
/-
**Function.Odd.add** 是 Mathlib 中的一个定理，位于命名空间 `Function.Odd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] [inst_1 : SubtractionCommMo
noid β] {f g : α → β},   Function.Odd f → Function.Odd g → Function.Odd (f + g)
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Odd.add [SubtractionCommMonoid β] {f g : α → β} (hf : f.Odd) (hg : g.Odd) : (f + g).Odd := by
  intro a
  simp only [hf a, hg a, Pi.add_apply, neg_add]

section smul

variable {γ : Type*} {f : α → β} {g : α → γ}

/-
**Function.Even.smul_even** 是 Mathlib 中的一个定理，位于命名空间 `Function.Even`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] {γ : Type u_3} {f : α → β} 
{g : α → γ} [inst_1 : SMul β γ],   Function.Even f → Function.Even g → Function.
Even (f • g)
参数：f • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Even.smul_even [SMul β γ] (hf : f.Even) (hg : g.Even) : (f • g).Even := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a]
/-
**Function.Even.smul_odd** 是 Mathlib 中的一个定理，位于命名空间 `Function.Even`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] {γ : Type u_3} {f : α → β} 
{g : α → γ} [inst_1 : Monoid β]   [inst_2 : AddGroup γ] [inst_3 : DistribMulActi
on β γ], Function.Even f → Function.Odd g → Function.Odd (f • g)
参数：f • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Even.smul_odd [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hf : f.Even) (hg : g.Odd) :
    (f • g).Odd := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg]
/-
**Function.Odd.smul_even** 是 Mathlib 中的一个定理，位于命名空间 `Function.Odd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] {γ : Type u_3} {f : α → β} 
{g : α → γ} [inst_1 : Ring β]   [inst_2 : AddCommGroup γ] [inst_3 : _root_.Modul
e β γ], Function.Odd f → Function.Even g → Function.Odd (f • g)
参数：f • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Odd.smul_even [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Even) :
    (f • g).Odd := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, neg_smul]
/-
**Function.Odd.smul_odd** 是 Mathlib 中的一个定理，位于命名空间 `Function.Odd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] {γ : Type u_3} {f : α → β} 
{g : α → γ} [inst_1 : Ring β]   [inst_2 : AddCommGroup γ] [inst_3 : _root_.Modul
e β γ], Function.Odd f → Function.Odd g → Function.Even (f • g)
参数：f • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Odd.smul_odd [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Odd) :
    (f • g).Even := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg, neg_smul, neg_neg]
/-
**Function.Even.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Even`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] {γ : Type u_3} {g : α → γ} 
[inst_1 : SMul β γ],   Function.Even g → ∀ (r : β), Function.Even (r • g)
参数：r : β；r • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Even.const_smul [SMul β γ] (hg : g.Even) (r : β) : (r • g).Even := by
  intro a
  simp only [Pi.smul_apply, hg a]
/-
**Function.Odd.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Odd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] {γ : Type u_3} {g : α → γ} 
[inst_1 : Monoid β] [inst_2 : AddGroup γ]   [inst_3 : DistribMulAction β γ], Fun
ction.Odd g → ∀ (r : β), Function.Odd (r • g)
参数：r : β；r • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Odd.const_smul [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hg : g.Odd) (r : β) :
    (r • g).Odd := by
  intro a
  simp only [Pi.smul_apply, hg a, smul_neg]

end smul

section mul

variable {R : Type*} [Mul R] {f g : α → R}

/-
**Function.Even.mul_even** 是 Mathlib 中的一个定理，位于命名空间 `Function.Even`。
形式化陈述：∀ {α : Type u_1} [inst : Neg α] {R : Type u_3} [inst_1 : Mul R] {f g : α →
 R},   Function.Even f → Function.Even g → Function.Even (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Even.mul_even (hf : f.Even) (hg : g.Even) : (f * g).Even := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a]
/-
**Function.Even.mul_odd** 是 Mathlib 中的一个定理，位于命名空间 `Function.Even`。
形式化陈述：∀ {α : Type u_1} [inst : Neg α] {R : Type u_3} [inst_1 : Mul R] {f g : α →
 R} [inst_2 : HasDistribNeg R],   Function.Even f → Function.Odd g → Function.Od
d (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Even.mul_odd [HasDistribNeg R] (hf : f.Even) (hg : g.Odd) : (f * g).Odd := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg]
/-
**Function.Odd.mul_even** 是 Mathlib 中的一个定理，位于命名空间 `Function.Odd`。
形式化陈述：∀ {α : Type u_1} [inst : Neg α] {R : Type u_3} [inst_1 : Mul R] {f g : α →
 R} [inst_2 : HasDistribNeg R],   Function.Odd f → Function.Even g → Function.Od
d (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Odd.mul_even [HasDistribNeg R] (hf : f.Odd) (hg : g.Even) : (f * g).Odd := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, neg_mul]
/-
**Function.Odd.mul_odd** 是 Mathlib 中的一个定理，位于命名空间 `Function.Odd`。
形式化陈述：∀ {α : Type u_1} [inst : Neg α] {R : Type u_3} [inst_1 : Mul R] {f g : α →
 R} [inst_2 : HasDistribNeg R],   Function.Odd f → Function.Odd g → Function.Eve
n (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Odd.mul_odd [HasDistribNeg R] (hf : f.Odd) (hg : g.Odd) : (f * g).Even := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg, neg_mul, neg_neg]

end mul

section torsionfree

-- need to redeclare variables since `InvolutiveNeg α` conflicts with `Neg α`
variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

/--
If `f` is both even and odd, and its target is a torsion-free commutative additive group,
then `f = 0`.
-/
/-
**Function.zero_of_even_and_odd** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：zero_of_even_and_odd [Neg α] (he : f.Even) (ho : f.Odd) : f = 0
参数：he : f.Even；ho : f.Odd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_self`：∀ {G : Type u_2} [inst : AddGroup G] [IsAddTorsionFree G] {
a : G}, -a = a ↔ a = 0

--- 原说明 ---
If `f` is both even and odd, and its target is a torsion-free commutative additi
ve group,
then `f = 0`.
-/
lemma zero_of_even_and_odd [Neg α] (he : f.Even) (ho : f.Odd) : f = 0 := by
  ext r
  rw [Pi.zero_apply, ← neg_eq_self, ← ho, he]

/-- The sum of values of an odd function over a symmetric finite set is zero. -/
/-
**Function.Odd.finsetSum_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.Odd`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommGroup β] [IsAddTorsionFree 
β] [inst_2 : InvolutiveNeg α] {f : α → β},   Function.Odd f → ∀ {s : Finset α}, 
Finset.map (Equiv.toEmbedding (Equiv.neg α)) s = s → s.sum f = 0
参数：Equiv.toEmbedding (Equiv.neg α)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …

--- 原说明 ---
The sum of values of an odd function over a symmetric finite set is zero.
-/
lemma Odd.finsetSum_eq_zero [InvolutiveNeg α] {f : α → β} (hf : f.Odd) {s : Finset α}
    (hs : Finset.map (Equiv.neg α).toEmbedding s = s) :
    s.sum f = 0 := by
  simpa [neg_eq_self, funext hf, hs] using (Finset.sum_map s (Equiv.neg α).toEmbedding f).symm

@[deprecated (since := "2026-04-08")] alias Odd.finset_sum_eq_zero := Odd.finsetSum_eq_zero

/-- The sum of the values of an odd function is 0. -/
/-
**Function.Odd.sum_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.Odd`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommGroup β] [IsAddTorsionFree 
β] [inst_2 : Fintype α]   [inst_3 : InvolutiveNeg α] {f : α → β}, Function.Odd f
 → ∑ a, f a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Odd.finsetSum_eq_zero`：∀ {α : Type u_3} {β : Type u_4} [inst : 
AddCommGroup β] [IsAddTorsionFree β] [inst_2 : InvolutiveNeg α] {f : α → β},   F
unction.Odd f → ∀ {s…
· 使用定理 `Finset.map_univ_equiv`：map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map
 f.toEmbedding = univ

--- 原说明 ---
The sum of the values of an odd function is 0.
-/
lemma Odd.sum_eq_zero [Fintype α] [InvolutiveNeg α] {f : α → β} (hf : f.Odd) : ∑ a, f a = 0 :=
  hf.finsetSum_eq_zero <| Finset.map_univ_equiv (Equiv.neg α)

/-- An odd function vanishes at zero. -/
/-
**Function.Odd.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.Odd`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommGroup β] [IsAddTorsionFree 
β] {f : α → β} [inst_2 : NegZeroClass α],   Function.Odd f → f 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An odd function vanishes at zero.
-/
lemma Odd.map_zero [NegZeroClass α] (hf : f.Odd) : f 0 = 0 := by simp [← neg_eq_self, ← hf 0]

end torsionfree

end Function

