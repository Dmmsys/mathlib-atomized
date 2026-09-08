/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Asymptotic equivalence up to a constant

In this file we prove basic properties of the equivalence relation
given by `f =Θ[l] g ↔ f =O[l] g ∧ g =O[l] f`.
-/

public section


open Filter

open Topology

namespace Asymptotics


variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']

variable [NormedField 𝕜] [NormedField 𝕜']
variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}
variable {f' : α → E'} {g' : α → F'} {k' : α → G'}
variable {f'' : α → E''} {g'' : α → F''}
variable {l l' : Filter α}

@[refl]
/-
**Asymptotics.isTheta_refl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_refl (f : α -> E) (l : Filter α) : f =Θ[l] f
参数：f : α -> E；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
-/
theorem isTheta_refl (f : α → E) (l : Filter α) : f =Θ[l] f :=
  ⟨isBigO_refl _ _, isBigO_refl _ _⟩
/-
**Asymptotics.isTheta_rfl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_rfl : f =Θ[l] f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isTheta_refl`：isTheta_refl (f : α -> E) (l : Filter α) : f =
Θ[l] f
-/
theorem isTheta_rfl : f =Θ[l] f :=
  isTheta_refl _ _

@[symm]
nonrec theorem IsTheta.symm (h : f =Θ[l] g) : g =Θ[l] f :=
  h.symm
/-
**Asymptotics.isTheta_comm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_comm : f =Θ[l] g ↔ g =Θ[l] f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.symm`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
Θ[l] g → g =Θ[…
-/
theorem isTheta_comm : f =Θ[l] g ↔ g =Θ[l] f :=
  ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

@[trans]
/-
**Asymptotics.IsTheta.trans** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5} {F' : Type u_7} [inst : Nor
m E] [inst_1 : Norm G]   [inst_2 : SeminormedAddCommGroup F'] {l : Filter α} {f 
: α → E} {g : α → F'} {k : α → G},   f =Θ[l] g → g =Θ[l] k → f =Θ[l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsTheta.trans {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g) (h₂ : g =Θ[l] k) :
    f =Θ[l] k :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩
/-
**Asymptotics.** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (α := α → E) (β := α → F') (γ := α → G) (IsTheta l) (IsTheta l) (IsTheta l) :=
  ⟨IsTheta.trans⟩

@[trans]
/-
**Asymptotics.IsBigO.trans_isTheta** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5} {F' : Type u_7} [inst : Nor
m E] [inst_1 : Norm G]   [inst_2 : SeminormedAddCommGroup F'] {l : Filter α} {f 
: α → E} {g : α → F'} {k : α → G},   f =O[l] g → g =Θ[l] k → f =O[l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsBigO.trans_isTheta {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =O[l] g)
    (h₂ : g =Θ[l] k) : f =O[l] k :=
  h₁.trans h₂.1
/-
**Asymptotics.** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (α := α → E) (β := α → F') (γ := α → G) (IsBigO l) (IsTheta l) (IsBigO l) :=
  ⟨IsBigO.trans_isTheta⟩

@[trans]
/-
**Asymptotics.IsTheta.trans_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsThet
a`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5} {F' : Type u_7} [inst : Nor
m E] [inst_1 : Norm G]   [inst_2 : SeminormedAddCommGroup F'] {l : Filter α} {f 
: α → E} {g : α → F'} {k : α → G},   f =Θ[l] g → g =O[l] k → f =O[l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsTheta.trans_isBigO {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g)
    (h₂ : g =O[l] k) : f =O[l] k :=
  h₁.1.trans h₂
/-
**Asymptotics.** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (α := α → E) (β := α → F') (γ := α → G) (IsTheta l) (IsBigO l) (IsBigO l) :=
  ⟨IsTheta.trans_isBigO⟩

@[trans]
/-
**Asymptotics.IsLittleO.trans_isTheta** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsL
ittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} {G' : Type u_8} [inst : Nor
m E] [inst_1 : Norm F]   [inst_2 : SeminormedAddCommGroup G'] {l : Filter α} {f 
: α → E} {g : α → F} {k : α → G'},   f =o[l] g → g =Θ[l] k → f =o[l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsLittleO.trans_isTheta {f : α → E} {g : α → F} {k : α → G'} (h₁ : f =o[l] g)
    (h₂ : g =Θ[l] k) : f =o[l] k :=
  h₁.trans_isBigO h₂.1
/-
**Asymptotics.** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (α := α → E) (β := α → F') (γ := α → G') (IsLittleO l) (IsTheta l) (IsLittleO l) :=
  ⟨IsLittleO.trans_isTheta⟩

@[trans]
/-
**Asymptotics.IsTheta.trans_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsT
heta`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5} {F' : Type u_7} [inst : Nor
m E] [inst_1 : Norm G]   [inst_2 : SeminormedAddCommGroup F'] {l : Filter α} {f 
: α → E} {g : α → F'} {k : α → G},   f =Θ[l] g → g =o[l] k → f =o[l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsTheta.trans_isLittleO {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g)
    (h₂ : g =o[l] k) : f =o[l] k :=
  h₁.1.trans_isLittleO h₂
/-
**Asymptotics.** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (α := α → E) (β := α → F') (γ := α → G) (IsTheta l) (IsLittleO l) (IsLittleO l) :=
  ⟨IsTheta.trans_isLittleO⟩

@[trans]
/-
**Asymptotics.IsTheta.trans_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsTheta`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {l : Filter α} {f : α → E}   {g₁ g₂ : α → F}, f =Θ[l] g₁ → g₁ =ᶠ[l] g₂ → 
f =Θ[l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_eventuallyEq`：∀ {α : Type u_1} {E : Type u_3} {
F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f : α → E}   {g₁
 g₂ : α → F}, f =O[l] g₁ → …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.EventuallyEq.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g :
 α → F}, f₁ =ᶠ[l] f₂ →…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsTheta.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =Θ[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =Θ[l] g₂ :=
  ⟨h.1.trans_eventuallyEq hg, hg.symm.trans_isBigO h.2⟩
/-
**Asymptotics.** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (α := α → E) (β := α → F) (γ := α → F) (IsTheta l) (EventuallyEq l) (IsTheta l) :=
  ⟨IsTheta.trans_eventuallyEq⟩

@[trans]
/-
**Asymptotics._root_.Filter.EventuallyEq.trans_isTheta** 是 Mathlib 中的一个定理，位于命名空间
 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.trans_isTheta {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =Θ[l] g) : f₁ =Θ[l] g :=
  ⟨hf.trans_isBigO h.1, h.2.trans_eventuallyEq hf.symm⟩
/-
**Asymptotics.** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (α := α → E) (β := α → E) (γ := α → F) (EventuallyEq l) (IsTheta l) (IsTheta l) :=
  ⟨EventuallyEq.trans_isTheta⟩
/-
**Asymptotics._root_.Filter.EventuallyEq.isTheta** 是 Mathlib 中的一个引理，位于命名空间 `Asym
ptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Filter.EventuallyEq.isTheta {f g : α → E} (h : f =ᶠ[l] g) : f =Θ[l] g :=
  h.trans_isTheta isTheta_rfl

@[simp]
/-
**Asymptotics.isTheta_bot** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_bot : f =Θ[⊥] g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isTheta_bot : f =Θ[⊥] g := by simp [IsTheta]

@[simp]
/-
**Asymptotics.isTheta_norm_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_norm_left : (fun x => ‖f' x‖) =Θ[l] g ↔ f' =Θ[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isTheta_norm_left : (fun x ↦ ‖f' x‖) =Θ[l] g ↔ f' =Θ[l] g := by simp [IsTheta]

@[simp]
/-
**Asymptotics.isTheta_norm_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_norm_right : (f =Θ[l] fun x => ‖g' x‖) ↔ f =Θ[l] g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isTheta_norm_right : (f =Θ[l] fun x ↦ ‖g' x‖) ↔ f =Θ[l] g' := by simp [IsTheta]

alias ⟨IsTheta.of_norm_left, IsTheta.norm_left⟩ := isTheta_norm_left

alias ⟨IsTheta.of_norm_right, IsTheta.norm_right⟩ := isTheta_norm_right
/-
**Asymptotics.IsTheta.of_norm_eventuallyEq_norm** 是 Mathlib 中的一个定理，位于命名空间 `Asymp
totics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F} {l : Filter α},   ((fun x => ‖f x‖) =ᶠ[l] fun x =
> ‖g x‖) → f =Θ[l] g
参数：(fun x => ‖f x‖) =ᶠ[l] fun x => ‖g x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.of_bound'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 (∀ᶠ (x : α) in l,…
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem IsTheta.of_norm_eventuallyEq_norm (h : (fun x ↦ ‖f x‖) =ᶠ[l] fun x ↦ ‖g x‖) : f =Θ[l] g :=
  ⟨.of_bound' h.le, .of_bound' h.symm.le⟩
/-
**Asymptotics.IsTheta.of_norm_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s.IsTheta`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {f' : 
α → E'} {l : Filter α} {g : α → ℝ},   (fun x => ‖f' x‖) =ᶠ[l] g → f' =Θ[l] g
参数：fun x => ‖f' x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.of_norm_eventuallyEq_norm`：∀ {α : Type u_1} {E : Typ
e u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} 
{l : Filter α},   ((fun x => ‖f x‖)…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsTheta.of_norm_eventuallyEq {g : α → ℝ} (h : (fun x ↦ ‖f' x‖) =ᶠ[l] g) : f' =Θ[l] g :=
  of_norm_eventuallyEq_norm <| h.mono fun x hx ↦ by simp only [← hx, norm_norm]
/-
**Asymptotics.IsTheta.isLittleO_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s.IsTheta`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} {E' : Type u_6} {F' : Type u_7} [inst : No
rm G] [inst_1 : SeminormedAddCommGroup E']   [inst_2 : SeminormedAddCommGroup F'
] {k : α → G} {f' : α → E'} {g' : α → F'} {l : Filter α},   f' =Θ[l] g' → (f' =o
[l] k ↔ g' =o[l] k)
参数：f' =o[l] k ↔ g' =o[l] k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G 
: Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Semino
rmedAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.IsTheta.symm`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
Θ[l] g → g =Θ[…
-/
theorem IsTheta.isLittleO_congr_left (h : f' =Θ[l] g') : f' =o[l] k ↔ g' =o[l] k :=
  ⟨h.symm.trans_isLittleO, h.trans_isLittleO⟩
/-
**Asymptotics.IsTheta.isLittleO_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptoti
cs.IsTheta`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} {G' : Type u_8} [inst : No
rm E] [inst_1 : SeminormedAddCommGroup F']   [inst_2 : SeminormedAddCommGroup G'
] {f : α → E} {g' : α → F'} {k' : α → G'} {l : Filter α},   g' =Θ[l] k' → (f =o[
l] g' ↔ f =o[l] k')
参数：f =o[l] g' ↔ f =o[l] k'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_isTheta`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Semino
rmedAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.IsTheta.symm`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
Θ[l] g → g =Θ[…
-/
theorem IsTheta.isLittleO_congr_right (h : g' =Θ[l] k') : f =o[l] g' ↔ f =o[l] k' :=
  ⟨fun H ↦ H.trans_isTheta h, fun H ↦ H.trans_isTheta h.symm⟩
/-
**Asymptotics.IsTheta.isBigO_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sTheta`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} {E' : Type u_6} {F' : Type u_7} [inst : No
rm G] [inst_1 : SeminormedAddCommGroup E']   [inst_2 : SeminormedAddCommGroup F'
] {k : α → G} {f' : α → E'} {g' : α → F'} {l : Filter α},   f' =Θ[l] g' → (f' =O
[l] k ↔ g' =O[l] k)
参数：f' =O[l] k ↔ g' =O[l] k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {G : T
ype u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminorme
dAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.IsTheta.symm`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
Θ[l] g → g =Θ[…
-/
theorem IsTheta.isBigO_congr_left (h : f' =Θ[l] g') : f' =O[l] k ↔ g' =O[l] k :=
  ⟨h.symm.trans_isBigO, h.trans_isBigO⟩
/-
**Asymptotics.IsTheta.isBigO_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsTheta`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} {G' : Type u_8} [inst : No
rm E] [inst_1 : SeminormedAddCommGroup F']   [inst_2 : SeminormedAddCommGroup G'
] {f : α → E} {g' : α → F'} {k' : α → G'} {l : Filter α},   g' =Θ[l] k' → (f =O[
l] g' ↔ f =O[l] k')
参数：f =O[l] g' ↔ f =O[l] k'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isTheta`：∀ {α : Type u_1} {E : Type u_3} {G : T
ype u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminorme
dAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.IsTheta.symm`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
Θ[l] g → g =Θ[…
-/
theorem IsTheta.isBigO_congr_right (h : g' =Θ[l] k') : f =O[l] g' ↔ f =O[l] k' :=
  ⟨fun H ↦ H.trans_isTheta h, fun H ↦ H.trans_isTheta h.symm⟩
/-
**Asymptotics.IsTheta.isTheta_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsTheta`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} {E' : Type u_6} {F' : Type u_7} [inst : No
rm G] [inst_1 : SeminormedAddCommGroup E']   [inst_2 : SeminormedAddCommGroup F'
] {k : α → G} {f' : α → E'} {g' : α → F'} {l : Filter α},   f' =Θ[l] g' → (f' =Θ
[l] k ↔ g' =Θ[l] k)
参数：f' =Θ[l] k ↔ g' =Θ[l] k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Asymptotics.IsTheta.isBigO_congr_left`：∀ {α : Type u_1} {G : Type u_5} {
E' : Type u_6} {F' : Type u_7} [inst : Norm G] [inst_1 : SeminormedAddCommGroup 
E']   [inst_2 : SeminormedA…
· 使用定理 `Asymptotics.IsTheta.isBigO_congr_right`：∀ {α : Type u_1} {E : Type u_3} 
{F' : Type u_7} {G' : Type u_8} [inst : Norm E] [inst_1 : SeminormedAddCommGroup
 F']   [inst_2 : SeminormedA…
-/
lemma IsTheta.isTheta_congr_left (h : f' =Θ[l] g') : f' =Θ[l] k ↔ g' =Θ[l] k :=
  h.isBigO_congr_left.and h.isBigO_congr_right
/-
**Asymptotics.IsTheta.isTheta_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics
.IsTheta`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} {E' : Type u_6} {F' : Type u_7} [inst : No
rm G] [inst_1 : SeminormedAddCommGroup E']   [inst_2 : SeminormedAddCommGroup F'
] {k : α → G} {f' : α → E'} {g' : α → F'} {l : Filter α},   f' =Θ[l] g' → (k =Θ[
l] f' ↔ k =Θ[l] g')
参数：k =Θ[l] f' ↔ k =Θ[l] g'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Asymptotics.IsTheta.isBigO_congr_right`：∀ {α : Type u_1} {E : Type u_3} 
{F' : Type u_7} {G' : Type u_8} [inst : Norm E] [inst_1 : SeminormedAddCommGroup
 F']   [inst_2 : SeminormedA…
· 使用定理 `Asymptotics.IsTheta.isBigO_congr_left`：∀ {α : Type u_1} {G : Type u_5} {
E' : Type u_6} {F' : Type u_7} [inst : Norm G] [inst_1 : SeminormedAddCommGroup 
E']   [inst_2 : SeminormedA…
-/
lemma IsTheta.isTheta_congr_right (h : f' =Θ[l] g') : k =Θ[l] f' ↔ k =Θ[l] g' :=
  h.isBigO_congr_right.and h.isBigO_congr_left
/-
**Asymptotics.IsTheta.mono** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f =Θ[l] g → l' ≤ l → f =Θ[l'
] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsTheta.mono (h : f =Θ[l] g) (hl : l' ≤ l) : f =Θ[l'] g :=
  ⟨h.1.mono hl, h.2.mono hl⟩
/-
**Asymptotics.IsTheta.sup** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [inst : SeminormedAddComm
Group E'] [inst_1 : SeminormedAddCommGroup F']   {f' : α → E'} {g' : α → F'} {l 
l' : Filter α}, f' =Θ[l] g' → f' =Θ[l'] g' → f' =Θ[l ⊔ l'] g'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.sup`：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} 
[inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : α → F'}
 {l l' : Fil…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsTheta.sup (h : f' =Θ[l] g') (h' : f' =Θ[l'] g') : f' =Θ[l ⊔ l'] g' :=
  ⟨h.1.sup h'.1, h.2.sup h'.2⟩

@[simp]
/-
**Asymptotics.isTheta_sup** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_sup : f' =Θ[l ⊔ l'] g' ↔ f' =Θ[l] g' ∧ f' =Θ[l'] g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, 
f =Θ[l] g → l'…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Asymptotics.IsTheta.sup`：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7
} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F']   {f' 
: α → E'} {g'…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isTheta_sup : f' =Θ[l ⊔ l'] g' ↔ f' =Θ[l] g' ∧ f' =Θ[l'] g' :=
  ⟨fun h ↦ ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h ↦ h.1.sup h.2⟩
/-
**Asymptotics.IsTheta.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta
`。
形式化陈述：∀ {α : Type u_1} {E'' : Type u_9} {F'' : Type u_10} [inst : NormedAddCommG
roup E''] [inst_1 : NormedAddCommGroup F'']   {f'' : α → E''} {g'' : α → F''} {l
 : Filter α}, f'' =Θ[l] g'' → ∀ᶠ (x : α) in l, f'' x = 0 ↔ g'' x = 0
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Asymptotics.IsBigO.eq_zero_imp`：∀ {α : Type u_1} {E'' : Type u_9} {F'' :
 Type u_10} [inst : NormedAddCommGroup E''] [inst_1 : NormedAddCommGroup F'']   
{f'' : α → E''} {g''…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsTheta.eq_zero_iff (h : f'' =Θ[l] g'') : ∀ᶠ x in l, f'' x = 0 ↔ g'' x = 0 :=
  h.1.eq_zero_imp.mp <| h.2.eq_zero_imp.mono fun _ ↦ Iff.intro
/-
**Asymptotics.IsTheta.tendsto_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
Theta`。
形式化陈述：∀ {α : Type u_1} {E'' : Type u_9} {F'' : Type u_10} [inst : NormedAddCommG
roup E''] [inst_1 : NormedAddCommGroup F'']   {f'' : α → E''} {g'' : α → F''} {l
 : Filter α},   f'' =Θ[l] g'' → (Filter.Tendsto f'' l (nhds 0) ↔ Filter.Tendsto 
g'' l (nhds 0))
参数：Filter.Tendsto f'' l (nhds 0) ↔ Filter.Tendsto g'' l (nhds 0)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Asymptotics.IsTheta.isLittleO_congr_left`：∀ {α : Type u_1} {G : Type u_5
} {E' : Type u_6} {F' : Type u_7} [inst : Norm G] [inst_1 : SeminormedAddCommGro
up E']   [inst_2 : SeminormedA…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsTheta.tendsto_zero_iff (h : f'' =Θ[l] g'') :
    Tendsto f'' l (𝓝 0) ↔ Tendsto g'' l (𝓝 0) := by
  simp only [← isLittleO_one_iff ℝ, h.isLittleO_congr_left]
/-
**Asymptotics.IsTheta.tendsto_norm_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [inst : SeminormedAddComm
Group E'] [inst_1 : SeminormedAddCommGroup F']   {f' : α → E'} {g' : α → F'} {l 
: Filter α},   f' =Θ[l] g' → (Filter.Tendsto (norm ∘ f') l Filter.atTop ↔ Filter
.Tendsto (norm ∘ g') l Filter.atTop)
参数：Filter.Tendsto (norm ∘ f') l Filter.atTop ↔ Filter.Tendsto (norm ∘ g') l Filt
er.atTop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_const_left_of_ne`：isLittleO_const_left_of_ne {c : 
E''} (hc : c != 0) : (fun _x => c) =o[l] g ↔ Tendsto (fun x => ‖g x‖) l atTop
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Asymptotics.IsTheta.isLittleO_congr_right`：∀ {α : Type u_1} {E : Type u_
3} {F' : Type u_7} {G' : Type u_8} [inst : Norm E] [inst_1 : SeminormedAddCommGr
oup F']   [inst_2 : SeminormedA…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsTheta.tendsto_norm_atTop_iff (h : f' =Θ[l] g') :
    Tendsto (norm ∘ f') l atTop ↔ Tendsto (norm ∘ g') l atTop := by
  simp only [Function.comp_def, ← isLittleO_const_left_of_ne (one_ne_zero' ℝ),
    h.isLittleO_congr_right]
/-
**Asymptotics.IsTheta.isBoundedUnder_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptoti
cs.IsTheta`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [inst : SeminormedAddComm
Group E'] [inst_1 : SeminormedAddCommGroup F']   {f' : α → E'} {g' : α → F'} {l 
: Filter α},   f' =Θ[l] g' →     (Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) l
 (norm ∘ f') ↔       Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) l (norm ∘ g'))
参数：Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) l (norm ∘ f') ↔       Filter.IsB
oundedUnder (fun x1 x2 => x1 ≤ x2) l (norm ∘ g')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isBigO_const_of_ne`：isBigO_const_of_ne {c : F''} (hc : c != 
0) : (f =O[l] fun _x => c) ↔ IsBoundedUnder (· <= ·) l (norm ∘ f)
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Asymptotics.IsTheta.isBigO_congr_left`：∀ {α : Type u_1} {G : Type u_5} {
E' : Type u_6} {F' : Type u_7} [inst : Norm G] [inst_1 : SeminormedAddCommGroup 
E']   [inst_2 : SeminormedA…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsTheta.isBoundedUnder_le_iff (h : f' =Θ[l] g') :
    IsBoundedUnder (· ≤ ·) l (norm ∘ f') ↔ IsBoundedUnder (· ≤ ·) l (norm ∘ g') := by
  simp only [← isBigO_const_of_ne (one_ne_zero' ℝ), h.isBigO_congr_left]
/-
**Asymptotics.IsTheta.smul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {𝕜 : Type u_14} {𝕜' : Typ
e u_15} [inst : SeminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'
] [inst_2 : NormedField 𝕜] [inst_3 : NormedField 𝕜'] {l : Filter α}   [inst_4 : 
NormedSpace 𝕜 E'] [inst_5 : NormedSpace 𝕜' F'] {f₁ : α → 𝕜} {f₂ : α → 𝕜'} {g₁ : 
α → E'} {g₂ : α → F'},   f₁ =Θ[l] f₂ → g₁ =Θ[l] g₂ → (fun x => f₁ x • g₁ x) =Θ[l
] fun x => f₂ x • g₂ x
参数：fun x => f₁ x • g₁ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.smul`：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7
} {R : Type u_13} {𝕜' : Type u_16} [inst : SeminormedAddCommGroup E']   [inst_1 
: SeminormedA…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsTheta.smul [NormedSpace 𝕜 E'] [NormedSpace 𝕜' F'] {f₁ : α → 𝕜} {f₂ : α → 𝕜'} {g₁ : α → E'}
    {g₂ : α → F'} (hf : f₁ =Θ[l] f₂) (hg : g₁ =Θ[l] g₂) :
    (fun x ↦ f₁ x • g₁ x) =Θ[l] fun x ↦ f₂ x • g₂ x :=
  ⟨hf.1.smul hg.1, hf.2.smul hg.2⟩
/-
**Asymptotics.IsTheta.mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_15} [inst : NormedField 𝕜] [
inst_1 : NormedField 𝕜'] {l : Filter α}   {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'}, f₁ =
Θ[l] g₁ → f₂ =Θ[l] g₂ → (fun x => f₁ x * f₂ x) =Θ[l] fun x => g₁ x * g₂ x
参数：fun x => f₁ x * f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.smul`：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_
7} {𝕜 : Type u_14} {𝕜' : Type u_15} [inst : SeminormedAddCommGroup E']   [inst_1
 : SeminormedA…
-/
theorem IsTheta.mul {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂) :
    (fun x ↦ f₁ x * f₂ x) =Θ[l] fun x ↦ g₁ x * g₂ x :=
  h₁.smul h₂
/-
**Asymptotics.IsTheta.listProd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_15} [inst : NormedField 𝕜] [
inst_1 : NormedField 𝕜'] {l : Filter α}   {ι : Type u_16} {L : List ι} {f : ι → 
α → 𝕜} {g : ι → α → 𝕜'},   (∀ i ∈ L, f i =Θ[l] g i) →     (fun x => (List.map (f
un x_1 => f x_1 x) L).prod) =Θ[l] fun x => (List.map (fun x_1 => g x_1 x) L).pro
d
参数：∀ i ∈ L, f i =Θ[l] g i；fun x => (List.map (fun x_1 => f x_1 x) L).prod；List.m
ap (fun x_1 => g x_1 x) L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.listProd`：∀ {α : Type u_1} {R : Type u_13} {𝕜 : Type 
u_15} [inst : SeminormedRing R] [inst_1 : NormedDivisionRing 𝕜]   {l : Filter α}
 {ι : Type u_17} …
· 使用定理 `Asymptotics.IsTheta.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f
 =Θ[l] g → f =O[…
· 使用定理 `Asymptotics.IsTheta.symm`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
Θ[l] g → g =Θ[…
-/
theorem IsTheta.listProd {ι : Type*} {L : List ι} {f : ι → α → 𝕜} {g : ι → α → 𝕜'}
    (h : ∀ i ∈ L, f i =Θ[l] g i) :
    (fun x ↦ (L.map (f · x)).prod) =Θ[l] (fun x ↦ (L.map (g · x)).prod) :=
  ⟨.listProd fun i hi ↦ (h i hi).isBigO, .listProd fun i hi ↦ (h i hi).symm.isBigO⟩
/-
**Asymptotics.IsTheta.multisetProd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsThet
a`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_15} [inst : NormedField 𝕜] [
inst_1 : NormedField 𝕜'] {l : Filter α}   {ι : Type u_16} {s : Multiset ι} {f : 
ι → α → 𝕜} {g : ι → α → 𝕜'},   (∀ i ∈ s, f i =Θ[l] g i) →     (fun x => (Multise
t.map (fun x_1 => f x_1 x) s).prod) =Θ[l] fun x => (Multiset.map (fun x_1 => g x
_1 x) s).prod
参数：∀ i ∈ s, f i =Θ[l] g i；fun x => (Multiset.map (fun x_1 => f x_1 x) s).prod；Mu
ltiset.map (fun x_1 => g x_1 x) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.multisetProd`：∀ {α : Type u_1} {l : Filter α} {ι : Ty
pe u_17} {R : Type u_18} {𝕜 : Type u_19} [inst : SeminormedCommRing R]   [inst_1
 : NormedField 𝕜] {s …
· 使用定理 `Asymptotics.IsTheta.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f
 =Θ[l] g → f =O[…
· 使用定理 `Asymptotics.IsTheta.symm`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
Θ[l] g → g =Θ[…
-/
theorem IsTheta.multisetProd {ι : Type*} {s : Multiset ι} {f : ι → α → 𝕜} {g : ι → α → 𝕜'}
    (h : ∀ i ∈ s, f i =Θ[l] g i) :
    (fun x ↦ (s.map (f · x)).prod) =Θ[l] (fun x ↦ (s.map (g · x)).prod) :=
  ⟨.multisetProd fun i hi ↦ (h i hi).isBigO, .multisetProd fun i hi ↦ (h i hi).symm.isBigO⟩
/-
**Asymptotics.IsTheta.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`
。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_15} [inst : NormedField 𝕜] [
inst_1 : NormedField 𝕜'] {l : Filter α}   {ι : Type u_16} {s : Finset ι} {f : ι 
→ α → 𝕜} {g : ι → α → 𝕜'},   (∀ i ∈ s, f i =Θ[l] g i) → (fun x => ∏ i ∈ s, f i x
) =Θ[l] fun x => ∏ i ∈ s, g i x
参数：∀ i ∈ s, f i =Θ[l] g i；fun x => ∏ i ∈ s, f i x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.finsetProd`：∀ {α : Type u_1} {l : Filter α} {ι : Type
 u_17} {R : Type u_18} {𝕜 : Type u_19} [inst : SeminormedCommRing R]   [inst_1 :
 NormedField 𝕜] {s …
· 使用定理 `Asymptotics.IsTheta.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f
 =Θ[l] g → f =O[…
· 使用定理 `Asymptotics.IsTheta.symm`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
Θ[l] g → g =Θ[…
-/
theorem IsTheta.finsetProd {ι : Type*} {s : Finset ι} {f : ι → α → 𝕜} {g : ι → α → 𝕜'}
    (h : ∀ i ∈ s, f i =Θ[l] g i) : (∏ i ∈ s, f i ·) =Θ[l] (∏ i ∈ s, g i ·) :=
  ⟨.finsetProd fun i hi ↦ (h i hi).isBigO, .finsetProd fun i hi ↦ (h i hi).symm.isBigO⟩
/-
**Asymptotics.IsTheta.inv** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_15} [inst : NormedField 𝕜] [
inst_1 : NormedField 𝕜'] {l : Filter α}   {f : α → 𝕜} {g : α → 𝕜'}, f =Θ[l] g → 
(fun x => (f x)⁻¹) =Θ[l] fun x => (g x)⁻¹
参数：fun x => (f x)⁻¹；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.inv_rev`：∀ {α : Type u_1} {𝕜 : Type u_15} {𝕜' : Type 
u_16} [inst : NormedDivisionRing 𝕜] [inst_1 : NormedDivisionRing 𝕜']   {l : Filt
er α} {f : α → 𝕜…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Asymptotics.IsBigO.eq_zero_imp`：∀ {α : Type u_1} {E'' : Type u_9} {F'' :
 Type u_10} [inst : NormedAddCommGroup E''] [inst_1 : NormedAddCommGroup F'']   
{f'' : α → E''} {g''…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsTheta.inv {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) :
    (fun x ↦ (f x)⁻¹) =Θ[l] fun x ↦ (g x)⁻¹ :=
  ⟨h.2.inv_rev h.1.eq_zero_imp, h.1.inv_rev h.2.eq_zero_imp⟩

@[simp]
/-
**Asymptotics.isTheta_inv** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_inv {f : α -> 𝕜} {g : α -> 𝕜'} : ((fun x => (f x)⁻¹) =Θ[l] fun x =
> (g x)⁻¹) ↔ f =Θ[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Asymptotics.IsTheta.inv`：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_1
5} [inst : NormedField 𝕜] [inst_1 : NormedField 𝕜'] {l : Filter α}   {f : α → 𝕜}
 {g : α → 𝕜'}…
-/
theorem isTheta_inv {f : α → 𝕜} {g : α → 𝕜'} :
    ((fun x ↦ (f x)⁻¹) =Θ[l] fun x ↦ (g x)⁻¹) ↔ f =Θ[l] g :=
  ⟨fun h ↦ by simpa only [inv_inv] using h.inv, IsTheta.inv⟩
/-
**Asymptotics.IsTheta.div** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_15} [inst : NormedField 𝕜] [
inst_1 : NormedField 𝕜'] {l : Filter α}   {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'}, f₁ =
Θ[l] g₁ → f₂ =Θ[l] g₂ → (fun x => f₁ x / f₂ x) =Θ[l] fun x => g₁ x / g₂ x
参数：fun x => f₁ x / f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Asymptotics.IsTheta.mul`：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_1
5} [inst : NormedField 𝕜] [inst_1 : NormedField 𝕜'] {l : Filter α}   {f₁ f₂ : α 
→ 𝕜} {g₁ g₂ :…
· 使用定理 `Asymptotics.IsTheta.inv`：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_1
5} [inst : NormedField 𝕜] [inst_1 : NormedField 𝕜'] {l : Filter α}   {f : α → 𝕜}
 {g : α → 𝕜'}…
-/
theorem IsTheta.div {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂) :
    (fun x ↦ f₁ x / f₂ x) =Θ[l] fun x ↦ g₁ x / g₂ x := by
  simpa only [div_eq_mul_inv] using h₁.mul h₂.inv
/-
**Asymptotics.IsTheta.pow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_15} [inst : NormedField 𝕜] [
inst_1 : NormedField 𝕜'] {l : Filter α}   {f : α → 𝕜} {g : α → 𝕜'}, f =Θ[l] g → 
∀ (n : ℕ), (fun x => f x ^ n) =Θ[l] fun x => g x ^ n
参数：n : ℕ；fun x => f x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.pow`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} [NormOn…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsTheta.pow {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) (n : ℕ) :
    (fun x ↦ f x ^ n) =Θ[l] fun x ↦ g x ^ n :=
  ⟨h.1.pow n, h.2.pow n⟩
/-
**Asymptotics.IsTheta.zpow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_15} [inst : NormedField 𝕜] [
inst_1 : NormedField 𝕜'] {l : Filter α}   {f : α → 𝕜} {g : α → 𝕜'}, f =Θ[l] g → 
∀ (n : ℤ), (fun x => f x ^ n) =Θ[l] fun x => g x ^ n
参数：n : ℤ；fun x => f x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Asymptotics.IsTheta.pow`：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_1
5} [inst : NormedField 𝕜] [inst_1 : NormedField 𝕜'] {l : Filter α}   {f : α → 𝕜}
 {g : α → 𝕜'}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Asymptotics.IsTheta.inv`：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_1
5} [inst : NormedField 𝕜] [inst_1 : NormedField 𝕜'] {l : Filter α}   {f : α → 𝕜}
 {g : α → 𝕜'}…
-/
theorem IsTheta.zpow {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) (n : ℤ) :
    (fun x ↦ f x ^ n) =Θ[l] fun x ↦ g x ^ n := by
  cases n
  · simpa only [Int.ofNat_eq_natCast, zpow_natCast] using h.pow _
  · simpa only [zpow_negSucc] using (h.pow _).inv
/-
**Asymptotics.isTheta_const_const** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_const_const {c₁ : E''} {c₂ : F''} (h₁ : c₁ != 0) (h₂ : c₂ != 0) : 
(fun _ : α => c₁) =Θ[l] fun _ => c₂
参数：h₁ : c₁ != 0；h₂ : c₂ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_const_const`：isBigO_const_const (c : E) {c' : F''} (h
c' : c' != 0) (l : Filter α) : (fun _x : α => c) =O[l] fun _x => c'
-/
theorem isTheta_const_const {c₁ : E''} {c₂ : F''} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    (fun _ : α ↦ c₁) =Θ[l] fun _ ↦ c₂ :=
  ⟨isBigO_const_const _ h₂ _, isBigO_const_const _ h₁ _⟩

@[simp]
/-
**Asymptotics.isTheta_const_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_const_const_iff [NeBot l] {c₁ : E''} {c₂ : F''} : ((fun _ : α => c
₁) =Θ[l] fun _ => c₂) ↔ (c₁ = 0 ↔ c₂ = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
-/
theorem isTheta_const_const_iff [NeBot l] {c₁ : E''} {c₂ : F''} :
    ((fun _ : α ↦ c₁) =Θ[l] fun _ ↦ c₂) ↔ (c₁ = 0 ↔ c₂ = 0) := by
  simpa only [IsTheta, isBigO_const_const_iff, ← iff_def] using Iff.comm

@[simp]
/-
**Asymptotics.isTheta_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_zero_left : (fun _ => (0 : E')) =Θ[l] g'' ↔ g'' =ᶠ[l] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isTheta_zero_left : (fun _ ↦ (0 : E')) =Θ[l] g'' ↔ g'' =ᶠ[l] 0 := by
  simp only [IsTheta, isBigO_zero, isBigO_zero_right_iff, true_and]

@[simp]
/-
**Asymptotics.isTheta_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_zero_right : (f'' =Θ[l] fun _ => (0 : F')) ↔ f'' =ᶠ[l] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isTheta_comm`：isTheta_comm : f =Θ[l] g ↔ g =Θ[l] f
· 使用定理 `Asymptotics.isTheta_zero_left`：isTheta_zero_left : (fun _ => (0 : E')) =
Θ[l] g'' ↔ g'' =ᶠ[l] 0
-/
theorem isTheta_zero_right : (f'' =Θ[l] fun _ ↦ (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  isTheta_comm.trans isTheta_zero_left
/-
**Asymptotics.isTheta_const_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_const_smul_left [NormedSpace 𝕜 E'] {c : 𝕜} (hc : c != 0) : (fun x 
=> c • f' x) =Θ[l] g ↔ f' =Θ[l] g
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Asymptotics.isBigO_const_smul_left`：isBigO_const_smul_left {c : 𝕜} (hc :
 c != 0) : (fun x => c • f' x) =O[l] g ↔ f' =O[l] g
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Asymptotics.isBigO_const_smul_right`：isBigO_const_smul_right {c : 𝕜} (hc
 : c != 0) : (f =O[l] fun x => c • f' x) ↔ f =O[l] f'
-/
theorem isTheta_const_smul_left [NormedSpace 𝕜 E'] {c : 𝕜} (hc : c ≠ 0) :
    (fun x ↦ c • f' x) =Θ[l] g ↔ f' =Θ[l] g :=
  and_congr (isBigO_const_smul_left hc) (isBigO_const_smul_right hc)

alias ⟨IsTheta.of_const_smul_left, IsTheta.const_smul_left⟩ := isTheta_const_smul_left
/-
**Asymptotics.isTheta_const_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_const_smul_right [NormedSpace 𝕜 F'] {c : 𝕜} (hc : c != 0) : (f =Θ[
l] fun x => c • g' x) ↔ f =Θ[l] g'
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Asymptotics.isBigO_const_smul_right`：isBigO_const_smul_right {c : 𝕜} (hc
 : c != 0) : (f =O[l] fun x => c • f' x) ↔ f =O[l] f'
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Asymptotics.isBigO_const_smul_left`：isBigO_const_smul_left {c : 𝕜} (hc :
 c != 0) : (fun x => c • f' x) =O[l] g ↔ f' =O[l] g
-/
theorem isTheta_const_smul_right [NormedSpace 𝕜 F'] {c : 𝕜} (hc : c ≠ 0) :
    (f =Θ[l] fun x ↦ c • g' x) ↔ f =Θ[l] g' :=
  and_congr (isBigO_const_smul_right hc) (isBigO_const_smul_left hc)

alias ⟨IsTheta.of_const_smul_right, IsTheta.const_smul_right⟩ := isTheta_const_smul_right
/-
**Asymptotics.isTheta_const_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_const_mul_left {c : 𝕜} {f : α -> 𝕜} (hc : c != 0) : (fun x => c * 
f x) =Θ[l] g ↔ f =Θ[l] g
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isTheta_const_smul_left`：isTheta_const_smul_left [NormedSpac
e 𝕜 E'] {c : 𝕜} (hc : c != 0) : (fun x => c • f' x) =Θ[l] g ↔ f' =Θ[l] g
-/
theorem isTheta_const_mul_left {c : 𝕜} {f : α → 𝕜} (hc : c ≠ 0) :
    (fun x ↦ c * f x) =Θ[l] g ↔ f =Θ[l] g := by
  simpa only [← smul_eq_mul] using isTheta_const_smul_left hc

alias ⟨IsTheta.of_const_mul_left, IsTheta.const_mul_left⟩ := isTheta_const_mul_left
/-
**Asymptotics.isTheta_const_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isTheta_const_mul_right {c : 𝕜} {g : α -> 𝕜} (hc : c != 0) : (f =Θ[l] fun 
x => c * g x) ↔ f =Θ[l] g
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isTheta_const_smul_right`：isTheta_const_smul_right [NormedSp
ace 𝕜 F'] {c : 𝕜} (hc : c != 0) : (f =Θ[l] fun x => c • g' x) ↔ f =Θ[l] g'
-/
theorem isTheta_const_mul_right {c : 𝕜} {g : α → 𝕜} (hc : c ≠ 0) :
    (f =Θ[l] fun x ↦ c * g x) ↔ f =Θ[l] g := by
  simpa only [← smul_eq_mul] using isTheta_const_smul_right hc

alias ⟨IsTheta.of_const_mul_right, IsTheta.const_mul_right⟩ := isTheta_const_mul_right
/-
**Asymptotics.IsLittleO.right_isTheta_add** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics
.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {l : F
ilter α} {f₁ f₂ : α → E'},   f₁ =o[l] f₂ → f₂ =Θ[l] (f₁ + f₂)
参数：f₁ + f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.right_isBigO_add`：∀ {α : Type u_1} {E' : Type u_6}
 [inst : SeminormedAddCommGroup E'] {l : Filter α} {f₁ f₂ : α → E'},   f₁ =o[l] 
f₂ → f₂ =O[l] fun x => f₁ x …
· 使用定理 `Asymptotics.IsLittleO.add_isBigO`：∀ {α : Type u_1} {F : Type u_4} {E' : 
Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l 
: Filter α} {f₁ f₂ : α…
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
-/
theorem IsLittleO.right_isTheta_add {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =Θ[l] (f₁ + f₂) :=
  ⟨h.right_isBigO_add, h.add_isBigO (isBigO_refl _ _)⟩
/-
**Asymptotics.IsLittleO.right_isTheta_add'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {l : F
ilter α} {f₁ f₂ : α → E'},   f₁ =o[l] f₂ → f₂ =Θ[l] (f₂ + f₁)
参数：f₂ + f₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.right_isTheta_add`：∀ {α : Type u_1} {E' : Type u_6
} [inst : SeminormedAddCommGroup E'] {l : Filter α} {f₁ f₂ : α → E'},   f₁ =o[l]
 f₂ → f₂ =Θ[l] (f₁ + f₂)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsLittleO.right_isTheta_add' {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =Θ[l] (f₂ + f₁) :=
  add_comm f₁ f₂ ▸ h.right_isTheta_add
/-
**Asymptotics.IsTheta.add_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsThe
ta`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {l : Filter α}   {f₁ f₂ : α → E'} {g : α → F}, f₁ =Θ[
l] g → f₂ =o[l] g → (f₁ + f₂) =Θ[l] g
参数：f₁ + f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5
} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddCom
mGroup F'] {l :…
· 使用定理 `Asymptotics.IsTheta.symm`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
Θ[l] g → g =Θ[…
· 使用定理 `Asymptotics.IsLittleO.right_isTheta_add'`：∀ {α : Type u_1} {E' : Type u_
6} [inst : SeminormedAddCommGroup E'] {l : Filter α} {f₁ f₂ : α → E'},   f₁ =o[l
] f₂ → f₂ =Θ[l] (f₂ + f₁)
· 使用定理 `Asymptotics.IsLittleO.trans_isTheta`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Semino
rmedAddCommGroup G'] {l :…
-/
lemma IsTheta.add_isLittleO {f₁ f₂ : α → E'} {g : α → F}
    (hΘ : f₁ =Θ[l] g) (ho : f₂ =o[l] g) : (f₁ + f₂) =Θ[l] g :=
  (ho.trans_isTheta hΘ.symm).right_isTheta_add'.symm.trans hΘ
/-
**Asymptotics.IsLittleO.add_isTheta** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLit
tleO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {l : Filter α}   {f₁ f₂ : α → E'} {g : α → F}, f₁ =o[
l] g → f₂ =Θ[l] g → (f₁ + f₂) =Θ[l] g
参数：f₁ + f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.add_isLittleO`：∀ {α : Type u_1} {F : Type u_4} {E' :
 Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {l : Filter α}  
 {f₁ f₂ : α → E'} {g : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma IsLittleO.add_isTheta {f₁ f₂ : α → E'} {g : α → F}
    (ho : f₁ =o[l] g) (hΘ : f₂ =Θ[l] g) : (f₁ + f₂) =Θ[l] g :=
  add_comm f₁ f₂ ▸ hΘ.add_isLittleO ho
/-
**Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Asy
mptotics`。
形式化陈述：isTheta_of_div_tendsto_nhds_ne_zero {c : 𝕜} {f g : α -> 𝕜} (h : Tendsto (f
un x => g x / f x) l (𝓝 c)) (hc : c != 0) : f =Θ[l] g
参数：h : Tendsto (fun x => g x / f x) l (𝓝 c)；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_of_div_tendsto_nhds_of_ne_zero`：isBigO_of_div_tendsto
_nhds_of_ne_zero {l : Filter α} {f g : α -> 𝕜} {a : 𝕜} (h : Tendsto (fun x => g 
x / f x) l (𝓝 a)) (ha : a != 0) : f =O[…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.inv₀`：Filter.Tendsto.inv₀ {a : G₀} (hf : Tendsto f l (𝓝 a
)) (ha : a != 0) : Tendsto (fun x => (f x)⁻¹) l (𝓝 a⁻¹)
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem isTheta_of_div_tendsto_nhds_ne_zero {c : 𝕜} {f g : α → 𝕜}
    (h : Tendsto (fun x ↦ g x / f x) l (𝓝 c)) (hc : c ≠ 0) :
    f =Θ[l] g := by
  refine ⟨isBigO_of_div_tendsto_nhds_of_ne_zero h hc,
    isBigO_of_div_tendsto_nhds_of_ne_zero ?_ (inv_ne_zero hc)⟩
  convert! h.inv₀ hc using 1
  ext
  simp

section

variable {f : α × β → E} {g : α × β → F} {l' : Filter β}

/-
**Asymptotics.IsTheta.fiberwise_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsT
heta`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {l : Filter α}   {f : α × β → E} {g : α × β → F} {l' : Fil
ter β},   f =Θ[l ×ˢ l'] g → ∀ᶠ (x : α) in l, (fun x_1 => f (x, x_1)) =Θ[l'] fun 
x_1 => g (x, x_1)
参数：x : α；fun x_1 => f (x, x_1)；x, x_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Asymptotics.IsBigO.fiberwise_right`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α}   {f 
: α × β → E} {g : α × β …
-/
protected theorem IsTheta.fiberwise_right :
    f =Θ[l ×ˢ l'] g → ∀ᶠ x in l, (f ⟨x, ·⟩) =Θ[l'] (g ⟨x, ·⟩) := by
  simp only [IsTheta, eventually_and]
  exact fun ⟨h₁, h₂⟩ ↦ ⟨h₁.fiberwise_right, h₂.fiberwise_right⟩
/-
**Asymptotics.IsTheta.fiberwise_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTh
eta`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {l : Filter α}   {f : α × β → E} {g : α × β → F} {l' : Fil
ter β},   f =Θ[l ×ˢ l'] g → ∀ᶠ (y : β) in l', (fun x => f (x, y)) =Θ[l] fun x =>
 g (x, y)
参数：y : β；fun x => f (x, y)；x, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Asymptotics.IsBigO.fiberwise_left`：∀ {α : Type u_1} {β : Type u_2} {E : 
Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α}   {f :
 α × β → E} {g : α × β …
-/
protected theorem IsTheta.fiberwise_left :
    f =Θ[l ×ˢ l'] g → ∀ᶠ y in l', (f ⟨·, y⟩) =Θ[l] (g ⟨·, y⟩) := by
  simp only [IsTheta, eventually_and]
  exact fun ⟨h₁, h₂⟩ ↦ ⟨h₁.fiberwise_left, h₂.fiberwise_left⟩

end

section

variable (l' : Filter β)

/-
**Asymptotics.IsTheta.comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l : Filter α} (l' : Filter β), 
f =Θ[l] g → (f ∘ Prod.fst) =Θ[l ×ˢ l'] (g ∘ Prod.fst)
参数：l' : Filter β；f ∘ Prod.fst；g ∘ Prod.fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.comp_fst`：∀ {α : Type u_1} {β : Type u_2} {E : Type u
_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {
l : Filter α} (l'…
-/
protected theorem IsTheta.comp_fst : f =Θ[l] g → (f ∘ Prod.fst) =Θ[l ×ˢ l'] (g ∘ Prod.fst) := by
  simp only [IsTheta]
  exact fun ⟨h₁, h₂⟩ ↦ ⟨h₁.comp_fst l', h₂.comp_fst l'⟩
/-
**Asymptotics.IsTheta.comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l : Filter α} (l' : Filter β), 
f =Θ[l] g → (f ∘ Prod.snd) =Θ[l' ×ˢ l] (g ∘ Prod.snd)
参数：l' : Filter β；f ∘ Prod.snd；g ∘ Prod.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.comp_snd`：∀ {α : Type u_1} {β : Type u_2} {E : Type u
_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {
l : Filter α} (l'…
-/
protected theorem IsTheta.comp_snd : f =Θ[l] g → (f ∘ Prod.snd) =Θ[l' ×ˢ l] (g ∘ Prod.snd) := by
  simp only [IsTheta]
  exact fun ⟨h₁, h₂⟩ ↦ ⟨h₁.comp_snd l', h₂.comp_snd l'⟩

end

end Asymptotics

namespace ContinuousOn

variable {α E F : Type*} [NormedAddGroup E] [SeminormedAddGroup F] [TopologicalSpace α]
  {s : Set α} {f : α → E} {c : F}

/-
**ContinuousOn.isTheta_principal** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddGroup E] [
inst_1 : SeminormedAddGroup F]   [inst_2 : TopologicalSpace α] {s : Set α} {f : 
α → E} {c : F},   ContinuousOn f s → IsCompact s → ‖c‖ ≠ 0 → (∀ i ∈ s, f i ≠ 0) 
→ f =Θ[Filter.principal s] fun x => c
参数：∀ i ∈ s, f i ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.isBigO_principal`：∀ {α : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : TopologicalSpace α] {s : Set α} {f : α → E} {c : F}   [inst_1 : Se
minormedAddGroup E]…
· 使用定理 `ContinuousOn.isBigO_rev_principal`：∀ {α : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : TopologicalSpace α] {s : Set α} {f : α → E}   [inst_1 : Normed
AddGroup E] [inst_2 : S…
-/
protected theorem isTheta_principal
    (hf : ContinuousOn f s) (hs : IsCompact s) (hc : ‖c‖ ≠ 0) (hC : ∀ i ∈ s, f i ≠ 0) :
    f =Θ[𝓟 s] fun _ => c :=
  ⟨hf.isBigO_principal hs hc, hf.isBigO_rev_principal hs hC c⟩

end ContinuousOn

