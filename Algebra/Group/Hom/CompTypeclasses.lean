/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Logic.Function.CompTypeclasses
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Propositional typeclasses on several monoid homs

This file contains typeclasses used in the definition of equivariant maps,
in the spirit what was initially developed by Frédéric Dupuis and Heather Macbeth for linear maps.
However, we do not expect that all maps should be guessed automatically,
as it happens for linear maps.

If `φ`, `ψ`… are monoid homs and `M`, `N`… are monoids, we add two instances:
* `MonoidHom.CompTriple φ ψ χ`, which expresses that `ψ.comp φ = χ`
* `MonoidHom.IsId φ`, which expresses that `φ = id`

Some basic lemmas are proved:
* `MonoidHom.CompTriple.comp` asserts `MonoidHom.CompTriple φ ψ (ψ.comp φ)`
* `MonoidHom.CompTriple.id_comp` asserts `MonoidHom.CompTriple φ ψ ψ`
  in the presence of `MonoidHom.IsId φ`
* its variant `MonoidHom.CompTriple.comp_id`

TODO :
* align with RingHomCompTriple
* probably rename MonoidHom.CompTriple as MonoidHomCompTriple
  (or, on the opposite, rename RingHomCompTriple as RingHom.CompTriple)
* does one need AddHom.CompTriple ?

-/

public section

section MonoidHomCompTriple

namespace MonoidHom

/-- Class of composing triples -/
/-
**MonoidHom.CompTriple** 是 Mathlib 中的一个归纳类型，位于命名空间 `MonoidHom`。
形式化陈述：{M : Type u_1} →   {N : Type u_2} →     {P : Type u_3} →       [inst : Mon
oid M] → [inst_1 : Monoid N] → [inst_2 : Monoid P] → (M →* N) → (N →* P) → outPa
ram (M →* P) → Prop
参数：M →* N；N →* P；M →* P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class of composing triples
-/
class CompTriple {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (φ : M →* N) (ψ : N →* P) (χ : outParam (M →* P)) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTriple.comp_eq

namespace CompTriple

variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

/-- Class of Id maps -/
/-
**MonoidHom.CompTriple.IsId** 是 Mathlib 中的一个归纳类型，位于命名空间 `MonoidHom.CompTriple`。
形式化陈述：{M : Type u_1} → [inst : Monoid M] → (M →* M) → Prop
参数：M →* M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class of Id maps
-/
class IsId (σ : M →* M) : Prop where
  eq_id : σ = MonoidHom.id M
/-
**MonoidHom.CompTriple.instIsId** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom.CompTriple`
。
形式化陈述：instIsId {M : Type*} [Monoid M] : IsId (MonoidHom.id M) where eq_id
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsId {M : Type*} [Monoid M] : IsId (MonoidHom.id M) where
  eq_id := rfl
/-
**MonoidHom.CompTriple.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom.CompTriple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ : M →* M} [h : _root_.CompTriple.IsId σ] : IsId σ where
  eq_id := by ext; exact congr_fun h.eq_id _
/-
**MonoidHom.CompTriple.instComp_id** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom.CompTrip
le`。
形式化陈述：instComp_id {N P : Type*} [Monoid N] [Monoid P] {φ : N ->* N} [IsId φ] {ψ 
: N ->* P} : CompTriple φ ψ ψ where comp_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.CompTriple.IsId.eq_id`：∀ {M : Type u_1} {inst : Monoid M} {σ :
 M →* M} [self : MonoidHom.CompTriple.IsId σ], σ = MonoidHom.id M
· 使用定理 `MonoidHom.comp_id`：MonoidHom.comp_id [MulOne M] [MulOne N] (f : M ->* N)
 : f.comp (MonoidHom.id M) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instComp_id {N P : Type*} [Monoid N] [Monoid P]
    {φ : N →* N} [IsId φ] {ψ : N →* P} :
    CompTriple φ ψ ψ where
  comp_eq := by simp only [IsId.eq_id, MonoidHom.comp_id]
/-
**MonoidHom.CompTriple.instId_comp** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom.CompTrip
le`。
形式化陈述：instId_comp {M N : Type*} [Monoid M] [Monoid N] {φ : M ->* N} {ψ : N ->* N
} [IsId ψ] : CompTriple φ ψ φ where comp_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.CompTriple.IsId.eq_id`：∀ {M : Type u_1} {inst : Monoid M} {σ :
 M →* M} [self : MonoidHom.CompTriple.IsId σ], σ = MonoidHom.id M
· 使用定理 `MonoidHom.id_comp`：MonoidHom.id_comp [MulOne M] [MulOne N] (f : M ->* N)
 : (MonoidHom.id N).comp f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instId_comp {M N : Type*} [Monoid M] [Monoid N]
    {φ : M →* N} {ψ : N →* N} [IsId ψ] :
    CompTriple φ ψ φ where
  comp_eq := by simp only [IsId.eq_id, MonoidHom.id_comp]
/-
**MonoidHom.CompTriple.comp_inv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom.CompTriple`
。
形式化陈述：comp_inv {φ : M ->* N} {ψ : N ->* M} (h : Function.RightInverse φ ψ) {χ : 
M ->* M} [IsId χ] : CompTriple φ ψ χ where comp_eq
参数：h : Function.RightInverse φ ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.CompTriple.IsId.eq_id`：∀ {M : Type u_1} {inst : Monoid M} {σ :
 M →* M} [self : MonoidHom.CompTriple.IsId σ], σ = MonoidHom.id M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.RightInverse.id`：∀ {α : Sort u_1} {β : Sort u_2} {g : β → α} {f
 : α → β}, Function.RightInverse g f → f ∘ g = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_inv {φ : M →* N} {ψ : N →* M} (h : Function.RightInverse φ ψ)
    {χ : M →* M} [IsId χ] :
    CompTriple φ ψ χ where
  comp_eq := by simp only [IsId.eq_id, ← DFunLike.coe_fn_eq, coe_comp, h.id, coe_id]
/-
**MonoidHom.CompTriple.instRootCompTriple** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom.C
ompTriple`。
形式化陈述：instRootCompTriple {φ : M ->* N} {ψ : N ->* P} {χ : M ->* P} [κ : CompTrip
le φ ψ χ] : _root_.CompTriple φ ψ χ where comp_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.coe_comp`：MonoidHom.coe_comp [MulOne M] [MulOne N] [MulOne P] 
(g : N ->* P) (f : M ->* N) : ↑(g.comp f) = g ∘ f
· 使用定理 `MonoidHom.CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type 
u_3} {inst : Monoid M} {inst_1 : Monoid N} {inst_2 : Monoid P} {φ : M →* N}   {ψ
 : N →* P} {χ : ou…
-/
instance instRootCompTriple {φ : M →* N} {ψ : N →* P} {χ : M →* P} [κ : CompTriple φ ψ χ] :
    _root_.CompTriple φ ψ χ where
  comp_eq := by rw [← MonoidHom.coe_comp, κ.comp_eq]

/-- `φ`, `ψ` and `ψ.comp φ` form a `MonoidHom.CompTriple`

  (to be used with care, because no simplification is done) -/
/-
**MonoidHom.CompTriple.comp** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom.CompTriple`。
形式化陈述：comp {φ : M ->* N} {ψ : N ->* P} : CompTriple φ ψ (ψ.comp φ) where comp_eq
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`φ`, `ψ` and `ψ.comp φ` form a `MonoidHom.CompTriple`

  (to be used with care, because no simplification is done)
-/
theorem comp {φ : M →* N} {ψ : N →* P} :
    CompTriple φ ψ (ψ.comp φ) where
  comp_eq := rfl
/-
**MonoidHom.CompTriple.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom.CompTripl
e`。
形式化陈述：comp_apply {φ : M ->* N} {ψ : N ->* P} {χ : M ->* P} (h : CompTriple φ ψ χ
) (x : M) : ψ (φ x) = χ x
参数：h : CompTriple φ ψ χ；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type 
u_3} {inst : Monoid M} {inst_1 : Monoid N} {inst_2 : Monoid P} {φ : M →* N}   {ψ
 : N →* P} {χ : ou…
· 使用定理 `MonoidHom.comp_apply`：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne
 P] (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x)
-/
lemma comp_apply
    {φ : M →* N} {ψ : N →* P} {χ : M →* P} (h : CompTriple φ ψ χ) (x : M) :
    ψ (φ x) = χ x := by
  rw [← h.comp_eq, MonoidHom.comp_apply]
/-
**MonoidHom.CompTriple.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom.CompTripl
e`。
形式化陈述：comp_assoc {Q : Type*} [Monoid Q] {φ₁ : M ->* N} {φ₂ : N ->* P} {φ₁₂ : M -
>* P} (κ : CompTriple φ₁ φ₂ φ₁₂) {φ₃ : P ->* Q} {φ₂₃ : N ->* Q} (κ' : CompTriple
 φ₂ φ₃ φ₂₃) {φ₁₂₃ : M ->* Q} : CompTriple φ₁ φ₂₃ φ₁₂₃ ↔ CompTriple φ₁₂ φ₃ φ₁₂₃
参数：κ : CompTriple φ₁ φ₂ φ₁₂；κ' : CompTriple φ₂ φ₃ φ₂₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type 
u_3} {inst : Monoid M} {inst_1 : Monoid N} {inst_2 : Monoid P} {φ : M →* N}   {ψ
 : N →* P} {χ : ou…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_assoc {Q : Type*} [Monoid Q]
    {φ₁ : M →* N} {φ₂ : N →* P} {φ₁₂ : M →* P}
    (κ : CompTriple φ₁ φ₂ φ₁₂)
    {φ₃ : P →* Q} {φ₂₃ : N →* Q} (κ' : CompTriple φ₂ φ₃ φ₂₃)
    {φ₁₂₃ : M →* Q} :
    CompTriple φ₁ φ₂₃ φ₁₂₃ ↔ CompTriple φ₁₂ φ₃ φ₁₂₃ := by
  constructor <;>
  · rintro ⟨h⟩
    exact ⟨by simp only [← κ.comp_eq, ← h, ← κ'.comp_eq, MonoidHom.comp_assoc]⟩

end MonoidHom.CompTriple

end MonoidHomCompTriple

