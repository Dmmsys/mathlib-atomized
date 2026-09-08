/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Logic.Function.Basic

/-!
# Semiconjugate and commuting maps

We define the following predicates:

* `Function.Semiconj`: `f : α → β` semiconjugates `ga : α → α` to `gb : β → β` if `f ∘ ga = gb ∘ f`;
* `Function.Semiconj₂`: `f : α → β` semiconjugates a binary operation `ga : α → α → α`
  to `gb : β → β → β` if `f (ga x y) = gb (f x) (f y)`;
* `Function.Commute`: `f : α → α` commutes with `g : α → α` if `f ∘ g = g ∘ f`,
  or equivalently `Semiconj f g g`.
-/

@[expose] public section

namespace Function

variable {α : Type*} {β : Type*} {γ : Type*}

/--
We say that `f : α → β` semiconjugates `ga : α → α` to `gb : β → β` if `f ∘ ga = gb ∘ f`.
We use `∀ x, f (ga x) = gb (f x)` as the definition, so given `h : Function.Semiconj f ga gb` and
`a : α`, we have `h a : f (ga a) = gb (f a)` and `h.comp_eq : f ∘ ga = gb ∘ f`.
-/
/-
**Function.Semiconj** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：Semiconj (f : α -> β) (ga : α -> α) (gb : β -> β) : Prop
参数：f : α -> β；ga : α -> α；gb : β -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `f : α → β` semiconjugates `ga : α → α` to `gb : β → β` if `f ∘ ga =
 gb ∘ f`.
We use `∀ x, f (ga x) = gb (f x)` as the definition, so given `h : Function.Semi
conj f ga gb` and
`a : α`, we have `h a : f (ga a) = gb (f a)` and `h.comp_eq : f ∘ ga = gb ∘ f`.
-/
def Semiconj (f : α → β) (ga : α → α) (gb : β → β) : Prop :=
  ∀ x, f (ga x) = gb (f x)

namespace Semiconj

variable {f fab : α → β} {fbc : β → γ} {ga ga' : α → α} {gb gb' : β → β} {gc : γ → γ}

/-- Definition of `Function.Semiconj` in terms of functional equality. -/
/-
**Function.Semiconj._root_.Function.semiconj_iff_comp_eq** 是 Mathlib 中的一个引理，位于命名
空间 `Function.Semiconj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of `Function.Semiconj` in terms of functional equality.
-/
lemma _root_.Function.semiconj_iff_comp_eq : Semiconj f ga gb ↔ f ∘ ga = gb ∘ f := funext_iff.symm

protected alias ⟨comp_eq, _⟩ := semiconj_iff_comp_eq
/-
**Function.Semiconj.eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α} {gb : β → β},   F
unction.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x)
参数：x : α；ga x；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem eq (h : Semiconj f ga gb) (x : α) : f (ga x) = gb (f x) :=
  h x

/-- If `f` semiconjugates `ga` to `gb` and `ga'` to `gb'`,
then it semiconjugates `ga ∘ ga'` to `gb ∘ gb'`. -/
/-
**Function.Semiconj.comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：comp_right (h : Semiconj f ga gb) (h' : Semiconj f ga' gb') : Semiconj f (
ga ∘ ga') (gb ∘ gb')
参数：h : Semiconj f ga gb；h' : Semiconj f ga' gb'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Semiconj.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : 
α → α} {gb : β → β},   Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x
)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` semiconjugates `ga` to `gb` and `ga'` to `gb'`,
then it semiconjugates `ga ∘ ga'` to `gb ∘ gb'`.
-/
theorem comp_right (h : Semiconj f ga gb) (h' : Semiconj f ga' gb') :
    Semiconj f (ga ∘ ga') (gb ∘ gb') := fun x ↦ by
  simp only [comp_apply, h.eq, h'.eq]

/-- If `fab : α → β` semiconjugates `ga` to `gb` and `fbc : β → γ` semiconjugates `gb` to `gc`,
then `fbc ∘ fab` semiconjugates `ga` to `gc`.

See also `Function.Semiconj.comp_left` for a version with reversed arguments. -/
/-
**Function.Semiconj.trans** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {fab : α → β} {fbc : β → γ}
 {ga : α → α} {gb : β → β} {gc : γ → γ},   Function.Semiconj fab ga gb → Functio
n.Semiconj fbc gb gc → Function.Semiconj (fbc ∘ fab) ga gc
参数：fbc ∘ fab。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Semiconj.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : 
α → α} {gb : β → β},   Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x
)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `fab : α → β` semiconjugates `ga` to `gb` and `fbc : β → γ` semiconjugates `g
b` to `gc`,
then `fbc ∘ fab` semiconjugates `ga` to `gc`.

See also `Function.Semiconj.comp_left` for a version with reversed arguments.
-/
protected theorem trans (hab : Semiconj fab ga gb) (hbc : Semiconj fbc gb gc) :
    Semiconj (fbc ∘ fab) ga gc := fun x ↦ by
  simp only [comp_apply, hab.eq, hbc.eq]

/-- If `fbc : β → γ` semiconjugates `gb` to `gc` and `fab : α → β` semiconjugates `ga` to `gb`,
then `fbc ∘ fab` semiconjugates `ga` to `gc`.

See also `Function.Semiconj.trans` for a version with reversed arguments.

**Backward compatibility note:** before 2024-01-13,
this lemma used to have the same order of arguments that `Function.Semiconj.trans` has now. -/
/-
**Function.Semiconj.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：comp_left (hbc : Semiconj fbc gb gc) (hab : Semiconj fab ga gb) : Semiconj
 (fbc ∘ fab) ga gc
参数：hbc : Semiconj fbc gb gc；hab : Semiconj fab ga gb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Semiconj.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{fab : α → β} {fbc : β → γ} {ga : α → α} {gb : β → β} {gc : γ → γ},   Function.S
emiconj fab g…

--- 原说明 ---
If `fbc : β → γ` semiconjugates `gb` to `gc` and `fab : α → β` semiconjugates `g
a` to `gb`,
then `fbc ∘ fab` semiconjugates `ga` to `gc`.

See also `Function.Semiconj.trans` for a version with reversed arguments.

**Backward compatibility note:** before 2024-01-13,
this lemma used to have the same order of arguments that `Function.Semiconj.tran
s` has now.
-/
theorem comp_left (hbc : Semiconj fbc gb gc) (hab : Semiconj fab ga gb) :
    Semiconj (fbc ∘ fab) ga gc :=
  hab.trans hbc

/-- Any function semiconjugates the identity function to the identity function. -/
/-
**Function.Semiconj.id_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：id_right : Semiconj f id id
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any function semiconjugates the identity function to the identity function.
-/
theorem id_right : Semiconj f id id := fun _ ↦ rfl

/-- The identity function semiconjugates any function to itself. -/
/-
**Function.Semiconj.id_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：id_left : Semiconj id ga ga
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity function semiconjugates any function to itself.
-/
theorem id_left : Semiconj id ga ga := fun _ ↦ rfl

/-- If `f : α → β` semiconjugates `ga : α → α` to `gb : β → β`,
`ga'` is a right inverse of `ga`, and `gb'` is a left inverse of `gb`,
then `f` semiconjugates `ga'` to `gb'` as well. -/
/-
**Function.Semiconj.inverses_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`
。
形式化陈述：inverses_right (h : Semiconj f ga gb) (ha : RightInverse ga' ga) (hb : Lef
tInverse gb' gb) : Semiconj f ga' gb'
参数：h : Semiconj f ga gb；ha : RightInverse ga' ga；hb : LeftInverse gb' gb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Semiconj.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : 
α → α} {gb : β → β},   Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x
)

--- 原说明 ---
If `f : α → β` semiconjugates `ga : α → α` to `gb : β → β`,
`ga'` is a right inverse of `ga`, and `gb'` is a left inverse of `gb`,
then `f` semiconjugates `ga'` to `gb'` as well.
-/
theorem inverses_right (h : Semiconj f ga gb) (ha : RightInverse ga' ga) (hb : LeftInverse gb' gb) :
    Semiconj f ga' gb' := fun x ↦ by
  rw [← hb (f (ga' x)), ← h.eq, ha x]

/-- If `f` semiconjugates `ga` to `gb` and `f'` is both a left and a right inverse of `f`,
then `f'` semiconjugates `gb` to `ga`. -/
/-
**Function.Semiconj.inverse_left** 是 Mathlib 中的一个引理，位于命名空间 `Function.Semiconj`。
形式化陈述：inverse_left {f' : β -> α} (h : Semiconj f ga gb) (hf₁ : LeftInverse f' f)
 (hf₂ : RightInverse f' f) : Semiconj f' gb ga
参数：h : Semiconj f ga gb；hf₁ : LeftInverse f' f；hf₂ : RightInverse f' f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f

--- 原说明 ---
If `f` semiconjugates `ga` to `gb` and `f'` is both a left and a right inverse o
f `f`,
then `f'` semiconjugates `gb` to `ga`.
-/
lemma inverse_left {f' : β → α} (h : Semiconj f ga gb)
    (hf₁ : LeftInverse f' f) (hf₂ : RightInverse f' f) : Semiconj f' gb ga := fun x ↦ by
  rw [← hf₁.injective.eq_iff, h, hf₂, hf₂]

/-- If `f : α → β` semiconjugates `ga : α → α` to `gb : β → β`,
then `Option.map f` semiconjugates `Option.map ga` to `Option.map gb`. -/
/-
**Function.Semiconj.option_map** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α} {gb : β → β},   F
unction.Semiconj f ga gb → Function.Semiconj (Option.map f) (Option.map ga) (Opt
ion.map gb)
参数：Option.map f；Option.map ga；Option.map gb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If `f : α → β` semiconjugates `ga : α → α` to `gb : β → β`,
then `Option.map f` semiconjugates `Option.map ga` to `Option.map gb`.
-/
theorem option_map {f : α → β} {ga : α → α} {gb : β → β} (h : Semiconj f ga gb) :
    Semiconj (Option.map f) (Option.map ga) (Option.map gb)
  | none => rfl
  | some _ => congr_arg some <| h _

end Semiconj

/--
Two maps `f g : α → α` commute if `f (g x) = g (f x)` for all `x : α`.
Given `h : Function.commute f g` and `a : α`, we have `h a : f (g a) = g (f a)` and
`h.comp_eq : f ∘ g = g ∘ f`.
-/
/-
**Function.Commute** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：{α : Type u_1} → (α → α) → (α → α) → Prop
参数：α → α；α → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two maps `f g : α → α` commute if `f (g x) = g (f x)` for all `x : α`.
Given `h : Function.commute f g` and `a : α`, we have `h a : f (g a) = g (f a)` 
and
`h.comp_eq : f ∘ g = g ∘ f`.
-/
protected def Commute (f g : α → α) : Prop :=
  Semiconj f g g

open Function (Commute)

/-- Reinterpret `Function.Semiconj f g g` as `Function.Commute f g`. These two predicates are
definitionally equal but have different dot-notation lemmas. -/
/-
**Function.Semiconj.commute** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：∀ {α : Type u_1} {f g : α → α}, Function.Semiconj f g g → Function.Commute
 f g
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `Function.Semiconj f g g` as `Function.Commute f g`. These two predi
cates are
definitionally equal but have different dot-notation lemmas.
-/
theorem Semiconj.commute {f g : α → α} (h : Semiconj f g g) : Commute f g := h

namespace Commute

variable {f f' g g' : α → α}

/-- Reinterpret `Function.Commute f g` as `Function.Semiconj f g g`. These two predicates are
definitionally equal but have different dot-notation lemmas. -/
/-
**Function.Commute.semiconj** 是 Mathlib 中的一个定理，位于命名空间 `Function.Commute`。
形式化陈述：semiconj (h : Commute f g) : Semiconj f g g
参数：h : Commute f g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `Function.Commute f g` as `Function.Semiconj f g g`. These two predi
cates are
definitionally equal but have different dot-notation lemmas.
-/
theorem semiconj (h : Commute f g) : Semiconj f g g := h

@[refl]
/-
**Function.Commute.refl** 是 Mathlib 中的一个定理，位于命名空间 `Function.Commute`。
形式化陈述：refl (f : α -> α) : Commute f f
参数：f : α -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl (f : α → α) : Commute f f := fun _ ↦ Eq.refl _

@[symm]
/-
**Function.Commute.symm** 是 Mathlib 中的一个定理，位于命名空间 `Function.Commute`。
形式化陈述：symm (h : Commute f g) : Commute g f
参数：h : Commute f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem symm (h : Commute f g) : Commute g f := fun x ↦ (h x).symm

/-- If `f` commutes with `g` and `g'`, then it commutes with `g ∘ g'`. -/
/-
**Function.Commute.comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Commute`。
形式化陈述：comp_right (h : Commute f g) (h' : Commute f g') : Commute f (g ∘ g')
参数：h : Commute f g；h' : Commute f g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Semiconj.comp_right`：comp_right (h : Semiconj f ga gb) (h' : Se
miconj f ga' gb') : Semiconj f (ga ∘ ga') (gb ∘ gb')

--- 原说明 ---
If `f` commutes with `g` and `g'`, then it commutes with `g ∘ g'`.
-/
theorem comp_right (h : Commute f g) (h' : Commute f g') : Commute f (g ∘ g') :=
  Semiconj.comp_right h h'

/-- If `f` and `f'` commute with `g`, then `f ∘ f'` commutes with `g` as well. -/
nonrec theorem comp_left (h : Commute f g) (h' : Commute f' g) : Commute (f ∘ f') g :=
  h.comp_left h'

/-- Any self-map commutes with the identity map. -/
/-
**Function.Commute.id_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Commute`。
形式化陈述：id_right : Commute f id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Semiconj.id_right`：id_right : Semiconj f id id

--- 原说明 ---
Any self-map commutes with the identity map.
-/
theorem id_right : Commute f id := Semiconj.id_right

/-- The identity map commutes with any self-map. -/
/-
**Function.Commute.id_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Commute`。
形式化陈述：id_left : Commute id f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Semiconj.id_left`：id_left : Semiconj id ga ga

--- 原说明 ---
The identity map commutes with any self-map.
-/
theorem id_left : Commute id f :=
  Semiconj.id_left

/-- If `f` commutes with `g`, then `Option.map f` commutes with `Option.map g`. -/
nonrec theorem option_map {f g : α → α} (h : Commute f g) : Commute (Option.map f) (Option.map g) :=
  h.option_map

end Commute

/--
A map `f` semiconjugates a binary operation `ga` to a binary operation `gb` if
for all `x`, `y` we have `f (ga x y) = gb (f x) (f y)`. E.g., a `MonoidHom`
semiconjugates `(*)` to `(*)`.
-/
/-
**Function.Semiconj** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：Semiconj (f : α -> β) (ga : α -> α) (gb : β -> β) : Prop
参数：f : α -> β；ga : α -> α；gb : β -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f` semiconjugates a binary operation `ga` to a binary operation `gb` if
for all `x`, `y` we have `f (ga x y) = gb (f x) (f y)`. E.g., a `MonoidHom`
semiconjugates `(*)` to `(*)`.
-/
def Semiconj₂ (f : α → β) (ga : α → α → α) (gb : β → β → β) : Prop :=
  ∀ x y, f (ga x y) = gb (f x) (f y)

namespace Semiconj₂

variable {f : α → β} {ga : α → α → α} {gb : β → β → β}

/-
**Function.Semiconj₂.eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj₂`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α → α} {gb : β → β →
 β},   Function.Semiconj₂ f ga gb → ∀ (x y : α), f (ga x y) = gb (f x) (f y)
参数：x y : α；ga x y；f x；f y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem eq (h : Semiconj₂ f ga gb) (x y : α) : f (ga x y) = gb (f x) (f y) :=
  h x y
/-
**Function.Semiconj₂.comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj₂`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α → α} {gb : β → β →
 β},   Function.Semiconj₂ f ga gb → Function.bicompr f ga = Function.bicompl gb 
f f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem comp_eq (h : Semiconj₂ f ga gb) : bicompr f ga = bicompl gb f f :=
  funext fun x ↦ funext <| h x
/-
**Function.Semiconj₂.id_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj₂`。
形式化陈述：id_left (op : α -> α -> α) : Semiconj₂ id op op
参数：op : α -> α -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_left (op : α → α → α) : Semiconj₂ id op op := fun _ _ ↦ rfl
/-
**Function.Semiconj₂.comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj₂`。
形式化陈述：comp {f' : β -> γ} {gc : γ -> γ -> γ} (hf' : Semiconj₂ f' gb gc) (hf : Sem
iconj₂ f ga gb) : Semiconj₂ (f' ∘ f) ga gc
参数：hf' : Semiconj₂ f' gb gc；hf : Semiconj₂ f ga gb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Semiconj₂.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga :
 α → α → α} {gb : β → β → β},   Function.Semiconj₂ f ga gb → ∀ (x y : α), f (ga 
x y) = gb (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp {f' : β → γ} {gc : γ → γ → γ} (hf' : Semiconj₂ f' gb gc) (hf : Semiconj₂ f ga gb) :
    Semiconj₂ (f' ∘ f) ga gc := fun x y ↦ by simp only [hf'.eq, hf.eq, comp_apply]
/-
**Function.Semiconj₂.isAssociative_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Sem
iconj₂`。
形式化陈述：isAssociative_right [Std.Associative ga] (h : Semiconj₂ f ga gb) (h_surj :
 Surjective f) : Std.Associative gb
参数：h : Semiconj₂ f ga gb；h_surj : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall₃`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}
,   Function.Surjective f →     ∀ {p : β → β → β → Prop}, (∀ (y₁ y₂ y₃ : β), p y
₁ y₂ y₃) ↔ ∀ (x₁ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Semiconj₂.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga :
 α → α → α} {gb : β → β → β},   Function.Semiconj₂ f ga gb → ∀ (x y : α), f (ga 
x y) = gb (…
· 使用定理 `Std.Associative.assoc`：∀ {α : Sort u} {op : α → α → α} [self : Std.Assoc
iative op] (a b c : α), op (op a b) c = op a (op b c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isAssociative_right [Std.Associative ga] (h : Semiconj₂ f ga gb) (h_surj : Surjective f) :
    Std.Associative gb :=
  ⟨h_surj.forall₃.2 fun x₁ x₂ x₃ ↦ by simp only [← h.eq, Std.Associative.assoc (op := ga)]⟩
/-
**Function.Semiconj₂.isAssociative_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semi
conj₂`。
形式化陈述：isAssociative_left [Std.Associative gb] (h : Semiconj₂ f ga gb) (h_inj : I
njective f) : Std.Associative ga
参数：h : Semiconj₂ f ga gb；h_inj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Semiconj₂.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga :
 α → α → α} {gb : β → β → β},   Function.Semiconj₂ f ga gb → ∀ (x y : α), f (ga 
x y) = gb (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Std.Associative.assoc`：∀ {α : Sort u} {op : α → α → α} [self : Std.Assoc
iative op] (a b c : α), op (op a b) c = op a (op b c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isAssociative_left [Std.Associative gb] (h : Semiconj₂ f ga gb) (h_inj : Injective f) :
    Std.Associative ga :=
  ⟨fun x₁ x₂ x₃ ↦ h_inj <| by simp only [h.eq, Std.Associative.assoc (op := gb)]⟩
/-
**Function.Semiconj₂.isIdempotent_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semi
conj₂`。
形式化陈述：isIdempotent_right [Std.IdempotentOp ga] (h : Semiconj₂ f ga gb) (h_surj :
 Surjective f) : Std.IdempotentOp gb
参数：h : Semiconj₂ f ga gb；h_surj : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Semiconj₂.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga :
 α → α → α} {gb : β → β → β},   Function.Semiconj₂ f ga gb → ∀ (x y : α), f (ga 
x y) = gb (…
· 使用定理 `Std.IdempotentOp.idempotent`：∀ {α : Sort u} {op : α → α → α} [self : Std
.IdempotentOp op] (x : α), op x x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isIdempotent_right [Std.IdempotentOp ga] (h : Semiconj₂ f ga gb) (h_surj : Surjective f) :
    Std.IdempotentOp gb :=
  ⟨h_surj.forall.2 fun x ↦ by simp only [← h.eq, Std.IdempotentOp.idempotent (op := ga)]⟩
/-
**Function.Semiconj₂.isIdempotent_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semic
onj₂`。
形式化陈述：isIdempotent_left [Std.IdempotentOp gb] (h : Semiconj₂ f ga gb) (h_inj : I
njective f) : Std.IdempotentOp ga
参数：h : Semiconj₂ f ga gb；h_inj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Semiconj₂.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga :
 α → α → α} {gb : β → β → β},   Function.Semiconj₂ f ga gb → ∀ (x y : α), f (ga 
x y) = gb (…
· 使用定理 `Std.IdempotentOp.idempotent`：∀ {α : Sort u} {op : α → α → α} [self : Std
.IdempotentOp op] (x : α), op x x = x
-/
theorem isIdempotent_left [Std.IdempotentOp gb] (h : Semiconj₂ f ga gb) (h_inj : Injective f) :
    Std.IdempotentOp ga :=
  ⟨fun x ↦ h_inj <| by rw [h.eq, Std.IdempotentOp.idempotent (op := gb)]⟩

end Semiconj₂

end Function

