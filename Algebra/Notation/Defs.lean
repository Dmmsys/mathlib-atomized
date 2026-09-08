/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
module

public import Mathlib.Tactic.Simps.NotationClass
public import Mathlib.Tactic.ToAdditive

/-!
# Typeclasses for algebraic operations

Notation typeclass for `Inv`, the multiplicative analogue of `Neg`.

We also introduce notation classes `SMul` and `VAdd` for multiplicative and additive
actions.

We introduce the notation typeclass `Star` for algebraic structures with a star operation. Note: to
accommodate diverse notational preferences, no default notation is provided for `Star.star`.

`SMul` is typically, but not exclusively, used for scalar multiplication-like operators.
See the module `Algebra.Torsor.Defs` for a motivating example for the name `VAdd` (vector addition).

Note `Zero` has already been defined in core Lean.

## Notation

- `a • b` is used as notation for `HSMul.hSMul a b`.
- `a +ᵥ b` is used as notation for `HVAdd.hVAdd a b`.

-/

public section

assert_not_exists Function.Bijective

universe u v w


/--
The notation typeclass for heterogeneous additive actions.
This enables the notation `a +ᵥ b : γ` where `a : α`, `b : β`.
-/
/-
**HVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type v → outParam (Type w) → Type (max (max u v) w)
参数：Type w；max (max u v) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The notation typeclass for heterogeneous additive actions.
This enables the notation `a +ᵥ b : γ` where `a : α`, `b : β`.
-/
class HVAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a +ᵥ b` computes the sum of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hVAdd : α → β → γ

attribute [notation_class smul Simps.copySecond] HSMul
attribute [notation_class nsmul Simps.nsmulArgs] HSMul
attribute [notation_class zsmul Simps.zsmulArgs] HSMul
attribute [notation_class vadd Simps.copySecond] HVAdd

/-- Type class for the `+ᵥ` notation. -/
/-
**VAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type v → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type class for the `+ᵥ` notation.
-/
class VAdd (G : Type u) (P : Type v) where
  /-- `a +ᵥ b` computes the sum of `a` and `b`. The meaning of this notation is type-dependent,
  but it is intended to be used for left actions. -/
  vadd : G → P → P

/-- Type class for the `-ᵥ` notation. -/
/-
**VSub** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：outParam (Type u_1) → Type u_2 → Type (max u_1 u_2)
参数：Type u_1；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type class for the `-ᵥ` notation.
-/
class VSub (G : outParam Type*) (P : Type*) where
  /-- `a -ᵥ b` computes the difference of `a` and `b`. The meaning of this notation is
  type-dependent, but it is intended to be used for additive torsors. -/
  vsub : P → P → G

/-- Type class for the `/ₛ` notation. -/
@[to_additive (attr := ext)]
/-
**SDiv** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：SDiv (G : outParam Type*) (P : Type*) where /-- `a /ₛ b` computes the quot
ient of `a` and `b`. The meaning of this notation is type-dependent, but it is i
ntended to be used for multiplicative torsors. -/ sdiv : P -> P -> G  attribute 
[to_additive existing] SMul HSMul attribute [to_additive (attr
参数：G : outParam Type*；P : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type class for the `/ₛ` notation.
-/
class SDiv (G : outParam Type*) (P : Type*) where
  /-- `a /ₛ b` computes the quotient of `a` and `b`. The meaning of this notation is
  type-dependent, but it is intended to be used for multiplicative torsors. -/
  sdiv : P → P → G

attribute [to_additive existing] SMul HSMul
attribute [to_additive (attr := default_instance)] instHSMul

attribute [ext] SMul VAdd

@[inherit_doc] infixr:65 " +ᵥ " => HVAdd.hVAdd
@[inherit_doc] infixl:65 " -ᵥ " => VSub.vsub
@[inherit_doc] infixl:65 " /ₛ " => SDiv.sdiv

recommended_spelling "vadd" for "+ᵥ" in [HVAdd.hVAdd, «term_+ᵥ_»]
recommended_spelling "vsub" for "-ᵥ" in [VSub.vsub, «term_-ᵥ_»]
recommended_spelling "sdiv" for "/ₛ" in [SDiv.sdiv, «term_/ₛ_»]

variable {G : Type*}

section Star

/-- Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
/-
**Star** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Notation typeclass (with no default notation!) for an algebraic structure with a
 star operation.
-/
class Star (R : Type u) where
  star : R → R

export Star (star)

/-- A star operation (e.g. complex conjugate).
-/
add_decl_doc star

end Star

section ite
variable {α : Type*} (P : Prop) [Decidable P]

section Mul
variable [Mul α]

@[to_additive]
/-
**mul_dite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_dite (a : α) (b : P -> α) (c : ¬P -> α) : (a * if h : P then b h else 
c h) = if h : P then a * b h else a * c h
参数：a : α；b : P -> α；c : ¬P -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma mul_dite (a : α) (b : P → α) (c : ¬P → α) :
    (a * if h : P then b h else c h) = if h : P then a * b h else a * c h := by split <;> rfl

@[to_additive]
/-
**mul_ite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * b else a * 
c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_dite`：mul_dite (a : α) (b : P -> α) (c : ¬P -> α) : (a * if h : P th
en b h else c h) = if h : P then a * b h else a * c h
-/
lemma mul_ite (a b c : α) : (a * if P then b else c) = if P then a * b else a * c := mul_dite ..

@[to_additive]
/-
**dite_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dite_mul (a : P -> α) (b : ¬P -> α) (c : α) : (if h : P then a h else b h)
 * c = if h : P then a h * c else b h * c
参数：a : P -> α；b : ¬P -> α；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma dite_mul (a : P → α) (b : ¬P → α) (c : α) :
    (if h : P then a h else b h) * c = if h : P then a h * c else b h * c := by split <;> rfl

@[to_additive]
/-
**ite_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * c else b * 
c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `dite_mul`：dite_mul (a : P -> α) (b : ¬P -> α) (c : α) : (if h : P then a
 h else b h) * c = if h : P then a h * c else b h * c
-/
lemma ite_mul (a b c : α) : (if P then a else b) * c = if P then a * c else b * c := dite_mul ..

-- We make `mul_ite` and `ite_mul` simp lemmas, but not `add_ite` or `ite_add`.
-- The problem we're trying to avoid is dealing with sums of the form `∑ x ∈ s, (f x + ite P 1 0)`,
-- in which `add_ite` followed by `sum_ite` would needlessly slice up
-- the `f x` terms according to whether `P` holds at `x`.
-- There doesn't appear to be a corresponding difficulty so far with `mul_ite` and `ite_mul`.
attribute [simp] mul_dite dite_mul mul_ite ite_mul

@[to_additive]
/-
**dite_mul_dite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dite_mul_dite (a : P -> α) (b : ¬P -> α) (c : P -> α) (d : ¬P -> α) : ((if
 h : P then a h else b h) * if h : P then c h else d h) = if h : P then a h * c 
h else b h * d h
参数：a : P -> α；b : ¬P -> α；c : P -> α；d : ¬P -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma dite_mul_dite (a : P → α) (b : ¬P → α) (c : P → α) (d : ¬P → α) :
    ((if h : P then a h else b h) * if h : P then c h else d h) =
      if h : P then a h * c h else b h * d h := by split <;> rfl

@[to_additive]
/-
**ite_mul_ite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ite_mul_ite (a b c d : α) : ((if P then a else b) * if P then c else d) = 
if P then a * c else b * d
参数：a b c d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma ite_mul_ite (a b c d : α) :
    ((if P then a else b) * if P then c else d) = if P then a * c else b * d := by split <;> rfl

end Mul

/-
**neg_ite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_ite {α : Type*} (P : Prop) [Decidable P] [Neg α] (b : α) (c : α) : -(i
f P then b else c) = if P then -b else -c
参数：P : Prop；b : α；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma neg_ite {α : Type*} (P : Prop) [Decidable P] [Neg α] (b : α) (c : α) :
    -(if P then b else c) = if P then -b else -c := by split <;> rfl

section Div
variable [Div α]

@[to_additive]
/-
**div_dite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_dite (a : α) (b : P -> α) (c : ¬P -> α) : (a / if h : P then b h else 
c h) = if h : P then a / b h else a / c h
参数：a : α；b : P -> α；c : ¬P -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma div_dite (a : α) (b : P → α) (c : ¬P → α) :
    (a / if h : P then b h else c h) = if h : P then a / b h else a / c h := by split <;> rfl

@[to_additive]
/-
**div_ite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_ite (a b c : α) : (a / if P then b else c) = if P then a / b else a / 
c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_dite`：div_dite (a : α) (b : P -> α) (c : ¬P -> α) : (a / if h : P th
en b h else c h) = if h : P then a / b h else a / c h
-/
lemma div_ite (a b c : α) : (a / if P then b else c) = if P then a / b else a / c := div_dite ..

@[to_additive]
/-
**dite_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dite_div (a : P -> α) (b : ¬P -> α) (c : α) : (if h : P then a h else b h)
 / c = if h : P then a h / c else b h / c
参数：a : P -> α；b : ¬P -> α；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma dite_div (a : P → α) (b : ¬P → α) (c : α) :
    (if h : P then a h else b h) / c = if h : P then a h / c else b h / c := by split <;> rfl

@[to_additive]
/-
**ite_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ite_div (a b c : α) : (if P then a else b) / c = if P then a / c else b / 
c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `dite_div`：dite_div (a : P -> α) (b : ¬P -> α) (c : α) : (if h : P then a
 h else b h) / c = if h : P then a h / c else b h / c
-/
lemma ite_div (a b c : α) : (if P then a else b) / c = if P then a / c else b / c := dite_div ..

@[to_additive]
/-
**dite_div_dite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dite_div_dite (a : P -> α) (b : ¬P -> α) (c : P -> α) (d : ¬P -> α) : ((if
 h : P then a h else b h) / if h : P then c h else d h) = if h : P then a h / c 
h else b h / d h
参数：a : P -> α；b : ¬P -> α；c : P -> α；d : ¬P -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma dite_div_dite (a : P → α) (b : ¬P → α) (c : P → α) (d : ¬P → α) :
    ((if h : P then a h else b h) / if h : P then c h else d h) =
      if h : P then a h / c h else b h / d h := by split <;> rfl

@[to_additive]
/-
**ite_div_ite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ite_div_ite (a b c d : α) : ((if P then a else b) / if P then c else d) = 
if P then a / c else b / d
参数：a b c d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `dite_div_dite`：dite_div_dite (a : P -> α) (b : ¬P -> α) (c : P -> α) (d 
: ¬P -> α) : ((if h : P then a h else b h) / if h : P then c h else d h) = if h 
: P…
-/
lemma ite_div_ite (a b c d : α) :
    ((if P then a else b) / if P then c else d) = if P then a / c else b / d := dite_div_dite ..

end Div
end ite

variable {α : Type u}

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 20) One.instNonempty [One α] : Nonempty α := ⟨1⟩

@[to_additive]
/-
**Subsingleton.eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsingleton.eq_one [One α] [Subsingleton α] (a : α) : a = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem Subsingleton.eq_one [One α] [Subsingleton α] (a : α) : a = 1 :=
  Subsingleton.elim _ _
