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
Definition of `HVAdd` / `HVAdd` 的定义

English:
class HVAdd
  parameters: (α : Type u) (β : Type v) (γ : outParam (Type w))
  axioms and operations (1):
    - hVAdd : α -> β -> γ

中文:
类 HVAdd
  参数: (α : 类型u) (β : 类型v) (γ : outParam (Type w))
  公理与运算 (1 个):
    - hVAdd : α -> β -> γ
-/
class HVAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a +ᵥ b` computes the sum of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hVAdd : α -> β -> γ

attribute [notation_class smul Simps.copySecond] HSMul
attribute [notation_class nsmul Simps.nsmulArgs] HSMul
attribute [notation_class zsmul Simps.zsmulArgs] HSMul
attribute [notation_class vadd Simps.copySecond] HVAdd

/--
Definition of `VAdd` / `VAdd` 的定义

English:
class VAdd
  parameters: (G : Type u) (P : Type v)
  axioms and operations (1):
    - vadd : G -> P -> P

中文:
类 VAdd
  参数: (G : 类型u) (P : 类型v)
  公理与运算 (1 个):
    - vadd : G -> P -> P
-/
class VAdd (G : Type u) (P : Type v) where
  /-- `a +ᵥ b` computes the sum of `a` and `b`. The meaning of this notation is type-dependent,
  but it is intended to be used for left actions. -/
  vadd : G -> P -> P

/--
Definition of `VSub` / `VSub` 的定义

English:
class VSub
  parameters: (G : outParam Type*) (P : Type*)
  axioms and operations (1):
    - vsub : P -> P -> G

中文:
类 VSub
  参数: (G : outParam 类型) (P : 类型)
  公理与运算 (1 个):
    - vsub : P -> P -> G
-/
class VSub (G : outParam Type*) (P : Type*) where
  /-- `a -ᵥ b` computes the difference of `a` and `b`. The meaning of this notation is
  type-dependent, but it is intended to be used for additive torsors. -/
  vsub : P -> P -> G

/-- Type class for the `/ₛ` notation. -/
@[to_additive (attr := ext)]
/--
Definition of `SDiv` / `SDiv` 的定义

English:
class SDiv
  parameters: (G : outParam Type*) (P : Type*)
  axioms and operations (1):
    - sdiv : P -> P -> G

中文:
类 SDiv
  参数: (G : outParam 类型) (P : 类型)
  公理与运算 (1 个):
    - sdiv : P -> P -> G

Depends on / 依赖: default_instance, instHSMul
-/
class SDiv (G : outParam Type*) (P : Type*) where
  /-- `a /ₛ b` computes the quotient of `a` and `b`. The meaning of this notation is
  type-dependent, but it is intended to be used for multiplicative torsors. -/
  sdiv : P -> P -> G

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

/--
Definition of `Star` / `Star` 的定义

English:
class Star
  parameters: (R : Type u)
  axioms and operations (1):
    - star : R -> R

中文:
类 Star
  参数: (R : 类型u)
  公理与运算 (1 个):
    - star : R -> R
-/
class Star (R : Type u) where
  star : R -> R

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
/--
lemma `mul_dite` / 引理 `mul_dite`

English:
lemma mul_dite
  given: (a : α) (b : P -> α) (c : ¬P -> α)
  proof: by split <;> rfl

@[to_additive]

中文:
引理 mul_dite
  条件: (a : α) (b : P -> α) (c : ¬P -> α)
  证明: by split <;> rfl

@[to_additive]
-/
lemma mul_dite (a : α) (b : P -> α) (c : ¬P -> α) :
    (a * if h : P then b h else c h) = if h : P then a * b h else a * c h := by split <;> rfl

@[to_additive]
/--
lemma `mul_ite` / 引理 `mul_ite`

English:
lemma mul_ite
  given: (a b c : α)
  statement: (a * if P then b else c) = if P then a * b else a * c
  proof: mul_dite ..

@[to_additive]

中文:
引理 mul_ite
  条件: (a b c : α)
  结论: (a * if P then b else c) = if P then a * b else a * c
  证明: mul_dite ..

@[to_additive]

Depends on / 依赖: mul_dite
-/
lemma mul_ite (a b c : α) : (a * if P then b else c) = if P then a * b else a * c := mul_dite ..

@[to_additive]
/--
lemma `dite_mul` / 引理 `dite_mul`

English:
lemma dite_mul
  given: (a : P -> α) (b : ¬P -> α) (c : α)
  proof: by split <;> rfl

@[to_additive]

中文:
引理 dite_mul
  条件: (a : P -> α) (b : ¬P -> α) (c : α)
  证明: by split <;> rfl

@[to_additive]
-/
lemma dite_mul (a : P -> α) (b : ¬P -> α) (c : α) :
    (if h : P then a h else b h) * c = if h : P then a h * c else b h * c := by split <;> rfl

@[to_additive]
/--
lemma `ite_mul` / 引理 `ite_mul`

English:
lemma ite_mul
  given: (a b c : α)
  statement: (if P then a else b) * c = if P then a * c else b * c
  proof: dite_mul ..

中文:
引理 ite_mul
  条件: (a b c : α)
  结论: (if P then a else b) * c = if P then a * c else b * c
  证明: dite_mul ..

Depends on / 依赖: dite_mul
-/
lemma ite_mul (a b c : α) : (if P then a else b) * c = if P then a * c else b * c := dite_mul ..

-- We make `mul_ite` and `ite_mul` simp lemmas, but not `add_ite` or `ite_add`.
-- The problem we're trying to avoid is dealing with sums of the form `∑ x ∈ s, (f x + ite P 1 0)`,
-- in which `add_ite` followed by `sum_ite` would needlessly slice up
-- the `f x` terms according to whether `P` holds at `x`.
-- There doesn't appear to be a corresponding difficulty so far with `mul_ite` and `ite_mul`.
attribute [simp] mul_dite dite_mul mul_ite ite_mul

@[to_additive]
/--
lemma `dite_mul_dite` / 引理 `dite_mul_dite`

English:
lemma dite_mul_dite
  given: (a : P -> α) (b : ¬P -> α) (c : P -> α) (d : ¬P -> α)
  proof: by split <;> rfl

@[to_additive]

中文:
引理 dite_mul_dite
  条件: (a : P -> α) (b : ¬P -> α) (c : P -> α) (d : ¬P -> α)
  证明: by split <;> rfl

@[to_additive]
-/
lemma dite_mul_dite (a : P -> α) (b : ¬P -> α) (c : P -> α) (d : ¬P -> α) :
    ((if h : P then a h else b h) * if h : P then c h else d h) =
      if h : P then a h * c h else b h * d h := by split <;> rfl

@[to_additive]
/--
lemma `ite_mul_ite` / 引理 `ite_mul_ite`

English:
lemma ite_mul_ite
  given: (a b c d : α)
  proof: by split <;> rfl

中文:
引理 ite_mul_ite
  条件: (a b c d : α)
  证明: by split <;> rfl
-/
lemma ite_mul_ite (a b c d : α) :
    ((if P then a else b) * if P then c else d) = if P then a * c else b * d := by split <;> rfl

end Mul

/--
lemma `neg_ite` / 引理 `neg_ite`

English:
lemma neg_ite
  given: {α : Type*} (P : Prop) [Decidable P] [Neg α] (b : α) (c : α)
  proof: by split <;> rfl

中文:
引理 neg_ite
  条件: {α : 类型} (P : 命题) [Decidable P] [Neg α] (b : α) (c : α)
  证明: by split <;> rfl
-/
lemma neg_ite {α : Type*} (P : Prop) [Decidable P] [Neg α] (b : α) (c : α) :
    -(if P then b else c) = if P then -b else -c := by split <;> rfl

section Div
variable [Div α]

@[to_additive]
/--
lemma `div_dite` / 引理 `div_dite`

English:
lemma div_dite
  given: (a : α) (b : P -> α) (c : ¬P -> α)
  proof: by split <;> rfl

@[to_additive]

中文:
引理 div_dite
  条件: (a : α) (b : P -> α) (c : ¬P -> α)
  证明: by split <;> rfl

@[to_additive]
-/
lemma div_dite (a : α) (b : P -> α) (c : ¬P -> α) :
    (a / if h : P then b h else c h) = if h : P then a / b h else a / c h := by split <;> rfl

@[to_additive]
/--
lemma `div_ite` / 引理 `div_ite`

English:
lemma div_ite
  given: (a b c : α)
  statement: (a / if P then b else c) = if P then a / b else a / c
  proof: div_dite ..

@[to_additive]

中文:
引理 div_ite
  条件: (a b c : α)
  结论: (a / if P then b else c) = if P then a / b else a / c
  证明: div_dite ..

@[to_additive]

Depends on / 依赖: div_dite
-/
lemma div_ite (a b c : α) : (a / if P then b else c) = if P then a / b else a / c := div_dite ..

@[to_additive]
/--
lemma `dite_div` / 引理 `dite_div`

English:
lemma dite_div
  given: (a : P -> α) (b : ¬P -> α) (c : α)
  proof: by split <;> rfl

@[to_additive]

中文:
引理 dite_div
  条件: (a : P -> α) (b : ¬P -> α) (c : α)
  证明: by split <;> rfl

@[to_additive]
-/
lemma dite_div (a : P -> α) (b : ¬P -> α) (c : α) :
    (if h : P then a h else b h) / c = if h : P then a h / c else b h / c := by split <;> rfl

@[to_additive]
/--
lemma `ite_div` / 引理 `ite_div`

English:
lemma ite_div
  given: (a b c : α)
  statement: (if P then a else b) / c = if P then a / c else b / c
  proof: dite_div ..

@[to_additive]

中文:
引理 ite_div
  条件: (a b c : α)
  结论: (if P then a else b) / c = if P then a / c else b / c
  证明: dite_div ..

@[to_additive]

Depends on / 依赖: dite_div
-/
lemma ite_div (a b c : α) : (if P then a else b) / c = if P then a / c else b / c := dite_div ..

@[to_additive]
/--
lemma `dite_div_dite` / 引理 `dite_div_dite`

English:
lemma dite_div_dite
  given: (a : P -> α) (b : ¬P -> α) (c : P -> α) (d : ¬P -> α)
  proof: by split <;> rfl

@[to_additive]

中文:
引理 dite_div_dite
  条件: (a : P -> α) (b : ¬P -> α) (c : P -> α) (d : ¬P -> α)
  证明: by split <;> rfl

@[to_additive]
-/
lemma dite_div_dite (a : P -> α) (b : ¬P -> α) (c : P -> α) (d : ¬P -> α) :
    ((if h : P then a h else b h) / if h : P then c h else d h) =
      if h : P then a h / c h else b h / d h := by split <;> rfl

@[to_additive]
/--
lemma `ite_div_ite` / 引理 `ite_div_ite`

English:
lemma ite_div_ite
  given: (a b c d : α)
  proof: dite_div_dite ..

中文:
引理 ite_div_ite
  条件: (a b c d : α)
  证明: dite_div_dite ..

Depends on / 依赖: dite_div_dite
-/
lemma ite_div_ite (a b c d : α) :
    ((if P then a else b) / if P then c else d) = if P then a / c else b / d := dite_div_dite ..

end Div
end ite

variable {α : Type u}

@[to_additive]
instance (priority := 20) One.instNonempty [One α] : Nonempty α := ⟨1⟩

@[to_additive]
/--
theorem `Subsingleton.eq_one` / 定理 `Subsingleton.eq_one`

English:
theorem Subsingleton.eq_one
  given: [One α] [Subsingleton α] (a : α)
  statement: a = 1
  proof: Subsingleton.elim _ _

中文:
定理 Subsingleton.eq_one
  条件: [One α] [Subsingleton α] (a : α)
  结论: a = 1
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem Subsingleton.eq_one [One α] [Subsingleton α] (a : α) : a = 1 :=
  Subsingleton.elim _ _
