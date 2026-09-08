/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Algebra.Module.Defs

/-!
# Symmetrized algebra

A commutative multiplication on a real or complex space can be constructed from any multiplication
by "symmetrization" i.e.
$$
a \circ b = \frac{1}{2}(ab + ba)
$$

We provide the symmetrized version of a type `α` as `SymAlg α`, with notation `αˢʸᵐ`.

## Implementation notes

The approach taken here is inspired by `Mathlib/Algebra/Opposites.lean`. We use Oxford Spellings
(IETF en-GB-oxendict).

## Note

See `SymmetricAlgebra` instead if you are looking for the symmetric algebra of a module.

## References

* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
-/

@[expose] public section


open Function

/-- The symmetrized algebra (denoted as `αˢʸᵐ`)
has the same underlying space as the original algebra `α`. -/
/-
**SymAlg** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SymAlg (α : Type*) : Type _
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symmetrized algebra (denoted as `αˢʸᵐ`)
has the same underlying space as the original algebra `α`.
-/
def SymAlg (α : Type*) : Type _ :=
  α

@[inherit_doc] postfix:max "ˢʸᵐ" => SymAlg

namespace SymAlg

variable {α : Type*}

/-- The element of `SymAlg α` that represents `a : α`. -/
@[match_pattern]
/-
**SymAlg.sym** 是 Mathlib 中的一个定义，位于命名空间 `SymAlg`。
形式化陈述：sym : α ≃ αˢʸᵐ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The element of `SymAlg α` that represents `a : α`.
-/
def sym : α ≃ αˢʸᵐ :=
  Equiv.refl _

/-- The element of `α` represented by `x : αˢʸᵐ`. -/
-- We add `@[pp_nodot]` in case RFC https://github.com/leanprover/lean4/issues/6178 happens.
@[pp_nodot]
/-
**SymAlg.unsym** 是 Mathlib 中的一个定义，位于命名空间 `SymAlg`。
形式化陈述：unsym : αˢʸᵐ ≃ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
def unsym : αˢʸᵐ ≃ α :=
  Equiv.refl _

@[simp]
/-
**SymAlg.unsym_sym** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_sym (a : α) : unsym (sym a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unsym_sym (a : α) : unsym (sym a) = a :=
  rfl

@[simp]
/-
**SymAlg.sym_unsym** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_unsym (a : α) : sym (unsym a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym_unsym (a : α) : sym (unsym a) = a :=
  rfl

@[simp]
/-
**SymAlg.sym_comp_unsym** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_comp_unsym : (sym : α -> αˢʸᵐ) ∘ unsym = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym_comp_unsym : (sym : α → αˢʸᵐ) ∘ unsym = id :=
  rfl

@[simp]
/-
**SymAlg.unsym_comp_sym** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_comp_sym : (unsym : αˢʸᵐ -> α) ∘ sym = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unsym_comp_sym : (unsym : αˢʸᵐ → α) ∘ sym = id :=
  rfl

@[simp]
/-
**SymAlg.sym_symm** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_symm : (@sym α).symm = unsym
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem sym_symm : (@sym α).symm = unsym :=
  rfl

@[simp]
/-
**SymAlg.unsym_symm** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_symm : (@unsym α).symm = sym
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem unsym_symm : (@unsym α).symm = sym :=
  rfl
/-
**SymAlg.sym_bijective** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_bijective : Bijective (sym : α -> αˢʸᵐ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem sym_bijective : Bijective (sym : α → αˢʸᵐ) :=
  sym.bijective
/-
**SymAlg.unsym_bijective** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_bijective : Bijective (unsym : αˢʸᵐ -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem unsym_bijective : Bijective (unsym : αˢʸᵐ → α) :=
  unsym.symm.bijective
/-
**SymAlg.sym_injective** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_injective : Injective (sym : α -> αˢʸᵐ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem sym_injective : Injective (sym : α → αˢʸᵐ) :=
  sym.injective
/-
**SymAlg.sym_surjective** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_surjective : Surjective (sym : α -> αˢʸᵐ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem sym_surjective : Surjective (sym : α → αˢʸᵐ) :=
  sym.surjective
/-
**SymAlg.unsym_injective** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_injective : Injective (unsym : αˢʸᵐ -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem unsym_injective : Injective (unsym : αˢʸᵐ → α) :=
  unsym.injective
/-
**SymAlg.unsym_surjective** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_surjective : Surjective (unsym : αˢʸᵐ -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem unsym_surjective : Surjective (unsym : αˢʸᵐ → α) :=
  unsym.surjective
/-
**SymAlg.sym_inj** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_inj {a b : α} : sym a = sym b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SymAlg.sym_injective`：sym_injective : Injective (sym : α -> αˢʸᵐ)
-/
theorem sym_inj {a b : α} : sym a = sym b ↔ a = b :=
  sym_injective.eq_iff
/-
**SymAlg.unsym_inj** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_inj {a b : αˢʸᵐ} : unsym a = unsym b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SymAlg.unsym_injective`：unsym_injective : Injective (unsym : αˢʸᵐ -> α)
-/
theorem unsym_inj {a b : αˢʸᵐ} : unsym a = unsym b ↔ a = b :=
  unsym_injective.eq_iff
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial α] : Nontrivial αˢʸᵐ :=
  sym_injective.nontrivial
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited αˢʸᵐ :=
  ⟨sym default⟩
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : Subsingleton αˢʸᵐ :=
  unsym_injective.subsingleton
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique α] : Unique αˢʸᵐ :=
  Unique.mk' _
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : IsEmpty αˢʸᵐ :=
  Function.isEmpty unsym

@[to_additive]
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [One α] : One αˢʸᵐ where one := sym 1
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add α] : Add αˢʸᵐ where add a b := sym (unsym a + unsym b)
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Sub α] : Sub αˢʸᵐ where sub a b := sym (unsym a - unsym b)
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Neg α] : Neg αˢʸᵐ where neg a := sym (-unsym a)

-- Introduce the symmetrized multiplication
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add α] [Mul α] [One α] [OfNat α 2] [Invertible (2 : α)] : Mul αˢʸᵐ where
  mul a b := sym (⅟2 * (unsym a * unsym b + unsym b * unsym a))

@[to_additive existing]
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inv α] : Inv αˢʸᵐ where inv a := sym <| (unsym a)⁻¹
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [SMul R α] : SMul R αˢʸᵐ where smul r a := sym (r • unsym a)

@[to_additive (attr := simp)]
/-
**SymAlg.sym_one** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_one [One α] : sym (1 : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym_one [One α] : sym (1 : α) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**SymAlg.unsym_one** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_one [One α] : unsym (1 : αˢʸᵐ) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unsym_one [One α] : unsym (1 : αˢʸᵐ) = 1 :=
  rfl

@[simp]
/-
**SymAlg.sym_add** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_add [Add α] (a b : α) : sym (a + b) = sym a + sym b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym_add [Add α] (a b : α) : sym (a + b) = sym a + sym b :=
  rfl

@[simp]
/-
**SymAlg.unsym_add** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_add [Add α] (a b : αˢʸᵐ) : unsym (a + b) = unsym a + unsym b
参数：a b : αˢʸᵐ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unsym_add [Add α] (a b : αˢʸᵐ) : unsym (a + b) = unsym a + unsym b :=
  rfl

@[simp]
/-
**SymAlg.sym_sub** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_sub [Sub α] (a b : α) : sym (a - b) = sym a - sym b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym_sub [Sub α] (a b : α) : sym (a - b) = sym a - sym b :=
  rfl

@[simp]
/-
**SymAlg.unsym_sub** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_sub [Sub α] (a b : αˢʸᵐ) : unsym (a - b) = unsym a - unsym b
参数：a b : αˢʸᵐ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unsym_sub [Sub α] (a b : αˢʸᵐ) : unsym (a - b) = unsym a - unsym b :=
  rfl

@[simp]
/-
**SymAlg.sym_neg** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_neg [Neg α] (a : α) : sym (-a) = -sym a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym_neg [Neg α] (a : α) : sym (-a) = -sym a :=
  rfl

@[simp]
/-
**SymAlg.unsym_neg** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_neg [Neg α] (a : αˢʸᵐ) : unsym (-a) = -unsym a
参数：a : αˢʸᵐ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unsym_neg [Neg α] (a : αˢʸᵐ) : unsym (-a) = -unsym a :=
  rfl
/-
**SymAlg.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：mul_def [Add α] [Mul α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢ
ʸᵐ) : a * b = sym (⅟2 * (unsym a * unsym b + unsym b * unsym a))
参数：2 : α；a b : αˢʸᵐ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def [Add α] [Mul α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢʸᵐ) :
    a * b = sym (⅟2 * (unsym a * unsym b + unsym b * unsym a)) := rfl
/-
**SymAlg.unsym_mul** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_mul [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : 
αˢʸᵐ) : unsym (a * b) = ⅟2 * (unsym a * unsym b + unsym b * unsym a)
参数：2 : α；a b : αˢʸᵐ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unsym_mul [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢʸᵐ) :
    unsym (a * b) = ⅟2 * (unsym a * unsym b + unsym b * unsym a) := rfl
/-
**SymAlg.sym_mul_sym** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_mul_sym [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b 
: α) : sym a * sym b = sym (⅟2 * (a * b + b * a))
参数：2 : α；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym_mul_sym [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : α) :
    sym a * sym b = sym (⅟2 * (a * b + b * a)) :=
  rfl

@[simp, to_additive existing]
/-
**SymAlg.sym_inv** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_inv [Inv α] (a : α) : sym a⁻¹ = (sym a)⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym_inv [Inv α] (a : α) : sym a⁻¹ = (sym a)⁻¹ :=
  rfl

@[simp, to_additive existing]
/-
**SymAlg.unsym_inv** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_inv [Inv α] (a : αˢʸᵐ) : unsym a⁻¹ = (unsym a)⁻¹
参数：a : αˢʸᵐ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unsym_inv [Inv α] (a : αˢʸᵐ) : unsym a⁻¹ = (unsym a)⁻¹ :=
  rfl

@[simp]
/-
**SymAlg.sym_smul** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_smul {R : Type*} [SMul R α] (c : R) (a : α) : sym (c • a) = c • sym a
参数：c : R；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym_smul {R : Type*} [SMul R α] (c : R) (a : α) : sym (c • a) = c • sym a :=
  rfl

@[simp]
/-
**SymAlg.unsym_smul** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_smul {R : Type*} [SMul R α] (c : R) (a : αˢʸᵐ) : unsym (c • a) = c •
 unsym a
参数：c : R；a : αˢʸᵐ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unsym_smul {R : Type*} [SMul R α] (c : R) (a : αˢʸᵐ) : unsym (c • a) = c • unsym a :=
  rfl

@[to_additive (attr := simp)]
/-
**SymAlg.unsym_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_eq_one_iff [One α] (a : αˢʸᵐ) : unsym a = 1 ↔ a = 1
参数：a : αˢʸᵐ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `SymAlg.unsym_injective`：unsym_injective : Injective (unsym : αˢʸᵐ -> α)
-/
theorem unsym_eq_one_iff [One α] (a : αˢʸᵐ) : unsym a = 1 ↔ a = 1 :=
  unsym_injective.eq_iff' rfl

@[to_additive (attr := simp)]
/-
**SymAlg.sym_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_eq_one_iff [One α] (a : α) : sym a = 1 ↔ a = 1
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `SymAlg.sym_injective`：sym_injective : Injective (sym : α -> αˢʸᵐ)
-/
theorem sym_eq_one_iff [One α] (a : α) : sym a = 1 ↔ a = 1 :=
  sym_injective.eq_iff' rfl

@[to_additive]
/-
**SymAlg.unsym_ne_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_ne_one_iff [One α] (a : αˢʸᵐ) : unsym a != (1 : α) ↔ a != (1 : αˢʸᵐ)
参数：a : αˢʸᵐ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `SymAlg.unsym_eq_one_iff`：unsym_eq_one_iff [One α] (a : αˢʸᵐ) : unsym a =
 1 ↔ a = 1
-/
theorem unsym_ne_one_iff [One α] (a : αˢʸᵐ) : unsym a ≠ (1 : α) ↔ a ≠ (1 : αˢʸᵐ) :=
  not_congr <| unsym_eq_one_iff a

@[to_additive]
/-
**SymAlg.sym_ne_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_ne_one_iff [One α] (a : α) : sym a != (1 : αˢʸᵐ) ↔ a != (1 : α)
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `SymAlg.sym_eq_one_iff`：sym_eq_one_iff [One α] (a : α) : sym a = 1 ↔ a = 
1
-/
theorem sym_ne_one_iff [One α] (a : α) : sym a ≠ (1 : αˢʸᵐ) ↔ a ≠ (1 : α) :=
  not_congr <| sym_eq_one_iff a
/-
**SymAlg.addCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
形式化陈述：addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup αˢʸᵐ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SymAlg.unsym_injective`：unsym_injective : Injective (unsym : αˢʸᵐ -> α)
-/
instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup αˢʸᵐ :=
  unsym_injective.addCommSemigroup _ unsym_add
/-
**SymAlg.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
形式化陈述：addMonoid [AddMonoid α] : AddMonoid αˢʸᵐ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SymAlg.unsym_injective`：unsym_injective : Injective (unsym : αˢʸᵐ -> α)
-/
instance addMonoid [AddMonoid α] : AddMonoid αˢʸᵐ :=
  unsym_injective.addMonoid _ unsym_zero unsym_add fun _ _ => rfl
/-
**SymAlg.addGroup** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
形式化陈述：addGroup [AddGroup α] : AddGroup αˢʸᵐ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SymAlg.unsym_injective`：unsym_injective : Injective (unsym : αˢʸᵐ -> α)
-/
instance addGroup [AddGroup α] : AddGroup αˢʸᵐ :=
  unsym_injective.addGroup _ unsym_zero unsym_add unsym_neg unsym_sub (fun _ _ => rfl) fun _ _ =>
    rfl
/-
**SymAlg.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
形式化陈述：addCommMonoid [AddCommMonoid α] : AddCommMonoid αˢʸᵐ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid [AddCommMonoid α] : AddCommMonoid αˢʸᵐ :=
  { SymAlg.addCommSemigroup, SymAlg.addMonoid with }
/-
**SymAlg.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
形式化陈述：addCommGroup [AddCommGroup α] : AddCommGroup αˢʸᵐ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup [AddCommGroup α] : AddCommGroup αˢʸᵐ :=
  { SymAlg.addCommMonoid, SymAlg.addGroup with }
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [Semiring R] [AddCommMonoid α] [Module R α] : Module R αˢʸᵐ :=
  Function.Injective.module R ⟨⟨unsym, unsym_zero⟩, unsym_add⟩ unsym_injective unsym_smul
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [AddMonoidWithOne α] [Invertible (2 : α)] (a : α) [Invertible a] :
    Invertible (sym a) where
  invOf := sym (⅟a)
  invOf_mul_self := by
    rw [sym_mul_sym, mul_invOf_self, invOf_mul_self, one_add_one_eq_two, invOf_mul_self, sym_one]
  mul_invOf_self := by
    rw [sym_mul_sym, mul_invOf_self, invOf_mul_self, one_add_one_eq_two, invOf_mul_self, sym_one]

@[simp]
/-
**SymAlg.invOf_sym** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：invOf_sym [Mul α] [AddMonoidWithOne α] [Invertible (2 : α)] (a : α) [Inver
tible a] : ⅟(sym a) = sym (⅟a)
参数：2 : α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem invOf_sym [Mul α] [AddMonoidWithOne α] [Invertible (2 : α)] (a : α) [Invertible a] :
    ⅟(sym a) = sym (⅟a) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**SymAlg.nonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
形式化陈述：nonAssocSemiring [Semiring α] [Invertible (2 : α)] : NonAssocSemiring αˢʸᵐ
参数：2 : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonAssocSemiring [Semiring α] [Invertible (2 : α)] : NonAssocSemiring αˢʸᵐ :=
  { SymAlg.addCommMonoid with
    zero_mul := fun _ => by
      rw [mul_def, unsym_zero, zero_mul, mul_zero, add_zero,
        mul_zero, sym_zero]
    mul_zero := fun _ => by
      rw [mul_def, unsym_zero, zero_mul, mul_zero, add_zero,
        mul_zero, sym_zero]
    mul_one := fun _ => by
      rw [mul_def, unsym_one, mul_one, one_mul, ← two_mul, invOf_mul_cancel_left, sym_unsym]
    one_mul := fun _ => by
      rw [mul_def, unsym_one, mul_one, one_mul, ← two_mul, invOf_mul_cancel_left, sym_unsym]
    left_distrib := fun a b c => by
      rw [mul_def, mul_def, mul_def, ← sym_add, ← mul_add, unsym_add, add_mul]
      congr 2
      rw [mul_add]
      abel
    right_distrib := fun a b c => by
      rw [mul_def, mul_def, mul_def, ← sym_add, ← mul_add, unsym_add, add_mul]
      congr 2
      rw [mul_add]
      abel }

/-- The symmetrization of a real (unital, associative) algebra is a non-associative ring. -/
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symmetrization of a real (unital, associative) algebra is a non-associative 
ring.
-/
instance [Ring α] [Invertible (2 : α)] : NonAssocRing αˢʸᵐ :=
  { SymAlg.nonAssocSemiring, SymAlg.addCommGroup with }

/-! The squaring operation coincides for both multiplications -/


/-
**SymAlg.unsym_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：unsym_mul_self [Semiring α] [Invertible (2 : α)] (a : αˢʸᵐ) : unsym (a * a
) = unsym a * unsym a
参数：2 : α；a : αˢʸᵐ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SymAlg.mul_def`：mul_def [Add α] [Mul α] [One α] [OfNat α 2] [Invertible 
(2 : α)] (a b : αˢʸᵐ) : a * b = sym (⅟2 * (unsym a * unsym b + unsym b * unsym a
))
· 使用定理 `SymAlg.unsym_sym`：unsym_sym (a : α) : unsym (sym a) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `invOf_mul_cancel_left`：invOf_mul_cancel_left [Invertible a] : ⅟a * (a * 
b) = b

--- 原说明 ---
The squaring operation coincides for both multiplications
-/
theorem unsym_mul_self [Semiring α] [Invertible (2 : α)] (a : αˢʸᵐ) :
    unsym (a * a) = unsym a * unsym a := by
  rw [mul_def, unsym_sym, ← two_mul, invOf_mul_cancel_left]
/-
**SymAlg.sym_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：sym_mul_self [Semiring α] [Invertible (2 : α)] (a : α) : sym (a * a) = sym
 a * sym a
参数：2 : α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SymAlg.sym_mul_sym`：sym_mul_sym [Mul α] [Add α] [One α] [OfNat α 2] [Inv
ertible (2 : α)] (a b : α) : sym a * sym b = sym (⅟2 * (a * b + b * a))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `invOf_mul_cancel_left`：invOf_mul_cancel_left [Invertible a] : ⅟a * (a * 
b) = b
-/
theorem sym_mul_self [Semiring α] [Invertible (2 : α)] (a : α) : sym (a * a) = sym a * sym a := by
  rw [sym_mul_sym, ← two_mul, invOf_mul_cancel_left]
/-
**SymAlg.mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `SymAlg`。
形式化陈述：mul_comm [Mul α] [AddCommSemigroup α] [One α] [OfNat α 2] [Invertible (2 :
 α)] (a b : αˢʸᵐ) : a * b = b * a
参数：2 : α；a b : αˢʸᵐ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SymAlg.mul_def`：mul_def [Add α] [Mul α] [One α] [OfNat α 2] [Invertible 
(2 : α)] (a b : αˢʸᵐ) : a * b = sym (⅟2 * (unsym a * unsym b + unsym b * unsym a
))
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem mul_comm [Mul α] [AddCommSemigroup α] [One α] [OfNat α 2] [Invertible (2 : α)]
    (a b : αˢʸᵐ) :
    a * b = b * a := by rw [mul_def, mul_def, add_comm]
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring α] [Invertible (2 : α)] : CommMagma αˢʸᵐ where
  mul_comm := SymAlg.mul_comm
/-
**SymAlg.** 是 Mathlib 中的一个实例，位于命名空间 `SymAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring α] [Invertible (2 : α)] : IsCommJordan αˢʸᵐ where
  lmul_comm_rmul_rmul a b := by
    have commute_half_left := fun a : α => by
      have := (Commute.one_left a).add_left (Commute.one_left a)
      rw [one_add_one_eq_two] at this
      exact this.invOf_left.eq
    calc a * b * (a * a)
      _ = sym (⅟2 * ⅟2 * (unsym a * unsym b * unsym (a * a) +
          unsym b * unsym a * unsym (a * a) +
          unsym (a * a) * unsym a * unsym b +
          unsym (a * a) * unsym b * unsym a)) := ?_
      _ = sym (⅟2 * (unsym a *
          unsym (sym (⅟2 * (unsym b * unsym (a * a) + unsym (a * a) * unsym b))) +
          unsym (sym (⅟2 * (unsym b * unsym (a * a) + unsym (a * a) * unsym b))) * unsym a)) := ?_
      _ = a * (b * (a * a)) := ?_
    -- Rearrange LHS
    · rw [mul_def, mul_def a b, unsym_sym, ← mul_assoc, ← commute_half_left (unsym (a * a)),
        mul_assoc, mul_assoc, ← mul_add, ← mul_assoc, add_mul, mul_add (unsym (a * a)),
        ← add_assoc, ← mul_assoc, ← mul_assoc]
    · rw [unsym_sym, sym_inj, ← mul_assoc, ← commute_half_left (unsym a), mul_assoc (⅟2) (unsym a),
        mul_assoc (⅟2) _ (unsym a), ← mul_add, ← mul_assoc]
      conv_rhs => rw [mul_add (unsym a)]
      rw [add_mul, ← add_assoc, ← mul_assoc, ← mul_assoc]
      rw [unsym_mul_self]
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← sub_eq_zero, ← mul_sub]
      convert! mul_zero (⅟(2 : α) * ⅟(2 : α))
      rw [add_sub_add_right_eq_sub, add_assoc, add_assoc, add_sub_add_left_eq_sub, add_comm,
        add_sub_add_right_eq_sub, sub_eq_zero]
    -- Rearrange RHS
    · rw [← mul_def, ← mul_def]

end SymAlg

