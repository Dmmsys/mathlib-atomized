/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Torsion
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Tactic.Ring
public import Mathlib.Util.Qq

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way and it is shown that they form a field
of characteristic zero. For the result that the complex numbers are algebraically closed, see
`Complex.isAlgClosed` in `Mathlib.Analysis.Complex.Polynomial.Basic`.
-/

@[expose] public section

assert_not_exists Multiset Algebra

open Set Function

/-! ### Definition and basic arithmetic -/


/-- Complex numbers consist of two `Real`s: a real part `re` and an imaginary part `im`. -/
@[wikidata Q11567]
/-
**Complex** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Complex numbers consist of two `Real`s: a real part `re` and an imaginary part `
im`.
-/
structure Complex : Type where
  /-- The real part of a complex number. -/
  re : ℝ
  /-- The imaginary part of a complex number. -/
  im : ℝ

@[inherit_doc] notation "ℂ" => Complex

namespace Complex

open ComplexConjugate

/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : DecidableEq ℂ :=
  Classical.decEq _

/-- The equivalence between the complex numbers and `ℝ × ℝ`. -/
@[simps apply]
/-
**Complex.equivRealProd** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：equivRealProd : Complex ≃ Real × Real where toFun z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the complex numbers and `ℝ × ℝ`.
-/
def equivRealProd : ℂ ≃ ℝ × ℝ where
  toFun z := ⟨z.re, z.im⟩
  invFun p := ⟨p.1, p.2⟩

@[simp]
/-
**Complex.eta** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), { re := z.re, im := z.im } = z
参数：z : ℂ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eta : ∀ z : ℂ, Complex.mk z.re z.im = z
  | ⟨_, _⟩ => rfl

-- We only mark this lemma with `ext` *locally* to avoid it applying whenever terms of `ℂ` appear.
/-
**Complex.ext** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

attribute [local ext] Complex.ext
/-
**Complex.** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «forall» {p : ℂ → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ := by aesop
/-
**Complex.** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «exists» {p : ℂ → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ := by aesop
/-
**Complex.re_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：re_surjective : Surjective re
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_surjective : Surjective re := fun x => ⟨⟨x, 0⟩, rfl⟩
/-
**Complex.im_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：im_surjective : Surjective im
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_surjective : Surjective im := fun y => ⟨⟨0, y⟩, rfl⟩

@[simp]
/-
**Complex.range_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：range_re : range re = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Complex.re_surjective`：re_surjective : Surjective re
-/
theorem range_re : range re = univ :=
  re_surjective.range_eq

@[simp]
/-
**Complex.range_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：range_im : range im = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Complex.im_surjective`：im_surjective : Surjective im
-/
theorem range_im : range im = univ :=
  im_surjective.range_eq

/-- The natural inclusion of the real numbers into the complex numbers. -/
@[coe, instance_reducible]
/-
**Complex.ofReal** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ofReal (r : Real) : Complex
参数：r : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion of the real numbers into the complex numbers.
-/
def ofReal (r : ℝ) : ℂ :=
  ⟨r, 0⟩
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe ℝ ℂ :=
  ⟨ofReal⟩

@[simp, norm_cast]
/-
**Complex.ofReal_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_re (r : Real) : Complex.re (r : Complex) = r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofReal_re (r : ℝ) : Complex.re (r : ℂ) = r :=
  rfl

@[simp, norm_cast]
/-
**Complex.ofReal_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_im (r : Real) : (r : Complex).im = 0
参数：r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofReal_im (r : ℝ) : (r : ℂ).im = 0 :=
  rfl
/-
**Complex.ofReal_def** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_def (r : Real) : (r : Complex) = ⟨r, 0⟩
参数：r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofReal_def (r : ℝ) : (r : ℂ) = ⟨r, 0⟩ :=
  rfl

@[simp, norm_cast]
/-
**Complex.ofReal_inj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ofReal_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
  ⟨congrArg re, by apply congrArg⟩
/-
**Complex.ofReal_injective** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_injective : Function.Injective ((↑) : Real -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ofReal_injective : Function.Injective ((↑) : ℝ → ℂ) := fun _ _ => congrArg re
/-
**Complex.canLift** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：canLift : CanLift Complex Real (↑) fun z => z.im = 0 where prf z hz
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance canLift : CanLift ℂ ℝ (↑) fun z => z.im = 0 where
  prf z hz := ⟨z.re, ext rfl hz.symm⟩

/-- The product of a set on the real axis and a set on the imaginary axis of the complex plane,
denoted by `s ×ℂ t`. -/
/-
**Complex.reProdIm** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：reProdIm (s t : Set Real) : Set Complex
参数：s t : Set Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a set on the real axis and a set on the imaginary axis of the com
plex plane,
denoted by `s ×ℂ t`.
-/
def reProdIm (s t : Set ℝ) : Set ℂ :=
  re ⁻¹' s ∩ im ⁻¹' t

@[inherit_doc]
infixl:72 " ×ℂ " => reProdIm
/-
**Complex.mem_reProdIm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：mem_reProdIm {z : Complex} {s t : Set Real} : z in s ×Complex t ↔ z.re in 
s ∧ z.im in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_reProdIm {z : ℂ} {s t : Set ℝ} : z ∈ s ×ℂ t ↔ z.re ∈ s ∧ z.im ∈ t :=
  Iff.rfl
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero ℂ :=
  ⟨(0 : ℝ)⟩
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited ℂ :=
  ⟨0⟩

@[simp]
/-
**Complex.zero_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：zero_re : (0 : Complex).re = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_re : (0 : ℂ).re = 0 :=
  rfl

@[simp]
/-
**Complex.zero_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：zero_im : (0 : Complex).im = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_im : (0 : ℂ).im = 0 :=
  rfl

@[simp, norm_cast]
/-
**Complex.ofReal_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_zero : ((0 : Real) : Complex) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofReal_zero : ((0 : ℝ) : ℂ) = 0 :=
  rfl

@[simp]
/-
**Complex.ofReal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_eq_zero {z : Real} : (z : Complex) = 0 ↔ z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ofReal_inj`：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
-/
theorem ofReal_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 :=
  ofReal_inj
/-
**Complex.ofReal_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔ z != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Complex.ofReal_eq_zero`：ofReal_eq_zero {z : Real} : (z : Complex) = 0 ↔ 
z = 0
-/
theorem ofReal_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 :=
  not_congr ofReal_eq_zero
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One ℂ :=
  ⟨(1 : ℝ)⟩

@[simp]
/-
**Complex.one_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：one_re : (1 : Complex).re = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_re : (1 : ℂ).re = 1 :=
  rfl

@[simp]
/-
**Complex.one_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：one_im : (1 : Complex).im = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_im : (1 : ℂ).im = 0 :=
  rfl

@[simp, norm_cast]
/-
**Complex.ofReal_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_one : ((1 : Real) : Complex) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofReal_one : ((1 : ℝ) : ℂ) = 1 :=
  rfl

@[simp]
/-
**Complex.ofReal_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_eq_one {z : Real} : (z : Complex) = 1 ↔ z = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ofReal_inj`：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
-/
theorem ofReal_eq_one {z : ℝ} : (z : ℂ) = 1 ↔ z = 1 :=
  ofReal_inj
/-
**Complex.ofReal_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_ne_one {z : Real} : (z : Complex) != 1 ↔ z != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Complex.ofReal_eq_one`：ofReal_eq_one {z : Real} : (z : Complex) = 1 ↔ z 
= 1
-/
theorem ofReal_ne_one {z : ℝ} : (z : ℂ) ≠ 1 ↔ z ≠ 1 :=
  not_congr ofReal_eq_one
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add ℂ :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp]
/-
**Complex.add_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：add_re (z w : Complex) : (z + w).re = z.re + w.re
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_re (z w : ℂ) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
/-
**Complex.add_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：add_im (z w : Complex) : (z + w).im = z.im + w.im
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_im (z w : ℂ) : (z + w).im = z.im + w.im :=
  rfl

@[simp, norm_cast]
/-
**Complex.ofReal_add** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_add (r s : Real) : ((r + s : Real) : Complex) = r + s
参数：r s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
  Complex.ext_iff.2 <| by simp [ofReal]
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg ℂ :=
  ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp]
/-
**Complex.neg_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：neg_re (z : Complex) : (-z).re = -z.re
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_re (z : ℂ) : (-z).re = -z.re :=
  rfl

@[simp]
/-
**Complex.neg_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：neg_im (z : Complex) : (-z).im = -z.im
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_im (z : ℂ) : (-z).im = -z.im :=
  rfl

@[simp, norm_cast]
/-
**Complex.ofReal_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem ofReal_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r :=
  Complex.ext_iff.2 <| by simp [ofReal]
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub ℂ :=
  ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

/--
`mulAux` is an auxiliary definition for defining multiplication and scalar multiplication on `ℂ`
in such a way that `real_smul {x : ℝ} {z : ℂ} : x • z = x * z` holds definitionally.
This makes sure that `Module.restrictScalars ℝ ℂ ℂ = Complex.instModule` definitionally.
-/
@[no_expose]
/-
**Complex.mulAux** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：mulAux {R : Type*} [SMul R Real] (re : R) (im : Real) (z : Complex) : Comp
lex
参数：re : R；im : Real；z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mulAux` is an auxiliary definition for defining multiplication and scalar multi
plication on `ℂ`
in such a way that `real_smul {x : ℝ} {z : ℂ} : x • z = x * z` holds definitiona
lly.
This makes sure that `Module.restrictScalars ℝ ℂ ℂ = Complex.instModule` definit
ionally.
-/
def mulAux {R : Type*} [SMul R ℝ] (re : R) (im : ℝ) (z : ℂ) : ℂ :=
  ⟨re • z.re - im * z.im, re • z.im + im * z.re⟩
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul ℂ :=
  ⟨fun z w => mulAux z.re z.im w⟩
/-
**Complex.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：mk_mul_mk (x₁ x₂ y₁ y₂ : Real) : (⟨x₁, y₁⟩ : Complex) * ⟨x₂, y₂⟩ = ⟨x₁ * x
₂ - y₁ * y₂, x₁ * y₂ + y₁ * x₂⟩
参数：x₁ x₂ y₁ y₂ : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mul_mk (x₁ x₂ y₁ y₂ : ℝ) :
    (⟨x₁, y₁⟩ : ℂ) * ⟨x₂, y₂⟩ = ⟨x₁ * x₂ - y₁ * y₂, x₁ * y₂ + y₁ * x₂⟩ := (rfl)

@[simp]
/-
**Complex.mul_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im * w.im
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im :=
  (rfl)

@[simp]
/-
**Complex.mul_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im * w.re
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re :=
  (rfl)

@[simp, norm_cast]
/-
**Complex.ofReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_mul (r s : Real) : ((r * s : Real) : Complex) = r * s
参数：r s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem ofReal_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s :=
  Complex.ext_iff.2 <| by simp [ofReal]
/-
**Complex.re_ofReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：re_ofReal_mul (r : Real) (z : Complex) : (r * z).re = r * z.re
参数：r : Real；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem re_ofReal_mul (r : ℝ) (z : ℂ) : (r * z).re = r * z.re := by simp [ofReal]
/-
**Complex.im_ofReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：im_ofReal_mul (r : Real) (z : Complex) : (r * z).im = r * z.im
参数：r : Real；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem im_ofReal_mul (r : ℝ) (z : ℂ) : (r * z).im = r * z.im := by simp [ofReal]
/-
**Complex.re_mul_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：re_mul_ofReal (z : Complex) (r : Real) : (z * r).re = z.re * r
参数：z : Complex；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma re_mul_ofReal (z : ℂ) (r : ℝ) : (z * r).re = z.re * r := by simp [ofReal]
/-
**Complex.im_mul_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：im_mul_ofReal (z : Complex) (r : Real) : (z * r).im = z.im * r
参数：z : Complex；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma im_mul_ofReal (z : ℂ) (r : ℝ) : (z * r).im = z.im * r := by simp [ofReal]
/-
**Complex.ofReal_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_mul' (r : Real) (z : Complex) : ↑r * z = ⟨r * z.re, r * z.im⟩
参数：r : Real；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `Complex.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : Complex) : (r * z).
re = r * z.re
· 使用定理 `Complex.im_ofReal_mul`：im_ofReal_mul (r : Real) (z : Complex) : (r * z).
im = r * z.im
-/
theorem ofReal_mul' (r : ℝ) (z : ℂ) : ↑r * z = ⟨r * z.re, r * z.im⟩ :=
  ext (re_ofReal_mul _ _) (im_ofReal_mul _ _)

/-! ### The imaginary unit, `I` -/


/-- The imaginary unit. -/
/-
**Complex.I** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：I : Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The imaginary unit.
-/
def I : ℂ :=
  ⟨0, 1⟩

@[simp]
/-
**Complex.I_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：I_re : I.re = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem I_re : I.re = 0 :=
  rfl

@[simp]
/-
**Complex.I_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：I_im : I.im = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem I_im : I.im = 1 :=
  rfl

@[simp]
/-
**Complex.I_mul_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：I_mul_I : I * I = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem I_mul_I : I * I = -1 :=
  Complex.ext_iff.2 <| by simp
/-
**Complex.I_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：I_mul (z : Complex) : I * z = ⟨-z.im, z.re⟩
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem I_mul (z : ℂ) : I * z = ⟨-z.im, z.re⟩ :=
  Complex.ext_iff.2 <| by simp
/-
**Complex.I_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Complex.I ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
@[simp] lemma I_ne_zero : (I : ℂ) ≠ 0 := mt (congr_arg im) zero_ne_one.symm
/-
**Complex.mk_eq_add_mul_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：mk_eq_add_mul_I (a b : Real) : Complex.mk a b = a + b * I
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem mk_eq_add_mul_I (a b : ℝ) : Complex.mk a b = a + b * I :=
  Complex.ext_iff.2 <| by simp [ofReal]

@[simp]
/-
**Complex.re_add_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：re_add_im (z : Complex) : (z.re : Complex) + z.im * I = z
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
  Complex.ext_iff.2 <| by simp [ofReal]
/-
**Complex.mul_I_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：mul_I_re (z : Complex) : (z * I).re = -z.im
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_I_re (z : ℂ) : (z * I).re = -z.im := by simp
/-
**Complex.mul_I_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：mul_I_im (z : Complex) : (z * I).im = z.re
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_I_im (z : ℂ) : (z * I).im = z.re := by simp
/-
**Complex.I_mul_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：I_mul_re (z : Complex) : (I * z).re = -z.im
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem I_mul_re (z : ℂ) : (I * z).re = -z.im := by simp
/-
**Complex.I_mul_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：I_mul_im (z : Complex) : (I * z).im = z.re
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem I_mul_im (z : ℂ) : (I * z).im = z.re := by simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Complex.equivRealProd_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：equivRealProd_symm_apply (p : Real × Real) : equivRealProd.symm p = p.1 + 
p.2 * I
参数：p : Real × Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem equivRealProd_symm_apply (p : ℝ × ℝ) : equivRealProd.symm p = p.1 + p.2 * I := by
  ext <;> simp [Complex.equivRealProd, ofReal]

/-- The natural `AddEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! +simpRhs apply symm_apply_re symm_apply_im]
/-
**Complex.equivRealProdAddHom** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：equivRealProdAddHom : Complex ≃+ Real × Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `AddEquiv` from `ℂ` to `ℝ × ℝ`.
-/
def equivRealProdAddHom : ℂ ≃+ ℝ × ℝ :=
  { equivRealProd with map_add' := by simp }
/-
**Complex.equivRealProdAddHom_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：equivRealProdAddHom_symm_apply (p : Real × Real) : equivRealProdAddHom.sym
m p = p.1 + p.2 * I
参数：p : Real × Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.equivRealProd_symm_apply`：equivRealProd_symm_apply (p : Real × R
eal) : equivRealProd.symm p = p.1 + p.2 * I
-/
theorem equivRealProdAddHom_symm_apply (p : ℝ × ℝ) :
    equivRealProdAddHom.symm p = p.1 + p.2 * I := equivRealProd_symm_apply p

/-! ### Commutative ring instance and lemmas -/


/-- We use a nonstandard formula for the `ℕ` and `ℤ` actions to make sure there is no
diamond from the other actions they inherit through the `ℝ`-action on `ℂ` and action transitivity
defined in `Data.Complex.Module`. -/
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We use a nonstandard formula for the `ℕ` and `ℤ` actions to make sure there is n
o
diamond from the other actions they inherit through the `ℝ`-action on `ℂ` and ac
tion transitivity
defined in `Data.Complex.Module`.
-/
instance : Nontrivial ℂ :=
  domain_nontrivial re rfl rfl

namespace SMul

-- instance made scoped to avoid situations like instance synthesis
-- of `SMul ℂ ℂ` trying to proceed via `SMul ℂ ℝ`.
/-- Scalar multiplication by `R` on `ℝ` extends to `ℂ`. This is used here and in
`Mathlib/LinearAlgebra/Complex/Module.lean` to transfer instances from `ℝ` to `ℂ`, but is not
needed outside, so we make it scoped. -/
/-
**Complex.SMul.instSMulRealComplex** 是 Mathlib 中的一个定义，位于命名空间 `Complex.SMul`。
形式化陈述：{R : Type u_1} → [SMul R ℝ] → SMul R ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication by `R` on `ℝ` extends to `ℂ`. This is used here and in
`Mathlib/LinearAlgebra/Complex/Module.lean` to transfer instances from `ℝ` to `ℂ
`, but is not
needed outside, so we make it scoped.
-/
scoped instance instSMulRealComplex {R : Type*} [SMul R ℝ] : SMul R ℂ where
  smul r x := mulAux r 0 x

end SMul

open scoped Complex.SMul

section SMul

variable {R : Type*} [SMul R ℝ]

/-
**Complex.smul_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：smul_re (r : R) (z : Complex) : (r • z).re = r • z.re
参数：r : R；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re :=
  show r • z.re - 0 * z.im = r • z.re by simp
/-
**Complex.smul_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：smul_im (r : R) (z : Complex) : (r • z).im = r • z.im
参数：r : R；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im :=
  show r • z.im + 0 * z.re = r • z.im by simp

@[simp]
/-
**Complex.real_smul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：real_smul {x : Real} {z : Complex} : x • z = x * z
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem real_smul {x : ℝ} {z : ℂ} : x • z = x * z :=
  rfl

end SMul

/-
**Complex.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：addCommGroup : AddCommGroup Complex where zsmul_zero'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup : AddCommGroup ℂ where
  zsmul_zero' := by intros; ext <;> simp [smul_re, smul_im]
  nsmul_zero := by intros; ext <;> simp [smul_re, smul_im]
  nsmul_succ := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  zsmul_succ' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  zsmul_neg' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp

/-! ### Casts -/

/-
**Complex.instNatCast** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：instNatCast : NatCast Complex where natCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Casts
-/
instance instNatCast : NatCast ℂ where natCast n := ofReal n
/-
**Complex.instIntCast** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：instIntCast : IntCast Complex where intCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIntCast : IntCast ℂ where intCast n := ofReal n
/-
**Complex.instNNRatCast** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：instNNRatCast : NNRatCast Complex where nnratCast q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNNRatCast : NNRatCast ℂ where nnratCast q := ofReal q
/-
**Complex.instRatCast** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：instRatCast : RatCast Complex where ratCast q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRatCast : RatCast ℂ where ratCast q := ofReal q
/-
**Complex.ofReal_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofReal_ofNat (n : ℕ) [n.AtLeastTwo] : ofReal ofNat(n) = ofNat(n) := rfl
/-
**Complex.ofReal_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℕ), ↑↑n = ↑n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofReal_natCast (n : ℕ) : ofReal n = n := rfl
/-
**Complex.ofReal_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℤ), ↑↑n = ↑n
参数：n : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofReal_intCast (n : ℤ) : ofReal n = n := rfl
/-
**Complex.ofReal_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (q : ℚ≥0), ↑↑q = ↑q
参数：q : ℚ≥0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofReal_nnratCast (q : ℚ≥0) : ofReal q = q := rfl
/-
**Complex.ofReal_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (q : ℚ), ↑↑q = ↑q
参数：q : ℚ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofReal_ratCast (q : ℚ) : ofReal q = q := rfl
/-
**Complex.ofReal_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (m : ℕ) (s : Bool) (e : ℕ), ↑(OfScientific.ofScientific m s e) = OfScien
tific.ofScientific m s e
参数：m : ℕ；s : Bool；e : ℕ；OfScientific.ofScientific m s e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofReal_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    ofReal (OfScientific.ofScientific m s e : ℝ) = OfScientific.ofScientific m s e := rfl
/-
**Complex.re_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).re = OfNat.ofNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℂ).re = ofNat(n) := rfl
/-
**Complex.im_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).im = 0
参数：n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℂ).im = 0 := rfl
/-
**Complex.natCast_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℕ), (↑n).re = ↑n
参数：n : ℕ；↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma natCast_re (n : ℕ) : (n : ℂ).re = n := rfl
/-
**Complex.natCast_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℕ), (↑n).im = 0
参数：n : ℕ；↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma natCast_im (n : ℕ) : (n : ℂ).im = 0 := rfl
/-
**Complex.intCast_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℤ), (↑n).re = ↑n
参数：n : ℤ；↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma intCast_re (n : ℤ) : (n : ℂ).re = n := rfl
/-
**Complex.intCast_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℤ), (↑n).im = 0
参数：n : ℤ；↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma intCast_im (n : ℤ) : (n : ℂ).im = 0 := rfl
/-
**Complex.re_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (q : ℚ≥0), (↑q).re = ↑q
参数：q : ℚ≥0；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma re_nnratCast (q : ℚ≥0) : (q : ℂ).re = q := rfl
/-
**Complex.im_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (q : ℚ≥0), (↑q).im = 0
参数：q : ℚ≥0；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma im_nnratCast (q : ℚ≥0) : (q : ℂ).im = 0 := rfl
/-
**Complex.ratCast_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (q : ℚ), (↑q).re = ↑q
参数：q : ℚ；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ratCast_re (q : ℚ) : (q : ℂ).re = q := rfl
/-
**Complex.ratCast_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (q : ℚ), (↑q).im = 0
参数：q : ℚ；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ratCast_im (q : ℚ) : (q : ℂ).im = 0 := rfl
/-
**Complex.re_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (m : ℕ) (s : Bool) (e : ℕ), Complex.re (OfScientific.ofScientific m s e)
 = OfScientific.ofScientific m s e
参数：m : ℕ；s : Bool；e : ℕ；OfScientific.ofScientific m s e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma re_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℂ).re = OfScientific.ofScientific m s e := rfl
/-
**Complex.im_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (m : ℕ) (s : Bool) (e : ℕ), Complex.im (OfScientific.ofScientific m s e)
 = 0
参数：m : ℕ；s : Bool；e : ℕ；OfScientific.ofScientific m s e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma im_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℂ).im = 0 := rfl


/-! ### Ring structure -/

/-
**Complex.addGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：addGroupWithOne : AddGroupWithOne Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Ring structure
-/
instance addGroupWithOne : AddGroupWithOne ℂ :=
  { Complex.addCommGroup with
    natCast_zero := by ext <;> simp
    natCast_succ _ := by ext <;> simp
    intCast_ofNat _ := by ext <;> simp
    intCast_negSucc _ := by ext <;> simp }
/-
**Complex.commRing** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：commRing : CommRing Complex
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupWithOne.sub_eq_add_neg`：∀ {R : Type u} [self : AddGroupWithOne R
] (a b : R), a - b = a + -b
· 使用定理 `AddGroupWithOne.zsmul_zero'`：∀ {R : Type u} [self : AddGroupWithOne R] (
a : R), 0 • a = 0
· 使用定理 `AddGroupWithOne.zsmul_succ'`：∀ {R : Type u} [self : AddGroupWithOne R] (
n : ℕ) (a : R), ↑n.succ • a = ↑n • a + a
· 使用定理 `AddGroupWithOne.zsmul_neg'`：∀ {R : Type u} [self : AddGroupWithOne R] (n
 : ℕ) (a : R), Int.negSucc n • a = -(↑n.succ • a)
· 使用定理 `AddGroupWithOne.neg_add_cancel`：∀ {R : Type u} [self : AddGroupWithOne R
] (a : R), -a + a = 0
· 使用定理 `AddGroupWithOne.intCast_ofNat`：∀ {R : Type u} [self : AddGroupWithOne R]
 (n : ℕ), IntCast.intCast ↑n = ↑n
· 使用定理 `AddGroupWithOne.intCast_negSucc`：∀ {R : Type u} [self : AddGroupWithOne 
R] (n : ℕ), IntCast.intCast (Int.negSucc n) = -↑(n + 1)
-/
instance commRing : CommRing ℂ :=
  { addGroupWithOne with
    npow := @npowRec _ ⟨(1 : ℂ)⟩ ⟨(· * ·)⟩
    add_comm := by intros; ext <;> simp <;> ring
    left_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    right_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    zero_mul := by intros; ext <;> simp
    mul_zero := by intros; ext <;> simp
    mul_assoc := by intros; ext <;> simp <;> ring
    one_mul := by intros; ext <;> simp
    mul_one := by intros; ext <;> simp
    mul_comm := by intros; ext <;> simp <;> ring }

section computable_shortcuts

/-- This shortcut instance ensures we do not find `Ring` via the noncomputable `Complex.field`
instance. -/
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This shortcut instance ensures we do not find `Ring` via the noncomputable `Comp
lex.field`
instance.
-/
instance : Ring ℂ :=
  delta% inferInstance

/-- This shortcut instance ensures we do not find `NonUnitalCommRing` via the noncomputable
`instCommCStarAlgebraComplex` instance. -/
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This shortcut instance ensures we do not find `NonUnitalCommRing` via the noncom
putable
`instCommCStarAlgebraComplex` instance.
-/
instance : NonUnitalCommRing ℂ :=
  delta% inferInstance

/-- This shortcut instance ensures we do not find `CommSemiring` via the noncomputable
`Complex.field` instance. -/
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This shortcut instance ensures we do not find `CommSemiring` via the noncomputab
le
`Complex.field` instance.
-/
instance : CommSemiring ℂ :=
  delta% inferInstance

/-- This shortcut instance ensures we do not find `Semiring` via the noncomputable
`Complex.field` instance. -/
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This shortcut instance ensures we do not find `Semiring` via the noncomputable
`Complex.field` instance.
-/
instance : Semiring ℂ :=
  delta% inferInstance

/-- This shortcut instance ensures we do not find `AddCommMonoid` via the noncomputable
`Complex.instNormedField` instance. -/
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This shortcut instance ensures we do not find `AddCommMonoid` via the noncomputa
ble
`Complex.instNormedField` instance.
-/
instance : AddCommMonoid ℂ :=
  delta% inferInstance

end computable_shortcuts

/-- The "real part" map, considered as an additive group homomorphism. -/
/-
**Complex.reAddGroupHom** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：reAddGroupHom : Complex ->+ Real where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.zero_re`：zero_re : (0 : Complex).re = 0
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re

--- 原说明 ---
The "real part" map, considered as an additive group homomorphism.
-/
def reAddGroupHom : ℂ →+ ℝ where
  toFun := re
  map_zero' := zero_re
  map_add' := add_re

@[simp]
/-
**Complex.coe_reAddGroupHom** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：coe_reAddGroupHom : (reAddGroupHom : Complex -> Real) = re
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_reAddGroupHom : (reAddGroupHom : ℂ → ℝ) = re :=
  rfl

/-- The "imaginary part" map, considered as an additive group homomorphism. -/
/-
**Complex.imAddGroupHom** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：imAddGroupHom : Complex ->+ Real where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.zero_im`：zero_im : (0 : Complex).im = 0
· 使用定理 `Complex.add_im`：add_im (z w : Complex) : (z + w).im = z.im + w.im

--- 原说明 ---
The "imaginary part" map, considered as an additive group homomorphism.
-/
def imAddGroupHom : ℂ →+ ℝ where
  toFun := im
  map_zero' := zero_im
  map_add' := add_im

@[simp]
/-
**Complex.coe_imAddGroupHom** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：coe_imAddGroupHom : (imAddGroupHom : Complex -> Real) = im
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_imAddGroupHom : (imAddGroupHom : ℂ → ℝ) = im :=
  rfl
/-
**Complex.re_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：re_nsmul (n : Nat) (z : Complex) : (n • z).re = n • z.re
参数：n : Nat；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.smul_re`：smul_re (r : R) (z : Complex) : (r • z).re = r • z.re
-/
lemma re_nsmul (n : ℕ) (z : ℂ) : (n • z).re = n • z.re := smul_re ..
/-
**Complex.im_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：im_nsmul (n : Nat) (z : Complex) : (n • z).im = n • z.im
参数：n : Nat；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.smul_im`：smul_im (r : R) (z : Complex) : (r • z).im = r • z.im
-/
lemma im_nsmul (n : ℕ) (z : ℂ) : (n • z).im = n • z.im := smul_im ..
/-
**Complex.re_zsmul** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：re_zsmul (n : Int) (z : Complex) : (n • z).re = n • z.re
参数：n : Int；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.smul_re`：smul_re (r : R) (z : Complex) : (r • z).re = r • z.re
-/
lemma re_zsmul (n : ℤ) (z : ℂ) : (n • z).re = n • z.re := smul_re ..
/-
**Complex.im_zsmul** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：im_zsmul (n : Int) (z : Complex) : (n • z).im = n • z.im
参数：n : Int；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.smul_im`：smul_im (r : R) (z : Complex) : (r • z).im = r • z.im
-/
lemma im_zsmul (n : ℤ) (z : ℂ) : (n • z).im = n • z.im := smul_im ..
/-
**Complex.re_nnqsmul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (q : ℚ≥0) (z : ℂ), (q • z).re = q • z.re
参数：q : ℚ≥0；z : ℂ；q • z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.smul_re`：smul_re (r : R) (z : Complex) : (r • z).re = r • z.re
-/
@[simp] lemma re_nnqsmul (q : ℚ≥0) (z : ℂ) : (q • z).re = q • z.re := smul_re ..
/-
**Complex.im_nnqsmul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (q : ℚ≥0) (z : ℂ), (q • z).im = q • z.im
参数：q : ℚ≥0；z : ℂ；q • z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.smul_im`：smul_im (r : R) (z : Complex) : (r • z).im = r • z.im
-/
@[simp] lemma im_nnqsmul (q : ℚ≥0) (z : ℂ) : (q • z).im = q • z.im := smul_im ..
/-
**Complex.re_qsmul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (q : ℚ) (z : ℂ), (q • z).re = q • z.re
参数：q : ℚ；z : ℂ；q • z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.smul_re`：smul_re (r : R) (z : Complex) : (r • z).re = r • z.re
-/
@[simp] lemma re_qsmul (q : ℚ) (z : ℂ) : (q • z).re = q • z.re := smul_re ..
/-
**Complex.im_qsmul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (q : ℚ) (z : ℂ), (q • z).im = q • z.im
参数：q : ℚ；z : ℂ；q • z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.smul_im`：smul_im (r : R) (z : Complex) : (r • z).im = r • z.im
-/
@[simp] lemma im_qsmul (q : ℚ) (z : ℂ) : (q • z).im = q • z.im := smul_im ..
/-
**Complex.ofReal_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℕ) (r : ℝ), ↑(n • r) = n • ↑r
参数：n : ℕ；r : ℝ；n • r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma ofReal_nsmul (n : ℕ) (r : ℝ) : ↑(n • r) = n • (r : ℂ) := by simp
/-
**Complex.ofReal_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℤ) (r : ℝ), ↑(n • r) = n • ↑r
参数：n : ℤ；r : ℝ；n • r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma ofReal_zsmul (n : ℤ) (r : ℝ) : ↑(n • r) = n • (r : ℂ) := by simp

/-! ### Complex conjugation -/


/-- This defines the complex conjugate as the `star` operation of the `StarRing ℂ`. It
is recommended to use the ring endomorphism version `starRingEnd`, available under the
notation `conj` in the scope `ComplexConjugate`. -/
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This defines the complex conjugate as the `star` operation of the `StarRing ℂ`. 
It
is recommended to use the ring endomorphism version `starRingEnd`, available und
er the
notation `conj` in the scope `ComplexConjugate`.
-/
instance : StarRing ℂ where
  star z := ⟨z.re, -z.im⟩
  star_involutive x := by simp only [eta, neg_neg]
  star_mul a b := by ext <;> simp [add_comm] <;> ring
  star_add a b := by ext <;> simp [add_comm]

@[simp]
/-
**Complex.conj_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_re (z : Complex) : (conj z).re = z.re
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conj_re (z : ℂ) : (conj z).re = z.re :=
  rfl

@[simp]
/-
**Complex.conj_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_im (z : Complex) : (conj z).im = -z.im
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conj_im (z : ℂ) : (conj z).im = -z.im :=
  rfl

@[simp]
/-
**Complex.conj_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_ofReal (r : Real) : conj (r : Complex) = r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem conj_ofReal (r : ℝ) : conj (r : ℂ) = r :=
  Complex.ext_iff.2 <| by simp

@[simp]
/-
**Complex.conj_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_I : conj I = -I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem conj_I : conj I = -I :=
  Complex.ext_iff.2 <| by simp
/-
**Complex.conj_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_natCast (n : Nat) : conj (n : Complex) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
-/
theorem conj_natCast (n : ℕ) : conj (n : ℂ) = n := map_natCast _ _
/-
**Complex.conj_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_ofNat (n : Nat) [n.AtLeastTwo] : conj (ofNat(n) : Complex) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
-/
theorem conj_ofNat (n : ℕ) [n.AtLeastTwo] : conj (ofNat(n) : ℂ) = ofNat(n) :=
  map_ofNat _ _
/-
**Complex.conj_neg_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_neg_I : conj (-I) = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conj_neg_I : conj (-I) = I := by simp
/-
**Complex.conj_eq_iff_real** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_eq_iff_real {z : Complex} : conj z = z ↔ exists r : Real, z = r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `eq_zero_of_neg_eq`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Line
arOrder α] [IsOrderedAddMonoid α] {a : α}, -a = a → a = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
-/
theorem conj_eq_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
  ⟨fun h => ⟨z.re, ext rfl <| eq_zero_of_neg_eq (congr_arg im h)⟩, fun ⟨h, e⟩ => by
    rw [e, conj_ofReal]⟩
/-
**Complex.conj_eq_iff_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_eq_iff_re {z : Complex} : conj z = z ↔ (z.re : Complex) = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Complex.conj_eq_iff_real`：conj_eq_iff_real {z : Complex} : conj z = z ↔ 
exists r : Real, z = r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem conj_eq_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
  conj_eq_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp [ofReal], fun h => ⟨_, h.symm⟩⟩
/-
**Complex.conj_eq_iff_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_eq_iff_im {z : Complex} : conj z = z ↔ z.im = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_self_eq_zero`：add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem conj_eq_iff_im {z : ℂ} : conj z = z ↔ z.im = 0 :=
  ⟨fun h => add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)), fun h =>
    ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩

@[simp]
/-
**Complex.star_def** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：star_def : (Star.star : Complex -> Complex) = conj
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_def : (Star.star : ℂ → ℂ) = conj :=
  rfl

/-! ### Norm squared -/


/-- The norm squared function. -/
@[pp_nodot]
/-
**Complex.normSq** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：normSq : Complex ->*₀ Real where toFun z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm squared function.
-/
def normSq : ℂ →*₀ ℝ where
  toFun z := z.re * z.re + z.im * z.im
  map_zero' := by simp
  map_one' := by simp
  map_mul' z w := by
    simp only [mul_re, mul_im]
    ring
/-
**Complex.normSq_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_apply (z : Complex) : normSq z = z.re * z.re + z.im * z.im
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normSq_apply (z : ℂ) : normSq z = z.re * z.re + z.im * z.im :=
  rfl

@[simp]
/-
**Complex.normSq_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_ofReal (r : Real) : normSq r = r * r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_ofReal (r : ℝ) : normSq r = r * r := by
  simp [normSq, ofReal]

@[simp]
/-
**Complex.normSq_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_natCast (n : Nat) : normSq n = n * n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.normSq_ofReal`：normSq_ofReal (r : Real) : normSq r = r * r
-/
theorem normSq_natCast (n : ℕ) : normSq n = n * n := normSq_ofReal _

@[simp]
/-
**Complex.normSq_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_intCast (z : Int) : normSq z = z * z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.normSq_ofReal`：normSq_ofReal (r : Real) : normSq r = r * r
-/
theorem normSq_intCast (z : ℤ) : normSq z = z * z := normSq_ofReal _

@[simp]
/-
**Complex.normSq_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_ratCast (q : Rat) : normSq q = q * q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.normSq_ofReal`：normSq_ofReal (r : Real) : normSq r = r * r
-/
theorem normSq_ratCast (q : ℚ) : normSq q = q * q := normSq_ofReal _

@[simp]
/-
**Complex.normSq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_ofNat (n : Nat) [n.AtLeastTwo] : normSq (ofNat(n) : Complex) = ofNa
t(n) * ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.normSq_natCast`：normSq_natCast (n : Nat) : normSq n = n * n
-/
theorem normSq_ofNat (n : ℕ) [n.AtLeastTwo] :
    normSq (ofNat(n) : ℂ) = ofNat(n) * ofNat(n) :=
  normSq_natCast _

@[simp]
/-
**Complex.normSq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_mk (x y : Real) : normSq ⟨x, y⟩ = x * x + y * y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normSq_mk (x y : ℝ) : normSq ⟨x, y⟩ = x * x + y * y :=
  rfl
/-
**Complex.normSq_add_mul_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_add_mul_I (x y : Real) : normSq (x + y * I) = x ^ 2 + y ^ 2
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.mk_eq_add_mul_I`：mk_eq_add_mul_I (a b : Real) : Complex.mk a b =
 a + b * I
· 使用定理 `Complex.normSq_mk`：normSq_mk (x y : Real) : normSq ⟨x, y⟩ = x * x + y * 
y
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem normSq_add_mul_I (x y : ℝ) : normSq (x + y * I) = x ^ 2 + y ^ 2 := by
  rw [← mk_eq_add_mul_I, normSq_mk, sq, sq]
/-
**Complex.normSq_eq_conj_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_eq_conj_mul_self {z : Complex} : (normSq z : Complex) = conj z * z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
-/
theorem normSq_eq_conj_mul_self {z : ℂ} : (normSq z : ℂ) = conj z * z := by
  ext <;> simp [normSq, mul_comm, ofReal]
/-
**Complex.normSq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_zero : normSq 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_zero : normSq 0 = 0 := by simp
/-
**Complex.normSq_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_one : normSq 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_one : normSq 1 = 1 := by simp

@[simp]
/-
**Complex.normSq_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_I : normSq I = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_I : normSq I = 1 := by simp [normSq]
/-
**Complex.normSq_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_nonneg (z : Complex) : 0 <= normSq z
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem normSq_nonneg (z : ℂ) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
/-
**Complex.normSq_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_eq_zero {z : Complex} : normSq z = 0 ↔ z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用引理 `eq_zero_of_mul_self_add_mul_self_eq_zero`：eq_zero_of_mul_self_add_mul_se
lf_eq_zero [NoZeroDivisors R] [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (
h : a * a + b * b = 0) : a = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Complex.normSq_zero`：normSq_zero : normSq 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem normSq_eq_zero {z : ℂ} : normSq z = 0 ↔ z = 0 :=
  ⟨fun h =>
    ext (eq_zero_of_mul_self_add_mul_self_eq_zero h)
      (eq_zero_of_mul_self_add_mul_self_eq_zero <| (add_comm _ _).trans h),
    fun h => h.symm ▸ normSq_zero⟩

@[simp]
/-
**Complex.normSq_pos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_pos {z : Complex} : 0 < normSq z ↔ z != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `Complex.normSq_nonneg`：normSq_nonneg (z : Complex) : 0 <= normSq z
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Complex.normSq_eq_zero`：normSq_eq_zero {z : Complex} : normSq z = 0 ↔ z 
= 0
-/
theorem normSq_pos {z : ℂ} : 0 < normSq z ↔ z ≠ 0 :=
  (normSq_nonneg z).lt_iff_ne.trans <| not_congr (eq_comm.trans normSq_eq_zero)

@[simp]
/-
**Complex.normSq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_neg (z : Complex) : normSq (-z) = normSq z
参数：z : Complex。
该定理/引理给出了一组等式。
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
theorem normSq_neg (z : ℂ) : normSq (-z) = normSq z := by simp [normSq]

@[simp]
/-
**Complex.normSq_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_conj (z : Complex) : normSq (conj z) = normSq z
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_conj (z : ℂ) : normSq (conj z) = normSq z := by simp [normSq]
/-
**Complex.normSq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_mul (z w : Complex) : normSq (z * w) = normSq z * normSq w
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZe
roOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β) (a b : α),   f (a * b) 
= f a * f b
-/
theorem normSq_mul (z w : ℂ) : normSq (z * w) = normSq z * normSq w :=
  normSq.map_mul z w
/-
**Complex.normSq_add** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_add (z w : Complex) : normSq (z + w) = normSq z + normSq w + 2 * (z
 * conj w).re
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 32 条，此处仅展示前 30 条）
-/
theorem normSq_add (z w : ℂ) : normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re := by
  simp [normSq]; ring
/-
**Complex.re_sq_le_normSq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：re_sq_le_normSq (z : Complex) : z.re * z.re <= normSq z
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem re_sq_le_normSq (z : ℂ) : z.re * z.re ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)
/-
**Complex.im_sq_le_normSq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：im_sq_le_normSq (z : Complex) : z.im * z.im <= normSq z
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem im_sq_le_normSq (z : ℂ) : z.im * z.im ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)
/-
**Complex.mul_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：mul_conj (z : Complex) : z * conj z = normSq z
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem mul_conj (z : ℂ) : z * conj z = normSq z :=
  Complex.ext_iff.2 <| by simp [normSq, mul_comm, sub_eq_neg_add, add_comm, ofReal]
/-
**Complex.add_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：add_conj (z : Complex) : z + conj z = (2 * z.re : Real)
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
  Complex.ext_iff.2 <| by simp [two_mul, ofReal]

/-- The coercion `ℝ → ℂ` as a `RingHom`. -/
@[instance_reducible]
/-
**Complex.ofRealHom** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：ofRealHom : Real ->+* Complex where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_zero`：ofReal_zero : ((0 : Real) : Complex) = 0
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s

--- 原说明 ---
The coercion `ℝ → ℂ` as a `RingHom`.
-/
def ofRealHom : ℝ →+* ℂ where
  toFun x := (x : ℂ)
  map_one' := ofReal_one
  map_zero' := ofReal_zero
  map_mul' := ofReal_mul
  map_add' := ofReal_add
/-
**Complex.ofRealHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (r : ℝ), Complex.ofRealHom r = ↑r
参数：r : ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofRealHom_eq_coe (r : ℝ) : ofRealHom r = r := rfl

variable {α : Type*}
/-
**Complex.ofReal_comp_add** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} (f g : α → ℝ), Complex.ofReal ∘ (f + g) = Complex.ofReal 
∘ f + Complex.ofReal ∘ g
参数：f g : α → ℝ；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_comp_add`：∀ {ι : Type u_1} {M : Type u_4} {N : Type u_5} {F : Type u
_9} [inst : Add M] [inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M 
N]…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
@[simp] lemma ofReal_comp_add (f g : α → ℝ) : ofReal ∘ (f + g) = ofReal ∘ f + ofReal ∘ g :=
  map_comp_add ofRealHom ..
/-
**Complex.ofReal_comp_sub** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} (f g : α → ℝ), Complex.ofReal ∘ (f - g) = Complex.ofReal 
∘ f - Complex.ofReal ∘ g
参数：f g : α → ℝ；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_comp_sub`：∀ {ι : Type u_1} {G : Type u_7} {H : Type u_8} {F : Type u
_9} [inst : FunLike F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H
] …
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
@[simp] lemma ofReal_comp_sub (f g : α → ℝ) : ofReal ∘ (f - g) = ofReal ∘ f - ofReal ∘ g :=
  map_comp_sub ofRealHom ..
/-
**Complex.ofReal_comp_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} (f : α → ℝ), Complex.ofReal ∘ (-f) = -Complex.ofReal ∘ f
参数：f : α → ℝ；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_comp_neg`：∀ {ι : Type u_1} {G : Type u_7} {H : Type u_8} {F : Type u
_9} [inst : FunLike F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H
] …
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
@[simp] lemma ofReal_comp_neg (f : α → ℝ) : ofReal ∘ (-f) = -(ofReal ∘ f) :=
  map_comp_neg ofRealHom _
/-
**Complex.ofReal_comp_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：ofReal_comp_nsmul (n : Nat) (f : α -> Real) : ofReal ∘ (n • f) = n • (ofRe
al ∘ f)
参数：n : Nat；f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_comp_nsmul`：∀ {ι : Type u_1} {G : Type u_7} {H : Type u_8} {F : Type
 u_9} [inst : FunLike F G H] [inst_1 : AddMonoid G]   [inst_2 : AddMonoid H] [Ad
dMon…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma ofReal_comp_nsmul (n : ℕ) (f : α → ℝ) : ofReal ∘ (n • f) = n • (ofReal ∘ f) :=
  map_comp_nsmul ofRealHom ..
/-
**Complex.ofReal_comp_zsmul** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：ofReal_comp_zsmul (n : Int) (f : α -> Real) : ofReal ∘ (n • f) = n • (ofRe
al ∘ f)
参数：n : Int；f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_comp_zsmul`：∀ {ι : Type u_1} {G : Type u_7} {H : Type u_8} {F : Type
 u_9} [inst : FunLike F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid
 H] …
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma ofReal_comp_zsmul (n : ℤ) (f : α → ℝ) : ofReal ∘ (n • f) = n • (ofReal ∘ f) :=
  map_comp_zsmul ofRealHom ..
/-
**Complex.ofReal_comp_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} (f g : α → ℝ), Complex.ofReal ∘ (f * g) = Complex.ofReal 
∘ f * Complex.ofReal ∘ g
参数：f g : α → ℝ；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `map_comp_mul`：map_comp_mul [MulHomClass F M N] (f : F) (g h : ι -> M) : 
f ∘ (g * h) = f ∘ g * f ∘ h
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
@[simp] lemma ofReal_comp_mul (f g : α → ℝ) : ofReal ∘ (f * g) = ofReal ∘ f * ofReal ∘ g :=
  map_comp_mul ofRealHom ..
/-
**Complex.ofReal_comp_pow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {α : Type u_1} (f : α → ℝ) (n : ℕ), Complex.ofReal ∘ (f ^ n) = Complex.o
fReal ∘ f ^ n
参数：f : α → ℝ；n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `map_comp_pow`：map_comp_pow [Monoid G] [Monoid H] [MonoidHomClass F G H] 
(f : F) (g : ι -> G) (n : Nat) : f ∘ (g ^ n) = f ∘ g ^ n
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
@[simp] lemma ofReal_comp_pow (f : α → ℝ) (n : ℕ) : ofReal ∘ (f ^ n) = (ofReal ∘ f) ^ n :=
  map_comp_pow ofRealHom ..

@[simp]
/-
**Complex.I_sq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：I_sq : I ^ 2 = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
-/
theorem I_sq : I ^ 2 = -1 := by rw [sq, I_mul_I]

@[simp]
/-
**Complex.I_pow_three** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：I_pow_three : I ^ 3 = -I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Complex.I_sq`：I_sq : I ^ 2 = -1
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
-/
lemma I_pow_three : I ^ 3 = -I := by rw [pow_succ, I_sq, neg_one_mul]

@[simp]
/-
**Complex.I_pow_four** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：I_pow_four : I ^ 4 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Complex.I_sq`：I_sq : I ^ 2 = -1
· 使用引理 `neg_one_sq`：neg_one_sq : (-1 : R) ^ 2 = 1
-/
theorem I_pow_four : I ^ 4 = 1 := by rw [(by simp : 4 = 2 * 2), pow_mul, I_sq, neg_one_sq]
/-
**Complex.I_pow_eq_pow_mod** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：I_pow_eq_pow_mod (n : Nat) : I ^ n = I ^ (n % 4)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_add_mod`：∀ (m n : ℕ), n * (m / n) + m % n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Complex.I_pow_four`：I_pow_four : I ^ 4 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma I_pow_eq_pow_mod (n : ℕ) : I ^ n = I ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4]
  simp [pow_add, pow_mul, I_pow_four]

open Qq in
/-- Reduce `Complex.I ^ n` to `Complex.I ^ (n % 4)` when `n` is a literal natural number at
least `4`. Combined with `Nat.reduceMod` this normalises every literal power of `I` to one of
`I ^ 0`, `I ^ 1`, `I ^ 2`, `I ^ 3`, which the existing `@[simp]` lemmas dispatch. -/
simproc I_pow_eq_pow_mod' (I ^ _) := .ofQ fun u a e =>
  match u, a, e with
  | 1, ~q(ℂ), ~q(I ^ ($n : ℕ)) => do
    let some n' := n.nat? | return .continue
    if n' < 4 then return .continue
    -- we don't reduce `n % 4`, further, since `Nat.reduceMod` will handle that
    return .visit <| .mk q(I ^ ($n % 4)) <| .some q(I_pow_eq_pow_mod $n)
  | _, _, _ => return .continue

@[simp]
/-
**Complex.sub_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：sub_re (z w : Complex) : (z - w).re = z.re - w.re
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_re (z w : ℂ) : (z - w).re = z.re - w.re :=
  rfl

@[simp]
/-
**Complex.sub_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：sub_im (z w : Complex) : (z - w).im = z.im - w.im
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_im (z w : ℂ) : (z - w).im = z.im - w.im :=
  rfl

@[simp, norm_cast]
/-
**Complex.ofReal_sub** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_sub (r s : Real) : ((r - s : Real) : Complex) = r - s
参数：r s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem ofReal_sub (r s : ℝ) : ((r - s : ℝ) : ℂ) = r - s :=
  Complex.ext_iff.2 <| by simp [ofReal]

@[simp, norm_cast]
/-
**Complex.ofReal_pow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : Complex) = (r : Comple
x) ^ n
参数：r : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n := by
  induction n <;> simp [*, ofReal_mul, pow_succ]
/-
**Complex.sub_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：sub_conj (z : Complex) : z - conj z = (2 * z.im : Real) * I
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem sub_conj (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
  Complex.ext_iff.2 <| by simp [two_mul, sub_eq_add_neg, ofReal]
/-
**Complex.normSq_sub** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_sub (z w : Complex) : normSq (z - w) = normSq z + normSq w - 2 * (z
 * conj w).re
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Complex.normSq_add`：normSq_add (z w : Complex) : normSq (z + w) = normSq
 z + normSq w + 2 * (z * conj w).re
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.normSq_neg`：normSq_neg (z : Complex) : normSq (-z) = normSq z
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 40 条，此处仅展示前 30 条）
-/
theorem normSq_sub (z w : ℂ) : normSq (z - w) = normSq z + normSq w - 2 * (z * conj w).re := by
  rw [sub_eq_add_neg, normSq_add]
  simp only [map_neg, mul_neg, neg_re, normSq_neg]
  ring

/-! ### Inversion -/


@[no_expose]
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Inversion
-/
noncomputable instance : Inv ℂ :=
  ⟨fun z => conj z * ((normSq z)⁻¹ : ℝ)⟩
/-
**Complex.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：inv_def (z : Complex) : z⁻¹ = conj z * ((normSq z)⁻¹ : Real)
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def (z : ℂ) : z⁻¹ = conj z * ((normSq z)⁻¹ : ℝ) :=
  (rfl)

@[simp]
/-
**Complex.inv_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：inv_re (z : Complex) : z⁻¹.re = z.re / normSq z
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.inv_def`：inv_def (z : Complex) : z⁻¹ = conj z * ((normSq z)⁻¹ : 
Real)
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `division_def`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a b : G), a / b 
= a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_re (z : ℂ) : z⁻¹.re = z.re / normSq z := by simp [inv_def, division_def, ofReal]

@[simp]
/-
**Complex.inv_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：inv_im (z : Complex) : z⁻¹.im = -z.im / normSq z
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.inv_def`：inv_def (z : Complex) : z⁻¹ = conj z * ((normSq z)⁻¹ : 
Real)
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `division_def`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a b : G), a / b 
= a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_im (z : ℂ) : z⁻¹.im = -z.im / normSq z := by simp [inv_def, division_def, ofReal]

@[simp, norm_cast]
/-
**Complex.ofReal_inv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (r : Complex)⁻¹
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.inv_re`：inv_re (z : Complex) : z⁻¹.re = z.re / normSq z
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `div_self_mul_self'`：div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.inv_im`：inv_im (z : Complex) : z⁻¹.im = -z.im / normSq z
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem ofReal_inv (r : ℝ) : ((r⁻¹ : ℝ) : ℂ) = (r : ℂ)⁻¹ :=
  Complex.ext_iff.2 <| by simp [ofReal]
/-
**Complex.inv_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：0⁻¹ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_zero`：ofReal_zero : ((0 : Real) : Complex) = 0
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
-/
protected theorem inv_zero : (0⁻¹ : ℂ) = 0 := by
  rw [← ofReal_zero, ← ofReal_inv, inv_zero]
/-
**Complex.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {z : ℂ}, z ≠ 0 → z * z⁻¹ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.inv_def`：inv_def (z : Complex) : z⁻¹ = conj z * ((normSq z)⁻¹ : 
Real)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Complex.mul_conj`：mul_conj (z : Complex) : z * conj z = normSq z
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.normSq_eq_zero`：normSq_eq_zero {z : Complex} : normSq z = 0 ↔ z 
= 0
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
-/
protected theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * z⁻¹ = 1 := by
  rw [inv_def, ← mul_assoc, mul_conj, ← ofReal_mul, mul_inv_cancel₀ (mt normSq_eq_zero.1 h),
    ofReal_one]
/-
**Complex.instDivInvMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：DivInvMonoid ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instDivInvMonoid : DivInvMonoid ℂ where
/-
**Complex.div_re** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：div_re (z w : Complex) : (z / w).re = z.re * w.re / normSq w + z.im * w.im
 / normSq w
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `Complex.inv_re`：inv_re (z : Complex) : z⁻¹.re = z.re / normSq z
· 使用定理 `Complex.inv_im`：inv_im (z : Complex) : z⁻¹.im = -z.im / normSq z
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma div_re (z w : ℂ) : (z / w).re = z.re * w.re / normSq w + z.im * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]
/-
**Complex.div_im** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：div_im (z w : Complex) : (z / w).im = z.im * w.re / normSq w - z.re * w.im
 / normSq w
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `Complex.inv_im`：inv_im (z : Complex) : z⁻¹.im = -z.im / normSq z
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Complex.inv_re`：inv_re (z : Complex) : z⁻¹.re = z.re / normSq z
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma div_im (z w : ℂ) : (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]

/-! ### Field instance and lemmas -/

/-
**Complex.instField** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：instField : Field Complex where mul_inv_cancel
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DivInvMonoid.div_eq_mul_inv`：∀ {G : Type u} [self : DivInvMonoid G] (a b
 : G), a / b = a * b⁻¹
· 使用定理 `DivInvMonoid.zpow_zero'`：∀ {G : Type u} [self : DivInvMonoid G] (a : G),
 a ^ 0 = 1
· 使用定理 `DivInvMonoid.zpow_succ'`：∀ {G : Type u} [self : DivInvMonoid G] (n : ℕ) 
(a : G), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `DivInvMonoid.zpow_neg'`：∀ {G : Type u} [self : DivInvMonoid G] (n : ℕ) (
a : G), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Complex.mul_inv_cancel`：∀ {z : ℂ}, z ≠ 0 → z * z⁻¹ = 1
· 使用定理 `Complex.inv_zero`：0⁻¹ = 0

--- 原说明 ---
### Field instance and lemmas
-/
noncomputable instance instField : Field ℂ where
  mul_inv_cancel := @Complex.mul_inv_cancel
  inv_zero := Complex.inv_zero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by ext <;> simp [NNRat.cast_def, div_re, div_im, mul_div_mul_comm]
  ratCast_def q := by ext <;> simp [Rat.cast_def, div_re, div_im, mul_div_mul_comm]
  nnqsmul_def n z := Complex.ext_iff.2 <| by simp [NNRat.smul_def, smul_re, smul_im]
  qsmul_def n z := Complex.ext_iff.2 <| by simp [Rat.smul_def, smul_re, smul_im]

@[simp, norm_cast]
/-
**Complex.ofReal_nnqsmul** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：ofReal_nnqsmul (q : Rat>=0) (r : Real) : ofReal (q • r) = q • r
参数：q : Rat>=0；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.smul_def`：smul_def (q : Rat>=0) (a : K) : q • a = q * a
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofReal_nnqsmul (q : ℚ≥0) (r : ℝ) : ofReal (q • r) = q • r := by simp [NNRat.smul_def]

@[simp, norm_cast]
/-
**Complex.ofReal_qsmul** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：ofReal_qsmul (q : Rat) (r : Real) : ofReal (q • r) = q • r
参数：q : Rat；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.smul_def`：smul_def (a : Rat) (x : K) : a • x = ↑a * x
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofReal_qsmul (q : ℚ) (r : ℝ) : ofReal (q • r) = q • r := by simp [Rat.smul_def]
/-
**Complex.conj_inv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_inv (x : Complex) : conj x⁻¹ = (conj x)⁻¹
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_inv₀`：star_inv₀ [GroupWithZero R] [StarMul R] (x : R) : star x⁻¹ = 
(star x)⁻¹
-/
theorem conj_inv (x : ℂ) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv₀ _

@[simp, norm_cast]
/-
**Complex.ofReal_div** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_div (r s : Real) : ((r / s : Real) : Complex) = r / s
参数：r s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem ofReal_div (r s : ℝ) : ((r / s : ℝ) : ℂ) = r / s := map_div₀ ofRealHom r s

@[simp, norm_cast]
/-
**Complex.ofReal_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_zpow (r : Real) (n : Int) : ((r ^ n : Real) : Complex) = (r : Compl
ex) ^ n
参数：r : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem ofReal_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n := map_zpow₀ ofRealHom r n

@[simp]
/-
**Complex.div_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：div_I (z : Complex) : z / I = -(z * I)
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_eq_iff_mul_eq`：div_eq_iff_mul_eq (hb : b != 0) : a / b = c ↔ c * b =
 a
· 使用定理 `Complex.I_ne_zero`：Complex.I ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_I (z : ℂ) : z / I = -(z * I) :=
  (div_eq_iff_mul_eq I_ne_zero).2 <| by simp [mul_assoc]

@[simp]
/-
**Complex.inv_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：inv_I : I⁻¹ = -I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用定理 `Complex.div_I`：div_I (z : Complex) : z / I = -(z * I)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem inv_I : I⁻¹ = -I := by
  rw [inv_eq_one_div, div_I, one_mul]
/-
**Complex.I_zpow_eq_zpow_mod** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：I_zpow_eq_zpow_mod (m : Int) : I ^ m = I ^ (m % 4)
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.mul_ediv_add_emod`：∀ (a b : ℤ), b * (a / b) + a % b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `Complex.I_pow_four`：I_pow_four : I ^ 4 = 1
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma I_zpow_eq_zpow_mod (m : ℤ) : I ^ m = I ^ (m % 4) := by
  conv_lhs => rw [← Int.mul_ediv_add_emod m 4]
  simp [zpow_add₀, zpow_mul, zpow_ofNat]
/-
**Complex.normSq_inv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_inv (z : Complex) : normSq z⁻¹ = (normSq z)⁻¹
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_inv (z : ℂ) : normSq z⁻¹ = (normSq z)⁻¹ := by simp
/-
**Complex.normSq_div** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：normSq_div (z w : Complex) : normSq (z / w) = normSq z / normSq w
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normSq_div (z w : ℂ) : normSq (z / w) = normSq z / normSq w := by simp
/-
**Complex.div_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：div_ofReal (z : Complex) (x : Real) : z / x = ⟨z.re / x, z.im / x⟩
参数：z : Complex；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_mul'`：ofReal_mul' (r : Real) (z : Complex) : ↑r * z = ⟨r 
* z.re, r * z.im⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma div_ofReal (z : ℂ) (x : ℝ) : z / x = ⟨z.re / x, z.im / x⟩ := by
  simp_rw [div_eq_inv_mul, ← ofReal_inv, ofReal_mul']
/-
**Complex.div_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：div_natCast (z : Complex) (n : Nat) : z / n = ⟨z.re / n, z.im / n⟩
参数：z : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.div_ofReal`：div_ofReal (z : Complex) (x : Real) : z / x = ⟨z.re 
/ x, z.im / x⟩
-/
lemma div_natCast (z : ℂ) (n : ℕ) : z / n = ⟨z.re / n, z.im / n⟩ :=
  mod_cast div_ofReal z n
/-
**Complex.div_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：div_intCast (z : Complex) (n : Int) : z / n = ⟨z.re / n, z.im / n⟩
参数：z : Complex；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.div_ofReal`：div_ofReal (z : Complex) (x : Real) : z / x = ⟨z.re 
/ x, z.im / x⟩
-/
lemma div_intCast (z : ℂ) (n : ℤ) : z / n = ⟨z.re / n, z.im / n⟩ :=
  mod_cast div_ofReal z n
/-
**Complex.div_ratCast** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：div_ratCast (z : Complex) (x : Rat) : z / x = ⟨z.re / x, z.im / x⟩
参数：z : Complex；x : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.div_ofReal`：div_ofReal (z : Complex) (x : Real) : z / x = ⟨z.re 
/ x, z.im / x⟩
-/
lemma div_ratCast (z : ℂ) (x : ℚ) : z / x = ⟨z.re / x, z.im / x⟩ :=
  mod_cast div_ofReal z x
/-
**Complex.div_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：div_ofNat (z : Complex) (n : Nat) [n.AtLeastTwo] : z / ofNat(n) = ⟨z.re / 
ofNat(n), z.im / ofNat(n)⟩
参数：z : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.div_natCast`：div_natCast (z : Complex) (n : Nat) : z / n = ⟨z.re
 / n, z.im / n⟩
-/
lemma div_ofNat (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    z / ofNat(n) = ⟨z.re / ofNat(n), z.im / ofNat(n)⟩ :=
  div_natCast z n
/-
**Complex.div_ofReal_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ) (x : ℝ), (z / ↑x).re = z.re / x
参数：z : ℂ；x : ℝ；z / ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.div_ofReal`：div_ofReal (z : Complex) (x : Real) : z / x = ⟨z.re 
/ x, z.im / x⟩
-/
@[simp] lemma div_ofReal_re (z : ℂ) (x : ℝ) : (z / x).re = z.re / x := by rw [div_ofReal]
/-
**Complex.div_ofReal_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ) (x : ℝ), (z / ↑x).im = z.im / x
参数：z : ℂ；x : ℝ；z / ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.div_ofReal`：div_ofReal (z : Complex) (x : Real) : z / x = ⟨z.re 
/ x, z.im / x⟩
-/
@[simp] lemma div_ofReal_im (z : ℂ) (x : ℝ) : (z / x).im = z.im / x := by rw [div_ofReal]
/-
**Complex.div_natCast_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ) (n : ℕ), (z / ↑n).re = z.re / ↑n
参数：z : ℂ；n : ℕ；z / ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.div_natCast`：div_natCast (z : Complex) (n : Nat) : z / n = ⟨z.re
 / n, z.im / n⟩
-/
@[simp] lemma div_natCast_re (z : ℂ) (n : ℕ) : (z / n).re = z.re / n := by rw [div_natCast]
/-
**Complex.div_natCast_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ) (n : ℕ), (z / ↑n).im = z.im / ↑n
参数：z : ℂ；n : ℕ；z / ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.div_natCast`：div_natCast (z : Complex) (n : Nat) : z / n = ⟨z.re
 / n, z.im / n⟩
-/
@[simp] lemma div_natCast_im (z : ℂ) (n : ℕ) : (z / n).im = z.im / n := by rw [div_natCast]
/-
**Complex.div_intCast_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ) (n : ℤ), (z / ↑n).re = z.re / ↑n
参数：z : ℂ；n : ℤ；z / ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.div_intCast`：div_intCast (z : Complex) (n : Int) : z / n = ⟨z.re
 / n, z.im / n⟩
-/
@[simp] lemma div_intCast_re (z : ℂ) (n : ℤ) : (z / n).re = z.re / n := by rw [div_intCast]
/-
**Complex.div_intCast_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ) (n : ℤ), (z / ↑n).im = z.im / ↑n
参数：z : ℂ；n : ℤ；z / ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.div_intCast`：div_intCast (z : Complex) (n : Int) : z / n = ⟨z.re
 / n, z.im / n⟩
-/
@[simp] lemma div_intCast_im (z : ℂ) (n : ℤ) : (z / n).im = z.im / n := by rw [div_intCast]
/-
**Complex.div_ratCast_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ) (x : ℚ), (z / ↑x).re = z.re / ↑x
参数：z : ℂ；x : ℚ；z / ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.div_ratCast`：div_ratCast (z : Complex) (x : Rat) : z / x = ⟨z.re
 / x, z.im / x⟩
-/
@[simp] lemma div_ratCast_re (z : ℂ) (x : ℚ) : (z / x).re = z.re / x := by rw [div_ratCast]
/-
**Complex.div_ratCast_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ) (x : ℚ), (z / ↑x).im = z.im / ↑x
参数：z : ℂ；x : ℚ；z / ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.div_ratCast`：div_ratCast (z : Complex) (x : Rat) : z / x = ⟨z.re
 / x, z.im / x⟩
-/
@[simp] lemma div_ratCast_im (z : ℂ) (x : ℚ) : (z / x).im = z.im / x := by rw [div_ratCast]

@[simp]
/-
**Complex.div_ofNat_re** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：div_ofNat_re (z : Complex) (n : Nat) [n.AtLeastTwo] : (z / ofNat(n)).re = 
z.re / ofNat(n)
参数：z : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.div_natCast_re`：∀ (z : ℂ) (n : ℕ), (z / ↑n).re = z.re / ↑n
-/
lemma div_ofNat_re (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (z / ofNat(n)).re = z.re / ofNat(n) := div_natCast_re z n

@[simp]
/-
**Complex.div_ofNat_im** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：div_ofNat_im (z : Complex) (n : Nat) [n.AtLeastTwo] : (z / ofNat(n)).im = 
z.im / ofNat(n)
参数：z : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.div_natCast_im`：∀ (z : ℂ) (n : ℕ), (z / ↑n).im = z.im / ↑n
-/
lemma div_ofNat_im (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (z / ofNat(n)).im = z.im / ofNat(n) := div_natCast_im z n

/-! ### Characteristic zero -/


/-
**Complex.instCharZero** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：instCharZero : CharZero Complex
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `charZero_of_inj_zero`：charZero_of_inj_zero [AddGroupWithOne R] (H : fora
ll n : Nat, (n : R) = 0 -> n = 0) : CharZero R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Complex.ofReal_eq_zero`：ofReal_eq_zero {z : Real} : (z : Complex) = 0 ↔ 
z = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_natCast`：∀ (n : ℕ), ↑↑n = ↑n

--- 原说明 ---
### Characteristic zero
-/
instance instCharZero : CharZero ℂ :=
  charZero_of_inj_zero fun n h => by rwa [← ofReal_natCast, ofReal_eq_zero, Nat.cast_eq_zero] at h
/-
**Complex.instIsAddTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：instIsAddTorsionFree : IsAddTorsionFree Complex
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.instIsAddTorsionFreeOfCharZero`：∀ (R : Type u_1) [inst : Semiri
ng R] [IsDomain R] [CharZero R], IsAddTorsionFree R
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
-/
instance instIsAddTorsionFree : IsAddTorsionFree ℂ := IsDomain.instIsAddTorsionFreeOfCharZero _

/-- A complex number `z` plus its conjugate `conj z` is `2` times its real part. -/
/-
**Complex.re_eq_add_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：re_eq_add_conj (z : Complex) : (z.re : Complex) = (z + conj z) / 2
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.add_conj`：add_conj (z : Complex) : z + conj z = (2 * z.re : Real
)
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A complex number `z` plus its conjugate `conj z` is `2` times its real part.
-/
theorem re_eq_add_conj (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
  simp only [add_conj, ofReal_mul, ofReal_ofNat, mul_div_cancel_left₀ (z.re : ℂ) two_ne_zero]

/-- A complex number `z` minus its conjugate `conj z` is `2i` times its imaginary part. -/
/-
**Complex.im_eq_sub_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：im_eq_sub_conj (z : Complex) : (z.im : Complex) = (z - conj z) / (2 * I)
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.sub_conj`：sub_conj (z : Complex) : z - conj z = (2 * z.im : Real
) * I
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Complex.I_ne_zero`：Complex.I ≠ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A complex number `z` minus its conjugate `conj z` is `2i` times its imaginary pa
rt.
-/
theorem im_eq_sub_conj (z : ℂ) : (z.im : ℂ) = (z - conj z) / (2 * I) := by
  simp only [sub_conj, ofReal_mul, ofReal_ofNat, mul_right_comm,
    mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero I_ne_zero : 2 * I ≠ 0)]

/-- Show the imaginary number ⟨x, y⟩ as an `"x + y*I"` string

Note that the Real numbers used for x and y will show as Cauchy sequences due to the way Real
numbers are represented.
-/
/-
**Complex.instRepr** 是 Mathlib 中的一个unsafe-def，位于命名空间 `Complex`。
形式化陈述：Repr ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show the imaginary number ⟨x, y⟩ as an `"x + y*I"` string

Note that the Real numbers used for x and y will show as Cauchy sequences due to
 the way Real
numbers are represented.
-/
unsafe instance instRepr : Repr ℂ where
  reprPrec f p :=
    (if p > 65 then (Std.Format.bracket "(" · ")") else (·)) <|
      reprPrec f.re 65 ++ " + " ++ reprPrec f.im 70 ++ "*I"

section reProdIm

/-- The preimage under `equivRealProd` of `s ×ˢ t` is `s ×ℂ t`. -/
/-
**Complex.preimage_equivRealProd_prod** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：preimage_equivRealProd_prod (s t : Set Real) : equivRealProd ⁻¹' (s ×ˢ t) 
= s ×Complex t
参数：s t : Set Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage under `equivRealProd` of `s ×ˢ t` is `s ×ℂ t`.
-/
lemma preimage_equivRealProd_prod (s t : Set ℝ) : equivRealProd ⁻¹' (s ×ˢ t) = s ×ℂ t := rfl

/-- The inequality `s × t ⊆ s₁ × t₁` holds in `ℂ` iff it holds in `ℝ × ℝ`. -/
/-
**Complex.reProdIm_subset_iff** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：reProdIm_subset_iff {s s₁ t t₁ : Set Real} : s ×Complex t subseteq s₁ ×Com
plex t₁ ↔ s ×ˢ t subseteq s₁ ×ˢ t₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Complex.preimage_equivRealProd_prod`：preimage_equivRealProd_prod (s t : 
Set Real) : equivRealProd ⁻¹' (s ×ˢ t) = s ×Complex t
· 使用定理 `Equiv.preimage_subset`：preimage_subset {α β} (e : α ≃ β) (s t : Set β) :
 e ⁻¹' s subseteq e ⁻¹' t ↔ s subseteq t

--- 原说明 ---
The inequality `s × t ⊆ s₁ × t₁` holds in `ℂ` iff it holds in `ℝ × ℝ`.
-/
lemma reProdIm_subset_iff {s s₁ t t₁ : Set ℝ} : s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ×ˢ t ⊆ s₁ ×ˢ t₁ := by
  rw [← @preimage_equivRealProd_prod s t, ← @preimage_equivRealProd_prod s₁ t₁]
  exact Equiv.preimage_subset equivRealProd _ _

/-- If `s ⊆ s₁ ⊆ ℝ` and `t ⊆ t₁ ⊆ ℝ`, then `s × t ⊆ s₁ × t₁` in `ℂ`. -/
/-
**Complex.reProdIm_subset_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：reProdIm_subset_iff' {s s₁ t t₁ : Set Real} : s ×Complex t subseteq s₁ ×Co
mplex t₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Complex.reProdIm_subset_iff`：reProdIm_subset_iff {s s₁ t t₁ : Set Real} 
: s ×Complex t subseteq s₁ ×Complex t₁ ↔ s ×ˢ t subseteq s₁ ×ˢ t₁
· 使用定理 `Set.prod_subset_prod_iff`：prod_subset_prod_iff : s ×ˢ t subseteq s₁ ×ˢ t
₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅

--- 原说明 ---
If `s ⊆ s₁ ⊆ ℝ` and `t ⊆ t₁ ⊆ ℝ`, then `s × t ⊆ s₁ × t₁` in `ℂ`.
-/
lemma reProdIm_subset_iff' {s s₁ t t₁ : Set ℝ} :
    s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  convert! prod_subset_prod_iff
  exact reProdIm_subset_iff

variable {s t : Set ℝ}
/-
**Complex.reProdIm_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {s t : Set ℝ}, (s ×ℂ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
参数：s ×ℂ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma reProdIm_nonempty : (s ×ℂ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  simp [Set.Nonempty, reProdIm, Complex.exists]
/-
**Complex.reProdIm_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {s t : Set ℝ}, s ×ℂ t = ∅ ↔ s = ∅ ∨ t = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma reProdIm_eq_empty : s ×ℂ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp [← not_nonempty_iff_eq_empty, reProdIm_nonempty, -not_and, not_and_or]

end reProdIm

open scoped Interval

section Rectangle

/-- A `Rectangle` is an axis-parallel rectangle with corners `z` and `w`. -/
/-
**Complex.Rectangle** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：Rectangle (z w : Complex) : Set Complex
参数：z w : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Rectangle` is an axis-parallel rectangle with corners `z` and `w`.
-/
def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

end Rectangle

section Segments

/-- A real segment `[a₁, a₂]` translated by `b * I` is the complex line segment. -/
/-
**Complex.horizontalSegment_eq** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：horizontalSegment_eq (a₁ a₂ b : Real) : (fun (x : Real) => x + b * I) '' [
[a₁, a₂]] = [[a₁, a₂]] ×Complex {b}
参数：a₁ a₂ b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Complex.preimage_equivRealProd_prod`：preimage_equivRealProd_prod (s t : 
Set Real) : equivRealProd ⁻¹' (s ×ˢ t) = s ×Complex t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.equivRealProd_apply`：∀ (z : ℂ), Complex.equivRealProd z = (z.re,
 z.im)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z

--- 原说明 ---
A real segment `[a₁, a₂]` translated by `b * I` is the complex line segment.
-/
lemma horizontalSegment_eq (a₁ a₂ b : ℝ) :
    (fun (x : ℝ) ↦ x + b * I) '' [[a₁, a₂]] = [[a₁, a₂]] ×ℂ {b} := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.re, x₁, by simp⟩

/-- A vertical segment `[b₁, b₂]` translated by `a` is the complex line segment. -/
/-
**Complex.verticalSegment_eq** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：verticalSegment_eq (a b₁ b₂ : Real) : (fun (y : Real) => a + y * I) '' [[b
₁, b₂]] = {a} ×Complex [[b₁, b₂]]
参数：a b₁ b₂ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Complex.preimage_equivRealProd_prod`：preimage_equivRealProd_prod (s t : 
Set Real) : equivRealProd ⁻¹' (s ×ˢ t) = s ×Complex t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.equivRealProd_apply`：∀ (z : ℂ), Complex.equivRealProd z = (z.re,
 z.im)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.singleton_prod`：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z

--- 原说明 ---
A vertical segment `[b₁, b₂]` translated by `a` is the complex line segment.
-/
lemma verticalSegment_eq (a b₁ b₂ : ℝ) :
    (fun (y : ℝ) ↦ a + y * I) '' [[b₁, b₂]] = {a} ×ℂ [[b₁, b₂]] := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    simp only [equivRealProd_apply, singleton_prod, mem_image, Prod.mk.injEq,
      exists_eq_right_right, mem_preimage] at hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.im, x₁, by simp⟩

end Segments

end Complex

