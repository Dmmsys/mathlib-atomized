/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fin.Fin2
public import Mathlib.Data.PFun
public import Mathlib.Data.Vector3
public import Mathlib.NumberTheory.PellMatiyasevic

/-!
# Diophantine functions and Matiyasevic's theorem

Hilbert's tenth problem asked whether there exists an algorithm which for a given integer polynomial
determines whether this polynomial has integer solutions. It was answered in the negative in 1970,
the final step being completed by Matiyasevic who showed that the power function is Diophantine.

Here a function is called Diophantine if its graph is Diophantine as a set. A subset `S ⊆ ℕ ^ α` in
turn is called Diophantine if there exists an integer polynomial on `α ⊕ β` such that `v ∈ S` iff
there exists `t : ℕ^β` with `p (v, t) = 0`.

## Main definitions

* `IsPoly`: a predicate stating that a function is a multivariate integer polynomial.
* `Poly`: the type of multivariate integer polynomial functions.
* `Dioph`: a predicate stating that a set is Diophantine, i.e. a set `S ⊆ ℕ^α` is
  Diophantine if there exists a polynomial on `α ⊕ β` such that `v ∈ S` iff there
  exists `t : ℕ^β` with `p (v, t) = 0`.
* `DiophFn`: a predicate on a function stating that it is Diophantine in the sense that its graph
  is Diophantine as a set.

## Main statements

* `pell_dioph` states that solutions to Pell's equation form a Diophantine set.
* `pow_dioph` states that the power function is Diophantine, a version of Matiyasevic's theorem.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevic's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Matiyasevic's theorem, Hilbert's tenth problem

## TODO

* Finish the solution of Hilbert's tenth problem.
* Connect `Poly` to `MvPolynomial`
-/

@[expose] public section


open Fin2 Function Nat Sum

local infixr:67 " ::ₒ " => Option.elim'

local infixr:65 " ⊗ " => Sum.elim

universe u

/-!
### Multivariate integer polynomials

Note that this duplicates `MvPolynomial`.
-/


section Polynomials

variable {α β : Type*}

/-- A predicate asserting that a function is a multivariate integer polynomial.
  (We are being a bit lazy here by allowing many representations for multiplication,
  rather than only allowing monomials and addition, but the definition is equivalent
  and this is easier to use.) -/
/-
**IsPoly** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → ((α → ℕ) → ℤ) → Prop
参数：(α → ℕ) → ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate asserting that a function is a multivariate integer polynomial.
  (We are being a bit lazy here by allowing many representations for multiplicat
ion,
  rather than only allowing monomials and addition, but the definition is equiva
lent
  and this is easier to use.)
-/
inductive IsPoly : ((α → ℕ) → ℤ) → Prop
  | proj : ∀ i, IsPoly fun x : α → ℕ => x i
  | const : ∀ n : ℤ, IsPoly fun _ : α → ℕ => n
  | sub : ∀ {f g : (α → ℕ) → ℤ}, IsPoly f → IsPoly g → IsPoly fun x => f x - g x
  | mul : ∀ {f g : (α → ℕ) → ℤ}, IsPoly f → IsPoly g → IsPoly fun x => f x * g x
/-
**IsPoly.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPoly.neg {f : (α -> Nat) -> Int} : IsPoly f -> IsPoly (-f)
参数：α -> Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
-/
theorem IsPoly.neg {f : (α → ℕ) → ℤ} : IsPoly f → IsPoly (-f) := by
  rw [← zero_sub]; exact (IsPoly.const 0).sub
/-
**IsPoly.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPoly.add {f g : (α -> Nat) -> Int} (hf : IsPoly f) (hg : IsPoly g) : IsP
oly (f + g)
参数：α -> Nat；hf : IsPoly f；hg : IsPoly g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `IsPoly.neg`：IsPoly.neg {f : (α -> Nat) -> Int} : IsPoly f -> IsPoly (-f)
-/
theorem IsPoly.add {f g : (α → ℕ) → ℤ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (f + g) := by
  rw [← sub_neg_eq_add]; exact hf.sub hg.neg

/-- The type of multivariate integer polynomials -/
/-
**Poly** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Poly (α : Type u)
参数：α : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of multivariate integer polynomials
-/
def Poly (α : Type u) := { f : (α → ℕ) → ℤ // IsPoly f }

namespace Poly

section

/-
**Poly.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `Poly`。
形式化陈述：instFunLike : FunLike (Poly α) (α -> Nat) Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (Poly α) (α → ℕ) ℤ :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The underlying function of a `Poly` is a polynomial -/
/-
**Poly.isPoly** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：∀ {α : Type u_1} (f : Poly α), IsPoly ⇑f
参数：f : Poly α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The underlying function of a `Poly` is a polynomial
-/
protected theorem isPoly (f : Poly α) : IsPoly f := f.2

/-- Extensionality for `Poly α` -/
@[ext]
/-
**Poly.ext** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：ext {f g : Poly α} : (forall x, f x = g x) -> f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g

--- 原说明 ---
Extensionality for `Poly α`
-/
theorem ext {f g : Poly α} : (∀ x, f x = g x) → f = g := DFunLike.ext _ _

/-- The `i`th projection function, `x_i`. -/
/-
**Poly.proj** 是 Mathlib 中的一个定义，位于命名空间 `Poly`。
形式化陈述：proj (i : α) : Poly α
参数：i : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`th projection function, `x_i`.
-/
def proj (i : α) : Poly α := ⟨_, IsPoly.proj i⟩

@[simp]
/-
**Poly.proj_apply** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：proj_apply (i : α) (x) : proj i x = x i
参数：i : α；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem proj_apply (i : α) (x) : proj i x = x i := rfl

/-- The constant function with value `n : ℤ`. -/
/-
**Poly.const** 是 Mathlib 中的一个定义，位于命名空间 `Poly`。
形式化陈述：const (n : Int) : Poly α
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant function with value `n : ℤ`.
-/
def const (n : ℤ) : Poly α := ⟨_, IsPoly.const n⟩

@[simp]
/-
**Poly.const_apply** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：const_apply (n) (x : α -> Nat) : const n x = n
参数：n；x : α -> Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_apply (n) (x : α → ℕ) : const n x = n := rfl
/-
**Poly.** 是 Mathlib 中的一个实例，位于命名空间 `Poly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (Poly α) := ⟨const 0⟩
/-
**Poly.** 是 Mathlib 中的一个实例，位于命名空间 `Poly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (Poly α) := ⟨const 1⟩
/-
**Poly.** 是 Mathlib 中的一个实例，位于命名空间 `Poly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (Poly α) := ⟨fun f => ⟨-f, f.2.neg⟩⟩
/-
**Poly.** 是 Mathlib 中的一个实例，位于命名空间 `Poly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (Poly α) := ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩
/-
**Poly.** 是 Mathlib 中的一个实例，位于命名空间 `Poly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (Poly α) := ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩
/-
**Poly.** 是 Mathlib 中的一个实例，位于命名空间 `Poly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (Poly α) := ⟨fun f g => ⟨f * g, f.2.mul g.2⟩⟩

@[simp]
/-
**Poly.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：coe_zero : ⇑(0 : Poly α) = const 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : Poly α) = const 0 := rfl

@[simp]
/-
**Poly.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：coe_one : ⇑(1 : Poly α) = const 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : Poly α) = const 1 := rfl

@[simp]
/-
**Poly.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：coe_neg (f : Poly α) : ⇑(-f) = -f
参数：f : Poly α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (f : Poly α) : ⇑(-f) = -f := rfl

@[simp]
/-
**Poly.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：coe_add (f g : Poly α) : ⇑(f + g) = f + g
参数：f g : Poly α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (f g : Poly α) : ⇑(f + g) = f + g := rfl

@[simp]
/-
**Poly.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：coe_sub (f g : Poly α) : ⇑(f - g) = f - g
参数：f g : Poly α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (f g : Poly α) : ⇑(f - g) = f - g := rfl

@[simp]
/-
**Poly.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：coe_mul (f g : Poly α) : ⇑(f * g) = f * g
参数：f g : Poly α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (f g : Poly α) : ⇑(f * g) = f * g := rfl

@[simp]
/-
**Poly.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：zero_apply (x) : (0 : Poly α) x = 0
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (x) : (0 : Poly α) x = 0 := rfl

@[simp]
/-
**Poly.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：one_apply (x) : (1 : Poly α) x = 1
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (x) : (1 : Poly α) x = 1 := rfl

@[simp]
/-
**Poly.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：neg_apply (f : Poly α) (x) : (-f) x = -f x
参数：f : Poly α；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply (f : Poly α) (x) : (-f) x = -f x := rfl

@[simp]
/-
**Poly.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：add_apply (f g : Poly α) (x : α -> Nat) : (f + g) x = f x + g x
参数：f g : Poly α；x : α -> Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (f g : Poly α) (x : α → ℕ) : (f + g) x = f x + g x := rfl

@[simp]
/-
**Poly.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：sub_apply (f g : Poly α) (x : α -> Nat) : (f - g) x = f x - g x
参数：f g : Poly α；x : α -> Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (f g : Poly α) (x : α → ℕ) : (f - g) x = f x - g x := rfl

@[simp]
/-
**Poly.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：mul_apply (f g : Poly α) (x : α -> Nat) : (f * g) x = f x * g x
参数：f g : Poly α；x : α -> Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (f g : Poly α) (x : α → ℕ) : (f * g) x = f x * g x := rfl
/-
**Poly.** 是 Mathlib 中的一个实例，位于命名空间 `Poly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) : Inhabited (Poly α) := ⟨0⟩
/-
**Poly.** 是 Mathlib 中的一个实例，位于命名空间 `Poly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (Poly α) where
  nsmul := @nsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩)
  add_zero _ := by ext; simp_rw [add_apply, zero_apply, add_zero]
  zero_add _ := by ext; simp_rw [add_apply, zero_apply, zero_add]
  add_comm _ _ := by ext; simp_rw [add_apply, add_comm]
  add_assoc _ _ _ := by ext; simp_rw [add_apply, ← add_assoc]
  neg_add_cancel _ := by ext; simp_rw [add_apply, neg_apply, neg_add_cancel, zero_apply]
/-
**Poly.** 是 Mathlib 中的一个实例，位于命名空间 `Poly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddGroupWithOne (Poly α) where
  natCast := fun n => Poly.const n
  intCast := Poly.const
/-
**Poly.** 是 Mathlib 中的一个实例，位于命名空间 `Poly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (Poly α) where
  __ := (inferInstance : AddCommGroup (Poly α))
  __ := (inferInstance : AddGroupWithOne (Poly α))
  npow := @npowRec _ ⟨(1 : Poly α)⟩ ⟨(· * ·)⟩
  mul_zero _ := by ext; rw [mul_apply, zero_apply, mul_zero]
  zero_mul _ := by ext; rw [mul_apply, zero_apply, zero_mul]
  mul_one _ := by ext; rw [mul_apply, one_apply, mul_one]
  one_mul _ := by ext; rw [mul_apply, one_apply, one_mul]
  mul_comm _ _ := by ext; simp_rw [mul_apply, mul_comm]
  mul_assoc _ _ _ := by ext; simp_rw [mul_apply, mul_assoc]
  left_distrib _ _ _ := by ext; simp_rw [add_apply, mul_apply]; apply mul_add
  right_distrib _ _ _ := by ext; simp only [add_apply, mul_apply]; apply add_mul
/-
**Poly.induction** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：induction {C : Poly α -> Prop} (H1 : forall i, C (proj i)) (H2 : forall n,
 C (const n)) (H3 : forall f g, C f -> C g -> C (f - g)) (H4 : forall f g, C f -
> C g -> C (f * g)) (f : Poly α) : C f
参数：H1 : forall i, C (proj i)；H2 : forall n, C (const n)；H3 : forall f g, C f -> 
C g -> C (f - g)；H4 : forall f g, C f -> C g -> C (f * g)；f : Poly α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem induction {C : Poly α → Prop} (H1 : ∀ i, C (proj i)) (H2 : ∀ n, C (const n))
    (H3 : ∀ f g, C f → C g → C (f - g)) (H4 : ∀ f g, C f → C g → C (f * g)) (f : Poly α) : C f := by
  obtain ⟨f, pf⟩ := f
  induction pf with
  | proj => apply H1
  | const => apply H2
  | sub _ _ ihf ihg => apply H3 _ _ ihf ihg
  | mul _ _ ihf ihg => apply H4 _ _ ihf ihg

/-- The sum of squares of a list of polynomials. This is relevant for
  Diophantine equations, because it means that a list of equations
  can be encoded as a single equation: `x = 0 ∧ y = 0 ∧ z = 0` is
  equivalent to `x^2 + y^2 + z^2 = 0`. -/
/-
**Poly.sumsq** 是 Mathlib 中的一个定义，位于命名空间 `Poly`。
形式化陈述：{α : Type u_1} → List (Poly α) → Poly α
参数：Poly α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of squares of a list of polynomials. This is relevant for
  Diophantine equations, because it means that a list of equations
  can be encoded as a single equation: `x = 0 ∧ y = 0 ∧ z = 0` is
  equivalent to `x^2 + y^2 + z^2 = 0`.
-/
def sumsq : List (Poly α) → Poly α
  | [] => 0
  | p::ps => p * p + sumsq ps
/-
**Poly.sumsq_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：∀ {α : Type u_1} (x : α → ℕ) (l : List (Poly α)), 0 ≤ (Poly.sumsq l) x
参数：x : α → ℕ；l : List (Poly α)；Poly.sumsq l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sumsq_nonneg (x : α → ℕ) : ∀ l, 0 ≤ sumsq l x
  | [] => le_refl 0
  | p::ps => by
    rw [sumsq]
    exact add_nonneg (mul_self_nonneg _) (sumsq_nonneg _ ps)
/-
**Poly.sumsq_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：∀ {α : Type u_1} (x : α → ℕ) (l : List (Poly α)), (Poly.sumsq l) x = 0 ↔ L
ist.Forall (fun a => a x = 0) l
参数：x : α → ℕ；l : List (Poly α)；Poly.sumsq l；fun a => a x = 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumsq_eq_zero (x) : ∀ l, sumsq l x = 0 ↔ l.Forall fun a : Poly α => a x = 0
  | [] => eq_self_iff_true _
  | p::ps => by simp [sumsq, add_eq_zero_iff_of_nonneg, mul_self_nonneg, sumsq_eq_zero]

end

/-- Map the index set of variables, replacing `x_i` with `x_(f i)`. -/
/-
**Poly.map** 是 Mathlib 中的一个定义，位于命名空间 `Poly`。
形式化陈述：map {α β} (f : α -> β) (g : Poly α) : Poly β
参数：f : α -> β；g : Poly α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map the index set of variables, replacing `x_i` with `x_(f i)`.
-/
def map {α β} (f : α → β) (g : Poly α) : Poly β :=
  ⟨fun v => g <| v ∘ f, Poly.induction (C := fun g => IsPoly (fun v => g (v ∘ f)))
    (fun i => by simpa using IsPoly.proj _) (fun n => by simpa using IsPoly.const _)
    (fun f g pf pg => by simpa using IsPoly.sub pf pg)
    (fun f g pf pg => by simpa using IsPoly.mul pf pg) _⟩

@[simp]
/-
**Poly.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `Poly`。
形式化陈述：map_apply {α β} (f : α -> β) (g : Poly α) (v) : map f g v = g (v ∘ f)
参数：f : α -> β；g : Poly α；v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply {α β} (f : α → β) (g : Poly α) (v) : map f g v = g (v ∘ f) := rfl

end Poly

end Polynomials

/-! ### Diophantine sets -/


/-- A set `S ⊆ ℕ^α` is Diophantine if there exists a polynomial on
  `α ⊕ β` such that `v ∈ S` iff there exists `t : ℕ^β` with `p (v, t) = 0`. -/
/-
**Dioph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Dioph {α : Type u} (S : Set (α -> Nat)) : Prop
参数：S : Set (α -> Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `S ⊆ ℕ^α` is Diophantine if there exists a polynomial on
  `α ⊕ β` such that `v ∈ S` iff there exists `t : ℕ^β` with `p (v, t) = 0`.
-/
def Dioph {α : Type u} (S : Set (α → ℕ)) : Prop :=
  ∃ (β : Type u) (p : Poly (α ⊕ β)), ∀ v, v ∈ S ↔ ∃ t, p (v ⊗ t) = 0

namespace Dioph

section

variable {α β γ : Type u} {S S' : Set (α → ℕ)}

/-
**Dioph.ext** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
参数：d : Dioph S；H : forall v, v in S ↔ v in S'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem ext (d : Dioph S) (H : ∀ v, v ∈ S ↔ v ∈ S') : Dioph S' := by rwa [← Set.ext H]
/-
**Dioph.of_no_dummies** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：of_no_dummies (S : Set (α -> Nat)) (p : Poly α) (h : forall v, v in S ↔ p 
v = 0) : Dioph S
参数：S : Set (α -> Nat)；p : Poly α；h : forall v, v in S ↔ p v = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
-/
theorem of_no_dummies (S : Set (α → ℕ)) (p : Poly α) (h : ∀ v, v ∈ S ↔ p v = 0) : Dioph S :=
  ⟨PEmpty, ⟨p.map inl, fun v => (h v).trans ⟨fun h => ⟨PEmpty.elim, h⟩, fun ⟨_, ht⟩ => ht⟩⟩⟩
/-
**Dioph.inject_dummies_lem** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：inject_dummies_lem (f : β -> γ) (g : γ -> Option β) (inv : forall x, g (f 
x) = some x) (p : Poly (α oplus β)) (v : α -> Nat) : (exists t, p (v otimes t) =
 0) ↔ exists t, p.map (inl otimes inr ∘ f) (v otimes t) = 0
参数：f : β -> γ；g : γ -> Option β；inv : forall x, g (f x) = some x；p : Poly (α opl
us β)；v : α -> Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem inject_dummies_lem (f : β → γ) (g : γ → Option β) (inv : ∀ x, g (f x) = some x)
    (p : Poly (α ⊕ β)) (v : α → ℕ) :
    (∃ t, p (v ⊗ t) = 0) ↔ ∃ t, p.map (inl ⊗ inr ∘ f) (v ⊗ t) = 0 := by
  dsimp; refine ⟨fun t => ?_, fun t => ?_⟩ <;> obtain ⟨t, ht⟩ := t
  · have : (v ⊗ (0 ::ₒ t) ∘ g) ∘ (inl ⊗ inr ∘ f) = v ⊗ t :=
      funext fun s => by rcases s with a | b <;> dsimp [(· ∘ ·)]; try rw [inv]; rfl
    exact ⟨(0 ::ₒ t) ∘ g, by rwa [this]⟩
  · have : v ⊗ t ∘ f = (v ⊗ t) ∘ (inl ⊗ inr ∘ f) := funext fun s => by rcases s with a | b <;> rfl
    exact ⟨t ∘ f, by rwa [this]⟩
/-
**Dioph.inject_dummies** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：inject_dummies (f : β -> γ) (g : γ -> Option β) (inv : forall x, g (f x) =
 some x) (p : Poly (α oplus β)) (h : forall v, v in S ↔ exists t, p (v otimes t)
 = 0) : exists q : Poly (α oplus γ), forall v, v in S ↔ exists t, q (v otimes t)
 = 0
参数：f : β -> γ；g : γ -> Option β；inv : forall x, g (f x) = some x；p : Poly (α opl
us β)；h : forall v, v in S ↔ exists t, p (v otimes t) = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Dioph.inject_dummies_lem`：inject_dummies_lem (f : β -> γ) (g : γ -> Opti
on β) (inv : forall x, g (f x) = some x) (p : Poly (α oplus β)) (v : α -> Nat) :
 (exists t, p …
-/
theorem inject_dummies (f : β → γ) (g : γ → Option β) (inv : ∀ x, g (f x) = some x)
    (p : Poly (α ⊕ β)) (h : ∀ v, v ∈ S ↔ ∃ t, p (v ⊗ t) = 0) :
    ∃ q : Poly (α ⊕ γ), ∀ v, v ∈ S ↔ ∃ t, q (v ⊗ t) = 0 :=
  ⟨p.map (inl ⊗ inr ∘ f), fun v => (h v).trans <| inject_dummies_lem f g inv _ _⟩

variable (β) in
/-
**Dioph.reindex_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：∀ {α : Type u} (β : Type u) {S : Set (α → ℕ)} (f : α → β), Dioph S → Dioph
 {v | v ∘ f ∈ S}
参数：β : Type u；α → ℕ；f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem reindex_dioph (f : α → β) : Dioph S → Dioph {v | v ∘ f ∈ S}
  | ⟨γ, p, pe⟩ => ⟨γ, p.map (inl ∘ f ⊗ inr), fun v =>
      (pe _).trans <|
        exists_congr fun t =>
          suffices v ∘ f ⊗ t = (v ⊗ t) ∘ (inl ∘ f ⊗ inr) by simp [this]
          funext fun s => by rcases s with a | b <;> rfl⟩
/-
**Dioph.DiophList.forall** 是 Mathlib 中的一个定理，位于命名空间 `Dioph.DiophList`。
形式化陈述：∀ {α : Type u} (l : List (Set (α → ℕ))), List.Forall Dioph l → Dioph {v | 
List.Forall (fun S => v ∈ S) l}
参数：l : List (Set (α → ℕ))；fun S => v ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.forall_cons`：∀ {α : Type u} (p : α → Prop) (x : α) (l : List α), Li
st.Forall p (x :: l) ↔ p x ∧ List.Forall p l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `List.Forall.imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (x : α), p x → q x)
 → ∀ {l : List α}, List.Forall p l → List.Forall q l
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Poly.sumsq_eq_zero`：∀ {α : Type u_1} (x : α → ℕ) (l : List (Poly α)), (P
oly.sumsq l) x = 0 ↔ List.Forall (fun a => a x = 0) l
-/
theorem DiophList.forall (l : List (Set <| α → ℕ)) (d : l.Forall Dioph) :
    Dioph {v | l.Forall fun S : Set (α → ℕ) => v ∈ S} := by
  suffices ∃ (β : _) (pl : List (Poly (α ⊕ β))), ∀ v, List.Forall (fun S : Set _ => v ∈ S) l ↔
          ∃ t, List.Forall (fun p : Poly (α ⊕ β) => p (v ⊗ t) = 0) pl
    from
    let ⟨β, pl, h⟩ := this
    ⟨β, Poly.sumsq pl, fun v => (h v).trans <| exists_congr fun t => (Poly.sumsq_eq_zero _ _).symm⟩
  induction l with | nil => exact ⟨ULift Empty, [], fun _ => by simp⟩ | cons S l IH =>
  obtain ⟨⟨β, p, pe⟩, dl⟩ := (List.forall_cons _ _ _).mp d
  exact
    let ⟨γ, pl, ple⟩ := IH dl
    ⟨β ⊕ γ, p.map (inl ⊗ inr ∘ inl)::pl.map fun q => q.map (inl ⊗ inr ∘ inr),
      fun v => by
      simpa using
        Iff.trans (and_congr (pe v) (ple v))
          ⟨fun ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ =>
            ⟨m ⊗ n, by
              rw [show (v ⊗ m ⊗ n) ∘ (inl ⊗ inr ∘ inl) = v ⊗ m from
                    funext fun s => by rcases s with a | b <;> rfl]; exact hm, by
              refine List.Forall.imp (fun q hq => ?_) hn; dsimp [Function.comp_def]
              rw [show
                    (fun x : α ⊕ γ => (v ⊗ m ⊗ n) ((inl ⊗ fun x : γ => inr (inr x)) x)) = v ⊗ n
                    from funext fun s => by rcases s with a | b <;> rfl]; exact hq⟩,
            fun ⟨t, hl, hr⟩ =>
            ⟨⟨t ∘ inl, by
                rwa [show (v ⊗ t) ∘ (inl ⊗ inr ∘ inl) = v ⊗ t ∘ inl from
                    funext fun s => by rcases s with a | b <;> rfl] at hl⟩,
              ⟨t ∘ inr, by
                refine List.Forall.imp (fun q hq => ?_) hr; dsimp [Function.comp_def] at hq
                rwa [show
                    (fun x : α ⊕ γ => (v ⊗ t) ((inl ⊗ fun x : γ => inr (inr x)) x)) =
                      v ⊗ t ∘ inr
                    from funext fun s => by rcases s with a | b <;> rfl] at hq ⟩⟩⟩⟩

/-- Diophantine sets are closed under intersection. -/
/-
**Dioph.inter** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：inter (d : Dioph S) (d' : Dioph S') : Dioph (S inter S')
参数：d : Dioph S；d' : Dioph S'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.DiophList.forall`：∀ {α : Type u} (l : List (Set (α → ℕ))), List.Fo
rall Dioph l → Dioph {v | List.Forall (fun S => v ∈ S) l}

--- 原说明 ---
Diophantine sets are closed under intersection.
-/
theorem inter (d : Dioph S) (d' : Dioph S') : Dioph (S ∩ S') := DiophList.forall [S, S'] ⟨d, d'⟩

/-- Diophantine sets are closed under union. -/
/-
**Dioph.union** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：∀ {α : Type u} {S S' : Set (α → ℕ)}, Dioph S → Dioph S' → Dioph (S ∪ S')
参数：α → ℕ；S ∪ S'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `Dioph.inject_dummies_lem`：inject_dummies_lem (f : β -> γ) (g : γ -> Opti
on β) (inv : forall x, g (f x) = some x) (p : Poly (α oplus β)) (v : α -> Nat) :
 (exists t, p …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `exists_or`：∀ {α : Sort u_1} {p q : α → Prop}, (∃ x, p x ∨ q x) ↔ (∃ x, p
 x) ∨ ∃ x, q x
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α

--- 原说明 ---
Diophantine sets are closed under union.
-/
theorem union : ∀ (_ : Dioph S) (_ : Dioph S'), Dioph (S ∪ S')
  | ⟨β, p, pe⟩, ⟨γ, q, qe⟩ =>
    ⟨β ⊕ γ, p.map (inl ⊗ inr ∘ inl) * q.map (inl ⊗ inr ∘ inr), fun v => by
      refine
        Iff.trans (or_congr ((pe v).trans ?_) ((qe v).trans ?_))
          (exists_or.symm.trans
            (exists_congr fun t =>
              (@mul_eq_zero _ _ _ (p ((v ⊗ t) ∘ (inl ⊗ inr ∘ inl)))
                  (q ((v ⊗ t) ∘ (inl ⊗ inr ∘ inr)))).symm))
      · -- Porting note: putting everything on the same line fails
        refine inject_dummies_lem _ (some ⊗ fun _ => none) ?_ _ _
        exact fun _ => by simp only [elim_inl]
      · -- Porting note: putting everything on the same line fails
        refine inject_dummies_lem _ ((fun _ => none) ⊗ some) ?_ _ _
        exact fun _ => by simp only [elim_inr]⟩

/-- A partial function is Diophantine if its graph is Diophantine. -/
/-
**Dioph.DiophPFun** 是 Mathlib 中的一个定义，位于命名空间 `Dioph`。
形式化陈述：DiophPFun (f : (α -> Nat) ->. Nat) : Prop
参数：f : (α -> Nat) ->. Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial function is Diophantine if its graph is Diophantine.
-/
def DiophPFun (f : (α → ℕ) →. ℕ) : Prop :=
  Dioph {v : Option α → ℕ | (v ∘ some, v none) ∈ f.graph}

/-- A function is Diophantine if its graph is Diophantine. -/
/-
**Dioph.DiophFn** 是 Mathlib 中的一个定义，位于命名空间 `Dioph`。
形式化陈述：DiophFn (f : (α -> Nat) -> Nat) : Prop
参数：f : (α -> Nat) -> Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is Diophantine if its graph is Diophantine.
-/
def DiophFn (f : (α → ℕ) → ℕ) : Prop :=
  Dioph {v : Option α → ℕ | f (v ∘ some) = v none}
/-
**Dioph.reindex_diophFn** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：reindex_diophFn {f : (α -> Nat) -> Nat} (g : α -> β) (d : DiophFn f) : Dio
phFn fun v => f (v ∘ g)
参数：α -> Nat；g : α -> β；d : DiophFn f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.reindex_dioph`：∀ {α : Type u} (β : Type u) {S : Set (α → ℕ)} (f : 
α → β), Dioph S → Dioph {v | v ∘ f ∈ S}
-/
theorem reindex_diophFn {f : (α → ℕ) → ℕ} (g : α → β) (d : DiophFn f) :
    DiophFn fun v => f (v ∘ g) := by convert! reindex_dioph (Option β) (Option.map g) d
/-
**Dioph.ex_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：ex_dioph {S : Set (α oplus β -> Nat)} : Dioph S -> Dioph {v | exists x, v 
otimes x in S} | ⟨γ, p, pe⟩ => ⟨β oplus γ, p.map ((inl otimes inr ∘ inl) otimes 
inr ∘ inr), fun v => ⟨fun ⟨x, hx⟩ => let ⟨t, ht⟩
参数：α oplus β -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem ex_dioph {S : Set (α ⊕ β → ℕ)} : Dioph S → Dioph {v | ∃ x, v ⊗ x ∈ S}
  | ⟨γ, p, pe⟩ =>
    ⟨β ⊕ γ, p.map ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr), fun v =>
      ⟨fun ⟨x, hx⟩ =>
        let ⟨t, ht⟩ := (pe _).1 hx
        ⟨x ⊗ t, by
          simp only [Poly.map_apply]
          rw [show (v ⊗ x ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr) = (v ⊗ x) ⊗ t from
            funext fun s => by rcases s with a | b <;> try { cases a <;> rfl }; rfl]
          exact ht⟩,
        fun ⟨t, ht⟩ =>
        ⟨t ∘ inl,
          (pe _).2
            ⟨t ∘ inr, by
              simp only [Poly.map_apply] at ht
              rwa [show (v ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr) = (v ⊗ t ∘ inl) ⊗ t ∘ inr from
                funext fun s => by rcases s with a | b <;> try { cases a <;> rfl }; rfl] at ht⟩⟩⟩⟩
/-
**Dioph.ex1_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：ex1_dioph {S : Set (Option α -> Nat)} : Dioph S -> Dioph {v | exists x, x 
::ₒ v in S} | ⟨β, p, pe⟩ => ⟨Option β, p.map (inr none ::ₒ inl otimes inr ∘ some
), fun v => ⟨fun ⟨x, hx⟩ => let ⟨t, ht⟩
参数：Option α -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem ex1_dioph {S : Set (Option α → ℕ)} : Dioph S → Dioph {v | ∃ x, x ::ₒ v ∈ S}
  | ⟨β, p, pe⟩ =>
    ⟨Option β, p.map (inr none ::ₒ inl ⊗ inr ∘ some), fun v =>
      ⟨fun ⟨x, hx⟩ =>
        let ⟨t, ht⟩ := (pe _).1 hx
        ⟨x ::ₒ t, by
          simp only [Poly.map_apply]
          rw [show (v ⊗ x ::ₒ t) ∘ (inr none ::ₒ inl ⊗ inr ∘ some) = x ::ₒ v ⊗ t from
            funext fun s => by rcases s with a | b <;> try { cases a <;> rfl}; rfl]
          exact ht⟩,
        fun ⟨t, ht⟩ =>
        ⟨t none,
          (pe _).2
            ⟨t ∘ some, by
              simp only [Poly.map_apply] at ht
              rwa [show (v ⊗ t) ∘ (inr none ::ₒ inl ⊗ inr ∘ some) = t none ::ₒ v ⊗ t ∘ some from
                funext fun s => by rcases s with a | b <;> try { cases a <;> rfl }; rfl] at ht ⟩⟩⟩⟩
/-
**Dioph.dom_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：dom_dioph {f : (α -> Nat) ->. Nat} (d : DiophPFun f) : Dioph f.Dom
参数：α -> Nat；d : DiophPFun f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `PFun.dom_iff_graph`：dom_iff_graph (f : α ->. β) (x : α) : x in f.Dom ↔ e
xists y, (x, y) in f.graph
· 使用定理 `Dioph.ex1_dioph`：ex1_dioph {S : Set (Option α -> Nat)} : Dioph S -> Diop
h {v | exists x, x ::ₒ v in S} | ⟨β, p, pe⟩ => ⟨Option β, p.map (inr none ::ₒ in
l oti…
-/
theorem dom_dioph {f : (α → ℕ) →. ℕ} (d : DiophPFun f) : Dioph f.Dom :=
  cast (congr_arg Dioph <| Set.ext fun _ => (PFun.dom_iff_graph _ _).symm) (ex1_dioph d)
/-
**Dioph.diophFn_iff_pFun** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：diophFn_iff_pFun (f : (α -> Nat) -> Nat) : DiophFn f = @DiophPFun α f
参数：f : (α -> Nat) -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `PFun.lift_graph`：lift_graph {f : α -> β} {a b} : (a, b) in (f : α ->. β)
.graph ↔ f a = b
-/
theorem diophFn_iff_pFun (f : (α → ℕ) → ℕ) : DiophFn f = @DiophPFun α f := by
  refine congr_arg Dioph (Set.ext fun v => ?_); exact PFun.lift_graph.symm
/-
**Dioph.abs_poly_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：abs_poly_dioph (p : Poly α) : DiophFn fun v => (p v).natAbs
参数：p : Poly α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.of_no_dummies`：of_no_dummies (S : Set (α -> Nat)) (p : Poly α) (h 
: forall v, v in S ↔ p v = 0) : Dioph S
· 使用定理 `Int.natAbs_eq_iff_mul_eq_zero`：∀ {a : ℤ} {n : ℕ}, a.natAbs = n ↔ (a - ↑n
) * (a + ↑n) = 0
-/
theorem abs_poly_dioph (p : Poly α) : DiophFn fun v => (p v).natAbs :=
  of_no_dummies _ ((p.map some - Poly.proj none) * (p.map some + Poly.proj none))
    fun v => (by dsimp; exact Int.natAbs_eq_iff_mul_eq_zero)
/-
**Dioph.proj_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：proj_dioph (i : α) : DiophFn fun v => v i
参数：i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.abs_poly_dioph`：abs_poly_dioph (p : Poly α) : DiophFn fun v => (p 
v).natAbs
-/
theorem proj_dioph (i : α) : DiophFn fun v => v i :=
  abs_poly_dioph (Poly.proj i)
/-
**Dioph.diophPFun_comp1** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：diophPFun_comp1 {S : Set (Option α -> Nat)} (d : Dioph S) {f} (df : DiophP
Fun f) : Dioph {v : α -> Nat | exists h : v in f.Dom, f.fn v h ::ₒ v in S}
参数：Option α -> Nat；d : Dioph S；df : DiophPFun f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.ext`：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `Dioph.ex1_dioph`：ex1_dioph {S : Set (Option α -> Nat)} : Dioph S -> Diop
h {v | exists x, x ::ₒ v in S} | ⟨β, p, pe⟩ => ⟨Option β, p.map (inr none ::ₒ in
l oti…
· 使用定理 `Dioph.inter`：inter (d : Dioph S) (d' : Dioph S') : Dioph (S inter S')
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PFun.fn.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α →. β) (a : α), f.fn
 a = (f a).get
-/
theorem diophPFun_comp1 {S : Set (Option α → ℕ)} (d : Dioph S) {f} (df : DiophPFun f) :
    Dioph {v : α → ℕ | ∃ h : v ∈ f.Dom, f.fn v h ::ₒ v ∈ S} :=
  ext (ex1_dioph (d.inter df)) fun v =>
    ⟨fun ⟨x, hS, (h : Exists _)⟩ => by
      rw [show (x ::ₒ v) ∘ some = v from funext fun s => rfl] at h
      obtain ⟨hf, h⟩ := h; refine ⟨hf, ?_⟩; rw [PFun.fn, h]; exact hS,
    fun ⟨x, hS⟩ =>
      ⟨f.fn v x, hS, show Exists _ by
        rw [show (f.fn v x ::ₒ v) ∘ some = v from funext fun s => rfl]; exact ⟨x, rfl⟩⟩⟩
/-
**Dioph.diophFn_comp1** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：diophFn_comp1 {S : Set (Option α -> Nat)} (d : Dioph S) {f : (α -> Nat) ->
 Nat} (df : DiophFn f) : Dioph {v | f v ::ₒ v in S}
参数：Option α -> Nat；d : Dioph S；α -> Nat；df : DiophFn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.ext`：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `Dioph.diophPFun_comp1`：diophPFun_comp1 {S : Set (Option α -> Nat)} (d : 
Dioph S) {f} (df : DiophPFun f) : Dioph {v : α -> Nat | exists h : v in f.Dom, f
.fn v h ::ₒ…
· 使用定理 `Dioph.diophFn_iff_pFun`：diophFn_iff_pFun (f : (α -> Nat) -> Nat) : Dioph
Fn f = @DiophPFun α f
· 使用定理 `trivial`：True
-/
theorem diophFn_comp1 {S : Set (Option α → ℕ)} (d : Dioph S) {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    Dioph {v | f v ::ₒ v ∈ S} :=
  ext (diophPFun_comp1 d <| cast (diophFn_iff_pFun f) df)
    fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨trivial, h⟩⟩

end

section

variable {α : Type} {n : ℕ}

open Vector3

open scoped Vector3

/-
**Dioph.diophFn_vec_comp1** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：diophFn_vec_comp1 {S : Set (Vector3 Nat (succ n))} (d : Dioph S) {f : Vect
or3 Nat n -> Nat} (df : DiophFn f) : Dioph {v : Vector3 Nat n | (f v :: v) in S}
参数：Vector3 Nat (succ n)；d : Dioph S；df : DiophFn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.ext`：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `Dioph.diophFn_comp1`：diophFn_comp1 {S : Set (Option α -> Nat)} (d : Diop
h S) {f : (α -> Nat) -> Nat} (df : DiophFn f) : Dioph {v | f v ::ₒ v in S}
· 使用定理 `Dioph.reindex_dioph`：∀ {α : Type u} (β : Type u) {S : Set (α → ℕ)} (f : 
α → β), Dioph S → Dioph {v | v ∘ f ∈ S}
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem diophFn_vec_comp1 {S : Set (Vector3 ℕ (succ n))} (d : Dioph S) {f : Vector3 ℕ n → ℕ}
    (df : DiophFn f) : Dioph {v : Vector3 ℕ n | (f v :: v) ∈ S} :=
  Dioph.ext (diophFn_comp1 (reindex_dioph _ (none :: some) d) df) (fun v => by
    dsimp
    -- TODO: `apply iff_of_eq` is required here, even though `congr!` works on iff below.
    apply iff_of_eq
    congr 1
    ext x; cases x <;> rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Deleting the first component preserves the Diophantine property. -/
/-
**Dioph.vec_ex1_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：vec_ex1_dioph (n) {S : Set (Vector3 Nat (succ n))} (d : Dioph S) : Dioph {
v : Fin2 n -> Nat | exists x, (x :: v) in S}
参数：n；Vector3 Nat (succ n)；d : Dioph S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.ext`：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `Dioph.ex1_dioph`：ex1_dioph {S : Set (Option α -> Nat)} : Dioph S -> Diop
h {v | exists x, x ::ₒ v in S} | ⟨β, p, pe⟩ => ⟨Option β, p.map (inr none ::ₒ in
l oti…
· 使用定理 `Dioph.reindex_dioph`：∀ {α : Type u} (β : Type u) {S : Set (α → ℕ)} (f : 
α → β), Dioph S → Dioph {v | v ∘ f ∈ S}
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Deleting the first component preserves the Diophantine property.
-/
theorem vec_ex1_dioph (n) {S : Set (Vector3 ℕ (succ n))} (d : Dioph S) :
    Dioph {v : Fin2 n → ℕ | ∃ x, (x :: v) ∈ S} :=
  ext (ex1_dioph <| reindex_dioph _ (none :: some) d) fun v =>
    exists_congr fun x => by
      dsimp
      rw [show Option.elim' x v ∘ cons none some = x :: v from
          funext fun s => by rcases s with a | b <;> rfl]
/-
**Dioph.diophFn_vec** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：diophFn_vec (f : Vector3 Nat n -> Nat) : DiophFn f ↔ Dioph {v | f (v ∘ fs)
 = v fz}
参数：f : Vector3 Nat n -> Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.reindex_dioph`：∀ {α : Type u} (β : Type u) {S : Set (α → ℕ)} (f : 
α → β), Dioph S → Dioph {v | v ∘ f ∈ S}
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
-/
theorem diophFn_vec (f : Vector3 ℕ n → ℕ) : DiophFn f ↔ Dioph {v | f (v ∘ fs) = v fz} :=
  ⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none::some)⟩
/-
**Dioph.diophPFun_vec** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：diophPFun_vec (f : Vector3 Nat n ->. Nat) : DiophPFun f ↔ Dioph {v | (v ∘ 
fs, v fz) in f.graph}
参数：f : Vector3 Nat n ->. Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.reindex_dioph`：∀ {α : Type u} (β : Type u) {S : Set (α → ℕ)} (f : 
α → β), Dioph S → Dioph {v | v ∘ f ∈ S}
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
-/
theorem diophPFun_vec (f : Vector3 ℕ n →. ℕ) : DiophPFun f ↔ Dioph {v | (v ∘ fs, v fz) ∈ f.graph} :=
  ⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none::some)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Dioph.diophFn_compn** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：diophFn_compn : forall {n} {S : Set (α oplus (Fin2 n) -> Nat)} (_ : Dioph 
S) {f : Vector3 ((α -> Nat) -> Nat) n} (_ : VectorAllP DiophFn f), Dioph {v : α 
-> Nat | (v otimes fun i => f i v) in S} | 0, S, d, f => fun _ => ext (reindex_d
ioph _ (id otimes Fin2.elim0) d) fun v => by dsimp -- TODO: `congr! 1; ext` shou
ld be equivalent to `congr! 1 with x` but that does not work. congr! 1 ext x; ob
tain _ | _ | _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diophFn_compn :
    ∀ {n} {S : Set (α ⊕ (Fin2 n) → ℕ)} (_ : Dioph S) {f : Vector3 ((α → ℕ) → ℕ) n}
      (_ : VectorAllP DiophFn f), Dioph {v : α → ℕ | (v ⊗ fun i => f i v) ∈ S}
  | 0, S, d, f => fun _ =>
    ext (reindex_dioph _ (id ⊗ Fin2.elim0) d) fun v => by
      dsimp
      -- TODO: `congr! 1; ext` should be equivalent to `congr! 1 with x` but that does not work.
      congr! 1
      ext x; obtain _ | _ | _ := x; rfl
  | succ n, S, d, f =>
    f.consElim fun f fl => by
        simp only [vectorAllP_cons, and_imp]
        exact fun df dfl =>
          have : Dioph {v | (v ∘ inl ⊗ f (v ∘ inl)::v ∘ inr) ∈ S} :=
            ext (diophFn_comp1 (reindex_dioph _ (some ∘ inl ⊗ none :: some ∘ inr) d) <|
                reindex_diophFn inl df)
              fun v => by
                dsimp
                -- TODO: `congr! 1; ext` should be equivalent to `congr! 1 with x`
                -- but that does not work.
                congr! 1
                ext x; obtain _ | _ | _ := x <;> rfl
          have : Dioph {v | (v ⊗ f v::fun i : Fin2 n => fl i v) ∈ S} :=
            @diophFn_compn n {v | (v ∘ inl ⊗ f (v ∘ inl) :: v ∘ inr) ∈ S} this _ dfl
          ext this fun v => by
            dsimp
            congr! 3 with x
            obtain _ | _ | _ := x <;> rfl
/-
**Dioph.dioph_comp** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：dioph_comp {S : Set (Vector3 Nat n)} (d : Dioph S) (f : Vector3 ((α -> Nat
) -> Nat) n) (df : VectorAllP DiophFn f) : Dioph {v | (fun i => f i v) in S}
参数：Vector3 Nat n；d : Dioph S；f : Vector3 ((α -> Nat) -> Nat) n；df : VectorAllP D
iophFn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.diophFn_compn`：diophFn_compn : forall {n} {S : Set (α oplus (Fin2 
n) -> Nat)} (_ : Dioph S) {f : Vector3 ((α -> Nat) -> Nat) n} (_ : VectorAllP Di
ophFn f),…
· 使用定理 `Dioph.reindex_dioph`：∀ {α : Type u} (β : Type u) {S : Set (α → ℕ)} (f : 
α → β), Dioph S → Dioph {v | v ∘ f ∈ S}
-/
theorem dioph_comp {S : Set (Vector3 ℕ n)} (d : Dioph S) (f : Vector3 ((α → ℕ) → ℕ) n)
    (df : VectorAllP DiophFn f) : Dioph {v | (fun i => f i v) ∈ S} :=
  diophFn_compn (reindex_dioph _ inr d) df

set_option backward.isDefEq.respectTransparency false in
/-
**Dioph.diophFn_comp** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：diophFn_comp {f : Vector3 Nat n -> Nat} (df : DiophFn f) (g : Vector3 ((α 
-> Nat) -> Nat) n) (dg : VectorAllP DiophFn g) : DiophFn fun v => f fun i => g i
 v
参数：df : DiophFn f；g : Vector3 ((α -> Nat) -> Nat) n；dg : VectorAllP DiophFn g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.dioph_comp`：dioph_comp {S : Set (Vector3 Nat n)} (d : Dioph S) (f 
: Vector3 ((α -> Nat) -> Nat) n) (df : VectorAllP DiophFn f) : Dioph {v | (fun i
 => f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Dioph.diophFn_vec`：diophFn_vec (f : Vector3 Nat n -> Nat) : DiophFn f ↔ 
Dioph {v | f (v ∘ fs) = v fz}
· 使用定理 `Dioph.proj_dioph`：proj_dioph (i : α) : DiophFn fun v => v i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vectorAllP_iff_forall`：vectorAllP_iff_forall (p : α -> Prop) (v : Vector
3 α n) : VectorAllP p v ↔ forall i, p (v i)
· 使用定理 `Dioph.reindex_diophFn`：reindex_diophFn {f : (α -> Nat) -> Nat} (g : α ->
 β) (d : DiophFn f) : DiophFn fun v => f (v ∘ g)
-/
theorem diophFn_comp {f : Vector3 ℕ n → ℕ} (df : DiophFn f) (g : Vector3 ((α → ℕ) → ℕ) n)
    (dg : VectorAllP DiophFn g) : DiophFn fun v => f fun i => g i v :=
  dioph_comp ((diophFn_vec _).1 df) ((fun v ↦ v none) :: fun i v ↦ g i (v ∘ some)) <| by
    simp only [vectorAllP_cons]
    exact ⟨proj_dioph none, (vectorAllP_iff_forall _ _).2 fun i =>
          reindex_diophFn _ <| (vectorAllP_iff_forall _ _).1 dg _⟩

@[inherit_doc]
scoped notation:35 x " D∧ " y => Dioph.inter x y

@[inherit_doc]
scoped notation:35 x " D∨ " y => Dioph.union x y

@[inherit_doc]
scoped notation:30 "D∃" => Dioph.vec_ex1_dioph

/-- Local abbreviation for `Fin2.ofNat'` -/
scoped prefix:arg "&" => Fin2.ofNat'

/-
**Dioph.proj_dioph_of_nat** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：proj_dioph_of_nat {n : Nat} (m : Nat) [IsLT m n] : DiophFn fun v : Vector3
 Nat n => v &m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.proj_dioph`：proj_dioph (i : α) : DiophFn fun v => v i
-/
theorem proj_dioph_of_nat {n : ℕ} (m : ℕ) [IsLT m n] : DiophFn fun v : Vector3 ℕ n => v &m :=
  proj_dioph &m

/-- Projection preserves Diophantine functions. -/
scoped prefix:100 "D&" => Dioph.proj_dioph_of_nat

/-
**Dioph.const_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：const_dioph (n : Nat) : DiophFn (const (α -> Nat) n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.abs_poly_dioph`：abs_poly_dioph (p : Poly α) : DiophFn fun v => (p 
v).natAbs
-/
theorem const_dioph (n : ℕ) : DiophFn (const (α → ℕ) n) :=
  abs_poly_dioph (Poly.const n)

/-- The constant function is Diophantine. -/
scoped prefix:100 "D." => Dioph.const_dioph

section
variable {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g)
include df dg

/-
**Dioph.dioph_comp2** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：dioph_comp2 {S : Nat -> Nat -> Prop} (d : Dioph {v : Vector3 Nat 2 | S (v 
&0) (v &1)}) : Dioph {v | S (f v) (g v)}
参数：d : Dioph {v : Vector3 Nat 2 | S (v &0) (v &1)}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ
· 使用定理 `Dioph.dioph_comp`：dioph_comp {S : Set (Vector3 Nat n)} (d : Dioph S) (f 
: Vector3 ((α -> Nat) -> Nat) n) (df : VectorAllP DiophFn f) : Dioph {v | (fun i
 => f …
-/
theorem dioph_comp2 {S : ℕ → ℕ → Prop} (d : Dioph {v : Vector3 ℕ 2 | S (v &0) (v &1)}) :
    Dioph {v | S (f v) (g v)} := dioph_comp d [f, g] ⟨df, dg⟩
/-
**Dioph.diophFn_comp2** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：diophFn_comp2 {h : Nat -> Nat -> Nat} (d : DiophFn fun v : Vector3 Nat 2 =
> h (v &0) (v &1)) : DiophFn fun v => h (f v) (g v)
参数：d : DiophFn fun v : Vector3 Nat 2 => h (v &0) (v &1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ
· 使用定理 `Dioph.diophFn_comp`：diophFn_comp {f : Vector3 Nat n -> Nat} (df : DiophF
n f) (g : Vector3 ((α -> Nat) -> Nat) n) (dg : VectorAllP DiophFn g) : DiophFn f
un v => …
-/
theorem diophFn_comp2 {h : ℕ → ℕ → ℕ} (d : DiophFn fun v : Vector3 ℕ 2 => h (v &0) (v &1)) :
    DiophFn fun v => h (f v) (g v) := diophFn_comp d [f, g] ⟨df, dg⟩

/-- The set of places where two Diophantine functions are equal is Diophantine. -/
/-
**Dioph.eq_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：eq_dioph : Dioph {v | f v = g v}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.dioph_comp2`：dioph_comp2 {S : Nat -> Nat -> Prop} (d : Dioph {v : 
Vector3 Nat 2 | S (v &0) (v &1)}) : Dioph {v | S (f v) (g v)}
· 使用定理 `Dioph.of_no_dummies`：of_no_dummies (S : Set (α -> Nat)) (p : Poly α) (h 
: forall v, v in S ↔ p v = 0) : Dioph S
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Int.ofNat_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `sub_eq_zero_of_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a = b
 → a - b = 0
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b

--- 原说明 ---
The set of places where two Diophantine functions are equal is Diophantine.
-/
theorem eq_dioph : Dioph {v | f v = g v} :=
  dioph_comp2 df dg <|
    of_no_dummies _ (Poly.proj &0 - Poly.proj &1) fun v => by
      exact Int.ofNat_inj.symm.trans ⟨@sub_eq_zero_of_eq ℤ _ (v &0) (v &1), eq_of_sub_eq_zero⟩

@[inherit_doc]
scoped infixl:50 " D= " => Dioph.eq_dioph

/-- Diophantine functions are closed under addition. -/
/-
**Dioph.add_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：add_dioph : DiophFn fun v => f v + g v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.diophFn_comp2`：diophFn_comp2 {h : Nat -> Nat -> Nat} (d : DiophFn 
fun v : Vector3 Nat 2 => h (v &0) (v &1)) : DiophFn fun v => h (f v) (g v)
· 使用定理 `Dioph.abs_poly_dioph`：abs_poly_dioph (p : Poly α) : DiophFn fun v => (p 
v).natAbs
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ

--- 原说明 ---
Diophantine functions are closed under addition.
-/
theorem add_dioph : DiophFn fun v => f v + g v :=
  diophFn_comp2 df dg <| abs_poly_dioph (@Poly.proj (Fin2 2) &0 + @Poly.proj (Fin2 2) &1)

@[inherit_doc]
scoped infixl:80 " D+ " => Dioph.add_dioph

/-- Diophantine functions are closed under multiplication. -/
/-
**Dioph.mul_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：mul_dioph : DiophFn fun v => f v * g v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.diophFn_comp2`：diophFn_comp2 {h : Nat -> Nat -> Nat} (d : DiophFn 
fun v : Vector3 Nat 2 => h (v &0) (v &1)) : DiophFn fun v => h (f v) (g v)
· 使用定理 `Dioph.abs_poly_dioph`：abs_poly_dioph (p : Poly α) : DiophFn fun v => (p 
v).natAbs
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ

--- 原说明 ---
Diophantine functions are closed under multiplication.
-/
theorem mul_dioph : DiophFn fun v => f v * g v :=
  diophFn_comp2 df dg <| abs_poly_dioph (@Poly.proj (Fin2 2) &0 * @Poly.proj (Fin2 2) &1)

@[inherit_doc]
scoped infixl:90 " D* " => Dioph.mul_dioph

/-- The set of places where one Diophantine function is at most another is Diophantine. -/
/-
**Dioph.le_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：le_dioph : Dioph {v | f v <= g v}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.dioph_comp2`：dioph_comp2 {S : Nat -> Nat -> Prop} (d : Dioph {v : 
Vector3 Nat 2 | S (v &0) (v &1)}) : Dioph {v | S (f v) (g v)}
· 使用定理 `Dioph.ext`：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Dioph.vec_ex1_dioph`：vec_ex1_dioph (n) {S : Set (Vector3 Nat (succ n))} 
(d : Dioph S) : Dioph {v : Fin2 n -> Nat | exists x, (x :: v) in S}
· 使用定理 `Dioph.eq_dioph`：eq_dioph : Dioph {v | f v = g v}
· 使用定理 `Dioph.add_dioph`：add_dioph : DiophFn fun v => f v + g v
· 使用定理 `Dioph.proj_dioph_of_nat`：proj_dioph_of_nat {n : Nat} (m : Nat) [IsLT m n
] : DiophFn fun v : Vector3 Nat n => v &m
· 使用定理 `Nat.le.intro`：∀ {n m k : ℕ}, n + k = m → n ≤ m
· 使用定理 `Nat.le.dest`：∀ {n m : ℕ}, n ≤ m → ∃ k, n + k = m

--- 原说明 ---
The set of places where one Diophantine function is at most another is Diophanti
ne.
-/
theorem le_dioph : Dioph {v | f v ≤ g v} :=
  dioph_comp2 df dg <|
    ext ((D∃) 2 <| D&1 D+ D&0 D= D&2) fun _ => ⟨fun ⟨_, hx⟩ => le.intro hx, le.dest⟩

@[inherit_doc]
scoped infixl:50 " D≤ " => Dioph.le_dioph

/-- The set of places where one Diophantine function is less than another is Diophantine. -/
/-
**Dioph.lt_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：lt_dioph : Dioph {v | f v < g v}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.le_dioph`：le_dioph : Dioph {v | f v <= g v}
· 使用定理 `Dioph.add_dioph`：add_dioph : DiophFn fun v => f v + g v
· 使用定理 `Dioph.const_dioph`：const_dioph (n : Nat) : DiophFn (const (α -> Nat) n)

--- 原说明 ---
The set of places where one Diophantine function is less than another is Diophan
tine.
-/
theorem lt_dioph : Dioph {v | f v < g v} := df D+ D.1 D≤ dg

@[inherit_doc]
scoped infixl:50 " D< " => Dioph.lt_dioph

/-- The set of places where two Diophantine functions are unequal is Diophantine. -/
/-
**Dioph.ne_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：ne_dioph : Dioph {v | f v != g v}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.ext`：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
· 使用定理 `Dioph.union`：∀ {α : Type u} {S S' : Set (α → ℕ)}, Dioph S → Dioph S' → D
ioph (S ∪ S')
· 使用定理 `Dioph.lt_dioph`：lt_dioph : Dioph {v | f v < g v}
· 使用定理 `lt_or_lt_iff_ne`：lt_or_lt_iff_ne : a < b ∨ b < a ↔ a != b

--- 原说明 ---
The set of places where two Diophantine functions are unequal is Diophantine.
-/
theorem ne_dioph : Dioph {v | f v ≠ g v} :=
  ext (df D< dg D∨ dg D< df) fun v => by dsimp; exact lt_or_lt_iff_ne (α := ℕ)

@[inherit_doc]
scoped infixl:50 " D≠ " => Dioph.ne_dioph

/-- Diophantine functions are closed under subtraction. -/
/-
**Dioph.sub_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：sub_dioph : DiophFn fun v => f v - g v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.diophFn_comp2`：diophFn_comp2 {h : Nat -> Nat -> Nat} (d : DiophFn 
fun v : Vector3 Nat 2 => h (v &0) (v &1)) : DiophFn fun v => h (f v) (g v)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ
· 使用定理 `Dioph.diophFn_vec`：diophFn_vec (f : Vector3 Nat n -> Nat) : DiophFn f ↔ 
Dioph {v | f (v ∘ fs) = v fz}
· 使用定理 `Dioph.ext`：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
· 使用定理 `Dioph.union`：∀ {α : Type u} {S S' : Set (α → ℕ)}, Dioph S → Dioph S' → D
ioph (S ∪ S')
· 使用定理 `Dioph.eq_dioph`：eq_dioph : Dioph {v | f v = g v}
· 使用定理 `Dioph.proj_dioph_of_nat`：proj_dioph_of_nat {n : Nat} (m : Nat) [IsLT m n
] : DiophFn fun v : Vector3 Nat n => v &m
· 使用定理 `Dioph.add_dioph`：add_dioph : DiophFn fun v => f v + g v
· 使用定理 `Dioph.inter`：inter (d : Dioph S) (d' : Dioph S') : Dioph (S inter S')
· 使用定理 `Dioph.le_dioph`：le_dioph : Dioph {v | f v <= g v}
· 使用定理 `Dioph.const_dioph`：const_dioph (n : Nat) : DiophFn (const (α -> Nat) n)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `vectorAll_iff_forall`：∀ {α : Type u_1} {n : ℕ} (f : Vector3 α n → Prop),
 VectorAll n f ↔ ∀ (v : Vector3 α n), f v

--- 原说明 ---
Diophantine functions are closed under subtraction.
-/
theorem sub_dioph : DiophFn fun v ↦ f v - g v :=
  diophFn_comp2 df dg <|
    (diophFn_vec _).2 <|
      ext (D&1 D= D&0 D+ D&2 D∨ D&1 D≤ D&2 D∧ D&0 D= D.0) <|
        (vectorAll_iff_forall _).1 fun x y z ↦
          show y = x + z ∨ y ≤ z ∧ x = 0 ↔ y - z = x by grind

@[inherit_doc]
scoped infixl:80 " D- " => Dioph.sub_dioph

/-- The set of places where one Diophantine function divides another is Diophantine. -/
/-
**Dioph.dvd_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：dvd_dioph : Dioph {v | f v ∣ g v}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.dioph_comp`：dioph_comp {S : Set (Vector3 Nat n)} (d : Dioph S) (f 
: Vector3 ((α -> Nat) -> Nat) n) (df : VectorAllP DiophFn f) : Dioph {v | (fun i
 => f …
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Dioph.vec_ex1_dioph`：vec_ex1_dioph (n) {S : Set (Vector3 Nat (succ n))} 
(d : Dioph S) : Dioph {v : Fin2 n -> Nat | exists x, (x :: v) in S}
· 使用定理 `Dioph.eq_dioph`：eq_dioph : Dioph {v | f v = g v}
· 使用定理 `Dioph.proj_dioph_of_nat`：proj_dioph_of_nat {n : Nat} (m : Nat) [IsLT m n
] : DiophFn fun v : Vector3 Nat n => v &m
· 使用定理 `Dioph.mul_dioph`：mul_dioph : DiophFn fun v => f v * g v

--- 原说明 ---
The set of places where one Diophantine function divides another is Diophantine.
-/
theorem dvd_dioph : Dioph {v | f v ∣ g v} :=
  dioph_comp ((D∃) 2 <| D&2 D= D&1 D* D&0) [f, g] ⟨df, dg⟩

@[inherit_doc]
scoped infixl:50 " D∣ " => Dioph.dvd_dioph

/-- Diophantine functions are closed under the modulo operation. -/
/-
**Dioph.mod_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：mod_dioph : DiophFn fun v => f v % g v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Dioph.inter`：inter (d : Dioph S) (d' : Dioph S') : Dioph (S inter S')
· 使用定理 `Dioph.union`：∀ {α : Type u} {S S' : Set (α → ℕ)}, Dioph S → Dioph S' → D
ioph (S ∪ S')
· 使用定理 `Dioph.eq_dioph`：eq_dioph : Dioph {v | f v = g v}
· 使用定理 `Dioph.proj_dioph_of_nat`：proj_dioph_of_nat {n : Nat} (m : Nat) [IsLT m n
] : DiophFn fun v : Vector3 Nat n => v &m
· 使用定理 `Dioph.const_dioph`：const_dioph (n : Nat) : DiophFn (const (α -> Nat) n)
· 使用定理 `Dioph.lt_dioph`：lt_dioph : Dioph {v | f v < g v}
· 使用定理 `Dioph.vec_ex1_dioph`：vec_ex1_dioph (n) {S : Set (Vector3 Nat (succ n))} 
(d : Dioph S) : Dioph {v : Fin2 n -> Nat | exists x, (x :: v) in S}
· 使用定理 `Dioph.add_dioph`：add_dioph : DiophFn fun v => f v + g v
· 使用定理 `Dioph.mul_dioph`：mul_dioph : DiophFn fun v => f v * g v
· 使用定理 `Dioph.diophFn_comp2`：diophFn_comp2 {h : Nat -> Nat -> Nat} (d : DiophFn 
fun v : Vector3 Nat 2 => h (v &0) (v &1)) : DiophFn fun v => h (f v) (g v)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Dioph.diophFn_vec`：diophFn_vec (f : Vector3 Nat n -> Nat) : DiophFn f ↔ 
Dioph {v | f (v ∘ fs) = v fz}
· 使用定理 `Dioph.ext`：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `vectorAll_iff_forall`：∀ {α : Type u_1} {n : ℕ} (f : Vector3 α n → Prop),
 VectorAll n f ↔ ∀ (v : Vector3 α n), f v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.add_mul_mod_self_left`：∀ (x y z : ℕ), (x + y * z) % y = x % y
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m

--- 原说明 ---
Diophantine functions are closed under the modulo operation.
-/
theorem mod_dioph : DiophFn fun v => f v % g v :=
  have : Dioph {v : Vector3 ℕ 3 | (v &2 = 0 ∨ v &0 < v &2) ∧ ∃ x : ℕ, v &0 + v &2 * x = v &1} :=
    (D&2 D= D.0 D∨ D&0 D< D&2) D∧ (D∃) 3 <| D&1 D+ D&3 D* D&0 D= D&2
  diophFn_comp2 df dg <|
    (diophFn_vec _).2 <|
      ext this <|
        (vectorAll_iff_forall _).1 fun z x y =>
          show ((y = 0 ∨ z < y) ∧ ∃ c, z + y * c = x) ↔ x % y = z from
            ⟨fun ⟨h, c, hc⟩ => by
              rw [← hc]; simp only [add_mul_mod_self_left]; rcases h with x0 | hl
              · rw [x0, mod_zero]
              exact mod_eq_of_lt hl, fun e => by
                rw [← e]
                exact ⟨or_iff_not_imp_left.2 fun h => mod_lt _ (Nat.pos_of_ne_zero h), x / y,
                  mod_add_div _ _⟩⟩

@[inherit_doc]
scoped infixl:80 " D% " => Dioph.mod_dioph

/-- The set of places where two Diophantine functions are congruent modulo a third
is Diophantine. -/
/-
**Dioph.modEq_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：modEq_dioph {h : (α -> Nat) -> Nat} (dh : DiophFn h) : Dioph {v | f v ≡ g 
v [MOD h v]}
参数：α -> Nat；dh : DiophFn h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dioph.eq_dioph`：eq_dioph : Dioph {v | f v = g v}
· 使用定理 `Dioph.mod_dioph`：mod_dioph : DiophFn fun v => f v % g v

--- 原说明 ---
The set of places where two Diophantine functions are congruent modulo a third
is Diophantine.
-/
theorem modEq_dioph {h : (α → ℕ) → ℕ} (dh : DiophFn h) : Dioph {v | f v ≡ g v [MOD h v]} :=
  df D% dh D= dg D% dh

@[inherit_doc]
scoped notation "D≡ " => Dioph.modEq_dioph

/-- Diophantine functions are closed under integer division. -/
/-
**Dioph.div_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：div_dioph : DiophFn fun v => f v / g v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Dioph.union`：∀ {α : Type u} {S S' : Set (α → ℕ)}, Dioph S → Dioph S' → D
ioph (S ∪ S')
· 使用定理 `Dioph.inter`：inter (d : Dioph S) (d' : Dioph S') : Dioph (S inter S')
· 使用定理 `Dioph.eq_dioph`：eq_dioph : Dioph {v | f v = g v}
· 使用定理 `Dioph.proj_dioph_of_nat`：proj_dioph_of_nat {n : Nat} (m : Nat) [IsLT m n
] : DiophFn fun v : Vector3 Nat n => v &m
· 使用定理 `Dioph.const_dioph`：const_dioph (n : Nat) : DiophFn (const (α -> Nat) n)
· 使用定理 `Dioph.le_dioph`：le_dioph : Dioph {v | f v <= g v}
· 使用定理 `Dioph.mul_dioph`：mul_dioph : DiophFn fun v => f v * g v
· 使用定理 `Dioph.lt_dioph`：lt_dioph : Dioph {v | f v < g v}
· 使用定理 `Dioph.add_dioph`：add_dioph : DiophFn fun v => f v + g v
· 使用定理 `Dioph.diophFn_comp2`：diophFn_comp2 {h : Nat -> Nat -> Nat} (d : DiophFn 
fun v : Vector3 Nat 2 => h (v &0) (v &1)) : DiophFn fun v => h (f v) (g v)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Dioph.diophFn_vec`：diophFn_vec (f : Vector3 Nat n -> Nat) : DiophFn f ↔ 
Dioph {v | f (v ∘ fs) = v fz}
· 使用定理 `Dioph.ext`：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `vectorAll_iff_forall`：∀ {α : Type u_1} {n : ℕ} (f : Vector3 α n → Prop),
 VectorAll n f ↔ ∀ (v : Vector3 α n), f v
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Diophantine functions are closed under integer division.
-/
theorem div_dioph : DiophFn fun v => f v / g v :=
  have :
    Dioph {v : Vector3 ℕ 3 | v &2 = 0 ∧ v &0 = 0 ∨ v &0 * v &2 ≤ v &1 ∧ v &1 < (v &0 + 1) * v &2} :=
    (D&2 D= D.0 D∧ D&0 D= D.0) D∨ D&0 D* D&2 D≤ D&1 D∧ D&1 D< (D&0 D+ D.1) D* D&2
  diophFn_comp2 df dg <|
    (diophFn_vec _).2 <|
      ext this <|
        (vectorAll_iff_forall _).1 fun z x y =>
          show y = 0 ∧ z = 0 ∨ z * y ≤ x ∧ x < (z + 1) * y ↔ x / y = z by
            rcases y.eq_zero_or_pos with rfl | hy
            · simp [eq_comm]
            · rw [Nat.div_eq_iff hy, Nat.succ_mul]
              grind

end

@[inherit_doc]
scoped infixl:80 " D/ " => Dioph.div_dioph

open Pell

/-
**Dioph.pell_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：pell_dioph : Dioph {v : Vector3 Nat 4 | exists h : 1 < v &0, xn h (v &1) =
 v &2 ∧ yn h (v &1) = v &3}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ
· 使用定理 `Dioph.inter`：inter (d : Dioph S) (d' : Dioph S') : Dioph (S inter S')
· 使用定理 `Dioph.lt_dioph`：lt_dioph : Dioph {v | f v < g v}
· 使用定理 `Dioph.const_dioph`：const_dioph (n : Nat) : DiophFn (const (α -> Nat) n)
· 使用定理 `Dioph.proj_dioph_of_nat`：proj_dioph_of_nat {n : Nat} (m : Nat) [IsLT m n
] : DiophFn fun v : Vector3 Nat n => v &m
· 使用定理 `Dioph.le_dioph`：le_dioph : Dioph {v | f v <= g v}
· 使用定理 `Dioph.union`：∀ {α : Type u} {S S' : Set (α → ℕ)}, Dioph S → Dioph S' → D
ioph (S ∪ S')
· 使用定理 `Dioph.eq_dioph`：eq_dioph : Dioph {v | f v = g v}
· 使用定理 `Dioph.vec_ex1_dioph`：vec_ex1_dioph (n) {S : Set (Vector3 Nat (succ n))} 
(d : Dioph S) : Dioph {v : Fin2 n -> Nat | exists x, (x :: v) in S}
· 使用定理 `Dioph.sub_dioph`：sub_dioph : DiophFn fun v => f v - g v
· 使用定理 `Dioph.mul_dioph`：mul_dioph : DiophFn fun v => f v * g v
· 使用定理 `Dioph.modEq_dioph`：modEq_dioph {h : (α -> Nat) -> Nat} (dh : DiophFn h) 
: Dioph {v | f v ≡ g v [MOD h v]}
· 使用定理 `Dioph.dvd_dioph`：dvd_dioph : Dioph {v | f v ∣ g v}
· 使用定理 `Dioph.ext`：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Pell.matiyasevic`：matiyasevic {a k x y} : (exists a1 : 1 < a, xn a1 k = 
x ∧ yn a1 k = y) ↔ 1 < a ∧ k <= y ∧ (x = 1 ∧ y = 0 ∨ exists u v s t b : Nat, x *
 x - (…
-/
theorem pell_dioph :
    Dioph {v : Vector3 ℕ 4 | ∃ h : 1 < v &0, xn h (v &1) = v &2 ∧ yn h (v &1) = v &3} := by
  have : Dioph {v : Vector3 ℕ 4 |
    1 < v &0 ∧ v &1 ≤ v &3 ∧
    (v &2 = 1 ∧ v &3 = 0 ∨
    ∃ u w s t b : ℕ,
      v &2 * v &2 - (v &0 * v &0 - 1) * v &3 * v &3 = 1 ∧
      u * u - (v &0 * v &0 - 1) * w * w = 1 ∧
      s * s - (b * b - 1) * t * t = 1 ∧
      1 < b ∧ b ≡ 1 [MOD 4 * v &3] ∧ b ≡ v &0 [MOD u] ∧
      0 < w ∧ v &3 * v &3 ∣ w ∧
      s ≡ v &2 [MOD u] ∧
      t ≡ v &1 [MOD 4 * v &3])} :=
  (D.1 D< D&0 D∧ D&1 D≤ D&3 D∧
    ((D&2 D= D.1 D∧ D&3 D= D.0) D∨
    ((D∃) 4 <| (D∃) 5 <| (D∃) 6 <| (D∃) 7 <| (D∃) 8 <|
    D&7 D* D&7 D- (D&5 D* D&5 D- D.1) D* D&8 D* D&8 D= D.1 D∧
    D&4 D* D&4 D- (D&5 D* D&5 D- D.1) D* D&3 D* D&3 D= D.1 D∧
    D&2 D* D&2 D- (D&0 D* D&0 D- D.1) D* D&1 D* D&1 D= D.1 D∧
    D.1 D< D&0 D∧ (D≡ (D&0) (D.1) (D.4 D* D&8)) D∧ (D≡ (D&0) (D&5) (D&4)) D∧
    D.0 D< D&3 D∧ D&8 D* D&8 D∣ D&3 D∧
    (D≡ (D&2) (D&7) (D&4)) D∧
    (D≡ (D&1) (D&6) (D.4 D* (D&8))))) :)
  exact Dioph.ext this fun v => matiyasevic.symm
/-
**Dioph.xn_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：xn_dioph : DiophPFun fun v : Vector3 Nat 2 => ⟨1 < v &0, fun h => xn h (v 
&1)⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Dioph.reindex_dioph`：∀ {α : Type u} (β : Type u) {S : Set (α → ℕ)} (f : 
α → β), Dioph S → Dioph {v | v ∘ f ∈ S}
· 使用定理 `Dioph.pell_dioph`：pell_dioph : Dioph {v : Vector3 Nat 4 | exists h : 1 <
 v &0, xn h (v &1) = v &2 ∧ yn h (v &1) = v &3}
· 使用定理 `Dioph.vec_ex1_dioph`：vec_ex1_dioph (n) {S : Set (Vector3 Nat (succ n))} 
(d : Dioph S) : Dioph {v : Fin2 n -> Nat | exists x, (x :: v) in S}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Dioph.diophPFun_vec`：diophPFun_vec (f : Vector3 Nat n ->. Nat) : DiophPF
un f ↔ Dioph {v | (v ∘ fs, v fz) in f.graph}
· 使用定理 `Dioph.ext`：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
-/
theorem xn_dioph : DiophPFun fun v : Vector3 ℕ 2 => ⟨1 < v &0, fun h => xn h (v &1)⟩ :=
  have : Dioph {v : Vector3 ℕ 3 | ∃ y, ∃ h : 1 < v &1, xn h (v &2) = v &0 ∧ yn h (v &2) = y} :=
    let D_pell := pell_dioph.reindex_dioph (Fin2 4) [&2, &3, &1, &0]
    (D∃) 3 D_pell
  (diophPFun_vec _).2 <|
    Dioph.ext this fun _ => ⟨fun ⟨_, h, xe, _⟩ => ⟨h, xe⟩, fun ⟨h, xe⟩ => ⟨_, h, xe, rfl⟩⟩

/-- A version of **Matiyasevic's theorem** -/
/-
**Dioph.pow_dioph** 是 Mathlib 中的一个定理，位于命名空间 `Dioph`。
形式化陈述：pow_dioph {f g : (α -> Nat) -> Nat} (df : DiophFn f) (dg : DiophFn g) : Di
ophFn fun v => f v ^ g v
参数：α -> Nat；df : DiophFn f；dg : DiophFn g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin2.IsLT.succ`：∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ
· 使用定理 `Fin2.IsLT.zero`：∀ (n : ℕ), Fin2.IsLT 0 n.succ
· 使用定理 `Dioph.union`：∀ {α : Type u} {S S' : Set (α → ℕ)}, Dioph S → Dioph S' → D
ioph (S ∪ S')
· 使用定理 `Dioph.inter`：inter (d : Dioph S) (d' : Dioph S') : Dioph (S inter S')
· 使用定理 `Dioph.eq_dioph`：eq_dioph : Dioph {v | f v = g v}
· 使用定理 `Dioph.proj_dioph_of_nat`：proj_dioph_of_nat {n : Nat} (m : Nat) [IsLT m n
] : DiophFn fun v : Vector3 Nat n => v &m
· 使用定理 `Dioph.const_dioph`：const_dioph (n : Nat) : DiophFn (const (α -> Nat) n)
· 使用定理 `Dioph.lt_dioph`：lt_dioph : Dioph {v | f v < g v}
· 使用定理 `Dioph.vec_ex1_dioph`：vec_ex1_dioph (n) {S : Set (Vector3 Nat (succ n))} 
(d : Dioph S) : Dioph {v : Fin2 n -> Nat | exists x, (x :: v) in S}
· 使用定理 `Dioph.reindex_dioph`：∀ {α : Type u} (β : Type u) {S : Set (α → ℕ)} (f : 
α → β), Dioph S → Dioph {v | v ∘ f ∈ S}
· 使用定理 `Dioph.pell_dioph`：pell_dioph : Dioph {v : Vector3 Nat 4 | exists h : 1 <
 v &0, xn h (v &1) = v &2 ∧ yn h (v &1) = v &3}
· 使用定理 `Dioph.modEq_dioph`：modEq_dioph {h : (α -> Nat) -> Nat} (dh : DiophFn h) 
: Dioph {v | f v ≡ g v [MOD h v]}
· 使用定理 `Dioph.add_dioph`：add_dioph : DiophFn fun v => f v + g v
· 使用定理 `Dioph.mul_dioph`：mul_dioph : DiophFn fun v => f v * g v
· 使用定理 `Dioph.sub_dioph`：sub_dioph : DiophFn fun v => f v - g v
· 使用定理 `Dioph.le_dioph`：le_dioph : Dioph {v | f v <= g v}
· 使用定理 `Dioph.diophFn_comp2`：diophFn_comp2 {h : Nat -> Nat -> Nat} (d : DiophFn 
fun v : Vector3 Nat 2 => h (v &0) (v &1)) : DiophFn fun v => h (f v) (g v)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Dioph.diophFn_vec`：diophFn_vec (f : Vector3 Nat n -> Nat) : DiophFn f ↔ 
Dioph {v | f (v ∘ fs) = v fz}
· 使用定理 `Dioph.ext`：ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S'
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Pell.eq_pow_of_pell`：eq_pow_of_pell {m n k} : n ^ k = m ↔ k = 0 ∧ m = 1 
∨ 0 < k ∧ (n = 0 ∧ m = 0 ∨ 0 < n ∧ exists (w a t z : Nat) (a1 : 1 < a), xn a1 k 
≡ yn a1 k…
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)

--- 原说明 ---
A version of **Matiyasevic's theorem**
-/
theorem pow_dioph {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => f v ^ g v := by
  have : Dioph {v : Vector3 ℕ 3 |
    v &2 = 0 ∧ v &0 = 1 ∨ 0 < v &2 ∧
    (v &1 = 0 ∧ v &0 = 0 ∨ 0 < v &1 ∧
    ∃ w a t z x y : ℕ,
      (∃ a1 : 1 < a, xn a1 (v &2) = x ∧ yn a1 (v &2) = y) ∧
      x ≡ y * (a - v &1) + v &0 [MOD t] ∧
      2 * a * v &1 = t + (v &1 * v &1 + 1) ∧
      v &0 < t ∧ v &1 ≤ w ∧ v &2 ≤ w ∧
      a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1)} :=
  (D&2 D= D.0 D∧ D&0 D= D.1) D∨ (D.0 D< D&2 D∧
    ((D&1 D= D.0 D∧ D&0 D= D.0) D∨ (D.0 D< D&1 D∧
    ((D∃) 3 <| (D∃) 4 <| (D∃) 5 <| (D∃) 6 <| (D∃) 7 <| (D∃) 8 <|
    pell_dioph.reindex_dioph (Fin2 9) [&4, &8, &1, &0] D∧
    (D≡ (D&1) (D&0 D* (D&4 D- D&7) D+ D&6) (D&3)) D∧
    D.2 D* D&4 D* D&7 D= D&3 D+ (D&7 D* D&7 D+ D.1) D∧
    D&6 D< D&3 D∧ D&7 D≤ D&5 D∧ D&8 D≤ D&5 D∧
    D&4 D* D&4 D- ((D&5 D+ D.1) D* (D&5 D+ D.1) D- D.1) D* (D&5 D* D&2) D* (D&5 D* D&2) D= D.1))) :)
  exact diophFn_comp2 df dg <| (diophFn_vec _).2 <| Dioph.ext this fun v => Iff.symm <|
    eq_pow_of_pell.trans <| or_congr Iff.rfl <| and_congr Iff.rfl <| or_congr Iff.rfl <|
       and_congr Iff.rfl <|
        ⟨fun ⟨w, a, t, z, a1, h⟩ => ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩,
        fun ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩ => ⟨w, a, t, z, a1, h⟩⟩

end

end Dioph

