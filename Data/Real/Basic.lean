/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.CauSeq.Completion
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Real numbers from Cauchy sequences

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.

The facts that the real numbers are an Archimedean floor ring,
and a conditionally complete linear order,
have been deferred to the file `Mathlib/Data/Real/Archimedean.lean`,
in order to keep the imports here simple.

The fact that the real numbers are a (trivial) \*-ring has similarly been deferred to
`Mathlib/Data/Real/Star.lean`.
-/

@[expose] public section


assert_not_exists Finset Module Submonoid FloorRing

/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
@[wikidata Q12916, wikidata Q2584477]
/-
**Real** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequen
ces of rational
numbers.
-/
structure Real where ofCauchy ::
  /-- The underlying Cauchy completion -/
  cauchy : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)

@[inherit_doc]
notation "ℝ" => Real

namespace CauSeq.Completion

-- this can't go in `Data.Real.CauSeqCompletion` as the structure on `ℚ` isn't available
@[simp]
/-
**CauSeq.Completion.ofRat_rat** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRat_rat {abv : Rat -> Rat} [IsAbsoluteValue abv] (q : Rat) : ofRat (q : 
Rat) = (q : Cauchy abv)
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRat_rat {abv : ℚ → ℚ} [IsAbsoluteValue abv] (q : ℚ) :
    ofRat (q : ℚ) = (q : Cauchy abv) :=
  rfl

end CauSeq.Completion

namespace Real

open CauSeq CauSeq.Completion

variable {x : ℝ}

/-
**Real.ext_cauchy_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {x y : ℝ}, x = y ↔ x.cauchy = y.cauchy
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.ofCauchy.injEq`：∀ (cauchy cauchy_1 : CauSeq.Completion.Cauchy abs),
   ({ cauchy := cauchy } = { cauchy := cauchy_1 }) = (cauchy = cauchy_1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ext_cauchy_iff : ∀ {x y : Real}, x = y ↔ x.cauchy = y.cauchy
  | ⟨a⟩, ⟨b⟩ => by rw [ofCauchy.injEq]
/-
**Real.ext_cauchy** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ext_cauchy {x y : Real} : x.cauchy = y.cauchy -> x = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.ext_cauchy_iff`：∀ {x y : ℝ}, x = y ↔ x.cauchy = y.cauchy
-/
theorem ext_cauchy {x y : Real} : x.cauchy = y.cauchy → x = y :=
  ext_cauchy_iff.2

/-- The real numbers are isomorphic to the quotient of Cauchy sequences on the rationals. -/
/-
**Real.equivCauchy** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：equivCauchy : Real ≃ CauSeq.Completion.Cauchy (abs : Rat -> Rat)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The real numbers are isomorphic to the quotient of Cauchy sequences on the ratio
nals.
-/
def equivCauchy : ℝ ≃ CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  ⟨Real.cauchy, Real.ofCauchy, fun ⟨_⟩ => rfl, fun _ => rfl⟩

set_option backward.privateInPublic true in
-- irreducible doesn't work for instances: https://github.com/leanprover-community/lean/issues/511
private irreducible_def zero : ℝ :=
  ⟨0⟩

set_option backward.privateInPublic true in
private irreducible_def one : ℝ :=
  ⟨1⟩

set_option backward.privateInPublic true in
private irreducible_def add : ℝ → ℝ → ℝ
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private irreducible_def neg : ℝ → ℝ
  | ⟨a⟩ => ⟨-a⟩

set_option backward.privateInPublic true in
private irreducible_def mul : ℝ → ℝ → ℝ
  | ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

set_option backward.privateInPublic true in
private noncomputable irreducible_def inv' : ℝ → ℝ
  | ⟨a⟩ => ⟨a⁻¹⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero ℝ :=
  ⟨zero⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One ℝ :=
  ⟨one⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add ℝ :=
  ⟨add⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg ℝ :=
  ⟨neg⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul ℝ :=
  ⟨mul⟩
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub ℝ :=
  ⟨fun a b => a + -b⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inv ℝ :=
  ⟨inv'⟩
/-
**Real.ofCauchy_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ofCauchy_zero : (⟨0⟩ : Real) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.zero_def`：Real.zero✝ = { cauchy 
:= 0 }
-/
theorem ofCauchy_zero : (⟨0⟩ : ℝ) = 0 :=
  zero_def.symm
/-
**Real.ofCauchy_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ofCauchy_one : (⟨1⟩ : Real) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.one_def`：Real.one✝ = { cauchy :=
 1 }
-/
theorem ofCauchy_one : (⟨1⟩ : ℝ) = 1 :=
  one_def.symm
/-
**Real.ofCauchy_add** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ofCauchy_add (a b) : (⟨a + b⟩ : Real) = ⟨a⟩ + ⟨b⟩
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.add_def`：∀ (x x_1 : ℝ),   Real.a
dd✝ x x_1 =     match x, x_1 with     | { cauchy := a }, { cauchy := b } => { ca
uchy := a + b }
-/
theorem ofCauchy_add (a b) : (⟨a + b⟩ : ℝ) = ⟨a⟩ + ⟨b⟩ :=
  (add_def _ _).symm
/-
**Real.ofCauchy_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ofCauchy_neg (a) : (⟨-a⟩ : Real) = -⟨a⟩
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.neg_def`：∀ (x : ℝ),   Real.neg✝ 
x =     match x with     | { cauchy := a } => { cauchy := -a }
-/
theorem ofCauchy_neg (a) : (⟨-a⟩ : ℝ) = -⟨a⟩ :=
  (neg_def _).symm
/-
**Real.ofCauchy_sub** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ofCauchy_sub (a b) : (⟨a - b⟩ : Real) = ⟨a⟩ - ⟨b⟩
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Real.ofCauchy_add`：ofCauchy_add (a b) : (⟨a + b⟩ : Real) = ⟨a⟩ + ⟨b⟩
· 使用定理 `Real.ofCauchy_neg`：ofCauchy_neg (a) : (⟨-a⟩ : Real) = -⟨a⟩
-/
theorem ofCauchy_sub (a b) : (⟨a - b⟩ : ℝ) = ⟨a⟩ - ⟨b⟩ := by
  rw [sub_eq_add_neg, ofCauchy_add, ofCauchy_neg]
  rfl
/-
**Real.ofCauchy_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ofCauchy_mul (a b) : (⟨a * b⟩ : Real) = ⟨a⟩ * ⟨b⟩
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.mul_def`：∀ (x x_1 : ℝ),   Real.m
ul✝ x x_1 =     match x, x_1 with     | { cauchy := a }, { cauchy := b } => { ca
uchy := a * b }
-/
theorem ofCauchy_mul (a b) : (⟨a * b⟩ : ℝ) = ⟨a⟩ * ⟨b⟩ :=
  (mul_def _ _).symm
/-
**Real.ofCauchy_inv** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ofCauchy_inv {f} : (⟨f⁻¹⟩ : Real) = ⟨f⟩⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.inv'_def`：∀ (x : ℝ),   Real.inv'
✝ x =     match x with     | { cauchy := a } => { cauchy := a⁻¹ }
-/
theorem ofCauchy_inv {f} : (⟨f⁻¹⟩ : ℝ) = ⟨f⟩⁻¹ :=
  show _ = inv' _ by rw [inv']
/-
**Real.cauchy_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cauchy_zero : (0 : Real).cauchy = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.zero_def`：Real.zero✝ = { cauchy 
:= 0 }
-/
theorem cauchy_zero : (0 : ℝ).cauchy = 0 :=
  show zero.cauchy = 0 by rw [zero_def]
/-
**Real.cauchy_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cauchy_one : (1 : Real).cauchy = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.one_def`：Real.one✝ = { cauchy :=
 1 }
-/
theorem cauchy_one : (1 : ℝ).cauchy = 1 :=
  show one.cauchy = 1 by rw [one_def]
/-
**Real.cauchy_add** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (a b : ℝ), (a + b).cauchy = a.cauchy + b.cauchy
参数：a b : ℝ；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.add_def`：∀ (x x_1 : ℝ),   Real.a
dd✝ x x_1 =     match x, x_1 with     | { cauchy := a }, { cauchy := b } => { ca
uchy := a + b }
-/
theorem cauchy_add : ∀ a b, (a + b : ℝ).cauchy = a.cauchy + b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (add _ _).cauchy = _ by rw [add_def]
/-
**Real.cauchy_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (a : ℝ), (-a).cauchy = -a.cauchy
参数：a : ℝ；-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.neg_def`：∀ (x : ℝ),   Real.neg✝ 
x =     match x with     | { cauchy := a } => { cauchy := -a }
-/
theorem cauchy_neg : ∀ a, (-a : ℝ).cauchy = -a.cauchy
  | ⟨a⟩ => show (neg _).cauchy = _ by rw [neg_def]
/-
**Real.cauchy_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (a b : ℝ), (a * b).cauchy = a.cauchy * b.cauchy
参数：a b : ℝ；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.mul_def`：∀ (x x_1 : ℝ),   Real.m
ul✝ x x_1 =     match x, x_1 with     | { cauchy := a }, { cauchy := b } => { ca
uchy := a * b }
-/
theorem cauchy_mul : ∀ a b, (a * b : ℝ).cauchy = a.cauchy * b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (mul _ _).cauchy = _ by rw [mul_def]
/-
**Real.cauchy_sub** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (a b : ℝ), (a - b).cauchy = a.cauchy - b.cauchy
参数：a b : ℝ；a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.cauchy_neg`：∀ (a : ℝ), (-a).cauchy = -a.cauchy
· 使用定理 `Real.cauchy_add`：∀ (a b : ℝ), (a + b).cauchy = a.cauchy + b.cauchy
-/
theorem cauchy_sub : ∀ a b, (a - b : ℝ).cauchy = a.cauchy - b.cauchy
  | ⟨a⟩, ⟨b⟩ => by
    rw [sub_eq_add_neg, ← cauchy_neg, ← cauchy_add]
    rfl
/-
**Real.cauchy_inv** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (f : ℝ), f⁻¹.cauchy = f.cauchy⁻¹
参数：f : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.inv'_def`：∀ (x : ℝ),   Real.inv'
✝ x =     match x with     | { cauchy := a } => { cauchy := a⁻¹ }
-/
theorem cauchy_inv : ∀ f, (f⁻¹ : ℝ).cauchy = f.cauchy⁻¹
  | ⟨f⟩ => show (inv' _).cauchy = _ by rw [inv']
/-
**Real.instNatCast** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instNatCast : NatCast Real where natCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNatCast : NatCast ℝ where natCast n := ⟨n⟩
/-
**Real.instIntCast** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instIntCast : IntCast Real where intCast z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIntCast : IntCast ℝ where intCast z := ⟨z⟩
/-
**Real.instNNRatCast** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instNNRatCast : NNRatCast Real where nnratCast q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNNRatCast : NNRatCast ℝ where nnratCast q := ⟨q⟩
/-
**Real.instRatCast** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instRatCast : RatCast Real where ratCast q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRatCast : RatCast ℝ where ratCast q := ⟨q⟩
/-
**Real.ofCauchy_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：ofCauchy_natCast (n : Nat) : (⟨n⟩ : Real) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofCauchy_natCast (n : ℕ) : (⟨n⟩ : ℝ) = n := rfl
/-
**Real.ofCauchy_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：ofCauchy_intCast (z : Int) : (⟨z⟩ : Real) = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofCauchy_intCast (z : ℤ) : (⟨z⟩ : ℝ) = z := rfl
/-
**Real.ofCauchy_nnratCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：ofCauchy_nnratCast (q : Rat>=0) : (⟨q⟩ : Real) = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofCauchy_nnratCast (q : ℚ≥0) : (⟨q⟩ : ℝ) = q := rfl
/-
**Real.ofCauchy_ratCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：ofCauchy_ratCast (q : Rat) : (⟨q⟩ : Real) = q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofCauchy_ratCast (q : ℚ) : (⟨q⟩ : ℝ) = q := rfl
/-
**Real.cauchy_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：cauchy_natCast (n : Nat) : (n : Real).cauchy = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cauchy_natCast (n : ℕ) : (n : ℝ).cauchy = n := rfl
/-
**Real.cauchy_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：cauchy_intCast (z : Int) : (z : Real).cauchy = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cauchy_intCast (z : ℤ) : (z : ℝ).cauchy = z := rfl
/-
**Real.cauchy_nnratCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：cauchy_nnratCast (q : Rat>=0) : (q : Real).cauchy = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cauchy_nnratCast (q : ℚ≥0) : (q : ℝ).cauchy = q := rfl
/-
**Real.cauchy_ratCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：cauchy_ratCast (q : Rat) : (q : Real).cauchy = q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cauchy_ratCast (q : ℚ) : (q : ℝ).cauchy = q := rfl
/-
**Real.commRing** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：commRing : CommRing Real where natCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commRing : CommRing ℝ where
  natCast n := ⟨n⟩
  intCast z := ⟨z⟩
  npow := @npowRec ℝ ⟨1⟩ ⟨(· * ·)⟩
  nsmul := @nsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩ ⟨@Neg.neg ℝ _⟩ (@nsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩)
  add_zero a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
  zero_add a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
  add_comm a b := by apply ext_cauchy; simp only [cauchy_add, add_comm]
  add_assoc a b c := by apply ext_cauchy; simp only [cauchy_add, add_assoc]
  mul_zero a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
  zero_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
  mul_one a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
  one_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
  mul_comm a b := by apply ext_cauchy; simp only [cauchy_mul, mul_comm]
  mul_assoc a b c := by apply ext_cauchy; simp only [cauchy_mul, mul_assoc]
  left_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, mul_add]
  right_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, add_mul]
  neg_add_cancel a := by apply ext_cauchy; simp [cauchy_add, cauchy_neg, cauchy_zero]
  natCast_zero := by apply ext_cauchy; simp [cauchy_zero]
  natCast_succ n := by apply ext_cauchy; simp [cauchy_one, cauchy_add]
  intCast_negSucc z := by apply ext_cauchy; simp [cauchy_neg, cauchy_natCast]

/-- `Real.equivCauchy` as a ring equivalence. -/
@[simps]
/-
**Real.ringEquivCauchy** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：ringEquivCauchy : Real ≃+* CauSeq.Completion.Cauchy (abs : Rat -> Rat)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Real.cauchy_mul`：∀ (a b : ℝ), (a * b).cauchy = a.cauchy * b.cauchy
· 使用定理 `Real.cauchy_add`：∀ (a b : ℝ), (a + b).cauchy = a.cauchy + b.cauchy

--- 原说明 ---
`Real.equivCauchy` as a ring equivalence.
-/
def ringEquivCauchy : ℝ ≃+* CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  { equivCauchy with
    toFun := cauchy
    invFun := ofCauchy
    map_add' := cauchy_add
    map_mul' := cauchy_mul }

/-! Extra instances to short-circuit type class resolution.

These short-circuits have an additional property of ensuring that a computable path is found; if
`Field ℝ` is found first, then decaying it to these typeclasses would result in a `noncomputable`
version of them. -/

/-
**Real.instRing** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instRing : Ring Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extra instances to short-circuit type class resolution.

These short-circuits have an additional property of ensuring that a computable p
ath is found; if
`Field ℝ` is found first, then decaying it to these typeclasses would result in 
a `noncomputable`
version of them.
-/
instance instRing : Ring ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommSemiring ℝ := by infer_instance
/-
**Real.semiring** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：semiring : Semiring Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semiring : Semiring ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoidWithZero ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidWithZero ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddGroup ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoid ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddLeftCancelSemigroup ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddRightCancelSemigroup ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommSemigroup ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddSemigroup ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoid ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommSemigroup ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semigroup ℝ := by infer_instance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited ℝ :=
  ⟨0⟩

/-- Make a real number from a Cauchy sequence of rationals (by taking the equivalence class). -/
/-
**Real.mk** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：mk (x : CauSeq Rat abs) : Real
参数：x : CauSeq Rat abs。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a real number from a Cauchy sequence of rationals (by taking the equivalenc
e class).
-/
def mk (x : CauSeq ℚ abs) : ℝ :=
  ⟨CauSeq.Completion.mk x⟩
/-
**Real.mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_eq {f g : CauSeq Rat abs} : mk f = mk g ↔ f ≈ g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Real.ext_cauchy_iff`：∀ {x y : ℝ}, x = y ↔ x.cauchy = y.cauchy
· 使用定理 `CauSeq.Completion.mk_eq`：mk_eq {f g : CauSeq _ abv} : mk f = mk g ↔ LimZ
ero (f - g)
-/
theorem mk_eq {f g : CauSeq ℚ abs} : mk f = mk g ↔ f ≈ g :=
  ext_cauchy_iff.trans CauSeq.Completion.mk_eq

set_option backward.privateInPublic true in
private irreducible_def lt : ℝ → ℝ → Prop
  | ⟨x⟩, ⟨y⟩ =>
    (Quotient.liftOn₂ x y (· < ·)) fun _ _ _ _ hf hg =>
      propext <|
        ⟨fun h => lt_of_eq_of_lt (Setoid.symm hf) (lt_of_lt_of_eq h hg), fun h =>
          lt_of_eq_of_lt hf (lt_of_lt_of_eq h (Setoid.symm hg))⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LT ℝ :=
  ⟨lt⟩
/-
**Real.lt_cauchy** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_cauchy {f g} : (⟨⟦f⟧⟩ : Real) < ⟨⟦g⟧⟩ ↔ f < g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.lt_def`：∀ (x x_1 : ℝ),   Real.lt
✝ x x_1 =     match x, x_1 with     | { cauchy := x }, { cauchy := y } => Quotie
nt.liftOn₂ x y (fun x1 x2 => x1 < x2…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_cauchy {f g} : (⟨⟦f⟧⟩ : ℝ) < ⟨⟦g⟧⟩ ↔ f < g :=
  show lt _ _ ↔ _ by rw [lt_def]; rfl

@[simp]
/-
**Real.mk_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_lt {f g : CauSeq Rat abs} : mk f < mk g ↔ f < g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.lt_cauchy`：lt_cauchy {f g} : (⟨⟦f⟧⟩ : Real) < ⟨⟦g⟧⟩ ↔ f < g
-/
theorem mk_lt {f g : CauSeq ℚ abs} : mk f < mk g ↔ f < g :=
  lt_cauchy
/-
**Real.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_zero : mk 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.ofCauchy_zero`：ofCauchy_zero : (⟨0⟩ : Real) = 0
-/
theorem mk_zero : mk 0 = 0 := by rw [← ofCauchy_zero]; rfl
/-
**Real.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_one : mk 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.ofCauchy_one`：ofCauchy_one : (⟨1⟩ : Real) = 1
-/
theorem mk_one : mk 1 = 1 := by rw [← ofCauchy_one]; rfl
/-
**Real.mk_add** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_add {f g : CauSeq Rat abs} : mk (f + g) = mk f + mk g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_add {f g : CauSeq ℚ abs} : mk (f + g) = mk f + mk g := by simp [mk, ← ofCauchy_add]
/-
**Real.mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_mul {f g : CauSeq Rat abs} : mk (f * g) = mk f * mk g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_mul {f g : CauSeq ℚ abs} : mk (f * g) = mk f * mk g := by simp [mk, ← ofCauchy_mul]
/-
**Real.mk_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_neg {f : CauSeq Rat abs} : mk (-f) = -mk f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_neg {f : CauSeq ℚ abs} : mk (-f) = -mk f := by simp [mk, ← ofCauchy_neg]

@[simp]
/-
**Real.mk_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_pos {f : CauSeq Rat abs} : 0 < mk f ↔ Pos f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.mk_zero`：mk_zero : mk 0 = 0
· 使用定理 `Real.mk_lt`：mk_lt {f g : CauSeq Rat abs} : mk f < mk g ↔ f < g
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem mk_pos {f : CauSeq ℚ abs} : 0 < mk f ↔ Pos f := by
  rw [← mk_zero, mk_lt]
  exact iff_of_eq (congr_arg Pos (sub_zero f))
/-
**Real.mk_const** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：mk_const {x : Rat} : mk (const abs x) = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_const {x : ℚ} : mk (const abs x) = x := rfl

set_option backward.privateInPublic true in
private irreducible_def le (x y : ℝ) : Prop :=
  x < y ∨ x = y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE ℝ :=
  ⟨le⟩
/-
**Real.le_def'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem le_def' {x y : ℝ} : x ≤ y ↔ x < y ∨ x = y :=
  iff_of_eq <| le_def _ _

@[simp]
/-
**Real.mk_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_le {f g : CauSeq Rat abs} : mk f <= mk g ↔ f <= g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le {f g : CauSeq ℚ abs} : mk f ≤ mk g ↔ f ≤ g := by
  simp only [le_def', mk_lt, mk_eq]; rfl

@[elab_as_elim]
/-
**Real.ind_mk** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {C : ℝ → Prop} (x : ℝ), (∀ (y : CauSeq ℚ abs), C (Real.mk y)) → C x
参数：x : ℝ；∀ (y : CauSeq ℚ abs), C (Real.mk y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
-/
protected theorem ind_mk {C : Real → Prop} (x : Real) (h : ∀ y, C (mk y)) : C x := by
  obtain ⟨x⟩ := x
  induction x using Quot.induction_on
  exact h _
/-
**Real.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：partialOrder : PartialOrder Real where lt_iff_le_not_ge a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance partialOrder : PartialOrder ℝ where
  lt_iff_le_not_ge a b := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa using lt_iff_le_not_ge
  le_refl a := by
    induction a using Real.ind_mk
    rw [mk_le]
  le_trans a b c := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simpa using le_trans
  le_antisymm a b := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa [mk_eq] using CauSeq.le_antisymm
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder ℝ := by infer_instance
/-
**Real.ratCast_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ratCast_lt {x y : Rat} : (x : Real) < (y : Real) ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.mk_const`：mk_const {x : Rat} : mk (const abs x) = x
· 使用定理 `Real.mk_lt`：mk_lt {f g : CauSeq Rat abs} : mk f < mk g ↔ f < g
· 使用定理 `CauSeq.const_lt`：const_lt {x y : α} : const x < const y ↔ x < y
-/
theorem ratCast_lt {x y : ℚ} : (x : ℝ) < (y : ℝ) ↔ x < y := by
  rw [← mk_const, ← mk_const, mk_lt]
  exact const_lt
/-
**Real.zero_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：0 < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `Real.ofCauchy_zero`：ofCauchy_zero : (⟨0⟩ : Real) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Real.ofCauchy_one`：ofCauchy_one : (⟨1⟩ : Real) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.ratCast_lt`：ratCast_lt {x y : Rat} : (x : Real) < (y : Real) ↔ x < 
y
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
-/
protected theorem zero_lt_one : (0 : ℝ) < 1 := by
  convert! ratCast_lt.2 zero_lt_one <;> simp [← ofCauchy_ratCast, ofCauchy_one, ofCauchy_zero]
/-
**Real.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instNontrivial : Nontrivial Real where exists_pair_ne
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Real.zero_lt_one`：0 < 1
-/
instance instNontrivial : Nontrivial ℝ where
  exists_pair_ne := ⟨0, 1, Real.zero_lt_one.ne⟩
/-
**Real.instZeroLEOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instZeroLEOneClass : ZeroLEOneClass Real where zero_le_one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.zero_lt_one`：0 < 1
-/
instance instZeroLEOneClass : ZeroLEOneClass ℝ where
  zero_le_one := le_of_lt Real.zero_lt_one
/-
**Real.instIsOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instIsOrderedAddMonoid : IsOrderedAddMonoid Real where add_le_add_left
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.ind_mk`：∀ {C : ℝ → Prop} (x : ℝ), (∀ (y : CauSeq ℚ abs), C (Real.mk
 y)) → C x
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
-/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid ℝ where
  add_le_add_left := by
    simp only [le_iff_eq_or_lt]
    rintro a b ⟨rfl, h⟩
    · simp only [lt_self_iff_false, or_false, forall_const]
    · refine fun c => Or.inr ?_
      induction a using Real.ind_mk with | _ a =>
      induction b using Real.ind_mk with | _ b =>
      induction c using Real.ind_mk with | _ c =>
      simp only [mk_lt, ← mk_add] at *
      change Pos _ at *
      rwa [add_sub_add_right_eq_sub]
/-
**Real.instIsStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instIsStrictOrderedRing : IsStrictOrderedRing Real
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsStrictOrderedRing.of_mul_pos`：IsStrictOrderedRing.of_mul_pos [Ring R] 
[PartialOrder R] [IsOrderedAddMonoid R] [ZeroLEOneClass R] [Nontrivial R] (mul_p
os : forall a b : R,…
· 使用定理 `Real.ind_mk`：∀ {C : ℝ → Prop} (x : ℝ), (∀ (y : CauSeq ℚ abs), C (Real.mk
 y)) → C x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CauSeq.mul_pos`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder 
α] [inst_2 : IsStrictOrderedRing α] {f g : CauSeq α abs},   f.Pos → g.Pos → (f *
 g).…
-/
instance instIsStrictOrderedRing : IsStrictOrderedRing ℝ :=
  .of_mul_pos fun a b ↦ by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa only [mk_lt, mk_pos, ← mk_mul] using CauSeq.mul_pos
/-
**Real.instIsOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instIsOrderedRing : IsOrderedRing Real
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
instance instIsOrderedRing : IsOrderedRing ℝ :=
  inferInstance
/-
**Real.instIsOrderedCancelAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid Real
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid ℝ :=
  inferInstance

set_option backward.privateInPublic true in
private irreducible_def sup : ℝ → ℝ → ℝ
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊔ ·) (fun _ _ hx _ _ hy => sup_equiv_sup hx hy) x y⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max ℝ :=
  ⟨sup⟩
/-
**Real.ofCauchy_sup** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ofCauchy_sup (a b) : (⟨⟦a ⊔ b⟧⟩ : Real) = ⟨⟦a⟧⟩ ⊔ ⟨⟦b⟧⟩
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.sup_equiv_sup`：sup_equiv_sup {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a
₁ ≈ a₂) (hb : b₁ ≈ b₂) : a₁ ⊔ b₁ ≈ a₂ ⊔ b₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.sup_def`：∀ (x x_1 : ℝ),   Real.s
up✝ x x_1 =     match x, x_1 with     | { cauchy := x }, { cauchy := y } => { ca
uchy := Quotient.map₂ (fun x1 x2 => x…
-/
theorem ofCauchy_sup (a b) : (⟨⟦a ⊔ b⟧⟩ : ℝ) = ⟨⟦a⟧⟩ ⊔ ⟨⟦b⟧⟩ :=
  show _ = sup _ _ by
    rw [sup_def]
    rfl

@[simp]
/-
**Real.mk_sup** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_sup (a b) : (mk (a ⊔ b) : Real) = mk a ⊔ mk b
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.ofCauchy_sup`：ofCauchy_sup (a b) : (⟨⟦a ⊔ b⟧⟩ : Real) = ⟨⟦a⟧⟩ ⊔ ⟨⟦b
⟧⟩
-/
theorem mk_sup (a b) : (mk (a ⊔ b) : ℝ) = mk a ⊔ mk b :=
  ofCauchy_sup _ _

set_option backward.privateInPublic true in
private irreducible_def inf : ℝ → ℝ → ℝ
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊓ ·) (fun _ _ hx _ _ hy => inf_equiv_inf hx hy) x y⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min ℝ :=
  ⟨inf⟩
/-
**Real.ofCauchy_inf** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ofCauchy_inf (a b) : (⟨⟦a ⊓ b⟧⟩ : Real) = ⟨⟦a⟧⟩ ⊓ ⟨⟦b⟧⟩
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.inf_equiv_inf`：inf_equiv_inf {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a
₁ ≈ a₂) (hb : b₁ ≈ b₂) : a₁ ⊓ b₁ ≈ a₂ ⊓ b₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Real.Basic.0.Real.inf_def`：∀ (x x_1 : ℝ),   Real.i
nf✝ x x_1 =     match x, x_1 with     | { cauchy := x }, { cauchy := y } => { ca
uchy := Quotient.map₂ (fun x1 x2 => x…
-/
theorem ofCauchy_inf (a b) : (⟨⟦a ⊓ b⟧⟩ : ℝ) = ⟨⟦a⟧⟩ ⊓ ⟨⟦b⟧⟩ :=
  show _ = inf _ _ by
    rw [inf_def]
    rfl

@[simp]
/-
**Real.mk_inf** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_inf (a b) : (mk (a ⊓ b) : Real) = mk a ⊓ mk b
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.ofCauchy_inf`：ofCauchy_inf (a b) : (⟨⟦a ⊓ b⟧⟩ : Real) = ⟨⟦a⟧⟩ ⊓ ⟨⟦b
⟧⟩
-/
theorem mk_inf (a b) : (mk (a ⊓ b) : ℝ) = mk a ⊓ mk b :=
  ofCauchy_inf _ _
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribLattice ℝ where
  sup := (· ⊔ ·)
  le_sup_left := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_sup, mk_le]
    exact CauSeq.le_sup_left
  le_sup_right := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_sup, mk_le]
    exact CauSeq.le_sup_right
  sup_le := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simp_rw [← mk_sup, mk_le]
    exact CauSeq.sup_le
  inf := (· ⊓ ·)
  inf_le_left := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_inf, mk_le]
    exact CauSeq.inf_le_left
  inf_le_right := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_inf, mk_le]
    exact CauSeq.inf_le_right
  le_inf := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simp_rw [← mk_inf, mk_le]
    exact CauSeq.le_inf
  le_sup_inf := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    apply Eq.le
    simp only [← mk_sup, ← mk_inf]
    exact congr_arg mk (CauSeq.sup_inf_distrib_left ..).symm

-- Extra instances to short-circuit type class resolution
/-
**Real.lattice** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：lattice : Lattice Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lattice : Lattice ℝ :=
  inferInstance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf ℝ :=
  inferInstance
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup ℝ :=
  inferInstance
/-
**Real.leTotal_R** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：leTotal_R : @Std.Total Real (· <= ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.ind_mk`：∀ {C : ℝ → Prop} (x : ℝ), (∀ (y : CauSeq ℚ abs), C (Real.mk
 y)) → C x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CauSeq.le_total`：le_total (f g : CauSeq α abs) : f <= g ∨ g <= f
-/
instance leTotal_R : @Std.Total ℝ (· ≤ ·) :=
  ⟨by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa using CauSeq.le_total ..⟩

open scoped Classical in
/-
**Real.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：linearOrder : LinearOrder Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance linearOrder : LinearOrder ℝ :=
  Lattice.toLinearOrder ℝ
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDomain ℝ := IsStrictOrderedRing.isDomain
/-
**Real.instDivInvMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：DivInvMonoid ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instDivInvMonoid : DivInvMonoid ℝ where
/-
**Real.ofCauchy_div** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：ofCauchy_div (f g) : (⟨f / g⟩ : Real) = (⟨f⟩ : Real) / (⟨g⟩ : Real)
参数：f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.ofCauchy_mul`：ofCauchy_mul (a b) : (⟨a * b⟩ : Real) = ⟨a⟩ * ⟨b⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.ofCauchy_inv`：ofCauchy_inv {f} : (⟨f⁻¹⟩ : Real) = ⟨f⟩⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofCauchy_div (f g) : (⟨f / g⟩ : ℝ) = (⟨f⟩ : ℝ) / (⟨g⟩ : ℝ) := by
  simp_rw [div_eq_mul_inv, ofCauchy_mul, ofCauchy_inv]
/-
**Real.instField** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instField : Field Real where mul_inv_cancel
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
-/
noncomputable instance instField : Field ℝ where
  mul_inv_cancel := by
    rintro ⟨a⟩ h
    rw [mul_comm]
    simp only [← ofCauchy_inv, ← ofCauchy_mul, ← ofCauchy_one, ← ofCauchy_zero,
      Ne, ofCauchy.injEq] at *
    exact CauSeq.Completion.inv_mul_cancel h
  inv_zero := by simp [← ofCauchy_zero, ← ofCauchy_inv]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
  nnratCast_def q := by
    rw [← ofCauchy_nnratCast, NNRat.cast_def, ofCauchy_div, ofCauchy_natCast, ofCauchy_natCast]
  ratCast_def q := by
    rw [← ofCauchy_ratCast, Rat.cast_def, ofCauchy_div, ofCauchy_natCast, ofCauchy_intCast]

-- Extra instances to short-circuit type class resolution
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : DivisionRing ℝ := by infer_instance
/-
**Real.decidableLT** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：decidableLT (a b : Real) : Decidable (a < b)
参数：a b : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance decidableLT (a b : ℝ) : Decidable (a < b) := by infer_instance
/-
**Real.decidableLE** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：decidableLE (a b : Real) : Decidable (a <= b)
参数：a b : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance decidableLE (a b : ℝ) : Decidable (a ≤ b) := by infer_instance
/-
**Real.decidableEq** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：decidableEq (a b : Real) : Decidable (a = b)
参数：a b : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance decidableEq (a b : ℝ) : Decidable (a = b) := by infer_instance

/-- Show an underlying Cauchy sequence for real numbers.

The representative chosen is the one passed in the VM to `Quot.mk`, so two Cauchy sequences
converging to the same number may be printed differently.
-/
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show an underlying Cauchy sequence for real numbers.

The representative chosen is the one passed in the VM to `Quot.mk`, so two Cauch
y sequences
converging to the same number may be printed differently.
-/
unsafe instance : Repr ℝ where
  reprPrec r p := Repr.addAppParen ("Real.ofCauchy " ++ repr r.cauchy) p
/-
**Real.le_mk_of_forall_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_mk_of_forall_le {f : CauSeq Rat abs} : (exists i, forall j >= i, x <= f
 j) -> x <= mk f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.ind_mk`：∀ {C : ℝ → Prop} (x : ℝ), (∀ (y : CauSeq ℚ abs), C (Real.mk
 y)) → C x
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.mk_lt`：mk_lt {f g : CauSeq Rat abs} : mk f < mk g ↔ f < g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
· 使用定理 `CauSeq.cauchy₃`：cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε -> exists i, fora
ll j >= i, forall k >= j, abv (f k - f j) < ε
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.mk_const`：mk_const {x : Rat} : mk (const abs x) = x
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `CauSeq.sub_apply`：sub_apply (f g : CauSeq β abv) (i : Nat) : (f - g) i =
 f i - g i
· 使用定理 `sub_self_div_two`：sub_self_div_two (a : α) : a - a / 2 = a / 2
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem le_mk_of_forall_le {f : CauSeq ℚ abs} : (∃ i, ∀ j ≥ i, x ≤ f j) → x ≤ mk f := by
  intro h
  induction x using Real.ind_mk
  apply le_of_not_gt
  rw [mk_lt]
  rintro ⟨K, K0, hK⟩
  obtain ⟨i, H⟩ := exists_forall_ge_and h (exists_forall_ge_and hK (f.cauchy₃ <| half_pos K0))
  apply not_lt_of_ge (H _ le_rfl).1
  rw [← mk_const, mk_lt]
  refine ⟨_, half_pos K0, i, fun j ij => ?_⟩
  have := add_le_add (H _ ij).2.1 (le_of_lt (abs_lt.1 <| (H _ le_rfl).2.2 _ ij).1)
  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this
/-
**Real.mk_le_of_forall_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_le_of_forall_le {f : CauSeq Rat abs} {x : Real} (h : exists i, forall j
 >= i, (f j : Real) <= x) : mk f <= x
参数：h : exists i, forall j >= i, (f j : Real) <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.mk_neg`：mk_neg {f : CauSeq Rat abs} : mk (-f) = -mk f
· 使用定理 `Real.le_mk_of_forall_le`：le_mk_of_forall_le {f : CauSeq Rat abs} : (exis
ts i, forall j >= i, x <= f j) -> x <= mk f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem mk_le_of_forall_le {f : CauSeq ℚ abs} {x : ℝ} (h : ∃ i, ∀ j ≥ i, (f j : ℝ) ≤ x) :
    mk f ≤ x := by
  obtain ⟨i, H⟩ := h
  rw [← neg_le_neg_iff, ← mk_neg]
  exact le_mk_of_forall_le ⟨i, fun j ij => by simp [H _ ij]⟩
/-
**Real.mk_near_of_forall_near** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mk_near_of_forall_near {f : CauSeq Rat abs} {x : Real} {ε : Real} (H : exi
sts i, forall j >= i, |(f j : Real) - x| <= ε) : |mk f - x| <= ε
参数：H : exists i, forall j >= i, |(f j : Real) - x| <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_sub_le_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| ≤ c ↔ a - b ≤ c ∧ b - a 
≤ c
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.mk_le_of_forall_le`：mk_le_of_forall_le {f : CauSeq Rat abs} {x : Re
al} (h : exists i, forall j >= i, (f j : Real) <= x) : mk f <= x
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sub_le_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE α] [Add
LeftMono α] {a b c : α}, a - b ≤ c ↔ a - c ≤ b
· 使用定理 `Real.le_mk_of_forall_le`：le_mk_of_forall_le {f : CauSeq Rat abs} : (exis
ts i, forall j >= i, x <= f j) -> x <= mk f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mk_near_of_forall_near {f : CauSeq ℚ abs} {x : ℝ} {ε : ℝ}
    (H : ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| ≤ ε) : |mk f - x| ≤ ε :=
  abs_sub_le_iff.2
    ⟨sub_le_iff_le_add'.2 <|
        mk_le_of_forall_le <|
          H.imp fun _ h j ij => sub_le_iff_le_add'.1 (abs_sub_le_iff.1 <| h j ij).1,
      sub_le_comm.1 <|
        le_mk_of_forall_le <| H.imp fun _ h j ij => sub_le_comm.1 (abs_sub_le_iff.1 <| h j ij).2⟩
/-
**Real.mul_add_one_le_add_one_pow** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：mul_add_one_le_add_one_pow {a : Real} (ha : 0 <= a) (b : Nat) : a * b + 1 
<= (a + 1) ^ b
参数：ha : 0 <= a；b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
（共 31 条，此处仅展示前 30 条）
-/
lemma mul_add_one_le_add_one_pow {a : ℝ} (ha : 0 ≤ a) (b : ℕ) : a * b + 1 ≤ (a + 1) ^ b := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  clear ha
  induction b generalizing a with
  | zero => simp
  | succ b hb =>
    calc
      a * ↑(b + 1) + 1 = (0 + 1) ^ b * a + (a * b + 1) := by
        simp [mul_add, add_assoc, add_left_comm]
      _ ≤ (a + 1) ^ b * a + (a + 1) ^ b := by
        gcongr
        · norm_num
        · exact hb ha'
      _ = (a + 1) ^ (b + 1) := by simp [pow_succ, mul_add]

end Real

/-- A function `f : R → ℝ` is power-multiplicative if for all `r ∈ R` and all positive `n ∈ ℕ`,
`f (r ^ n) = (f r) ^ n`. -/
/-
**IsPowMul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsPowMul {R : Type*} [Pow R Nat] (f : R -> Real)
参数：f : R -> Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : R → ℝ` is power-multiplicative if for all `r ∈ R` and all positi
ve `n ∈ ℕ`,
`f (r ^ n) = (f r) ^ n`.
-/
def IsPowMul {R : Type*} [Pow R ℕ] (f : R → ℝ) :=
  ∀ (a : R) {n : ℕ}, 1 ≤ n → f (a ^ n) = f a ^ n
/-
**IsPowMul.map_one_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsPowMul.map_one_le_one {R : Type*} [Monoid R] {f : R -> Real} (hf : IsPow
Mul f) : f 1 <= 1
参数：hf : IsPowMul f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `eq_zero_or_one_of_sq_eq_self`：eq_zero_or_one_of_sq_eq_self [MonoidWithZe
ro M₀] [IsRightCancelMulZero M₀] {x : M₀} (hx : x ^ 2 = x) : x = 0 ∨ x = 1
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma IsPowMul.map_one_le_one {R : Type*} [Monoid R] {f : R → ℝ} (hf : IsPowMul f) :
    f 1 ≤ 1 := by
  have hf1 : (f 1) ^ 2 = f 1 := by conv_rhs => rw [← one_pow 2, hf _ one_le_two]
  rcases eq_zero_or_one_of_sq_eq_self hf1 with h | h <;> rw [h]
  exact zero_le_one

/-- A ring homomorphism `f : α →+* β` is bounded with respect to the functions `nα : α → ℝ` and
  `nβ : β → ℝ` if there exists a positive constant `C` such that for all `x` in `α`,
  `nβ (f x) ≤ C * nα x`. -/
/-
**RingHom.IsBoundedWrt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.IsBoundedWrt {α : Type*} [Ring α] {β : Type*} [Ring β] (nα : α -> 
Real) (nβ : β -> Real) (f : α ->+* β) : Prop
参数：nα : α -> Real；nβ : β -> Real；f : α ->+* β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `f : α →+* β` is bounded with respect to the functions `nα :
 α → ℝ` and
  `nβ : β → ℝ` if there exists a positive constant `C` such that for all `x` in 
`α`,
  `nβ (f x) ≤ C * nα x`.
-/
def RingHom.IsBoundedWrt {α : Type*} [Ring α] {β : Type*} [Ring β] (nα : α → ℝ) (nβ : β → ℝ)
    (f : α →+* β) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : α, nβ (f x) ≤ C * nα x
