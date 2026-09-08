/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Finset.MulAntidiagonal
public import Mathlib.Data.Finset.SMulAntidiagonal
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.HahnSeries.Addition

/-!
# Multiplicative properties of Hahn series

If `Γ` is ordered and `R` has zero, then `R⟦Γ⟧` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. This module introduces
multiplication and scalar multiplication on Hahn series. If `Γ` is an ordered cancellative
commutative additive monoid and `R` is a semiring, then we get a semiring structure on
`R⟦Γ⟧`. If `Γ` has an ordered vector-addition on `Γ'` and `R` has a scalar multiplication
on `V`, we define `HahnModule Γ' R V` as a type alias for `V⟦Γ'⟧` that admits a scalar
multiplication from `R⟦Γ⟧`. The scalar action of `R` on `R⟦Γ⟧` is compatible
with the action of `R⟦Γ⟧` on `HahnModule Γ' R V`.

## Main Definitions
* `HahnModule` is a type alias for `HahnSeries`, which we use for defining scalar multiplication
  of `R⟦Γ⟧` on `HahnModule Γ' R V` for an `R`-module `V`, where `Γ'` admits an ordered
  cancellative vector addition operation from `Γ`. The type alias allows us to avoid a potential
  instance diamond.
* `HahnModule.of` is the isomorphism from `V⟦Γ⟧` to `HahnModule Γ R V`.
* `HahnSeries.C` is the `constant term` ring homomorphism `R →+* R⟦Γ⟧`.
* `HahnSeries.embDomainRingHom` is the ring homomorphism `R⟦Γ⟧ →+* R⟦Γ'⟧`
  induced by an order embedding `Γ ↪o Γ'`.
* `HahnSeries.orderTopSubOnePos` is the group of invertible Hahn series close to 1, i.e., those
  series such that subtracting one yields a series with strictly positive `orderTop`.

## Main results
* If `R` is a (commutative) (semi-)ring, then so is `R⟦Γ⟧`.
* If `V` is an `R`-module, then `HahnModule Γ' R V` is a `R⟦Γ⟧`-module.

## TODO
The following may be useful for composing vertex operators, but they seem to take time.
* rightTensorMap: `HahnModule Γ' R U ⊗[R] V →ₗ[R] HahnModule Γ' R (U ⊗[R] V)`
* leftTensorMap: `U ⊗[R] HahnModule Γ' R V →ₗ[R] HahnModule Γ' R (U ⊗[R] V)`

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section

open Finset Function HahnSeries Pointwise

noncomputable section

variable {Γ Γ' R S V : Type*}

namespace HahnSeries

variable [Zero Γ] [PartialOrder Γ]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] [One R] : One R⟦Γ⟧ where one := single 0 1
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] [NatCast R] : NatCast R⟦Γ⟧ where natCast n := single 0 n
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] [IntCast R] : IntCast R⟦Γ⟧ where intCast z := single 0 z
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] [NNRatCast R] : NNRatCast R⟦Γ⟧ where nnratCast q := single 0 q
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] [RatCast R] : RatCast R⟦Γ⟧ where ratCast q := single 0 q

open scoped Classical in
@[simp]
/-
**HahnSeries.coeff_one** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).coeff a = if a = 0 then 1 
else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.coeff_single`：coeff_single : (single a r).coeff b = if b = a 
then r else 0
-/
theorem coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).coeff a = if a = 0 then 1 else 0 :=
  coeff_single
/-
**HahnSeries.single_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} [inst : Zero Γ] [inst_1 : PartialOrder Γ] 
[inst_2 : Zero R] [inst_3 : One R],   (HahnSeries.single 0) 1 = 1
参数：HahnSeries.single 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem single_zero_one [Zero R] [One R] : single (0 : Γ) (1 : R) = 1 := rfl
/-
**HahnSeries.single_zero_natCast** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_zero_natCast [Zero R] [NatCast R] (n : Nat) : single (0 : Γ) (n : R
) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_zero_natCast [Zero R] [NatCast R] (n : ℕ) : single (0 : Γ) (n : R) = n := rfl
/-
**HahnSeries.single_zero_intCast** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_zero_intCast [Zero R] [IntCast R] (z : Int) : single (0 : Γ) (z : R
) = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_zero_intCast [Zero R] [IntCast R] (z : ℤ) : single (0 : Γ) (z : R) = z := rfl
/-
**HahnSeries.single_zero_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_zero_nnratCast [Zero R] [NNRatCast R] (q : Rat>=0) : single (0 : Γ)
 (q : R) = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_zero_nnratCast [Zero R] [NNRatCast R] (q : ℚ≥0) : single (0 : Γ) (q : R) = q := rfl
/-
**HahnSeries.single_zero_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_zero_ratCast [Zero R] [RatCast R] (q : Rat) : single (0 : Γ) (q : R
) = q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_zero_ratCast [Zero R] [RatCast R] (q : ℚ) : single (0 : Γ) (q : R) = q := rfl
/-
**HahnSeries.single_zero_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_zero_ofNat [Zero R] [NatCast R] (n : Nat) [n.AtLeastTwo] : single (
0 : Γ) (ofNat(n) : R) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_zero_ofNat [Zero R] [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    single (0 : Γ) (ofNat(n) : R) = ofNat(n) := rfl

@[simp]
/-
**HahnSeries.support_one** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_one [MulZeroOneClass R] [Nontrivial R] : support (1 : R⟦Γ⟧) = {0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.support_single_of_ne`：support_single_of_ne (h : r != 0) : sup
port (single a r) = {a}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem support_one [MulZeroOneClass R] [Nontrivial R] : support (1 : R⟦Γ⟧) = {0} :=
  support_single_of_ne one_ne_zero

@[simp]
/-
**HahnSeries.orderTop_one** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_one [Zero R] [One R] [NeZero (1 : R)] : orderTop (1 : R⟦Γ⟧) = 0
参数：1 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.single_zero_one`：∀ {Γ : Type u_1} {R : Type u_3} [inst : Zero
 Γ] [inst_1 : PartialOrder Γ] [inst_2 : Zero R] [inst_3 : One R],   (HahnSeries.
single 0) 1 = 1
· 使用定理 `HahnSeries.orderTop_single`：orderTop_single (h : r != 0) : (single a r).
orderTop = a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `WithTop.coe_eq_zero`：∀ {α : Type u} [inst : Zero α] {a : α}, ↑a = 0 ↔ a 
= 0
-/
theorem orderTop_one [Zero R] [One R] [NeZero (1 : R)] : orderTop (1 : R⟦Γ⟧) = 0 := by
  rw [← single_zero_one, orderTop_single one_ne_zero, WithTop.coe_eq_zero]

@[simp]
/-
**HahnSeries.order_one** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：order_one [MulZeroOneClass R] : order (1 : R⟦Γ⟧) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `HahnSeries.instSubsingleton`：∀ {Γ : Type u_1} {R : Type u_3} [inst : Par
tialOrder Γ] [inst_1 : Zero R] [Subsingleton R],   Subsingleton (HahnSeries Γ R)
· 使用定理 `HahnSeries.order_zero`：order_zero : order (0 : R⟦Γ⟧) = 0
· 使用定理 `HahnSeries.order_single`：order_single (h : r != 0) : (single a r).order 
= a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem order_one [MulZeroOneClass R] : order (1 : R⟦Γ⟧) = 0 := by
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (1 : R⟦Γ⟧) 0, order_zero]
  · exact order_single one_ne_zero

@[simp]
/-
**HahnSeries.leadingCoeff_one** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_one [MulZeroOneClass R] : (1 : R⟦Γ⟧).leadingCoeff = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.leadingCoeff_eq`：leadingCoeff_eq {x : R⟦Γ⟧} : x.leadingCoeff 
= x.coeff x.order
· 使用定理 `HahnSeries.order_one`：order_one [MulZeroOneClass R] : order (1 : R⟦Γ⟧) =
 0
· 使用定理 `HahnSeries.coeff_one`：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).co
eff a = if a = 0 then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_one [MulZeroOneClass R] : (1 : R⟦Γ⟧).leadingCoeff = 1 := by
  simp [leadingCoeff_eq]

@[simp]
/-
**HahnSeries.map_one** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [inst : Zero Γ] [inst_1 : P
artialOrder Γ] [inst_2 : MonoidWithZero R]   [inst_3 : MonoidWithZero S] (f : R 
→*₀ S), HahnSeries.map 1 f = 1
参数：f : R →*₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `HahnSeries.map_single`：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [i
nst : PartialOrder Γ] [inst_1 : Zero R] {a : Γ} {r : R}   [inst_2 : Zero S] (f :
 ZeroHom R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHom.map_one`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZe
roOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β), f 1 = 1
-/
protected lemma map_one [MonoidWithZero R] [MonoidWithZero S] (f : R →*₀ S) :
    (1 : R⟦Γ⟧).map f = (1 : S⟦Γ⟧) :=
  HahnSeries.map_single (a := (0 : Γ)) f.toZeroHom |>.trans <| congrArg _ <| f.map_one
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne R⟦Γ⟧ where
  natCast_zero := by simp [← single_zero_natCast]
  natCast_succ n := by simp [← single_zero_natCast]
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroupWithOne R] : AddCommGroupWithOne R⟦Γ⟧ where
  intCast_ofNat n := by simp [← single_zero_natCast, ← single_zero_intCast]
  intCast_negSucc n := by simp [← single_zero_natCast, ← single_zero_intCast]

end HahnSeries

/-- We introduce a type alias for `HahnSeries` in order to work with scalar multiplication by
series. If we wrote a `SMul R⟦Γ⟧ V⟦Γ⟧` instance, then when
`V = R⟦Γ⟧`, we would have two different actions of `R⟦Γ⟧` on `V⟦Γ⟧`.
See `Mathlib/Algebra/Polynomial/Module/Basic.lean` for more discussion on this problem. -/
@[nolint unusedArguments]
/-
**HahnModule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HahnModule (Γ R V : Type*) [PartialOrder Γ] [Zero V] [SMul R V]
参数：Γ R V : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We introduce a type alias for `HahnSeries` in order to work with scalar multipli
cation by
series. If we wrote a `SMul R⟦Γ⟧ V⟦Γ⟧` instance, then when
`V = R⟦Γ⟧`, we would have two different actions of `R⟦Γ⟧` on `V⟦Γ⟧`.
See `Mathlib/Algebra/Polynomial/Module/Basic.lean` for more discussion on this p
roblem.
-/
def HahnModule (Γ R V : Type*) [PartialOrder Γ] [Zero V] [SMul R V] :=
  V⟦Γ⟧

namespace HahnModule

section

variable [PartialOrder Γ] [Zero V] [SMul R V]

/-- The casting function to the type synonym. -/
/-
**HahnModule.of** 是 Mathlib 中的一个定义，位于命名空间 `HahnModule`。
形式化陈述：of (R : Type*) [SMul R V] : V⟦Γ⟧ ≃ HahnModule Γ R V
参数：R : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The casting function to the type synonym.
-/
def of (R : Type*) [SMul R V] : V⟦Γ⟧ ≃ HahnModule Γ R V :=
  Equiv.refl _

/-- Recursion principle to reduce a result about the synonym to the original type. -/
@[elab_as_elim]
/-
**HahnModule.rec** 是 Mathlib 中的一个定义，位于命名空间 `HahnModule`。
形式化陈述：rec {motive : HahnModule Γ R V -> Sort*} (h : forall x : V⟦Γ⟧, motive (of 
R x)) : forall x, motive x
参数：h : forall x : V⟦Γ⟧, motive (of R x)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Recursion principle to reduce a result about the synonym to the original type.
-/
def rec {motive : HahnModule Γ R V → Sort*} (h : ∀ x : V⟦Γ⟧, motive (of R x)) :
    ∀ x, motive x :=
  fun x => h <| (of R).symm x

@[ext]
/-
**HahnModule.ext** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：ext (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff = ((of R).symm y).
coeff) : x = y
参数：x y : HahnModule Γ R V；h : ((of R).symm x).coeff = ((of R).symm y).coeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `HahnSeries.coeff_inj`：coeff_inj {x y : R⟦Γ⟧} : x.coeff = y.coeff ↔ x = y
-/
theorem ext (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff = ((of R).symm y).coeff) : x = y :=
  (of R).symm.injective <| HahnSeries.coeff_inj.1 h

end

section SMul

variable [PartialOrder Γ] [SMul R V]

/-
**HahnModule.instZero** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
形式化陈述：instZero [Zero V] : Zero (HahnModule Γ R V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero [Zero V] : Zero (HahnModule Γ R V) :=
  inferInstanceAs <| Zero V⟦Γ⟧
/-
**HahnModule.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
形式化陈述：instAddCommMonoid [AddCommMonoid V] : AddCommMonoid (HahnModule Γ R V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid [AddCommMonoid V] : AddCommMonoid (HahnModule Γ R V) :=
  inferInstanceAs <| AddCommMonoid V⟦Γ⟧
/-
**HahnModule.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
形式化陈述：instAddCommGroup [AddCommGroup V] : AddCommGroup (HahnModule Γ R V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [AddCommGroup V] : AddCommGroup (HahnModule Γ R V) :=
  inferInstanceAs <| AddCommGroup V⟦Γ⟧
/-
**HahnModule.instBaseSMul** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
形式化陈述：instBaseSMul {V} [Monoid R] [AddMonoid V] [DistribMulAction R V] : SMul R 
(HahnModule Γ R V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBaseSMul {V} [Monoid R] [AddMonoid V] [DistribMulAction R V] :
    SMul R (HahnModule Γ R V) :=
  inferInstanceAs <| SMul R V⟦Γ⟧
/-
**HahnModule.of_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {V : Type u_5} [inst : PartialOrder Γ] [in
st_1 : SMul R V] [inst_2 : Zero V],   (HahnModule.of R) 0 = 0
参数：HahnModule.of R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem of_zero [Zero V] : of R (0 : V⟦Γ⟧) = 0 := rfl
/-
**HahnModule.of_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {V : Type u_5} [inst : PartialOrder Γ] [in
st_1 : SMul R V] [inst_2 : AddCommMonoid V]   (x y : HahnSeries Γ V), (HahnModul
e.of R) (x + y) = (HahnModule.of R) x + (HahnModule.of R) y
参数：x y : HahnSeries Γ V；HahnModule.of R；x + y；HahnModule.of R；HahnModule.of R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem of_add [AddCommMonoid V] (x y : V⟦Γ⟧) :
    of R (x + y) = of R x + of R y := rfl
/-
**HahnModule.of_sub** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {V : Type u_5} [inst : PartialOrder Γ] [in
st_1 : SMul R V] [inst_2 : AddCommGroup V]   (x y : HahnSeries Γ V), (HahnModule
.of R) (x - y) = (HahnModule.of R) x - (HahnModule.of R) y
参数：x y : HahnSeries Γ V；HahnModule.of R；x - y；HahnModule.of R；HahnModule.of R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem of_sub [AddCommGroup V] (x y : V⟦Γ⟧) :
    of R (x - y) = of R x - of R y := rfl
/-
**HahnModule.of_symm_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {V : Type u_5} [inst : PartialOrder Γ] [in
st_1 : SMul R V] [inst_2 : Zero V],   (HahnModule.of R).symm 0 = 0
参数：HahnModule.of R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem of_symm_zero [Zero V] : (of R).symm (0 : HahnModule Γ R V) = 0 := rfl
/-
**HahnModule.of_symm_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {V : Type u_5} [inst : PartialOrder Γ] [in
st_1 : SMul R V] [inst_2 : AddCommMonoid V]   (x y : HahnModule Γ R V), (HahnMod
ule.of R).symm (x + y) = (HahnModule.of R).symm x + (HahnModule.of R).symm y
参数：x y : HahnModule Γ R V；HahnModule.of R；x + y；HahnModule.of R；HahnModule.of R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem of_symm_add [AddCommMonoid V] (x y : HahnModule Γ R V) :
    (of R).symm (x + y) = (of R).symm x + (of R).symm y := rfl
/-
**HahnModule.of_symm_sub** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {V : Type u_5} [inst : PartialOrder Γ] [in
st_1 : SMul R V] [inst_2 : AddCommGroup V]   (x y : HahnModule Γ R V), (HahnModu
le.of R).symm (x - y) = (HahnModule.of R).symm x - (HahnModule.of R).symm y
参数：x y : HahnModule Γ R V；HahnModule.of R；x - y；HahnModule.of R；HahnModule.of R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem of_symm_sub [AddCommGroup V] (x y : HahnModule Γ R V) :
    (of R).symm (x - y) = (of R).symm x - (of R).symm y := rfl

variable [PartialOrder Γ'] [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [Zero R] [AddCommMonoid V]
/-
**HahnModule.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
形式化陈述：instSMul : SMul R⟦Γ⟧ (HahnModule Γ' R V) where smul x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance instSMul : SMul R⟦Γ⟧ (HahnModule Γ' R V) where
  smul x y := (of R) {
    coeff := fun a =>
      ∑ ij ∈ VAddAntidiagonal a
        (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support ((of R).symm y).isPWO_support a),
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd
    isPWO_support' :=
        have h : { a : Γ' | (∑ ij ∈ VAddAntidiagonal a
            (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support ((of R).symm y).isPWO_support a),
              x.coeff ij.fst • ((of R).symm y).coeff ij.snd) ≠ 0 } ⊆
            { a : Γ' | (VAddAntidiagonal a (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support
              ((of R).symm y).isPWO_support a)).Nonempty } := by
          intro a ha
          simp only [Set.mem_ofPred_eq]
          contrapose! ha
          simp [ha]
        (isPWO_support_vaddAntidiagonal x.isPWO_support ((of R).symm y).isPWO_support).mono h }
/-
**HahnModule.coeff_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：coeff_smul (x : R⟦Γ⟧) (y : HahnModule Γ' R V) (a : Γ') : ((of R).symm <| x
 • y).coeff a = ∑ ij in VAddAntidiagonal a (Set.VAddAntidiagonal.finite_of_isPWO
 x.isPWO_support ((of R).symm y).isPWO_support a), x.coeff ij.fst • ((of R).symm
 y).coeff ij.snd
参数：x : R⟦Γ⟧；y : HahnModule Γ' R V；a : Γ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coeff_smul (x : R⟦Γ⟧) (y : HahnModule Γ' R V) (a : Γ') :
    ((of R).symm <| x • y).coeff a =
      ∑ ij ∈ VAddAntidiagonal a
        (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support ((of R).symm y).isPWO_support a),
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd :=
  rfl

end SMul

section SMulZeroClass

variable [PartialOrder Γ] [PartialOrder Γ'] [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ']
  [AddCommMonoid V]

/-
**HahnModule.instBaseSMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
形式化陈述：instBaseSMulZeroClass [SMulZeroClass R V] : SMulZeroClass R (HahnModule Γ 
R V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBaseSMulZeroClass [SMulZeroClass R V] :
    SMulZeroClass R (HahnModule Γ R V) :=
  inferInstanceAs <| SMulZeroClass R V⟦Γ⟧
/-
**HahnModule.of_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {V : Type u_5} [inst : PartialOrder Γ] [in
st_1 : AddCommMonoid V]   [inst_2 : SMulZeroClass R V] (r : R) (x : HahnSeries Γ
 V), (HahnModule.of R) (r • x) = r • (HahnModule.of R) x
参数：r : R；x : HahnSeries Γ V；HahnModule.of R；r • x；HahnModule.of R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem of_smul [SMulZeroClass R V] (r : R) (x : V⟦Γ⟧) :
    (of R) (r • x) = r • (of R) x := rfl
/-
**HahnModule.of_symm_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {V : Type u_5} [inst : PartialOrder Γ] [in
st_1 : AddCommMonoid V]   [inst_2 : SMulZeroClass R V] (r : R) (x : HahnModule Γ
 R V),   (HahnModule.of R).symm (r • x) = r • (HahnModule.of R).symm x
参数：r : R；x : HahnModule Γ R V；HahnModule.of R；r • x；HahnModule.of R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem of_symm_smul [SMulZeroClass R V] (r : R) (x : HahnModule Γ R V) :
    (of R).symm (r • x) = r • (of R).symm x := rfl

variable [Zero R]
/-
**HahnModule.instSMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
形式化陈述：instSMulZeroClass [SMulZeroClass R V] : SMulZeroClass R⟦Γ⟧ (HahnModule Γ' 
R V) where smul_zero x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulZeroClass [SMulZeroClass R V] :
    SMulZeroClass R⟦Γ⟧ (HahnModule Γ' R V) where
  smul_zero x := by
    ext
    simp [coeff_smul]
/-
**HahnModule.coeff_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：coeff_smul_right [SMulZeroClass R V] {x : R⟦Γ⟧} {y : HahnModule Γ' R V} {a
 : Γ'} {s : Set Γ'} (hs : s.IsPWO) (hys : ((of R).symm y).support subseteq s) : 
((of R).symm <| x • y).coeff a = ∑ ij in VAddAntidiagonal a (Set.VAddAntidiagona
l.finite_of_isPWO x.isPWO_support hs a), x.coeff ij.fst • ((of R).symm y).coeff 
ij.snd
参数：hs : s.IsPWO；hys : ((of R).symm y).support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnModule.coeff_smul`：coeff_smul (x : R⟦Γ⟧) (y : HahnModule Γ' R V) (a 
: Γ') : ((of R).symm <| x • y).coeff a = ∑ ij in VAddAntidiagonal a (Set.VAddAnt
idiagonal.f…
· 使用定理 `Finset.sum_subset_zero_on_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ 
: Finset ι} [inst : AddCommMonoid M] {f g : ι → M} [inst_1 : DecidableEq ι],   s
₁ ⊆ s₂ → (∀ x ∈ s₂ \ …
· 使用定理 `Finset.vaddAntidiagonal_mono_right`：∀ {G : Type u_1} {P : Type u_2} [ins
t : VAdd G P] {s : Set G} {t v : Set P} (a : P)   (hst : (s.vaddAntidiagonal t a
).Finite) (hsv : (s.vadd…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem coeff_smul_right [SMulZeroClass R V] {x : R⟦Γ⟧} {y : HahnModule Γ' R V} {a : Γ'}
    {s : Set Γ'} (hs : s.IsPWO) (hys : ((of R).symm y).support ⊆ s) :
    ((of R).symm <| x • y).coeff a =
      ∑ ij ∈ VAddAntidiagonal a (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support hs a),
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd := by
  classical
  rw [coeff_smul]
  apply sum_subset_zero_on_sdiff (vaddAntidiagonal_mono_right _ _ _ hys) _ fun _ _ => rfl
  intro b hb
  simp only [not_and, mem_sdiff, mem_vaddAntidiagonal, HahnSeries.mem_support, not_imp_not] at hb
  rw [hb.2 hb.1.1 hb.1.2.2, smul_zero]
/-
**HahnModule.coeff_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：coeff_smul_left [SMulWithZero R V] {x : R⟦Γ⟧} {y : HahnModule Γ' R V} {a :
 Γ'} {s : Set Γ} (hs : s.IsPWO) (hxs : x.support subseteq s) : ((of R).symm <| x
 • y).coeff a = ∑ ij in VAddAntidiagonal a (Set.VAddAntidiagonal.finite_of_isPWO
 hs ((of R).symm y).isPWO_support a), x.coeff ij.fst • ((of R).symm y).coeff ij.
snd
参数：hs : s.IsPWO；hxs : x.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnModule.coeff_smul`：coeff_smul (x : R⟦Γ⟧) (y : HahnModule Γ' R V) (a 
: Γ') : ((of R).symm <| x • y).coeff a = ∑ ij in VAddAntidiagonal a (Set.VAddAnt
idiagonal.f…
· 使用定理 `Finset.sum_subset_zero_on_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ 
: Finset ι} [inst : AddCommMonoid M] {f g : ι → M} [inst_1 : DecidableEq ι],   s
₁ ⊆ s₂ → (∀ x ∈ s₂ \ …
· 使用定理 `Finset.vaddAntidiagonal_mono_left`：∀ {G : Type u_1} {P : Type u_2} [inst
 : VAdd G P] {s u : Set G} {t : Set P} (a : P),   u ⊆ s →     ∀ (hst : (s.vaddAn
tidiagonal t a).Finite)…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem coeff_smul_left [SMulWithZero R V] {x : R⟦Γ⟧}
    {y : HahnModule Γ' R V} {a : Γ'} {s : Set Γ}
    (hs : s.IsPWO) (hxs : x.support ⊆ s) :
    ((of R).symm <| x • y).coeff a =
      ∑ ij ∈ VAddAntidiagonal a
      (Set.VAddAntidiagonal.finite_of_isPWO hs ((of R).symm y).isPWO_support a),
      x.coeff ij.fst • ((of R).symm y).coeff ij.snd := by
  classical
  rw [coeff_smul]
  apply sum_subset_zero_on_sdiff (vaddAntidiagonal_mono_left _ hxs _ _) _ fun _ _ => rfl
  intro b hb
  simp only [not_and', mem_sdiff, mem_vaddAntidiagonal, HahnSeries.mem_support, not_ne_iff] at hb
  rw [hb.2 ⟨hb.1.2.1, hb.1.2.2⟩, zero_smul]

end SMulZeroClass

section DistribSMul

variable [PartialOrder Γ] [PartialOrder Γ'] [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [AddCommMonoid V]

/-
**HahnModule.smul_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：smul_add [Zero R] [DistribSMul R V] (x : R⟦Γ⟧) (y z : HahnModule Γ' R V) :
 x • (y + z) = x • y + x • z
参数：x : R⟦Γ⟧；y z : HahnModule Γ' R V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnModule.ext`：ext (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff 
= ((of R).symm y).coeff) : x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.IsPWO.union`：∀ {α : Type u_2} [inst : Preorder α] {s t : Set α}, s.I
sPWO → t.IsPWO → (s ∪ t).IsPWO
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnModule.coeff_smul_right`：coeff_smul_right [SMulZeroClass R V] {x : R
⟦Γ⟧} {y : HahnModule Γ' R V} {a : Γ'} {s : Set Γ'} (hs : s.IsPWO) (hys : ((of R)
.symm y).support …
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `HahnModule.of_symm_add`：∀ {Γ : Type u_1} {R : Type u_3} {V : Type u_5} [
inst : PartialOrder Γ] [inst_1 : SMul R V] [inst_2 : AddCommMonoid V]   (x y : H
ahnModule Γ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_add [Zero R] [DistribSMul R V] (x : R⟦Γ⟧) (y z : HahnModule Γ' R V) :
    x • (y + z) = x • y + x • z := by
  ext k
  have hwf := ((of R).symm y).isPWO_support.union ((of R).symm z).isPWO_support
  rw [coeff_smul_right hwf, of_symm_add]
  · simp_all only [HahnSeries.coeff_add', Pi.add_apply, of_symm_add]
    rw [coeff_smul_right hwf Set.subset_union_right,
      coeff_smul_right hwf Set.subset_union_left]
    simp_all [sum_add_distrib]
  · intro b
    simp_all only [Set.isPWO_union, HahnSeries.isPWO_support, and_self, of_symm_add,
      HahnSeries.coeff_add', Pi.add_apply, ne_eq, Set.mem_union, HahnSeries.mem_support]
    contrapose!
    intro h
    rw [h.1, h.2, add_zero]
/-
**HahnModule.instDistribSMul** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
形式化陈述：instDistribSMul [MonoidWithZero R] [DistribSMul R V] : DistribSMul R⟦Γ⟧ (H
ahnModule Γ' R V) where smul_add
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribSMul [MonoidWithZero R] [DistribSMul R V] : DistribSMul R⟦Γ⟧
    (HahnModule Γ' R V) where
  smul_add := smul_add
/-
**HahnModule.add_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：add_smul [AddCommMonoid R] [SMulWithZero R V] {x y : R⟦Γ⟧} {z : HahnModule
 Γ' R V} (h : forall (r s : R) (u : V), (r + s) • u = r • u + s • u) : (x + y) •
 z = x • z + y • z
参数：h : forall (r s : R) (u : V), (r + s) • u = r • u + s • u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnModule.ext`：ext (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff 
= ((of R).symm y).coeff) : x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.IsPWO.union`：∀ {α : Type u_2} [inst : Preorder α] {s t : Set α}, s.I
sPWO → t.IsPWO → (s ∪ t).IsPWO
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnModule.coeff_smul_left`：coeff_smul_left [SMulWithZero R V] {x : R⟦Γ⟧
} {y : HahnModule Γ' R V} {a : Γ'} {s : Set Γ} (hs : s.IsPWO) (hxs : x.support s
ubseteq s) : ((o…
· 使用定理 `HahnSeries.support_add_subset`：support_add_subset (x y : R⟦Γ⟧) : (x + y)
.support subseteq x.support union y.support
· 使用定理 `HahnSeries.coeff_add'`：coeff_add' (x y : R⟦Γ⟧) : (x + y).coeff = x.coeff
 + y.coeff
· 使用定理 `HahnModule.of_symm_add`：∀ {Γ : Type u_1} {R : Type u_3} {V : Type u_5} [
inst : PartialOrder Γ] [inst_1 : SMul R V] [inst_2 : AddCommMonoid V]   (x y : H
ahnModule Γ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_smul [AddCommMonoid R] [SMulWithZero R V] {x y : R⟦Γ⟧}
    {z : HahnModule Γ' R V} (h : ∀ (r s : R) (u : V), (r + s) • u = r • u + s • u) :
    (x + y) • z = x • z + y • z := by
  ext a
  have hwf := x.isPWO_support.union y.isPWO_support
  rw [coeff_smul_left hwf, HahnSeries.coeff_add', of_symm_add]
  · simp_all only [Pi.add_apply, HahnSeries.coeff_add']
    rw [coeff_smul_left hwf Set.subset_union_right,
      coeff_smul_left hwf Set.subset_union_left]
    simp only [sum_add_distrib]
  · exact support_add_subset _ _
/-
**HahnModule.coeff_single_smul_vadd** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：coeff_single_smul_vadd [MulZeroClass R] [SMulWithZero R V] {r : R} {x : Ha
hnModule Γ' R V} {a : Γ'} {b : Γ} : ((of R).symm (HahnSeries.single b r • x)).co
eff (b +ᵥ a) = r • ((of R).symm x).coeff a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `HahnSeries.support_zero`：support_zero : support (0 : R⟦Γ⟧) = ∅
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.VAddAntidiagonal.congr_simp`：∀ {G : Type u_1} {P : Type u_2} [ins
t : VAdd G P] {s s_1 : Set G} (e_s : s = s_1) {t t_1 : Set P} (e_t : t = t_1)   
(a a_1 : P) (e_a : a = a…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.support_single_of_ne`：support_single_of_ne (h : r != 0) : sup
port (single a r) = {a}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsCancelVAdd.left_cancel`：∀ {G : Type u_11} {P : Type u_12} [inst : VAdd
 G P] [IsCancelVAdd G P] (a : G) (b c : P), a +ᵥ b = a +ᵥ c → b = c
· 使用定理 `instIsCancelVAddOfIsOrderedCancelVAdd`：∀ {G : Type u_1} {P : Type u_2} [
inst : PartialOrder G] [inst_1 : PartialOrder P] [inst_2 : VAdd G P]   [IsOrdere
dCancelVAdd G P], IsCancelV…
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `HahnSeries.coeff_single_same`：coeff_single_same (a : Γ) (r : R) : (singl
e a r).coeff a = r
-/
theorem coeff_single_smul_vadd [MulZeroClass R] [SMulWithZero R V] {r : R} {x : HahnModule Γ' R V}
    {a : Γ'} {b : Γ} :
    ((of R).symm (HahnSeries.single b r • x)).coeff (b +ᵥ a) = r • ((of R).symm x).coeff a := by
  by_cases hr : r = 0
  · simp_all only [map_zero, zero_smul, coeff_smul, HahnSeries.support_zero, HahnSeries.coeff_zero,
    sum_const_zero]
  simp only [hr, coeff_smul, coeff_smul, HahnSeries.support_single_of_ne, ne_eq, not_false_iff]
  by_cases hx : ((of R).symm x).coeff a = 0
  · simp only [hx, smul_zero]
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    ext ⟨a1, a2⟩
    simp only [notMem_empty, not_and, Set.mem_singleton_iff,
      mem_vaddAntidiagonal, iff_false]
    rintro rfl h2 h1
    rw [IsCancelVAdd.left_cancel a1 a2 a h1] at h2
    exact h2 hx
  trans ∑ ij ∈ {(b, a)},
    (HahnSeries.single b r).coeff ij.fst • ((of R).symm x).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [Set.mem_singleton_iff, Prod.mk_inj, mem_vaddAntidiagonal, mem_singleton]
    constructor
    · rintro ⟨rfl, _, h1⟩
      exact ⟨rfl, IsCancelVAdd.left_cancel a1 a2 a h1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, by exact hx, rfl⟩
  · simp
/-
**HahnModule.coeff_single_zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：coeff_single_zero_smul {Γ} [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ
 Γ'] [IsOrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {r : R} {x :
 HahnModule Γ' R V} {a : Γ'} : ((of R).symm ((HahnSeries.single 0 r : R⟦Γ⟧) • x)
).coeff a = r • ((of R).symm x).coeff a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `HahnModule.coeff_single_smul_vadd`：coeff_single_smul_vadd [MulZeroClass 
R] [SMulWithZero R V] {r : R} {x : HahnModule Γ' R V} {a : Γ'} {b : Γ} : ((of R)
.symm (HahnSeries.singl…
-/
theorem coeff_single_zero_smul {Γ} [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ']
    [IsOrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {r : R}
    {x : HahnModule Γ' R V} {a : Γ'} :
    ((of R).symm ((HahnSeries.single 0 r : R⟦Γ⟧) • x)).coeff a =
    r • ((of R).symm x).coeff a := by
  nth_rw 1 [← zero_vadd Γ a]
  exact coeff_single_smul_vadd

@[simp]
/-
**HahnModule.single_zero_smul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：single_zero_smul_eq_smul (Γ) [AddCommMonoid Γ] [PartialOrder Γ] [AddAction
 Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {r : R} {x
 : HahnModule Γ' R V} : (HahnSeries.single (0 : Γ) r) • x = r • x
参数：Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnModule.ext`：ext (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff 
= ((of R).symm y).coeff) : x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `HahnModule.coeff_single_zero_smul`：coeff_single_zero_smul {Γ} [AddCommMo
noid Γ] [PartialOrder Γ] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [MulZeroCla
ss R] [SMulWithZero R V…
-/
theorem single_zero_smul_eq_smul (Γ) [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ']
    [IsOrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {r : R}
    {x : HahnModule Γ' R V} :
    (HahnSeries.single (0 : Γ) r) • x = r • x := by
  ext
  exact coeff_single_zero_smul

@[simp]
/-
**HahnModule.zero_smul'** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：zero_smul' [Zero R] [SMulWithZero R V] {x : HahnModule Γ' R V} : (0 : R⟦Γ⟧
) • x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnModule.ext`：ext (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff 
= ((of R).symm y).coeff) : x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `HahnSeries.support_zero`：support_zero : support (0 : R⟦Γ⟧) = ∅
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.VAddAntidiagonal.congr_simp`：∀ {G : Type u_1} {P : Type u_2} [ins
t : VAdd G P] {s s_1 : Set G} (e_s : s = s_1) {t t_1 : Set P} (e_t : t = t_1)   
(a a_1 : P) (e_a : a = a…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_smul' [Zero R] [SMulWithZero R V] {x : HahnModule Γ' R V} : (0 : R⟦Γ⟧) • x = 0 := by
  ext
  simp [coeff_smul]

@[simp]
/-
**HahnModule.one_smul'** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：one_smul' {Γ} [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ'] [IsOrder
edCancelVAdd Γ Γ'] [MonoidWithZero R] [MulActionWithZero R V] {x : HahnModule Γ'
 R V} : (1 : R⟦Γ⟧) • x = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnModule.ext`：ext (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff 
= ((of R).symm y).coeff) : x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnModule.coeff_single_zero_smul`：coeff_single_zero_smul {Γ} [AddCommMo
noid Γ] [PartialOrder Γ] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [MulZeroCla
ss R] [SMulWithZero R V…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem one_smul' {Γ} [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ']
    [MonoidWithZero R] [MulActionWithZero R V] {x : HahnModule Γ' R V} : (1 : R⟦Γ⟧) • x = x := by
  ext g
  exact coeff_single_zero_smul.trans (one_smul R (x.coeff g))
/-
**HahnModule.support_smul_subset_vadd_support'** 是 Mathlib 中的一个定理，位于命名空间 `HahnMo
dule`。
形式化陈述：support_smul_subset_vadd_support' [MulZeroClass R] [SMulWithZero R V] {x :
 R⟦Γ⟧} {y : HahnModule Γ' R V} : ((of R).symm (x • y)).support subseteq x.suppor
t +ᵥ ((of R).symm y).support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.support_vaddAntidiagonal_subset_vadd`：∀ {G : Type u_1} {P : Type 
u_2} [inst : VAdd G P] {s : Set G} {t : Set P}   (hst : ∀ (a : P), (s.vaddAntidi
agonal t a).Finite), {a | (Finset…
-/
theorem support_smul_subset_vadd_support' [MulZeroClass R] [SMulWithZero R V] {x : R⟦Γ⟧}
    {y : HahnModule Γ' R V} :
    ((of R).symm (x • y)).support ⊆ x.support +ᵥ ((of R).symm y).support := by
  refine Set.Subset.trans (fun x hx => ?_) (support_vaddAntidiagonal_subset_vadd
    fun a ↦ Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support ((of R).symm y).isPWO_support a)
  simp only [Set.mem_ofPred_eq]
  contrapose! hx
  simp [coeff_smul, hx]
/-
**HahnModule.support_smul_subset_vadd_support** 是 Mathlib 中的一个定理，位于命名空间 `HahnMod
ule`。
形式化陈述：support_smul_subset_vadd_support [MulZeroClass R] [SMulWithZero R V] {x : 
R⟦Γ⟧} {y : HahnModule Γ' R V} : ((of R).symm (x • y)).support subseteq x.support
 +ᵥ ((of R).symm y).support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnModule.support_smul_subset_vadd_support'`：support_smul_subset_vadd_s
upport' [MulZeroClass R] [SMulWithZero R V] {x : R⟦Γ⟧} {y : HahnModule Γ' R V} :
 ((of R).symm (x • y)).support sub…
-/
theorem support_smul_subset_vadd_support [MulZeroClass R] [SMulWithZero R V] {x : R⟦Γ⟧}
    {y : HahnModule Γ' R V} :
    ((of R).symm (x • y)).support ⊆ x.support +ᵥ ((of R).symm y).support := by
  exact support_smul_subset_vadd_support'
/-
**HahnModule.orderTop_vAdd_le_orderTop_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnModul
e`。
形式化陈述：orderTop_vAdd_le_orderTop_smul {Γ Γ'} [LinearOrder Γ] [LinearOrder Γ'] [VA
dd Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {x : R⟦Γ
⟧} [VAdd (WithTop Γ) (WithTop Γ')] {y : HahnModule Γ' R V} (h : forall (γ : Γ) (
γ' : Γ'), γ +ᵥ γ' = (γ : WithTop Γ) +ᵥ (γ' : WithTop Γ')) : x.orderTop +ᵥ ((of R
).symm y).orderTop <= ((of R).symm (x • y)).orderTop
参数：WithTop Γ；WithTop Γ'；h : forall (γ : Γ) (γ' : Γ'), γ +ᵥ γ' = (γ : WithTop Γ) 
+ᵥ (γ' : WithTop Γ')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `HahnModule.zero_smul'`：zero_smul' [Zero R] [SMulWithZero R V] {x : HahnM
odule Γ' R V} : (0 : R⟦Γ⟧) • x = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.IsWF.vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : LinearOrder G] [i
nst_1 : LinearOrder P] [inst_2 : VAdd G P] [IsOrderedVAdd G P]   {s : Set G} {t 
: S…
· 使用定理 `IsOrderedCancelVAdd.toIsOrderedVAdd`：∀ {G : Type u_3} {P : Type u_4} {in
st : LE G} {inst_1 : LE P} {inst_2 : VAdd G P} [self : IsOrderedCancelVAdd G P],
   IsOrderedVAdd G P
· 使用定理 `Set.Nonempty.vadd`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {s 
: Set α} {t : Set β}, s.Nonempty → t.Nonempty → (s +ᵥ t).Nonempty
· 使用定理 `Set.IsWF.min_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : LinearOrder G
] [inst_1 : LinearOrder P] [inst_2 : VAdd G P]   [inst_3 : IsOrderedVAdd G P] {s
 : Set …
· 使用定理 `OrderTop.le_top`：∀ {α : Type u} {inst : LE α} [self : OrderTop α] (a : α
), a ≤ ⊤
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `Set.IsWF.min_le_min_of_subset`：∀ {α : Type u_2} [inst : LinearOrder α] {
s t : Set α} {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty}, 
  s ⊆ t → ht.min ht…
· 使用定理 `HahnModule.support_smul_subset_vadd_support`：support_smul_subset_vadd_su
pport [MulZeroClass R] [SMulWithZero R V] {x : R⟦Γ⟧} {y : HahnModule Γ' R V} : (
(of R).symm (x • y)).support subs…
-/
theorem orderTop_vAdd_le_orderTop_smul {Γ Γ'} [LinearOrder Γ] [LinearOrder Γ'] [VAdd Γ Γ']
    [IsOrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {x : R⟦Γ⟧}
    [VAdd (WithTop Γ) (WithTop Γ')] {y : HahnModule Γ' R V}
    (h : ∀ (γ : Γ) (γ' : Γ'), γ +ᵥ γ' = (γ : WithTop Γ) +ᵥ (γ' : WithTop Γ')) :
    x.orderTop +ᵥ ((of R).symm y).orderTop ≤ ((of R).symm (x • y)).orderTop := by
  by_cases hx : x = 0; · simp_all
  by_cases hy : y = 0; · simp_all
  have hhy : ((of R).symm y) ≠ 0 := hy
  rw [HahnSeries.orderTop_of_ne_zero hx, HahnSeries.orderTop_of_ne_zero hhy, ← h,
      ← Set.IsWF.min_vadd]
  by_cases hxy : (of R).symm (x • y) = 0
  · rw [hxy, HahnSeries.orderTop_zero]
    exact OrderTop.le_top (α := WithTop Γ') _
  · rw [HahnSeries.orderTop_of_ne_zero hxy, WithTop.coe_le_coe]
    exact Set.IsWF.min_le_min_of_subset support_smul_subset_vadd_support
/-
**HahnModule.coeff_smul_order_add_order** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
形式化陈述：coeff_smul_order_add_order {Γ} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrdere
dCancelAddMonoid Γ] [Zero R] [SMulWithZero R V] (x : R⟦Γ⟧) (y : HahnModule Γ R V
) : ((of R).symm (x • y)).coeff (x.order + ((of R).symm y).order) = x.leadingCoe
ff • ((of R).symm y).leadingCoeff
参数：x : R⟦Γ⟧；y : HahnModule Γ R V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnModule.zero_smul'`：zero_smul' [Zero R] [SMulWithZero R V] {x : HahnM
odule Γ' R V} : (0 : R⟦Γ⟧) • x = 0
· 使用定理 `HahnSeries.order_zero`：order_zero : order (0 : R⟦Γ⟧) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HahnSeries.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧
) = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `HahnSeries.support_zero`：support_zero : support (0 : R⟦Γ⟧) = ∅
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.VAddAntidiagonal.congr_simp`：∀ {G : Type u_1} {P : Type u_2} [ins
t : VAdd G P] {s s_1 : Set G} (e_s : s = s_1) {t t_1 : Set P} (e_t : t = t_1)   
(a a_1 : P) (e_a : a = a…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `HahnModule.coeff_smul`：coeff_smul (x : R⟦Γ⟧) (y : HahnModule Γ' R V) (a 
: Γ') : ((of R).symm <| x • y).coeff a = ∑ ij in VAddAntidiagonal a (Set.VAddAnt
idiagonal.f…
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `HahnSeries.leadingCoeff_of_ne_zero`：leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (
hx : x != 0) : x.leadingCoeff = x.coeff (x.orderTop.untop <| orderTop_ne_top.2 h
x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
（共 37 条，此处仅展示前 30 条）
-/
theorem coeff_smul_order_add_order {Γ}
    [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Zero R]
    [SMulWithZero R V] (x : R⟦Γ⟧) (y : HahnModule Γ R V) :
    ((of R).symm (x • y)).coeff (x.order + ((of R).symm y).order) =
    x.leadingCoeff • ((of R).symm y).leadingCoeff := by
  by_cases hx : x = (0 : R⟦Γ⟧); · simp [HahnSeries.coeff_zero, hx]
  by_cases hy : (of R).symm y = 0; · simp [hy, coeff_smul]
  rw [HahnSeries.order_of_ne hx, HahnSeries.order_of_ne hy, coeff_smul,
    HahnSeries.leadingCoeff_of_ne_zero hx, HahnSeries.leadingCoeff_of_ne_zero hy, ← vadd_eq_add,
    Finset.vaddAntidiagonal_min_vadd_min, Finset.sum_singleton]
  simp [HahnSeries.orderTop, hx, hy]

end DistribSMul

end HahnModule

namespace HahnSeries

section mul

variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] : Mul R⟦Γ⟧ where
  mul x y := (HahnModule.of R).symm (x • HahnModule.of R y)
/-
**HahnSeries.of_symm_smul_of_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：of_symm_smul_of_eq_mul [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} : (HahnM
odule.of R).symm (x • HahnModule.of R y) = x * y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
-/
theorem of_symm_smul_of_eq_mul [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} :
    (HahnModule.of R).symm (x • HahnModule.of R y) = x * y := rfl
/-
**HahnSeries.coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_mul [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} {a : Γ} : (x * y).coe
ff a = ∑ ij in antidiagonal x.isPWO_support y.isPWO_support a, x.coeff ij.fst * 
y.coeff ij.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_mul [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} {a : Γ} :
    (x * y).coeff a =
      ∑ ij ∈ antidiagonal x.isPWO_support y.isPWO_support a, x.coeff ij.fst * y.coeff ij.snd :=
  rfl
/-
**HahnSeries.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [inst : AddCommMonoid Γ] [i
nst_1 : PartialOrder Γ]   [inst_2 : IsOrderedCancelAddMonoid Γ] [inst_3 : NonUni
talNonAssocSemiring R] [inst_4 : NonUnitalNonAssocSemiring S]   (f : R →ₙ+* S) {
x y : HahnSeries Γ R}, (x * y).map f = x.map f * y.map f
参数：f : R →ₙ+* S；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.map_coeff`：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [in
st : PartialOrder Γ] [inst_1 : Zero R] [inst_2 : Zero S]   (x : HahnSeries Γ R) 
{F : Type …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_eq_zero_of_left`：mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) :
 a * b = 0
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
protected lemma map_mul [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S)
    {x y : R⟦Γ⟧} : (x * y).map f = (x.map f : S⟦Γ⟧) * (y.map f) := by
  ext
  simp only [map_coeff, coeff_mul, map_sum, map_mul]
  refine Eq.symm (sum_subset (fun gh hgh => ?_) (fun gh hgh hz => ?_))
  · simp_all only [mem_antidiagonal, mem_support, map_coeff, ne_eq, and_true]
    exact ⟨fun h => hgh.1 (map_zero f ▸ congrArg f h), fun h => hgh.2.1 (map_zero f ▸ congrArg f h)⟩
  · simp_all only [mem_antidiagonal, mem_support, ne_eq, map_coeff, and_true,
      not_and, not_not]
    by_cases h : f (x.coeff gh.1) = 0
    · exact mul_eq_zero_of_left h (f (y.coeff gh.2))
    · exact mul_eq_zero_of_right (f (x.coeff gh.1)) (hz h)
/-
**HahnSeries.coeff_mul_left'** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_mul_left' [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} {a : Γ} {s : Se
t Γ} (hs : s.IsPWO) (hxs : x.support subseteq s) : (x * y).coeff a = ∑ ij in ant
idiagonal hs y.isPWO_support a, x.coeff ij.fst * y.coeff ij.snd
参数：hs : s.IsPWO；hxs : x.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnModule.coeff_smul_left`：coeff_smul_left [SMulWithZero R V] {x : R⟦Γ⟧
} {y : HahnModule Γ' R V} {a : Γ'} {s : Set Γ} (hs : s.IsPWO) (hxs : x.support s
ubseteq s) : ((o…
-/
theorem coeff_mul_left' [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} {a : Γ} {s : Set Γ}
    (hs : s.IsPWO) (hxs : x.support ⊆ s) :
    (x * y).coeff a =
      ∑ ij ∈ antidiagonal hs y.isPWO_support a, x.coeff ij.fst * y.coeff ij.snd :=
  HahnModule.coeff_smul_left hs hxs
/-
**HahnSeries.coeff_mul_right'** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_mul_right' [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} {a : Γ} {s : S
et Γ} (hs : s.IsPWO) (hys : y.support subseteq s) : (x * y).coeff a = ∑ ij in an
tidiagonal x.isPWO_support hs a, x.coeff ij.fst * y.coeff ij.snd
参数：hs : s.IsPWO；hys : y.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnModule.coeff_smul_right`：coeff_smul_right [SMulZeroClass R V] {x : R
⟦Γ⟧} {y : HahnModule Γ' R V} {a : Γ'} {s : Set Γ'} (hs : s.IsPWO) (hys : ((of R)
.symm y).support …
-/
theorem coeff_mul_right' [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} {a : Γ} {s : Set Γ}
    (hs : s.IsPWO) (hys : y.support ⊆ s) :
    (x * y).coeff a =
      ∑ ij ∈ antidiagonal x.isPWO_support hs a, x.coeff ij.fst * y.coeff ij.snd :=
  HahnModule.coeff_smul_right hs hys
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] : Distrib R⟦Γ⟧ where
  left_distrib x y z := by
    simp only [← of_symm_smul_of_eq_mul]
    exact HahnModule.smul_add x y z
  right_distrib x y z := by
    simp only [← of_symm_smul_of_eq_mul]
    refine HahnModule.add_smul ?_
    simp only [smul_eq_mul]
    exact add_mul
/-
**HahnSeries.coeff_single_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_single_mul_add [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a :
 Γ} {b : Γ} : (single b r * x).coeff (a + b) = r * x.coeff a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.of_symm_smul_of_eq_mul`：of_symm_smul_of_eq_mul [NonUnitalNonA
ssocSemiring R] {x y : R⟦Γ⟧} : (HahnModule.of R).symm (x • HahnModule.of R y) = 
x * y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `HahnModule.coeff_single_smul_vadd`：coeff_single_smul_vadd [MulZeroClass 
R] [SMulWithZero R V] {r : R} {x : HahnModule Γ' R V} {a : Γ'} {b : Γ} : ((of R)
.symm (HahnSeries.singl…
-/
theorem coeff_single_mul_add [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ}
    {b : Γ} : (single b r * x).coeff (a + b) = r * x.coeff a := by
  rw [← of_symm_smul_of_eq_mul, add_comm, ← vadd_eq_add]
  exact HahnModule.coeff_single_smul_vadd
/-
**HahnSeries.coeff_mul_single_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_mul_single_add [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a :
 Γ} {b : Γ} : (x * single b r).coeff (a + b) = x.coeff a * r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `HahnSeries.support_zero`：support_zero : support (0 : R⟦Γ⟧) = ∅
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.antidiagonal.congr_simp`：∀ {α : Type u_1} [inst : AddCommMonoid α
] [inst_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   {s s_1 : Set
 α} (e_s : s = s_1) …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.support_single_of_ne`：support_single_of_ne (h : r != 0) : sup
port (single a r) = {a}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 33 条，此处仅展示前 30 条）
-/
theorem coeff_mul_single_add [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ}
    {b : Γ} : (x * single b r).coeff (a + b) = x.coeff a * r := by
  by_cases hr : r = 0
  · simp [hr, coeff_mul]
  simp only [hr, coeff_mul, support_single_of_ne, Ne, not_false_iff]
  by_cases hx : x.coeff a = 0
  · simp only [hx, zero_mul]
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    ext ⟨a1, a2⟩
    simp only [notMem_empty, not_and, Set.mem_singleton_iff,
      mem_antidiagonal, iff_false]
    rintro h2 rfl h1
    rw [← add_right_cancel h1] at hx
    exact h2 hx
  trans ∑ ij ∈ {(a, b)}, x.coeff ij.fst * (single b r).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [Set.mem_singleton_iff, Prod.mk_inj, mem_antidiagonal, mem_singleton]
    constructor
    · rintro ⟨_, rfl, h1⟩
      exact ⟨add_right_cancel h1, rfl⟩
    · rintro ⟨rfl, rfl⟩
      simp [hx]
  · simp
/-
**HahnSeries.coeff_single_mul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_single_mul [NonUnitalNonAssocSemiring R] [PartialOrder Γ'] [AddCommG
roup Γ'] [IsOrderedAddMonoid Γ'] {r : R} {x : R⟦Γ'⟧} {a b : Γ'} : (single b r * 
x).coeff a = r * x.coeff (a - b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `HahnSeries.coeff_single_mul_add`：coeff_single_mul_add [NonUnitalNonAssoc
Semiring R] {r : R} {x : R⟦Γ⟧} {a : Γ} {b : Γ} : (single b r * x).coeff (a + b) 
= r * x.coeff a
-/
theorem coeff_single_mul [NonUnitalNonAssocSemiring R] [PartialOrder Γ'] [AddCommGroup Γ']
    [IsOrderedAddMonoid Γ'] {r : R} {x : R⟦Γ'⟧} {a b : Γ'} :
    (single b r * x).coeff a = r * x.coeff (a - b) := by
  simpa using coeff_single_mul_add (a := a - b) (b := b)
/-
**HahnSeries.coeff_mul_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_mul_single [NonUnitalNonAssocSemiring R] [PartialOrder Γ'] [AddCommG
roup Γ'] [IsOrderedAddMonoid Γ'] {r : R} {x : R⟦Γ'⟧} {a b : Γ'} : (x * single b 
r).coeff a = x.coeff (a - b) * r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `HahnSeries.coeff_mul_single_add`：coeff_mul_single_add [NonUnitalNonAssoc
Semiring R] {r : R} {x : R⟦Γ⟧} {a : Γ} {b : Γ} : (x * single b r).coeff (a + b) 
= x.coeff a * r
-/
theorem coeff_mul_single [NonUnitalNonAssocSemiring R] [PartialOrder Γ'] [AddCommGroup Γ']
    [IsOrderedAddMonoid Γ'] {r : R} {x : R⟦Γ'⟧} {a b : Γ'} :
    (x * single b r).coeff a = x.coeff (a - b) * r := by
  simpa using coeff_mul_single_add (a := a - b) (b := b)

@[simp]
/-
**HahnSeries.coeff_mul_single_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_mul_single_zero [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a 
: Γ} : (x * single 0 r).coeff a = x.coeff a * r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `HahnSeries.coeff_mul_single_add`：coeff_mul_single_add [NonUnitalNonAssoc
Semiring R] {r : R} {x : R⟦Γ⟧} {a : Γ} {b : Γ} : (x * single b r).coeff (a + b) 
= x.coeff a * r
-/
theorem coeff_mul_single_zero [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ} :
    (x * single 0 r).coeff a = x.coeff a * r := by rw [← add_zero a, coeff_mul_single_add, add_zero]
/-
**HahnSeries.coeff_single_zero_mul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_single_zero_mul [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a 
: Γ} : ((single 0 r : R⟦Γ⟧) * x).coeff a = r * x.coeff a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `HahnSeries.coeff_single_mul_add`：coeff_single_mul_add [NonUnitalNonAssoc
Semiring R] {r : R} {x : R⟦Γ⟧} {a : Γ} {b : Γ} : (single b r * x).coeff (a + b) 
= r * x.coeff a
-/
theorem coeff_single_zero_mul [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ} :
    ((single 0 r : R⟦Γ⟧) * x).coeff a = r * x.coeff a := by
  rw [← add_zero a, coeff_single_mul_add, add_zero]

@[simp]
/-
**HahnSeries.single_zero_mul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_zero_mul_eq_smul [Semiring R] {r : R} {x : R⟦Γ⟧} : single 0 r * x =
 r • x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HahnSeries.coeff_single_zero_mul`：coeff_single_zero_mul [NonUnitalNonAss
ocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ} : ((single 0 r : R⟦Γ⟧) * x).coeff a = r
 * x.coeff a
-/
theorem single_zero_mul_eq_smul [Semiring R] {r : R} {x : R⟦Γ⟧} : single 0 r * x = r • x := by
  ext
  exact coeff_single_zero_mul
/-
**HahnSeries.support_mul_subset** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_mul_subset [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} : support (x
 * y) subseteq support x + support y
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.of_symm_smul_of_eq_mul`：of_symm_smul_of_eq_mul [NonUnitalNonA
ssocSemiring R] {x y : R⟦Γ⟧} : (HahnModule.of R).symm (x • HahnModule.of R y) = 
x * y
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `HahnModule.support_smul_subset_vadd_support`：support_smul_subset_vadd_su
pport [MulZeroClass R] [SMulWithZero R V] {x : R⟦Γ⟧} {y : HahnModule Γ' R V} : (
(of R).symm (x • y)).support subs…
-/
theorem support_mul_subset [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} :
    support (x * y) ⊆ support x + support y := by
  rw [← of_symm_smul_of_eq_mul, ← vadd_eq_add]
  exact HahnModule.support_smul_subset_vadd_support
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring R⟦Γ⟧ where
  zero_mul _ := by
    ext
    simp [coeff_mul]
  mul_zero _ := by
    ext
    simp [coeff_mul]

end mul

section orderLemmas

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [NonUnitalNonAssocSemiring R]

/-
**HahnSeries.coeff_mul_order_add_order** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_mul_order_add_order (x y : R⟦Γ⟧) : (x * y).coeff (x.order + y.order)
 = x.leadingCoeff * y.leadingCoeff
参数：x y : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnModule.coeff_smul_order_add_order`：coeff_smul_order_add_order {Γ} [A
ddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Zero R] [SMulWithZ
ero R V] (x : R⟦Γ⟧) (y : Ha…
-/
theorem coeff_mul_order_add_order (x y : R⟦Γ⟧) :
    (x * y).coeff (x.order + y.order) = x.leadingCoeff * y.leadingCoeff := by
  simp only [← of_symm_smul_of_eq_mul]
  exact HahnModule.coeff_smul_order_add_order x y
/-
**HahnSeries.orderTop_mul_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_mul_of_ne_zero {x y : R⟦Γ⟧} (h : x.leadingCoeff * y.leadingCoeff 
!= 0) : (x * y).orderTop = x.orderTop + y.orderTop
参数：h : x.leadingCoeff * y.leadingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `HahnSeries.coeff_mul_order_add_order`：coeff_mul_order_add_order (x y : R
⟦Γ⟧) : (x * y).coeff (x.order + y.order) = x.leadingCoeff * y.leadingCoeff
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.order_eq_orderTop_of_ne_zero`：order_eq_orderTop_of_ne_zero (h
x : x != 0) : order x = orderTop x
· 使用定理 `WithTop.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用定理 `WithTop.coe_eq_coe`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `HahnSeries.order_le_of_coeff_ne_zero`：order_le_of_coeff_ne_zero {Γ} [Zer
o Γ] [LinearOrder Γ] {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : x.order <= g
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `Set.IsWF.add`：∀ {α : Type u_1} {s t : Set α} [inst : AddCommMonoid α] [i
nst_1 : LinearOrder α] [IsOrderedCancelAddMonoid α],   s.IsWF → t.IsWF → (s + t)
.I…
· 使用定理 `Set.Nonempty.add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α}, s.Nonem
pty → t.Nonempty → (s + t).Nonempty
· 使用定理 `Set.IsWF.min_add`：∀ {α : Type u_1} {s t : Set α} [inst : AddCommMonoid α
] [inst_1 : LinearOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   (hs : s.IsWF)
 (ht :…
· 使用定理 `Set.IsWF.min_le_min_of_subset`：∀ {α : Type u_2} [inst : LinearOrder α] {
s t : Set α} {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty}, 
  s ⊆ t → ht.min ht…
· 使用定理 `HahnSeries.support_mul_subset`：support_mul_subset [NonUnitalNonAssocSemi
ring R] {x y : R⟦Γ⟧} : support (x * y) subseteq support x + support y
-/
theorem orderTop_mul_of_ne_zero {x y : R⟦Γ⟧} (h : x.leadingCoeff * y.leadingCoeff ≠ 0) :
    (x * y).orderTop = x.orderTop + y.orderTop := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  have : (x * y).coeff (x.order + y.order) ≠ 0 := by rwa [coeff_mul_order_add_order x y]
  have hxy : x * y ≠ 0 := fun h ↦ (by simp [h] at this)
  rw [← order_eq_orderTop_of_ne_zero hx, ← order_eq_orderTop_of_ne_zero hy,
    ← order_eq_orderTop_of_ne_zero hxy, ← WithTop.coe_add, WithTop.coe_eq_coe]
  refine le_antisymm (order_le_of_coeff_ne_zero this) ?_
  rw [HahnSeries.order_of_ne hx, HahnSeries.order_of_ne hy, HahnSeries.order_of_ne hxy,
    ← Set.IsWF.min_add]
  exact Set.IsWF.min_le_min_of_subset support_mul_subset

@[deprecated (since := "2026-01-02")]
alias orderTop_mul_of_nonzero := orderTop_mul_of_ne_zero

@[simp]
/-
**HahnSeries.orderTop_mul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_mul (x y : R⟦Γ⟧) [NoZeroDivisors R] : (x * y).orderTop = x.orderT
op + y.orderTop
参数：x y : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `HahnSeries.orderTop_mul_of_ne_zero`：orderTop_mul_of_ne_zero {x y : R⟦Γ⟧}
 (h : x.leadingCoeff * y.leadingCoeff != 0) : (x * y).orderTop = x.orderTop + y.
orderTop
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem orderTop_mul (x y : R⟦Γ⟧) [NoZeroDivisors R] :
    (x * y).orderTop = x.orderTop + y.orderTop := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  apply orderTop_mul_of_ne_zero
  simp_all
/-
**HahnSeries.orderTop_add_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_add_le_mul {x y : R⟦Γ⟧} : x.orderTop + y.orderTop <= (x * y).orde
rTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `HahnModule.orderTop_vAdd_le_orderTop_smul`：orderTop_vAdd_le_orderTop_smu
l {Γ Γ'} [LinearOrder Γ] [LinearOrder Γ'] [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ']
 [MulZeroClass R] [SMulWithZero…
-/
theorem orderTop_add_le_mul {x y : R⟦Γ⟧} : x.orderTop + y.orderTop ≤ (x * y).orderTop := by
  rw [← smul_eq_mul]
  exact HahnModule.orderTop_vAdd_le_orderTop_smul fun i j ↦ rfl
/-
**HahnSeries.order_mul_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：order_mul_of_ne_zero {x y : R⟦Γ⟧} (h : x.leadingCoeff * y.leadingCoeff != 
0) : (x * y).order = x.order + y.order
参数：h : x.leadingCoeff * y.leadingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧
) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `HahnSeries.coeff_mul_order_add_order`：coeff_mul_order_add_order (x y : R
⟦Γ⟧) : (x * y).coeff (x.order + y.order) = x.leadingCoeff * y.leadingCoeff
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `HahnSeries.order_le_of_coeff_ne_zero`：order_le_of_coeff_ne_zero {Γ} [Zer
o Γ] [LinearOrder Γ] {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : x.order <= g
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `HahnSeries.leadingCoeff_ne_zero`：leadingCoeff_ne_zero {x : R⟦Γ⟧} : x.lea
dingCoeff != 0 ↔ x != 0
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `HahnSeries.ne_zero_of_coeff_ne_zero`：ne_zero_of_coeff_ne_zero {x : R⟦Γ⟧}
 {g : Γ} (h : x.coeff g != 0) : x != 0
· 使用定理 `Set.IsWF.add`：∀ {α : Type u_1} {s t : Set α} [inst : AddCommMonoid α] [i
nst_1 : LinearOrder α] [IsOrderedCancelAddMonoid α],   s.IsWF → t.IsWF → (s + t)
.I…
· 使用定理 `Set.Nonempty.add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α}, s.Nonem
pty → t.Nonempty → (s + t).Nonempty
· 使用定理 `Set.IsWF.min_add`：∀ {α : Type u_1} {s t : Set α} [inst : AddCommMonoid α
] [inst_1 : LinearOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   (hs : s.IsWF)
 (ht :…
· 使用定理 `Set.IsWF.min_le_min_of_subset`：∀ {α : Type u_2} [inst : LinearOrder α] {
s t : Set α} {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty}, 
  s ⊆ t → ht.min ht…
· 使用定理 `HahnSeries.support_mul_subset`：support_mul_subset [NonUnitalNonAssocSemi
ring R] {x y : R⟦Γ⟧} : support (x * y) subseteq support x + support y
-/
theorem order_mul_of_ne_zero {x y : R⟦Γ⟧}
    (h : x.leadingCoeff * y.leadingCoeff ≠ 0) : (x * y).order = x.order + y.order := by
  have hx : x.leadingCoeff ≠ 0 := by aesop
  have hy : y.leadingCoeff ≠ 0 := by aesop
  have hxy : (x * y).coeff (x.order + y.order) ≠ 0 :=
    ne_of_eq_of_ne (coeff_mul_order_add_order x y) h
  refine le_antisymm (order_le_of_coeff_ne_zero
    (Eq.mpr (congrArg (fun _a ↦ _a ≠ 0) (coeff_mul_order_add_order x y)) h)) ?_
  rw [order_of_ne <| leadingCoeff_ne_zero.mp hx, order_of_ne <| leadingCoeff_ne_zero.mp hy,
    order_of_ne <| ne_zero_of_coeff_ne_zero hxy, ← Set.IsWF.min_add]
  exact Set.IsWF.min_le_min_of_subset support_mul_subset

@[deprecated (since := "2026-01-02")]
alias order_mul_of_nonzero := order_mul_of_ne_zero
/-
**HahnSeries.leadingCoeff_mul_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_mul_of_ne_zero {x y : R⟦Γ⟧} (h : x.leadingCoeff * y.leadingCo
eff != 0) : (x * y).leadingCoeff = x.leadingCoeff * y.leadingCoeff
参数：h : x.leadingCoeff * y.leadingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.leadingCoeff_eq`：leadingCoeff_eq {x : R⟦Γ⟧} : x.leadingCoeff 
= x.coeff x.order
· 使用定理 `HahnSeries.order_mul_of_ne_zero`：order_mul_of_ne_zero {x y : R⟦Γ⟧} (h : 
x.leadingCoeff * y.leadingCoeff != 0) : (x * y).order = x.order + y.order
· 使用定理 `HahnSeries.coeff_mul_order_add_order`：coeff_mul_order_add_order (x y : R
⟦Γ⟧) : (x * y).coeff (x.order + y.order) = x.leadingCoeff * y.leadingCoeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_mul_of_ne_zero {x y : R⟦Γ⟧} (h : x.leadingCoeff * y.leadingCoeff ≠ 0) :
    (x * y).leadingCoeff = x.leadingCoeff * y.leadingCoeff := by
  simp only [leadingCoeff_eq, order_mul_of_ne_zero h, coeff_mul_order_add_order]

@[deprecated (since := "2026-01-02")]
alias leadingCoeff_mul_of_nonzero := leadingCoeff_mul_of_ne_zero

@[simp]
/-
**HahnSeries.leadingCoeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_mul (x y : R⟦Γ⟧) [NoZeroDivisors R] : (x * y).leadingCoeff = 
x.leadingCoeff * y.leadingCoeff
参数：x y : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HahnSeries.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧
) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `HahnSeries.leadingCoeff_mul_of_ne_zero`：leadingCoeff_mul_of_ne_zero {x y
 : R⟦Γ⟧} (h : x.leadingCoeff * y.leadingCoeff != 0) : (x * y).leadingCoeff = x.l
eadingCoeff * y.leadingCoeff
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem leadingCoeff_mul (x y : R⟦Γ⟧) [NoZeroDivisors R] :
    (x * y).leadingCoeff = x.leadingCoeff * y.leadingCoeff := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  apply leadingCoeff_mul_of_ne_zero
  simp_all
/-
**HahnSeries.order_single_mul_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries
`。
形式化陈述：order_single_mul_of_isRegular {g : Γ} {r : R} (hr : IsRegular r) {x : R⟦Γ⟧
} (hx : x != 0) : (((single g) r) * x).order = g + x.order
参数：hr : IsRegular r；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `HahnSeries.instSubsingleton`：∀ {Γ : Type u_1} {R : Type u_3} [inst : Par
tialOrder Γ] [inst_1 : Zero R] [Subsingleton R],   Subsingleton (HahnSeries Γ R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.leadingCoeff_of_single`：leadingCoeff_of_single {a : Γ} {r : R
} : leadingCoeff (single a r) = r
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `IsLeftRegular.mul_left_eq_zero_iff`：∀ {R : Type u_1} [inst : MulZeroClas
s R] {a b : R}, IsLeftRegular b → (b * a = 0 ↔ a = 0)
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `HahnSeries.leadingCoeff_eq_zero`：leadingCoeff_eq_zero {x : R⟦Γ⟧} : x.lea
dingCoeff = 0 ↔ x = 0
· 使用定理 `HahnSeries.order_mul_of_ne_zero`：order_mul_of_ne_zero {x y : R⟦Γ⟧} (h : 
x.leadingCoeff * y.leadingCoeff != 0) : (x * y).order = x.order + y.order
· 使用定理 `HahnSeries.order_single`：order_single (h : r != 0) : (single a r).order 
= a
· 使用定理 `IsRegular.ne_zero`：IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) :
 a != 0
-/
theorem order_single_mul_of_isRegular {g : Γ} {r : R} (hr : IsRegular r)
    {x : R⟦Γ⟧} (hx : x ≠ 0) : (((single g) r) * x).order = g + x.order := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact (hx <| Subsingleton.eq_zero x).elim
  have hrx : ((single g) r).leadingCoeff * x.leadingCoeff ≠ 0 := by
    rwa [leadingCoeff_of_single, ne_eq, hr.left.mul_left_eq_zero_iff, leadingCoeff_eq_zero]
  rw [order_mul_of_ne_zero hrx, order_single <| IsRegular.ne_zero hr]

end orderLemmas

section Ring

variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

set_option backward.privateInPublic true in
/-
**HahnSeries.mul_assoc'** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_assoc' [NonUnitalSemiring R] (x y z : R⟦Γ⟧) : x * y * z = x * (y * z) := by
  ext b
  rw [coeff_mul_left' (x.isPWO_support.add y.isPWO_support) support_mul_subset,
    coeff_mul_right' (y.isPWO_support.add z.isPWO_support) support_mul_subset]
  simp only [coeff_mul, sum_mul, mul_sum, sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;>
    aesop (add safe Set.add_mem_add) (add simp [add_assoc, mul_assoc])

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSemiring R] : NonUnitalSemiring R⟦Γ⟧ where
  mul_assoc := mul_assoc'
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocSemiring R] : NonAssocSemiring R⟦Γ⟧ where
  one_mul x := by
    ext
    exact coeff_single_zero_mul.trans (one_mul _)
  mul_one x := by
    ext
    exact coeff_mul_single_zero.trans (mul_one _)
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] : Semiring R⟦Γ⟧ where
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring R⟦Γ⟧ where
  __ : NonUnitalSemiring R⟦Γ⟧ := inferInstance
  mul_comm x y := by
    ext
    simp_rw [coeff_mul, mul_comm]
    exact Finset.sum_equiv (Equiv.prodComm _ _) (fun _ ↦ swap_mem_antidiagonal.symm) <| by simp
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring R] : CommSemiring R⟦Γ⟧ where
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing R⟦Γ⟧ where
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalRing R] : NonUnitalRing R⟦Γ⟧ where
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocRing R] : NonAssocRing R⟦Γ⟧ where
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring R] : Ring R⟦Γ⟧ where
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommRing R] : NonUnitalCommRing R⟦Γ⟧ where
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing R] : CommRing R⟦Γ⟧ where

end Ring

/-
**HahnSeries.orderTop_nsmul_le_orderTop_pow** 是 Mathlib 中的一个定理，位于命名空间 `HahnSerie
s`。
形式化陈述：orderTop_nsmul_le_orderTop_pow [AddCommMonoid Γ] [LinearOrder Γ] [IsOrdere
dCancelAddMonoid Γ] [Semiring R] {x : R⟦Γ⟧} {n : Nat} : n • x.orderTop <= (x ^ n
).orderTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.orderTop_one`：orderTop_one [Zero R] [One R] [NeZero (1 : R)] 
: orderTop (1 : R⟦Γ⟧) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `HahnSeries.orderTop_of_subsingleton`：orderTop_of_subsingleton [Subsingle
ton R] : x.orderTop = ⊤
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `one_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 1 • a = a
· 使用定理 `HahnSeries.orderTop_add_le_mul`：orderTop_add_le_mul {x y : R⟦Γ⟧} : x.ord
erTop + y.orderTop <= (x * y).orderTop
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem orderTop_nsmul_le_orderTop_pow [AddCommMonoid Γ] [LinearOrder Γ]
    [IsOrderedCancelAddMonoid Γ] [Semiring R] {x : R⟦Γ⟧} {n : ℕ} :
    n • x.orderTop ≤ (x ^ n).orderTop := by
  induction n with
  | zero =>
    simp only [zero_smul, pow_zero]
    by_cases h : NeZero (1 : R)
    · simp
    · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp fun _ ↦ h NeZero.one
      simp
  | succ n ih =>
    rw [add_nsmul, pow_add]
    calc
      n • x.orderTop + 1 • x.orderTop ≤ (x ^ n).orderTop + 1 • x.orderTop := by gcongr
      (x ^ n).orderTop + 1 • x.orderTop = (x ^ n).orderTop + x.orderTop := by rw [one_nsmul]
      (x ^ n).orderTop + x.orderTop ≤ (x ^ n * x).orderTop := orderTop_add_le_mul
      (x ^ n * x).orderTop ≤ (x ^ n * x ^ 1).orderTop := by rw [pow_one]
/-
**HahnSeries.orderTop_self_sub_one_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries
`。
形式化陈述：orderTop_self_sub_one_pos_iff [LinearOrder Γ] [Zero Γ] [NonAssocRing R] [N
ontrivial R] (x : R⟦Γ⟧) : 0 < (x - 1).orderTop ↔ x.orderTop = 0 ∧ x.leadingCoeff
 = 1
参数：x : R⟦Γ⟧。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `HahnSeries.orderTop_one`：orderTop_one [Zero R] [One R] [NeZero (1 : R)] 
: orderTop (1 : R⟦Γ⟧) = 0
· 使用定理 `HahnSeries.orderTop_add_eq_left`：orderTop_add_eq_left {Γ} [LinearOrder Γ
] {x y : R⟦Γ⟧} (hxy : x.orderTop < y.orderTop) : (x + y).orderTop = x.orderTop
· 使用定理 `HahnSeries.leadingCoeff_one`：leadingCoeff_one [MulZeroOneClass R] : (1 :
 R⟦Γ⟧).leadingCoeff = 1
· 使用定理 `HahnSeries.leadingCoeff_add_eq_left`：leadingCoeff_add_eq_left {Γ} [Linea
rOrder Γ] {x y : R⟦Γ⟧} (hxy : x.orderTop < y.orderTop) : (x + y).leadingCoeff = 
x.leadingCoeff
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.min_orderTop_le_orderTop_sub`：min_orderTop_le_orderTop_sub {Γ
} [LinearOrder Γ] {x y : R⟦Γ⟧} : min x.orderTop y.orderTop <= (x - y).orderTop
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `HahnSeries.orderTop_sub_ne`：orderTop_sub_ne {x y : R⟦Γ⟧} {g : Γ} (hxg : 
x.orderTop = g) (hyg : y.orderTop = g) (hxyc : x.leadingCoeff = y.leadingCoeff) 
: (x - y).orderT…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem orderTop_self_sub_one_pos_iff [LinearOrder Γ] [Zero Γ] [NonAssocRing R] [Nontrivial R]
    (x : R⟦Γ⟧) :
    0 < (x - 1).orderTop ↔ x.orderTop = 0 ∧ x.leadingCoeff = 1 := by
  constructor
  · intro hx
    constructor
    · rw [← sub_add_cancel x 1, add_comm, ← orderTop_one (R := R)]
      exact orderTop_add_eq_left (Γ := Γ) (R := R) (orderTop_one (R := R) (Γ := Γ) ▸ hx)
    · rw [← sub_add_cancel x 1, add_comm, ← leadingCoeff_one (Γ := Γ) (R := R)]
      exact leadingCoeff_add_eq_left (Γ := Γ) (R := R) (orderTop_one (R := R) (Γ := Γ) ▸ hx)
  · intro h
    refine lt_of_le_of_ne (le_of_eq_of_le (by simp_all)
      (min_orderTop_le_orderTop_sub (Γ := Γ) (R := R))) <| Ne.symm <|
      orderTop_sub_ne h.1 orderTop_one ?_
    rw [h.2, leadingCoeff_one]
/-
**HahnSeries.orderTop_sub_pos** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_sub_pos [PartialOrder Γ] [Zero Γ] [AddCommGroup R] [One R] {g : Γ
} (hg : 0 < g) (r : R) : 0 < ((1 + single g r) - 1).orderTop
参数：hg : 0 < g；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `HahnSeries.orderTop_single`：orderTop_single (h : r != 0) : (single a r).
orderTop = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem orderTop_sub_pos [PartialOrder Γ] [Zero Γ] [AddCommGroup R] [One R] {g : Γ} (hg : 0 < g)
    (r : R) :
    0 < ((1 + single g r) - 1).orderTop := by
  by_cases hr : r = 0 <;> simp [hr, hg]

/-- The group of invertible Hahn series close to 1, i.e., those series such that subtracting 1
  yields a series with strictly positive `orderTop`. -/
/-
**HahnSeries.orderTopSubOnePos** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：orderTopSubOnePos (Γ R) [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancel
AddMonoid Γ] [CommRing R] : Subgroup R⟦Γ⟧ˣ where carrier
参数：Γ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group of invertible Hahn series close to 1, i.e., those series such that sub
tracting 1
  yields a series with strictly positive `orderTop`.
-/
def orderTopSubOnePos (Γ R) [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [CommRing R] : Subgroup R⟦Γ⟧ˣ where
  carrier := { x : R⟦Γ⟧ˣ | 0 < (x.val - 1).orderTop}
  mul_mem' := by
    intro x y hx hy
    obtain (_ | _) := subsingleton_or_nontrivial R
    · simp
    · simp_all only [Set.mem_ofPred_eq, orderTop_self_sub_one_pos_iff]
      have h1 : x.val.leadingCoeff * y.val.leadingCoeff = 1 := by rw [hx.2, hy.2, mul_one]
      constructor
      · rw [Units.val_mul, orderTop_mul_of_ne_zero (by simp [h1]), hx.1, hy.1, add_zero]
      · rw [Units.val_mul, leadingCoeff_mul_of_ne_zero (h1 ▸ one_ne_zero), h1]
  one_mem' := by simp
  inv_mem' {y} h := by
    suffices 0 < (y.inv - 1).orderTop by exact this
    obtain (_ | _) := subsingleton_or_nontrivial R
    · simp
    · have : 0 < (y.val - 1).orderTop := h
      rw [orderTop_self_sub_one_pos_iff] at this
      have nz : y.val.leadingCoeff * y.inv.leadingCoeff ≠ 0 := by
        rw [this.2, one_mul]
        exact leadingCoeff_ne_zero.mpr (by simp)
      refine y.inv.orderTop_self_sub_one_pos_iff.mpr ⟨?_, ?_⟩
      · simpa [this.1, y.val_inv] using (orderTop_mul_of_ne_zero nz).symm
      · simpa [this.2, y.val_inv] using (leadingCoeff_mul_of_ne_zero nz).symm

@[simp]
/-
**HahnSeries.mem_orderTopSubOnePos_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：mem_orderTopSubOnePos_iff [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCanc
elAddMonoid Γ] [CommRing R] (x : R⟦Γ⟧ˣ) : x in orderTopSubOnePos Γ R ↔ 0 < (x.va
l - 1).orderTop
参数：x : R⟦Γ⟧ˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_orderTopSubOnePos_iff [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [CommRing R] (x : R⟦Γ⟧ˣ) :
    x ∈ orderTopSubOnePos Γ R ↔ 0 < (x.val - 1).orderTop := .rfl

end HahnSeries

namespace HahnModule
variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
variable [PartialOrder Γ'] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [AddCommMonoid V]

set_option backward.privateInPublic true in
/-
**HahnModule.mul_smul'** 是 Mathlib 中的一个定理，位于命名空间 `HahnModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_smul' [Semiring R] [Module R V] (x y : R⟦Γ⟧)
    (z : HahnModule Γ' R V) : (x * y) • z = x • (y • z) := by
  ext b
  rw [coeff_smul_left (x.isPWO_support.add y.isPWO_support)
    HahnSeries.support_mul_subset, coeff_smul_right
    (y.isPWO_support.vadd ((of R).symm z).isPWO_support) support_smul_subset_vadd_support]
  simp only [HahnSeries.coeff_mul, coeff_smul, sum_smul, smul_sum, sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l +ᵥ j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;>
    aesop (add safe [Set.vadd_mem_vadd, Set.add_mem_add]) (add simp [add_vadd, mul_smul])
/-
**HahnModule.instBaseModule** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
形式化陈述：instBaseModule [Semiring R] [Module R V] : Module R (HahnModule Γ' R V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBaseModule [Semiring R] [Module R V] : Module R (HahnModule Γ' R V) :=
  inferInstanceAs <| Module R V⟦Γ'⟧

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**HahnModule.instModule** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
形式化陈述：instModule [Semiring R] [Module R V] : Module R⟦Γ⟧ (HahnModule Γ' R V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.HahnSeries.Multiplication.0.HahnModule.mul_s
mul'`：∀ {Γ : Type u_1} {Γ' : Type u_2} {R : Type u_3} {V : Type u_5} [inst : Add
CommMonoid Γ] [inst_1 : PartialOrder Γ]   [inst_2 : IsOrderedCance…
-/
instance instModule [Semiring R] [Module R V] : Module R⟦Γ⟧
    (HahnModule Γ' R V) := {
  (inferInstance : DistribSMul R⟦Γ⟧ (HahnModule Γ' R V)) with
  mul_smul := mul_smul'
  one_smul := fun _ => one_smul'
  add_smul := fun _ _ _ => add_smul Module.add_smul
  zero_smul := fun _ => zero_smul' }
/-
**HahnModule.** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] {S : Type*} [Zero S] [SMul R S] [SMulWithZero R V] [SMulWithZero S V]
    [IsScalarTower R S V] : IsScalarTower R S V⟦Γ⟧ where
  smul_assoc r s a := by
    ext
    simp

set_option backward.isDefEq.respectTransparency false in
/-
**HahnModule.** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [Module R V] : IsScalarTower R R⟦Γ⟧ (HahnModule Γ' R V) where
  smul_assoc r x a := by
    rw [← HahnSeries.single_zero_mul_eq_smul, mul_smul', ← single_zero_smul_eq_smul Γ]

set_option backward.isDefEq.respectTransparency false in
/-
**HahnModule.SMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
形式化陈述：SMulCommClass [CommSemiring R] [Module R V] : SMulCommClass R R⟦Γ⟧ (HahnMo
dule Γ' R V) where smul_comm r x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnModule.single_zero_smul_eq_smul`：single_zero_smul_eq_smul (Γ) [AddCo
mmMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [MulZer
oClass R] [SMulWithZero R…
· 使用定理 `_private.Mathlib.RingTheory.HahnSeries.Multiplication.0.HahnModule.mul_s
mul'`：∀ {Γ : Type u_1} {Γ' : Type u_2} {R : Type u_3} {V : Type u_5} [inst : Add
CommMonoid Γ] [inst_1 : PartialOrder Γ]   [inst_2 : IsOrderedCance…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
instance SMulCommClass [CommSemiring R] [Module R V] :
    SMulCommClass R R⟦Γ⟧ (HahnModule Γ' R V) where
  smul_comm r x y := by
    rw [← single_zero_smul_eq_smul Γ, ← mul_smul', mul_comm, mul_smul', single_zero_smul_eq_smul Γ]
/-
**HahnModule.instIsTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `HahnModule`。
形式化陈述：instIsTorsionFree {Γ V : Type*} [Ring R] [IsDomain R] [AddCommGroup V] [Ad
dCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Module R V] [Module
.IsTorsionFree R V] : Module.IsTorsionFree R⟦Γ⟧ (HahnModule Γ R V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.IsTorsionFree.of_smul_eq_zero`：Module.IsTorsionFree.of_smul_eq_ze
ro [Nontrivial R] (h : forall (r : R) (m : M), r • m = 0 -> r = 0 ∨ m = 0) : IsT
orsionFree R M where isSMu…
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
· 使用定理 `HahnSeries.instNontrivialOfNonempty`：∀ {Γ : Type u_1} {R : Type u_3} [in
st : PartialOrder Γ] [inst_1 : Zero R] [Nonempty Γ] [Nontrivial R],   Nontrivial
 (HahnSeries Γ R)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `HahnModule.ext_iff`：∀ {Γ : Type u_1} {R : Type u_3} {V : Type u_5} [inst
 : PartialOrder Γ] [inst_1 : Zero V] [inst_2 : SMul R V]   {x y : HahnModule Γ R
 V}, x =…
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnModule.coeff_smul_order_add_order`：coeff_smul_order_add_order {Γ} [A
ddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Zero R] [SMulWithZ
ero R V] (x : R⟦Γ⟧) (y : Ha…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
instance instIsTorsionFree {Γ V : Type*} [Ring R] [IsDomain R] [AddCommGroup V] [AddCommMonoid Γ]
    [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Module R V] [Module.IsTorsionFree R V] :
    Module.IsTorsionFree R⟦Γ⟧ (HahnModule Γ R V) :=
  .of_smul_eq_zero fun x y hxy ↦ by
    contrapose! hxy
    rw [ne_eq, HahnModule.ext_iff, funext_iff, not_forall]
    exact ⟨x.order + ((of R).symm y).order, by simpa [coeff_smul_order_add_order]⟩

end HahnModule

namespace HahnSeries

section PartialOrder
variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R]

@[simp]
/-
**HahnSeries.single_mul_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_mul_single {a b : Γ} {r s : R} : single a r * single b s = single (
a + b) (r * s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.coeff_mul_single_add`：coeff_mul_single_add [NonUnitalNonAssoc
Semiring R] {r : R} {x : R⟦Γ⟧} {a : Γ} {b : Γ} : (x * single b r).coeff (a + b) 
= x.coeff a * r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.coeff_single_same`：coeff_single_same (a : Γ) (r : R) : (singl
e a r).coeff a = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.coeff_single_of_ne`：coeff_single_of_ne (h : b != a) : (single
 a r).coeff b = 0
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `HahnSeries.coeff_mul`：coeff_mul [NonUnitalNonAssocSemiring R] {x y : R⟦Γ
⟧} {a : Γ} : (x * y).coeff a = ∑ ij in antidiagonal x.isPWO_support y.isPWO_supp
ort a, x.c…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `HahnSeries.eq_of_mem_support_single`：eq_of_mem_support_single {b : Γ} (h
 : b in support (single a r)) : b = a
-/
theorem single_mul_single {a b : Γ} {r s : R} :
    single a r * single b s = single (a + b) (r * s) := by
  ext x
  by_cases h : x = a + b
  · rw [h, coeff_mul_single_add]
    simp
  · rw [coeff_single_of_ne h, coeff_mul, sum_eq_zero]
    simp_rw [mem_antidiagonal]
    rintro ⟨y, z⟩ ⟨hy, hz, rfl⟩
    rw [eq_of_mem_support_single hy, eq_of_mem_support_single hz] at h
    exact (h rfl).elim

end NonUnitalNonAssocSemiring

section Semiring

variable [Semiring R]

@[simp]
/-
**HahnSeries.single_pow** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_pow (a : Γ) (n : Nat) (r : R) : single a r ^ n = single (n • a) (r 
^ n)
参数：a : Γ；n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `HahnSeries.coeff_one`：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).co
eff a = if a = 0 then 1 else 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `HahnSeries.coeff_single`：coeff_single : (single a r).coeff b = if b = a 
then r else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `HahnSeries.single_mul_single`：single_mul_single {a b : Γ} {r s : R} : si
ngle a r * single b s = single (a + b) (r * s)
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
-/
theorem single_pow (a : Γ) (n : ℕ) (r : R) : single a r ^ n = single (n • a) (r ^ n) := by
  induction n with
  | zero => ext; simp only [pow_zero, coeff_one, zero_smul, coeff_single]
  | succ n IH => rw [pow_succ, pow_succ, IH, single_mul_single, succ_nsmul]

end Semiring

section NonAssocSemiring

variable [NonAssocSemiring R]

/-- `C a` is the constant Hahn Series `a`. `C` is provided as a ring homomorphism. -/
@[simps]
/-
**HahnSeries.C** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：C : R ->+* R⟦Γ⟧ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C a` is the constant Hahn Series `a`. `C` is provided as a ring homomorphism.
-/
def C : R →+* R⟦Γ⟧ where
  toFun := single 0
  map_zero' := single_eq_zero
  map_one' := rfl
  map_add' x y := by
    ext a
    by_cases h : a = 0 <;> simp [h]
  map_mul' x y := by rw [single_mul_single, zero_add]
/-
**HahnSeries.C_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：C_zero : C (0 : R) = (0 : R⟦Γ⟧)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
-/
theorem C_zero : C (0 : R) = (0 : R⟦Γ⟧) :=
  C.map_zero
/-
**HahnSeries.C_one** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：C_one : C (1 : R) = (1 : R⟦Γ⟧)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
-/
theorem C_one : C (1 : R) = (1 : R⟦Γ⟧) :=
  C.map_one
/-
**HahnSeries.map_C** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：map_C [NonAssocSemiring S] (a : R) (f : R ->+* S) : ((C a).map f : S⟦Γ⟧) =
 C (f a)
参数：a : R；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.map.congr_simp`：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4
} [inst : PartialOrder Γ] [inst_1 : Zero R] [inst_2 : Zero S]   (x x_1 : HahnSer
ies Γ R),   x =…
· 使用定理 `HahnSeries.C_apply`：∀ {Γ : Type u_1} {R : Type u_3} [inst : AddCommMonoi
d Γ] [inst_1 : PartialOrder Γ] [inst_2 : IsOrderedCancelAddMonoid Γ]   [inst_3 :
 NonAsso…
· 使用定理 `HahnSeries.map_coeff`：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [in
st : PartialOrder Γ] [inst_1 : Zero R] [inst_2 : Zero S]   (x : HahnSeries Γ R) 
{F : Type …
· 使用定理 `HahnSeries.coeff_single_same`：coeff_single_same (a : Γ) (r : R) : (singl
e a r).coeff a = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.coeff_single_of_ne`：coeff_single_of_ne (h : b != a) : (single
 a r).coeff b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
-/
theorem map_C [NonAssocSemiring S] (a : R) (f : R →+* S) :
    ((C a).map f : S⟦Γ⟧) = C (f a) := by
  ext g
  by_cases h : g = 0 <;> simp [h]
/-
**HahnSeries.C_injective** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：C_injective : Function.Injective (C : R -> R⟦Γ⟧)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `HahnSeries.ext_iff`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder
 Γ} {inst_1 : Zero R} {x y : HahnSeries Γ R},   x = y ↔ x.coeff = y.coeff
· 使用定理 `HahnSeries.coeff_single_same`：coeff_single_same (a : Γ) (r : R) : (singl
e a r).coeff a = r
· 使用定理 `HahnSeries.C_apply`：∀ {Γ : Type u_1} {R : Type u_3} [inst : AddCommMonoi
d Γ] [inst_1 : PartialOrder Γ] [inst_2 : IsOrderedCancelAddMonoid Γ]   [inst_3 :
 NonAsso…
-/
theorem C_injective : Function.Injective (C : R → R⟦Γ⟧) := by
  intro r s rs
  rw [HahnSeries.ext_iff, funext_iff] at rs
  have h := rs 0
  rwa [C_apply, coeff_single_same, C_apply, coeff_single_same] at h
/-
**HahnSeries.C_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：C_ne_zero {r : R} (h : r != 0) : (C r : R⟦Γ⟧) != 0
参数：h : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.ne_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {x y : α} {z : β}, f y = z → (f x ≠ z ↔ x ≠ y)
· 使用定理 `HahnSeries.C_injective`：C_injective : Function.Injective (C : R -> R⟦Γ⟧)
· 使用定理 `HahnSeries.C_zero`：C_zero : C (0 : R) = (0 : R⟦Γ⟧)
-/
theorem C_ne_zero {r : R} (h : r ≠ 0) : (C r : R⟦Γ⟧) ≠ 0 :=
  C_injective.ne_iff' C_zero |>.mpr h
/-
**HahnSeries.order_C** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：order_C {r : R} : order (C r : R⟦Γ⟧) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.C_zero`：C_zero : C (0 : R) = (0 : R⟦Γ⟧)
· 使用定理 `HahnSeries.order_zero`：order_zero : order (0 : R⟦Γ⟧) = 0
· 使用定理 `HahnSeries.order_single`：order_single (h : r != 0) : (single a r).order 
= a
-/
theorem order_C {r : R} : order (C r : R⟦Γ⟧) = 0 := by
  by_cases h : r = 0
  · rw [h, C_zero, order_zero]
  · exact order_single h

end NonAssocSemiring

section Semiring

variable [Semiring R]

/-
**HahnSeries.C_mul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：C_mul_eq_smul {r : R} {x : R⟦Γ⟧} : C r * x = r • x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.single_zero_mul_eq_smul`：single_zero_mul_eq_smul [Semiring R]
 {r : R} {x : R⟦Γ⟧} : single 0 r * x = r • x
-/
theorem C_mul_eq_smul {r : R} {x : R⟦Γ⟧} : C r * x = r • x :=
  single_zero_mul_eq_smul

end Semiring

section Domain

variable {Γ' : Type*} [AddCommMonoid Γ'] [PartialOrder Γ'] [IsOrderedCancelAddMonoid Γ']

/-
**HahnSeries.embDomain_mul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：embDomain_mul [NonUnitalNonAssocSemiring R] (f : Γ ↪o Γ') (hf : forall x y
, f (x + y) = f x + f y) (x y : R⟦Γ⟧) : embDomain f (x * y) = embDomain f x * em
bDomain f y
参数：f : Γ ↪o Γ'；hf : forall x y, f (x + y) = f x + f y；x y : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.embDomain_coeff`：embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a 
: Γ} : (embDomain f x).coeff (f a) = x.coeff a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.antidiagonal.congr_simp`：∀ {α : Type u_1} [inst : AddCommMonoid α
] [inst_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   {s s_1 : Set
 α} (e_s : s = s_1) …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `HahnSeries.support_embDomain_subset`：support_embDomain_subset {f : Γ ↪o 
Γ'} {x : R⟦Γ⟧} : support (embDomain f x) subseteq f '' x.support
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ne_zero_and_ne_zero_of_mul`：ne_zero_and_ne_zero_of_mul (h : a * b != 0) 
: a != 0 ∧ b != 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `HahnSeries.embDomain_of_notMem_range`：embDomain_of_notMem_range {f : Γ ↪
o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ Set.range f) : (embDomain f x).coeff b = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `HahnSeries.support_mul_subset`：support_mul_subset [NonUnitalNonAssocSemi
ring R] {x y : R⟦Γ⟧} : support (x * y) subseteq support x + support y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.mem_support`：mem_support (x : R⟦Γ⟧) (a : Γ) : a in x.support 
↔ x.coeff a != 0
-/
theorem embDomain_mul [NonUnitalNonAssocSemiring R] (f : Γ ↪o Γ')
    (hf : ∀ x y, f (x + y) = f x + f y) (x y : R⟦Γ⟧) :
    embDomain f (x * y) = embDomain f x * embDomain f y := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨g, rfl⟩ := hg
    simp only [coeff_mul, embDomain_coeff]
    trans
      ∑ ij ∈
        (antidiagonal x.isPWO_support y.isPWO_support g).map
          (f.toEmbedding.prodMap f.toEmbedding),
        (embDomain f x).coeff ij.1 * (embDomain f y).coeff ij.2
    · simp
    apply sum_subset
    · rintro ⟨i, j⟩ hij
      simp only [mem_map, mem_antidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists] at hij
      obtain ⟨i, j, ⟨hx, hy, rfl⟩, rfl, rfl⟩ := hij
      simp [hx, hy, hf]
    · rintro ⟨_, _⟩ h1 h2
      contrapose! h2
      obtain ⟨i, _, rfl⟩ := support_embDomain_subset (ne_zero_and_ne_zero_of_mul h2).1
      obtain ⟨j, _, rfl⟩ := support_embDomain_subset (ne_zero_and_ne_zero_of_mul h2).2
      simp only [mem_map, mem_antidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists]
      simp only [mem_antidiagonal, embDomain_coeff, mem_support, ← hf,
        OrderEmbedding.eq_iff_eq] at h1
      exact ⟨i, j, h1, rfl⟩
  · rw [embDomain_of_notMem_range hg, eq_comm]
    contrapose! hg
    obtain ⟨_, hi, _, hj, rfl⟩ := support_mul_subset ((mem_support _ _).2 hg)
    obtain ⟨i, _, rfl⟩ := support_embDomain_subset hi
    obtain ⟨j, _, rfl⟩ := support_embDomain_subset hj
    exact ⟨i + j, hf i j⟩

omit [IsOrderedCancelAddMonoid Γ] [IsOrderedCancelAddMonoid Γ'] in
/-
**HahnSeries.embDomain_one** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：embDomain_one [NonAssocSemiring R] (f : Γ ↪o Γ') (hf : f 0 = 0) : embDomai
n f (1 : R⟦Γ⟧) = (1 : R⟦Γ'⟧)
参数：f : Γ ↪o Γ'；hf : f 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.embDomain_single`：embDomain_single {f : Γ ↪o Γ'} {g : Γ} {r :
 R} : embDomain f (single g r) = single (f g) r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem embDomain_one [NonAssocSemiring R] (f : Γ ↪o Γ') (hf : f 0 = 0) :
    embDomain f (1 : R⟦Γ⟧) = (1 : R⟦Γ'⟧) :=
  embDomain_single.trans <| hf.symm ▸ rfl

/-- Extending the domain of Hahn series is a ring homomorphism. -/
@[simps]
/-
**HahnSeries.embDomainRingHom** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：embDomainRingHom [NonAssocSemiring R] (f : Γ ->+ Γ') (hfi : Function.Injec
tive f) (hf : forall g g' : Γ, f g <= f g' ↔ g <= g') : R⟦Γ⟧ ->+* R⟦Γ'⟧ where to
Fun
参数：f : Γ ->+ Γ'；hfi : Function.Injective f；hf : forall g g' : Γ, f g <= f g' ↔ g
 <= g'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extending the domain of Hahn series is a ring homomorphism.
-/
def embDomainRingHom [NonAssocSemiring R] (f : Γ →+ Γ') (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : R⟦Γ⟧ →+* R⟦Γ'⟧ where
  toFun := embDomain ⟨⟨f, hfi⟩, hf _ _⟩
  map_one' := embDomain_one _ f.map_zero
  map_mul' := embDomain_mul _ f.map_add
  map_zero' := embDomain_zero
  map_add' := embDomain_add _
/-
**HahnSeries.embDomainRingHom_C** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：embDomainRingHom_C [NonAssocSemiring R] {f : Γ ->+ Γ'} {hfi : Function.Inj
ective f} {hf : forall g g' : Γ, f g <= f g' ↔ g <= g'} {r : R} : embDomainRingH
om f hfi hf (C r) = C r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.embDomain_single`：embDomain_single {f : Γ ↪o Γ'} {g : Γ} {r :
 R} : embDomain f (single g r) = single (f g) r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `HahnSeries.C_apply`：∀ {Γ : Type u_1} {R : Type u_3} [inst : AddCommMonoi
d Γ] [inst_1 : PartialOrder Γ] [inst_2 : IsOrderedCancelAddMonoid Γ]   [inst_3 :
 NonAsso…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem embDomainRingHom_C [NonAssocSemiring R] {f : Γ →+ Γ'} {hfi : Function.Injective f}
    {hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g'} {r : R} : embDomainRingHom f hfi hf (C r) = C r :=
  embDomain_single.trans (by simp)

end Domain

section Algebra

variable [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R A⟦Γ⟧ where
  algebraMap := C.comp (algebraMap R A)
  smul_def' r x := by
    ext
    simp
  commutes' r x := by
    ext
    simp only [coeff_smul, single_zero_mul_eq_smul, RingHom.coe_comp, C_apply,
      Function.comp_apply, algebraMap_smul, coeff_mul_single_zero]
    rw [← Algebra.commutes, Algebra.smul_def]
/-
**HahnSeries.C_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：C_eq_algebraMap : C = algebraMap R R⟦Γ⟧
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_eq_algebraMap : C = algebraMap R R⟦Γ⟧ :=
  rfl
/-
**HahnSeries.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：algebraMap_apply {r : R} : algebraMap R A⟦Γ⟧ r = C (algebraMap R A r)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply {r : R} : algebraMap R A⟦Γ⟧ r = C (algebraMap R A r) :=
  rfl
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial Γ] [Nontrivial R] : Nontrivial (Subalgebra R R⟦Γ⟧) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne, SetLike.ext_iff, not_forall]
      obtain ⟨a, ha⟩ := exists_ne (0 : Γ)
      refine ⟨single a 1, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top]
      intro x
      rw [HahnSeries.ext_iff, funext_iff, not_forall]
      refine ⟨a, ?_⟩
      rw [coeff_single_same, algebraMap_apply, C_apply, coeff_single_of_ne ha]
      exact zero_ne_one⟩⟩

section Domain

variable {Γ' : Type*} [AddCommMonoid Γ'] [PartialOrder Γ'] [IsOrderedCancelAddMonoid Γ']

/-- Extending the domain of Hahn series is an algebra homomorphism. -/
@[simps!]
/-
**HahnSeries.embDomainAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：embDomainAlgHom (f : Γ ->+ Γ') (hfi : Function.Injective f) (hf : forall g
 g' : Γ, f g <= f g' ↔ g <= g') : A⟦Γ⟧ ->ₐ[R] A⟦Γ'⟧
参数：f : Γ ->+ Γ'；hfi : Function.Injective f；hf : forall g g' : Γ, f g <= f g' ↔ g
 <= g'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extending the domain of Hahn series is an algebra homomorphism.
-/
def embDomainAlgHom (f : Γ →+ Γ') (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : A⟦Γ⟧ →ₐ[R] A⟦Γ'⟧ :=
  { embDomainRingHom f hfi hf with commutes' := fun _ => embDomainRingHom_C (hf := hf) }

end Domain

end Algebra
end PartialOrder

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCancelAdd R] [IsCancelMulZero R] : IsCancelMulZero R⟦Γ⟧ where
  -- TODO: This proof is painful because `coeff_mul` isn't stated in terms of `Finsupp.sum`.
  mul_left_cancel_of_ne_zero {x} hx y z hyz := by
    let : AddCancelCommMonoid R := ⟨⟩
    contrapose! hyz
    simp only [ne_eq, ← coeff_inj, funext_iff, not_forall] at ⊢ hyz
    have : Set.IsWF {a | y.coeff a ≠ z.coeff a} :=
      .mono (y.isWF_support.union z.isWF_support) (by intro; simp; grind)
    let a : Γ := this.min hyz
    have ha : y.coeff a ≠ z.coeff a := this.min_mem hyz
    refine ⟨x.order + a, ?_⟩
    rwa [coeff_mul, coeff_mul, sum_subset subset_union_left,
      sum_subset (s₁ := antidiagonal _ _ _) subset_union_right,
      sum_eq_sum_iff_single (i := (x.order, a)), mul_right_inj' (coeff_order_eq_zero.not.2 hx)]
    · simp [hx]
      grind
    · simp +contextual only [mem_union, mem_antidiagonal, mul_eq_mul_left_iff, Prod.mk.injEq,
        ne_eq, ← and_or_left, ← or_and_right, or_false, and_imp, Prod.forall, mem_support, not_and]
      rintro b c hxb - hbc hbc'
      contrapose! hbc'
      rwa [eq_comm, eq_comm (a := c), ← add_eq_add_iff_eq_and_eq (order_le_of_coeff_ne_zero hxb)
        (Set.IsWF.min_le this hyz hbc'), eq_comm]
    · simp +contextual [← and_or_left, ← or_and_right]
    · simp +contextual [← and_or_left, ← or_and_right]
  mul_right_cancel_of_ne_zero {x} hx y z hyz := by
    let : AddCancelCommMonoid R := ⟨⟩
    contrapose! hyz
    simp only [ne_eq, ← coeff_inj, funext_iff, not_forall] at ⊢ hyz
    have : Set.IsWF {a | y.coeff a ≠ z.coeff a} :=
      .mono (y.isWF_support.union z.isWF_support) (by intro; simp; grind)
    let a : Γ := this.min hyz
    have ha : y.coeff a ≠ z.coeff a := this.min_mem hyz
    refine ⟨a + x.order, ?_⟩
    rwa [coeff_mul, coeff_mul, sum_subset subset_union_left,
      sum_subset (s₁ := antidiagonal _ _ _) subset_union_right,
      sum_eq_sum_iff_single (i := (a, x.order)), mul_left_inj' (coeff_order_eq_zero.not.2 hx)]
    · simp [hx]
      grind
    · simp +contextual only [mem_union, mem_antidiagonal, mul_eq_mul_right_iff, Prod.mk.injEq,
        ne_eq, ← or_and_right, or_false, and_imp, Prod.forall, mem_support, not_and]
      rintro b c - hxb hbc hbc'
      contrapose! hbc'
      rwa [eq_comm, eq_comm (a := c), ← add_eq_add_iff_eq_and_eq
        (Set.IsWF.min_le this hyz ((Set.mem_ofPred (p := fun a => y.coeff a ≠ z.coeff a)).mpr hbc'))
        (order_le_of_coeff_ne_zero hxb), eq_comm]
    · simp +contextual [← or_and_right]
    · simp +contextual [← or_and_right]

variable [NoZeroDivisors R] {x y : R⟦Γ⟧}
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoZeroDivisors R⟦Γ⟧ where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} hxy := by
    contrapose! hxy
    simp only [ne_eq, HahnSeries.ext_iff, funext_iff, not_forall]
    exact ⟨x.order + y.order, by simpa [coeff_mul_order_add_order]⟩

@[simp]
/-
**HahnSeries.order_mul** 是 Mathlib 中的一个引理，位于命名空间 `HahnSeries`。
形式化陈述：order_mul (hx : x != 0) (hy : y != 0) : (x * y).order = x.order + y.order
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `HahnSeries.order_le_of_coeff_ne_zero`：order_le_of_coeff_ne_zero {Γ} [Zer
o Γ] [LinearOrder Γ] {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : x.order <= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.coeff_mul_order_add_order`：coeff_mul_order_add_order (x y : R
⟦Γ⟧) : (x * y).coeff (x.order + y.order) = x.leadingCoeff * y.leadingCoeff
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `HahnSeries.instNoZeroDivisors`：∀ {Γ : Type u_1} {R : Type u_3} [inst : A
ddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMonoid Γ]  
 [inst_3 : NonUnita…
· 使用定理 `Set.IsWF.add`：∀ {α : Type u_1} {s t : Set α} [inst : AddCommMonoid α] [i
nst_1 : LinearOrder α] [IsOrderedCancelAddMonoid α],   s.IsWF → t.IsWF → (s + t)
.I…
· 使用定理 `Set.Nonempty.add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α}, s.Nonem
pty → t.Nonempty → (s + t).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.IsWF.min_add`：∀ {α : Type u_1} {s t : Set α} [inst : AddCommMonoid α
] [inst_1 : LinearOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   (hs : s.IsWF)
 (ht :…
· 使用定理 `Set.IsWF.min_le_min_of_subset`：∀ {α : Type u_2} [inst : LinearOrder α] {
s t : Set α} {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty}, 
  s ⊆ t → ht.min ht…
· 使用定理 `HahnSeries.support_mul_subset`：support_mul_subset [NonUnitalNonAssocSemi
ring R] {x y : R⟦Γ⟧} : support (x * y) subseteq support x + support y
-/
lemma order_mul (hx : x ≠ 0) (hy : y ≠ 0) : (x * y).order = x.order + y.order := by
  apply le_antisymm
  · apply order_le_of_coeff_ne_zero
    simp [coeff_mul_order_add_order x y, *]
  · rw [order_of_ne hx, order_of_ne hy, order_of_ne (mul_ne_zero hx hy), ← Set.IsWF.min_add]
    exact Set.IsWF.min_le_min_of_subset support_mul_subset

end NonUnitalNonAssocSemiring

section Semiring
variable [Semiring R]

/-
**HahnSeries.order_pow** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} [inst : AddCommMonoid Γ] [inst_1 : LinearO
rder Γ] [inst_2 : IsOrderedCancelAddMonoid Γ]   [inst_3 : Semiring R] [NoZeroDiv
isors R] (x : HahnSeries Γ R) (n : ℕ), (x ^ n).order = n • x.order
参数：x : HahnSeries Γ R；n : ℕ；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma order_pow [NoZeroDivisors R] (x : R⟦Γ⟧) : ∀ n, (x ^ n).order = n • x.order
  | 0 => by simp
  | n + 1 => by
    obtain rfl | hx := eq_or_ne x 0 <;> simp [pow_succ, succ_nsmul, order_pow, pow_ne_zero, *]
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCancelAdd R] [IsDomain R] : IsDomain R⟦Γ⟧ where

end Semiring
end HahnSeries

