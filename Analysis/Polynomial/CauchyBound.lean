/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Cauchy's bound on polynomial roots.

The bound is given by `Polynomial.cauchyBound`, which for `a_n x^n + a_(n-1) x^(n - 1) + ⋯ + a_0` is
`1 + max_(0 ≤ i < n) a_i / a_n`.

The theorem that this gives a bound to polynomial roots is `Polynomial.IsRoot.norm_lt_cauchyBound`.
-/

@[expose] public section

variable {K : Type*} [NormedDivisionRing K]

namespace Polynomial

open Finset NNReal

/--
Cauchy's bound on the roots of a given polynomial.
See `IsRoot.norm_lt_cauchyBound` for the proof that the roots satisfy this bound.
-/
/-
**Polynomial.cauchyBound** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：cauchyBound (p : K[X]) : Real>=0
参数：p : K[X]。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cauchy's bound on the roots of a given polynomial.
See `IsRoot.norm_lt_cauchyBound` for the proof that the roots satisfy this bound
.
-/
noncomputable def cauchyBound (p : K[X]) : ℝ≥0 :=
  sup (range p.natDegree) (‖p.coeff ·‖₊) / ‖p.leadingCoeff‖₊ + 1

@[simp]
/-
**Polynomial.one_le_cauchyBound** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：one_le_cauchyBound (p : K[X]) : 1 <= cauchyBound p
参数：p : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma one_le_cauchyBound (p : K[X]) : 1 ≤ cauchyBound p := by
  simp [cauchyBound]

@[simp]
/-
**Polynomial.cauchyBound_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：cauchyBound_zero : cauchyBound (0 : K[X]) = 1
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cauchyBound_zero : cauchyBound (0 : K[X]) = 1 := by
  simp [cauchyBound]

@[simp]
/-
**Polynomial.cauchyBound_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：cauchyBound_C (x : K) : cauchyBound (C x) = 1
参数：x : K。
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
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cauchyBound_C (x : K) : cauchyBound (C x) = 1 := by
  simp [cauchyBound]

@[simp]
/-
**Polynomial.cauchyBound_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：cauchyBound_one : cauchyBound (1 : K[X]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.cauchyBound_C`：cauchyBound_C (x : K) : cauchyBound (C x) = 1
-/
lemma cauchyBound_one : cauchyBound (1 : K[X]) = 1 := cauchyBound_C 1

@[simp]
/-
**Polynomial.cauchyBound_X** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：cauchyBound_X : cauchyBound (X : K[X]) = 1
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
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `nnnorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 :
 One G] [NormOneClass G], ‖1‖₊ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cauchyBound_X : cauchyBound (X : K[X]) = 1 := by
  simp [cauchyBound]

@[simp]
/-
**Polynomial.cauchyBound_X_add_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：cauchyBound_X_add_C (x : K) : cauchyBound (X + C x) = ‖x‖₊ + 1
参数：x : K。
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
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.leadingCoeff_X_add_C`：leadingCoeff_X_add_C [Semiring S] (r : 
S) : (X + C r).leadingCoeff = 1
· 使用定理 `nnnorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 :
 One G] [NormOneClass G], ‖1‖₊ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cauchyBound_X_add_C (x : K) : cauchyBound (X + C x) = ‖x‖₊ + 1 := by
  simp [cauchyBound]

@[simp]
/-
**Polynomial.cauchyBound_X_sub_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：cauchyBound_X_sub_C (x : K) : cauchyBound (X - C x) = ‖x‖₊ + 1
参数：x : K。
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
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `nnnorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖
₊ = ‖a‖₊
· 使用定理 `Polynomial.leadingCoeff_X_sub_C`：leadingCoeff_X_sub_C [Ring S] (r : S) :
 (X - C r).leadingCoeff = 1
· 使用定理 `nnnorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 :
 One G] [NormOneClass G], ‖1‖₊ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cauchyBound_X_sub_C (x : K) : cauchyBound (X - C x) = ‖x‖₊ + 1 := by
  simp [cauchyBound]

@[simp]
/-
**Polynomial.cauchyBound_smul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：cauchyBound_smul {x : K} (hx : x != 0) (p : K[X]) : cauchyBound (x • p) = 
cauchyBound p
参数：hx : x != 0；p : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_smul_of_smul_regular`：natDegree_smul_of_smul_regula
r {S : Type*} [SMulZeroClass S R] {k : S} (p : R[X]) (h : IsSMulRegular R k) : (
k • p).natDegree = p.natDegree
· 使用定理 `IsLeftRegular.isSMulRegular`：IsLeftRegular.isSMulRegular [Mul R] {c : R}
 (h : IsLeftRegular c) : IsSMulRegular R c
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `IsRegular.of_ne_zero`：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `nnnorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 :
 Mul α] [NormMulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Polynomial.leadingCoeff_smul_of_smul_regular`：leadingCoeff_smul_of_smul_
regular {S : Type*} [SMulZeroClass S R] {k : S} (p : R[X]) (h : IsSMulRegular R 
k) : (k • p).leadingCoeff = k • p.…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
-/
lemma cauchyBound_smul {x : K} (hx : x ≠ 0) (p : K[X]) : cauchyBound (x • p) = cauchyBound p := by
  simp only [cauchyBound, (IsRegular.of_ne_zero hx).left.isSMulRegular,
    natDegree_smul_of_smul_regular, coeff_smul, smul_eq_mul, nnnorm_mul, ← mul_finset_sup,
    leadingCoeff_smul_of_smul_regular, add_left_inj]
  apply mul_div_mul_left
  simpa

/--
`cauchyBound` is a bound on the norm of polynomial roots.
-/
/-
**Polynomial.IsRoot.norm_lt_cauchyBound** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Is
Root`。
形式化陈述：∀ {K : Type u_1} [inst : NormedDivisionRing K] {p : Polynomial K}, p ≠ 0 →
 ∀ {a : K}, p.IsRoot a → ‖a‖₊ < p.cauchyBound
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nnnorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 :
 Mul α] [NormMulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `nnnorm_pow`：nnnorm_pow (a : α) (n : Nat) : ‖a ^ n‖₊ = ‖a‖₊ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `nnnorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖
₊ = ‖a‖₊
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用定理 `Polynomial.eval_eq_sum_range`：eval_eq_sum_range {p : R[X]} (x : R) : p.e
val x = ∑ i in Finset.range (p.natDegree + 1), p.coeff i * x ^ i
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
（共 139 条，此处仅展示前 30 条）

--- 原说明 ---
`cauchyBound` is a bound on the norm of polynomial roots.
-/
theorem IsRoot.norm_lt_cauchyBound {p : K[X]} (hp : p ≠ 0) {a : K} (h : p.IsRoot a) :
    ‖a‖₊ < cauchyBound p := by
  rw [IsRoot.def, eval_eq_sum_range, range_add_one] at h
  simp only [mem_range, lt_self_iff_false, not_false_eq_true, sum_insert, coeff_natDegree,
    add_eq_zero_iff_eq_neg] at h
  apply_fun nnnorm at h
  simp only [nnnorm_mul, nnnorm_pow, nnnorm_neg] at h
  suffices ‖a‖₊ ^ p.natDegree ≤ (cauchyBound p - 1) * ∑ x ∈ range p.natDegree, ‖a‖₊ ^ x by
    rcases eq_or_ne ‖a‖₊ 1 with ha | ha
    · simp only [ha, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, gt_iff_lt] at this ⊢
      apply lt_of_le_of_ne (by simp)
      intro nh
      simp [← nh, tsub_self] at this
    rcases lt_or_gt_of_ne ha with ha | ha
    · apply ha.trans_le
      simp
    · rw [geom_sum_of_one_lt ha] at this
      calc
        ‖a‖₊ = ‖a‖₊ - 1 + 1 := (tsub_add_cancel_of_le ha.le).symm
        _ = ‖a‖₊ ^ p.natDegree * (‖a‖₊ - 1) / ‖a‖₊ ^ p.natDegree + 1 := by field
        _ ≤ (cauchyBound p - 1) * ((‖a‖₊ ^ p.natDegree - 1) / (‖a‖₊ - 1)) * (‖a‖₊ - 1)
            / ‖a‖₊ ^ p.natDegree + 1 := by gcongr
        _ = (cauchyBound p - 1) * (‖a‖₊ ^ p.natDegree - 1) / ‖a‖₊ ^ p.natDegree + 1 := by
          congr 2
          have : ‖a‖₊ - 1 ≠ 0 := fun nh ↦ (ha.trans_le (tsub_eq_zero_iff_le.mp nh)).false
          field
        _ < (cauchyBound p - 1) * ‖a‖₊ ^ p.natDegree / ‖a‖₊ ^ p.natDegree + 1 := by
          gcongr
          · apply lt_of_le_of_ne (by simp)
            contrapose! this
            simp only [← this, zero_mul]
            apply pow_pos
            exact zero_lt_one.trans ha
          simp [zero_lt_one.trans ha]
        _ = cauchyBound p := by simp [field, tsub_add_cancel_of_le]
  apply le_of_eq at h
  have pld : ‖p.leadingCoeff‖₊ ≠ 0 := by simpa
  calc ‖a‖₊ ^ p.natDegree
    _ = ‖p.leadingCoeff‖₊ * ‖a‖₊ ^ p.natDegree / ‖p.leadingCoeff‖₊ := by
      rw [mul_div_cancel_left₀]
      simpa
    _ ≤ ‖∑ x ∈ range p.natDegree, p.coeff x * a ^ x‖₊ / ‖p.leadingCoeff‖₊ := by gcongr
    _ ≤ (∑ x ∈ range p.natDegree, ‖p.coeff x * a ^ x‖₊) / ‖p.leadingCoeff‖₊ := by
      gcongr
      apply nnnorm_sum_le
    _ = (∑ x ∈ range p.natDegree, ‖p.coeff x‖₊ * ‖a‖₊ ^ x) / ‖p.leadingCoeff‖₊ := by simp
    _ ≤ (∑ x ∈ range p.natDegree, ‖p.leadingCoeff‖₊ * (cauchyBound p - 1) * ‖a‖₊ ^ x) /
        ‖p.leadingCoeff‖₊ := by
      gcongr (∑ x ∈ _, ?_ * _) / _
      rw [cauchyBound, add_tsub_cancel_right]
      field_simp
      apply le_sup (f := (‖p.coeff ·‖₊)) ‹_›
    _ = (cauchyBound p - 1) * ∑ x ∈ range p.natDegree, ‖a‖₊ ^ x := by
      simp only [← mul_sum]
      field

end Polynomial

