/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# Order properties of `CFC.rpow`

This file shows that `a ↦ a ^ p` is monotone for `p ∈ [0, 1]`, where `a` is an element of a
C⋆-algebra. The proof makes use of the integral representation of `rpow` in
`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation`.

## Main declarations

+ `CFC.monotone_nnrpow`, `CFC.monotone_rpow`: `a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`
+ `CFC.monotone_sqrt`: `CFC.sqrt` is operator monotone
+ `CFC.concaveOn_nnrpow`, `CFC.concaveOn_rpow`: `a ↦ a ^ p` is operator concave for `p ∈ [0,1]`
+ `CFC.concaveOn_sqrt`: `CFC.sqrt` is operator concave

## TODO

+ Show that `rpow` over `Icc (-1) 0` is operator antitone and operator convex
+ Show operator convexity of `rpow` over `Icc 1 2`

## References

+ [carlen2010] Eric A. Carlen, "Trace inequalities and quantum entropies: An introductory course"
  (see Lemma 2.8)
-/

public section

open Set
open scoped NNReal

namespace CFC

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Real MeasureTheory

/-- This is an intermediate result; use the more general `CFC.monotone_nnrpow` instead. -/
/-
**CFC.monotoneOn_nnrpow_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an intermediate result; use the more general `CFC.monotone_nnrpow` inste
ad.
-/
private lemma monotoneOn_nnrpow_Ioo {p : ℝ≥0} (hp : p ∈ Ioo 0 1) :
    MonotoneOn (fun a : A => a ^ p) (Ici 0) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine MonotoneOn.congr ?_ h₃'.symm
  refine integral_monotoneOn_of_integrand_ae ?_ fun a ha => (hμ a ha).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact monotoneOn_cfcₙ_rpowIntegrand₀₁ hp ht

/-- `a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`. -/
/-
**CFC.monotone_nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：monotone_nnrpow {p : Real>=0} (hp : p in Icc 0 1) : Monotone (fun a : A =>
 a ^ p)
参数：hp : p in Icc 0 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.Ioo_insert_left`：Ioo_insert_left (h : a < b) : insert a (Ioo a b) = 
Ico a b
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.Ico_insert_right`：Ico_insert_right (h : a <= b) : insert b (Ico a b)
 = Icc a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.
Rpow.Order.0.CFC.monotoneOn_nnrpow_Ioo`：∀ {A : Type u_1} [inst : NonUnitalCStarA
lgebra A] [inst_1 : PartialOrder A] [inst_2 : StarOrderedRing A] {p : NNReal},  
 p ∈ Set.Ioo 0 1 → M…
· 使用引理 `CFC.nnrpow_zero`：nnrpow_zero {a : A} : a ^ (0 : Real>=0) = 0
· 使用引理 `CFC.nnrpow_one`：nnrpow_one (a : A) (ha : 0 <= a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `cfcₙ_apply_of_not_predicate`：cfcₙ_apply_of_not_predicate {f : R -> R} (a
 : A) (ha : ¬ p a) : cfcₙ f a = 0
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
`a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`.
-/
lemma monotone_nnrpow {p : ℝ≥0} (hp : p ∈ Icc 0 1) :
    Monotone (fun a : A => a ^ p) := by
  intro a b hab
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab
    have hIcc : Icc (0 : ℝ≥0) 1 = Ioo 0 1 ∪ {0} ∪ {1} := by ext; simp
    rw [hIcc] at hp
    obtain (hp | hp) | hp := hp
    · exact monotoneOn_nnrpow_Ioo hp ha hb hab
    · simp_all [mem_singleton_iff]
    · simp_all [mem_singleton_iff, nnrpow_one a, nnrpow_one b]
  · have : a ^ p = 0 := cfcₙ_apply_of_not_predicate a ha
    simp [this]

/-- `CFC.sqrt` is operator monotone. -/
/-
**CFC.monotone_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：monotone_sqrt : Monotone (sqrt : A -> A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.sqrt_eq_nnrpow`：sqrt_eq_nnrpow (a : A) : sqrt a = a ^ (1 / 2 : Real>
=0)
· 使用引理 `CFC.monotone_nnrpow`：monotone_nnrpow {p : Real>=0} (hp : p in Icc 0 1) :
 Monotone (fun a : A => a ^ p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
`CFC.sqrt` is operator monotone.
-/
lemma monotone_sqrt : Monotone (sqrt : A → A) := by
  intro a b hab
  rw [CFC.sqrt_eq_nnrpow a, CFC.sqrt_eq_nnrpow b]
  refine (monotone_nnrpow (A := A) ?_) hab
  constructor <;> norm_num

@[gcongr]
/-
**CFC.nnrpow_le_nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_le_nnrpow {p : Real>=0} (hp : p in Icc 0 1) {a b : A} (hab : a <= b
) : a ^ p <= b ^ p
参数：hp : p in Icc 0 1；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CFC.monotone_nnrpow`：monotone_nnrpow {p : Real>=0} (hp : p in Icc 0 1) :
 Monotone (fun a : A => a ^ p)
-/
lemma nnrpow_le_nnrpow {p : ℝ≥0} (hp : p ∈ Icc 0 1) {a b : A} (hab : a ≤ b) :
    a ^ p ≤ b ^ p := monotone_nnrpow hp hab

@[gcongr]
/-
**CFC.sqrt_le_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_le_sqrt (a b : A) (hab : a <= b) : sqrt a <= sqrt b
参数：a b : A；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CFC.monotone_sqrt`：monotone_sqrt : Monotone (sqrt : A -> A)
-/
lemma sqrt_le_sqrt (a b : A) (hab : a ≤ b) : sqrt a ≤ sqrt b :=
  monotone_sqrt hab

/-- This is an intermediate result; use the more general `CFC.concaveOn_nnrpow` instead. -/
/-
**CFC.concaveOn_nnrpow_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an intermediate result; use the more general `CFC.concaveOn_nnrpow` inst
ead.
-/
private lemma concaveOn_nnrpow_Ioo {p : ℝ≥0} (hp : p ∈ Ioo 0 1) :
    ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine ConcaveOn.congr ?_ h₃'.symm
  refine integral_concaveOn_of_integrand_ae (convex_Ici _) ?_ fun a ha => (hμ a ha).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact concaveOn_cfcₙ_rpowIntegrand₀₁ hp ht

/-- `a ↦ a ^ p` is operator concave for `p ∈ [0,1]`. -/
/-
**CFC.concaveOn_nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：concaveOn_nnrpow {p : Real>=0} (hp : p in Icc 0 1) : ConcaveOn Real (Ici (
0 : A)) (fun a : A => a ^ p)
参数：hp : p in Icc 0 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.Ioo_insert_left`：Ioo_insert_left (h : a < b) : insert a (Ioo a b) = 
Ico a b
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.Ico_insert_right`：Ico_insert_right (h : a <= b) : insert b (Ico a b)
 = Icc a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.
Rpow.Order.0.CFC.concaveOn_nnrpow_Ioo`：∀ {A : Type u_1} [inst : NonUnitalCStarAl
gebra A] [inst_1 : PartialOrder A] [inst_2 : StarOrderedRing A] {p : NNReal},   
p ∈ Set.Ioo 0 1 → C…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CFC.nnrpow_zero`：nnrpow_zero {a : A} : a ^ (0 : Real>=0) = 0
· 使用定理 `concaveOn_const`：concaveOn_const (c : β) (hs : Convex 𝕜 s) : ConcaveOn 𝕜
 s fun _ => c
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
`a ↦ a ^ p` is operator concave for `p ∈ [0,1]`.
-/
lemma concaveOn_nnrpow {p : ℝ≥0} (hp : p ∈ Icc 0 1) :
    ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  have hIcc : Icc (0 : ℝ≥0) 1 = Ioo 0 1 ∪ {0} ∪ {1} := by ext; simp
  rw [hIcc] at hp
  obtain (hp | hp) | hp := hp
  · exact concaveOn_nnrpow_Ioo hp
  · simp only [mem_singleton_iff] at hp
    simp only [hp, nnrpow_zero]
    exact concaveOn_const _ (convex_Ici _)
  · simp only [mem_singleton_iff] at hp
    simp only [hp]
    exact ConcaveOn.congr (concaveOn_id (convex_Ici _)) nnrpow_one_eqOn.symm

/-- The square root is operator concave. -/
/-
**CFC.concaveOn_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：concaveOn_sqrt : ConcaveOn Real (Ici (0 : A)) (sqrt : A -> A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CFC.sqrt_eq_nnrpow`：sqrt_eq_nnrpow (a : A) : sqrt a = a ^ (1 / 2 : Real>
=0)
· 使用引理 `CFC.concaveOn_nnrpow`：concaveOn_nnrpow {p : Real>=0} (hp : p in Icc 0 1)
 : ConcaveOn Real (Ici (0 : A)) (fun a : A => a ^ p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The square root is operator concave.
-/
lemma concaveOn_sqrt : ConcaveOn ℝ (Ici (0 : A)) (sqrt : A → A) := by
  eta_expand
  simp_rw [sqrt_eq_nnrpow]
  exact concaveOn_nnrpow ⟨by norm_num, by norm_num⟩

end NonUnitalCStarAlgebra

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`. -/
/-
**CFC.monotone_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：monotone_rpow {p : Real} (hp : p in Icc 0 1) : Monotone (fun a : A => a ^ 
p)
参数：hp : p in Icc 0 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CFC.rpow_zero`：rpow_zero (a : A) (ha : 0 <= a
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.nnrpow_eq_rpow`：nnrpow_eq_rpow {a : A} {x : Real>=0} (hx : 0 < x) : 
a ^ x = a ^ (x : Real)
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `CFC.monotone_nnrpow`：monotone_nnrpow {p : Real>=0} (hp : p in Icc 0 1) :
 Monotone (fun a : A => a ^ p)

--- 原说明 ---
`a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`.
-/
lemma monotone_rpow {p : ℝ} (hp : p ∈ Icc 0 1) : Monotone (fun a : A => a ^ p) := by
  let q : ℝ≥0 := ⟨p, hp.1⟩
  change Monotone (fun a : A => a ^ (q : ℝ))
  obtain hq | hq := eq_zero_or_pos q
  · rw [hq]
    intro a b hab
    by_cases ha : 0 ≤ a
    · have hb : 0 ≤ b := ha.trans hab
      simp [CFC.rpow_zero a, CFC.rpow_zero b]
    · have : a ^ (0 : ℝ) = 0 := cfc_apply_of_not_predicate a ha
      simp [this]
  · simp_rw [← CFC.nnrpow_eq_rpow hq]
    exact monotone_nnrpow hp

@[gcongr]
/-
**CFC.rpow_le_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_le_rpow {p : Real} (hp : p in Icc 0 1) {a b : A} (hab : a <= b) : a ^
 p <= b ^ p
参数：hp : p in Icc 0 1；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CFC.monotone_rpow`：monotone_rpow {p : Real} (hp : p in Icc 0 1) : Monoto
ne (fun a : A => a ^ p)
-/
lemma rpow_le_rpow {p : ℝ} (hp : p ∈ Icc 0 1) {a b : A} (hab : a ≤ b) :
    a ^ p ≤ b ^ p := monotone_rpow hp hab

/-- `a ↦ a ^ p` is operator concave for `p ∈ [0,1]`. -/
/-
**CFC.concaveOn_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：concaveOn_rpow {p : Real} (hp : p in Icc 0 1) : ConcaveOn Real (Ici (0 : A
)) (fun a : A => a ^ p)
参数：hp : p in Icc 0 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ConcaveOn.congr`：ConcaveOn.congr (hf : ConcaveOn 𝕜 s f) (hfg : EqOn f g 
s) : ConcaveOn 𝕜 s g
· 使用定理 `concaveOn_const`：concaveOn_const (c : β) (hs : Convex 𝕜 s) : ConcaveOn 𝕜
 s fun _ => c
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `instIsOrderedModule`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 :
 NonUnita…
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
· 使用引理 `CFC.rpow_zero_eqOn`：rpow_zero_eqOn : (Set.Ici (0 : A)).EqOn (fun a => a 
^ (0 : Real)) (fun _ => 1)
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.nnrpow_eq_rpow`：nnrpow_eq_rpow {a : A} {x : Real>=0} (hx : 0 < x) : 
a ^ x = a ^ (x : Real)
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
`a ↦ a ^ p` is operator concave for `p ∈ [0,1]`.
-/
lemma concaveOn_rpow {p : ℝ} (hp : p ∈ Icc 0 1) :
    ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  let q : ℝ≥0 := ⟨p, hp.1⟩
  change ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ (q : ℝ))
  obtain hq | hq := eq_zero_or_pos q
  · simp only [hq, NNReal.coe_zero]
    exact ConcaveOn.congr (concaveOn_const _ (convex_Ici _)) rpow_zero_eqOn.symm
  · simp_rw [← CFC.nnrpow_eq_rpow hq]
    exact concaveOn_nnrpow hp

end UnitalCStarAlgebra

end CFC

