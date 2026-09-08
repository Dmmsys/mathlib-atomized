/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov, Andrew Yang
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.RingTheory.Binomial

/-!
# Binomial Series

This file introduces the binomial series:
$$
\sum_{k=0}^{\infty} \; \binom{a}{k} \; x^k = 1 + a x + \frac{a(a-1)}{2!} x^2 +
  \frac{a(a-1)(a-2)}{3!} x^3 + \cdots
$$
where $a$ is an element of a normed field $\mathbb{K}$,
and $x$ is an element of a normed algebra over $\mathbb{K}$.

## Main Statements

* `binomialSeries_radius_eq_one`: The radius of convergence of the binomial series is `1` when `a`
  is not a natural number.
* `binomialSeries_radius_eq_top_of_nat`: In case `a` is natural, the series converges everywhere,
  since it is finite.
-/

@[expose] public section

open scoped Nat

universe u v

@[norm_cast]
/-
**Complex.ofReal_choose** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Complex.ofReal_choose (a : Real) (n : Nat) : ↑(Ring.choose a n) = Ring.cho
ose (a : Complex) n
参数：a : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ring.map_choose`：map_choose {R S F : Type*} [Ring R] [Ring S] [BinomialR
ing R] [BinomialRing S] [FunLike F R S] [RingHomClass F R S] (f : F) (a : R) (n 
: Nat…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma Complex.ofReal_choose (a : ℝ) (n : ℕ) :
    ↑(Ring.choose a n) = Ring.choose (a : ℂ) n :=
  Ring.map_choose (algebraMap ℝ ℂ) _ _

/-- **Binomial series**: the (scalar) formal multilinear series with coefficients given
by `Ring.choose a`. The sum of this series is `fun x ↦ (1 + x) ^ a` within the radius
of convergence. -/
/-
**binomialSeries** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：binomialSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v) [Ring 𝔸] [
Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) : FormalMultilin
earSeries 𝕂 𝔸 𝔸
参数：𝔸 : Type v；a : 𝕂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Binomial series**: the (scalar) formal multilinear series with coefficients gi
ven
by `Ring.choose a`. The sum of this series is `fun x ↦ (1 + x) ^ a` within the r
adius
of convergence.
-/
noncomputable def binomialSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
    [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) :
    FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  .ofScalars 𝔸 (Ring.choose a ·)

@[simp]
/-
**binomialSeries_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：binomialSeries_apply {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v) [Rin
g 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) {n} (v : F
in n -> 𝔸) : binomialSeries 𝔸 a n v = Ring.choose a n • (List.ofFn v).prod
参数：𝔸 : Type v；a : 𝕂；v : Fin n -> 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem binomialSeries_apply {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
    [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) {n} (v : Fin n → 𝔸) :
    binomialSeries 𝔸 a n v = Ring.choose a n • (List.ofFn v).prod := by
  simp [binomialSeries, FormalMultilinearSeries.ofScalars]
/-
**binomialSeries_eq_ordinaryHypergeometricSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：binomialSeries_eq_ordinaryHypergeometricSeries {𝕂 : Type u} [Field 𝕂] [Cha
rZero 𝕂] {𝔸 : Type v} [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopological
Ring 𝔸] {a b : 𝕂} (h : forall (k : Nat), (k : 𝕂) != -b) : binomialSeries 𝔸 a = (
ordinaryHypergeometricSeries 𝔸 (-a) b b).compContinuousLinearMap (-(.id _ _))
参数：h : forall (k : Nat), (k : 𝕂) != -b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.ofScalars_comp_neg_id`：ofScalars_comp_neg_id : (
ofScalars E c).compContinuousLinearMap (-ContinuousLinearMap.id _ _) = (ofScalar
s E (fun k => (-1) ^ k * c k))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ordinaryHypergeometricCoefficient.eq_1`：∀ {𝕂 : Type u_1} [inst : Field 𝕂
] (a b c : 𝕂) (n : ℕ),   ordinaryHypergeometricCoefficient a b c n =     (↑n.fac
torial)⁻¹ * Polynomial.eval …
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ring.choose_eq_smul`：choose_eq_smul [Field R] [CharZero R] {a : R} {n : 
Nat} : Ring.choose a n = (n.factorial : R)⁻¹ • (descPochhammer Int n).smeval a
· 使用定理 `Polynomial.descPochhammer_smeval_eq_ascPochhammer`：descPochhammer_smeval
_eq_ascPochhammer (r : R) (n : Nat) : (descPochhammer Int n).smeval r = (ascPoch
hammer Nat n).smeval (r - n + 1)
· 使用定理 `Polynomial.ascPochhammer_smeval_cast`：ascPochhammer_smeval_cast (R : Typ
e*) [Semiring R] {S : Type*} [NonAssocSemiring S] [Pow S Nat] [Module R S] [IsSc
alarTower R S S] [NatPowAs…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Polynomial.ascPochhammer_smeval_eq_eval`：ascPochhammer_smeval_eq_eval [S
emiring R] (r : R) (n : Nat) : (ascPochhammer Nat n).smeval r = (ascPochhammer R
 n).eval r
· 使用定理 `ascPochhammer_eval_neg_eq_descPochhammer`：∀ (R : Type u) [inst : Ring R]
 (r : R) (k : ℕ),   Polynomial.eval (-r) (ascPochhammer R k) = (-1) ^ k * Polyno
mial.eval r (descPochhammer R …
· 使用定理 `descPochhammer_eval_eq_ascPochhammer`：descPochhammer_eval_eq_ascPochhamm
er (r : R) (n : Nat) : (descPochhammer R n).eval r = (ascPochhammer R n).eval (r
 - n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.Common.smul_congr`：∀ {R : Type u_2} {α : Type u_3} [
inst : CommSemiring α] [inst_1 : SMul R α] {r : R} {a b t c : α},   a = b → (∀ (
x : α), r • x = t * x) → t …
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 87 条，此处仅展示前 30 条）
-/
theorem binomialSeries_eq_ordinaryHypergeometricSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂]
    {𝔸 : Type v} [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] {a b : 𝕂}
    (h : ∀ (k : ℕ), (k : 𝕂) ≠ -b) :
    binomialSeries 𝔸 a =
    (ordinaryHypergeometricSeries 𝔸 (-a) b b).compContinuousLinearMap (-(.id _ _)) := by
  simp only [binomialSeries, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.ofScalars_comp_neg_id]
  congr! with n
  rw [ordinaryHypergeometricCoefficient,
    mul_inv_cancel_right₀ (by simp [ascPochhammer_eval_eq_zero_iff]; grind)]
  simp only [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_cast, Polynomial.ascPochhammer_smeval_eq_eval,
    ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_ascPochhammer]
  ring_nf
  simp

/-- The radius of convergence of `binomialSeries 𝔸 a` is `⊤` for natural `a`. -/
/-
**binomialSeries_radius_eq_top_of_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：binomialSeries_radius_eq_top_of_nat {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [
NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸] {a : Nat} : (binomialSeries 𝔸 (a : 𝕂))
.radius = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `binomialSeries_eq_ordinaryHypergeometricSeries`：binomialSeries_eq_ordina
ryHypergeometricSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] {𝔸 : Type v} [Ring 𝔸]
 [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `FormalMultilinearSeries.radius_compNeg`：radius_compNeg [Nontrivial E] (p
 : FormalMultilinearSeries 𝕜 E F) : (p.compContinuousLinearMap (-(.id _ _))).rad
ius = p.radius
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `ordinaryHypergeometric_radius_top_of_neg_nat₁`：ordinaryHypergeometric_ra
dius_top_of_neg_nat₁ {k : Nat} : (ordinaryHypergeometricSeries 𝔸 (-(k : 𝕂)) b c)
.radius = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The radius of convergence of `binomialSeries 𝔸 a` is `⊤` for natural `a`.
-/
theorem binomialSeries_radius_eq_top_of_nat {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u}
    [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸] {a : ℕ} :
    (binomialSeries 𝔸 (a : 𝕂)).radius = ⊤ := by
  simp [binomialSeries_eq_ordinaryHypergeometricSeries (b := (1 : 𝕂)) (by norm_cast; simp),
    ordinaryHypergeometric_radius_top_of_neg_nat₁]

/-- The radius of convergence of `binomialSeries 𝔸 a` is `1`, when `a` is not natural. -/
/-
**binomialSeries_radius_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：binomialSeries_radius_eq_one {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [NormedD
ivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸] {a : 𝕂} (ha : forall (k : Nat), a != k) : (bi
nomialSeries 𝔸 a).radius = 1
参数：ha : forall (k : Nat), a != k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `binomialSeries_eq_ordinaryHypergeometricSeries`：binomialSeries_eq_ordina
ryHypergeometricSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] {𝔸 : Type v} [Ring 𝔸]
 [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `FormalMultilinearSeries.radius_compNeg`：radius_compNeg [Nontrivial E] (p
 : FormalMultilinearSeries 𝕜 E F) : (p.compContinuousLinearMap (-(.id _ _))).rad
ius = p.radius
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `ordinaryHypergeometricSeries_radius_eq_one`：ordinaryHypergeometricSeries
_radius_eq_one (habc : forall kn : Nat, ↑kn != -a ∧ ↑kn != -b ∧ ↑kn != -c) : (or
dinaryHypergeometricSeries 𝔸 a b…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a

--- 原说明 ---
The radius of convergence of `binomialSeries 𝔸 a` is `1`, when `a` is not natura
l.
-/
theorem binomialSeries_radius_eq_one {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [NormedDivisionRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] {a : 𝕂} (ha : ∀ (k : ℕ), a ≠ k) : (binomialSeries 𝔸 a).radius = 1 := by
  simp only [binomialSeries_eq_ordinaryHypergeometricSeries (b := (1 : 𝕂)) (by norm_cast; simp),
    FormalMultilinearSeries.radius_compNeg]
  conv at ha => ext; rw [ne_comm]
  exact ordinaryHypergeometricSeries_radius_eq_one _ _ _ _ (by norm_cast; grind)
/-
**binomialSeries_radius_ge_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：binomialSeries_radius_ge_one {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedDiv
isionRing 𝔸] [NormedAlgebra 𝕂 𝔸] {a : 𝕂} : 1 <= (binomialSeries 𝔸 a).radius
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `binomialSeries_radius_eq_one`：binomialSeries_radius_eq_one {𝕂 : Type v} 
[RCLike 𝕂] {𝔸 : Type u} [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸] {a : 𝕂} (ha :
 forall (k : Nat),…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `binomialSeries_radius_eq_top_of_nat`：binomialSeries_radius_eq_top_of_nat
 {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
 {a : Nat} : (binomialSer…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem binomialSeries_radius_ge_one {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedDivisionRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] {a : 𝕂} :
    1 ≤ (binomialSeries 𝔸 a).radius := by
  by_cases ha : ∀ (k : ℕ), a ≠ k
  · rw [binomialSeries_radius_eq_one ha]
  · push Not at ha
    rcases ha with ⟨k, rfl⟩
    simp [binomialSeries_radius_eq_top_of_nat]

namespace Complex

/-
**Complex.one_add_cpow_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Com
plex`。
形式化陈述：one_add_cpow_hasFPowerSeriesOnBall_zero {a : Complex} : HasFPowerSeriesOnB
all (fun x => (1 + x) ^ a) (binomialSeries Complex a) 0 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_div_iff_mul_eq`：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c =
 b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul'`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (a : α) (n :
 ℕ), n • a = a * ↑n
· 使用定理 `Ring.descPochhammer_eq_factorial_smul_choose`：descPochhammer_eq_factoria
l_smul_choose [NatPowAssoc R] (r : R) (n : Nat) : (descPochhammer Int n).smeval 
r = n.factorial • choose r n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `Polynomial.smeval_one`：smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 97 条，此处仅展示前 30 条）
-/
theorem one_add_cpow_hasFPowerSeriesOnBall_zero {a : ℂ} :
    HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ a) (binomialSeries ℂ a) 0 1 := by
  suffices (binomialSeries ℂ a = FormalMultilinearSeries.ofScalars ℂ
      fun n ↦ iteratedDeriv n (fun (x : ℂ) ↦ (1 + x) ^ a) 0 / n !) by
    convert! AnalyticOn.hasFPowerSeriesOnSubball _ _ _
    · norm_num
    · -- TODO: use `fun_prop` for this subgoal
      apply AnalyticOn.cpow (analyticOn_const.add analyticOn_id) analyticOn_const
      intro z hz
      apply Complex.mem_slitPlane_of_norm_lt_one
      rw [← ENNReal.ofReal_one, Metric.eball_ofReal] at hz
      simpa using hz
    · rw [← this]
      exact binomialSeries_radius_ge_one
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_series_eq_iff]
  ext n
  rw [eq_div_iff_mul_eq (by simp [Nat.factorial_ne_zero]), ← nsmul_eq_mul',
    ← Ring.descPochhammer_eq_factorial_smul_choose]
  let B := Metric.ball (0 : ℂ) 1
  suffices Set.EqOn (iteratedDerivWithin n (fun x ↦ (1 + x) ^ a) B)
      (fun x ↦ (descPochhammer ℤ n).smeval a * (1 + x) ^ (a - n)) B by
    specialize this (show 0 ∈ _ by simp [B])
    rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (by simp)] at this
    symm
    simpa using this
  induction n with
  | zero => simp [Set.EqOn]
  | succ n ih =>
    have : iteratedDerivWithin (n + 1) (fun (x : ℂ) ↦ (1 + x) ^ a) B =
        derivWithin (iteratedDerivWithin n (fun x ↦ (1 + x) ^ a) B) B := by
      ext z
      rw [iteratedDerivWithin_succ]
    rw [this]
    have : Set.EqOn (derivWithin (iteratedDerivWithin n (fun (x : ℂ) ↦ (1 + x) ^ a) B) B)
        (derivWithin (fun x ↦ (descPochhammer ℤ n).smeval a * (1 + x) ^ (a - ↑n)) B) B := by
      intro z hz
      rw [derivWithin_congr (fun _ hz ↦ ih hz) (ih hz)]
    apply Set.EqOn.trans this
    intro z hz
    simp only [Nat.cast_add, Nat.cast_one, B, derivWithin_of_isOpen Metric.isOpen_ball hz,
      deriv_const_mul_field']
    rw [_root_.deriv_cpow_const (by fun_prop), deriv_const_add_id, mul_one,
      show a - (n + 1) = a - n - 1 by ring, ← mul_assoc]
    · congr
      simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_natCast]
    · apply Complex.mem_slitPlane_of_norm_lt_one
      simpa [B] using hz
/-
**Complex.one_add_cpow_hasFPowerSeriesAt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex
`。
形式化陈述：one_add_cpow_hasFPowerSeriesAt_zero {a : Complex} : HasFPowerSeriesAt (fun
 x => (1 + x) ^ a) (binomialSeries Complex a) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.one_add_cpow_hasFPowerSeriesOnBall_zero`：one_add_cpow_hasFPowerS
eriesOnBall_zero {a : Complex} : HasFPowerSeriesOnBall (fun x => (1 + x) ^ a) (b
inomialSeries Complex a) 0 1
-/
theorem one_add_cpow_hasFPowerSeriesAt_zero {a : ℂ} :
    HasFPowerSeriesAt (fun x ↦ (1 + x) ^ a) (binomialSeries ℂ a) 0 :=
  one_add_cpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt
/-
**Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命
名空间 `Complex`。
形式化陈述：one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a : Complex) : HasFPowerS
eriesOnBall (fun x => 1 / (1 - x) ^ a) (.ofScalars Complex fun n => Ring.choose 
(a + n - 1) n) 0 1
参数：a : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FormalMultilinearSeries.ofScalars.congr_simp`：∀ {𝕜 : Type u_1} (E : Type
 u_2) [inst : Field 𝕜] [inst_1 : Ring E] [inst_2 : Algebra 𝕜 E] [inst_3 : Topolo
gicalSpace E]   [inst_4 : IsTopolo…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ring.choose_neg`：choose_neg [NatPowAssoc R] (r : R) (n : Nat) : choose (
-r) n = Int.negOnePow n • choose (r + n - 1) n
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用引理 `Int.coe_negOnePow`：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.neg
OnePow : R) = (-1 : R) ^ n.natAbs
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
（共 49 条，此处仅展示前 30 条）
-/
theorem one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a : ℂ) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x) ^ a)
      (.ofScalars ℂ fun n ↦ Ring.choose (a + n - 1) n) 0 1 := by
  have H : ((binomialSeries ℂ (-a)).compContinuousLinearMap (-1)) =
      .ofScalars ℂ fun n ↦ Ring.choose (a + n - 1) n := by
    ext n; simp [FormalMultilinearSeries.compContinuousLinearMap, binomialSeries, Ring.choose_neg,
      Units.smul_def, ← pow_add, ← mul_assoc]
  have : HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ (-a)) (binomialSeries ℂ (-a : ℂ)) (-0) 1 := by
    simpa using one_add_cpow_hasFPowerSeriesOnBall_zero
  simpa [cpow_neg, Function.comp_def, ← sub_eq_add_neg, H] using
    this.compContinuousLinearMap (u := -1) (x := (0 : ℂ))
/-
**Complex.one_div_one_sub_pow_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名
空间 `Complex`。
形式化陈述：one_div_one_sub_pow_hasFPowerSeriesOnBall_zero (a : Nat) : HasFPowerSeries
OnBall (fun x => 1 / (1 - x) ^ (a + 1)) (.ofScalars Complex (𝕜
参数：a : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.cpow_natCast`：cpow_natCast (x : Complex) (n : Nat) : x ^ (n : Co
mplex) = x ^ n
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Ring.choose_natCast`：choose_natCast [NatPowAssoc R] (n k : Nat) : choose
 (n : R) k = Nat.choose n k
· 使用定理 `Nat.choose_symm_add`：choose_symm_add {a b : Nat} : choose (a + b) a = ch
oose (a + b) b
· 使用定理 `Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`：one_div_one_sub
_cpow_hasFPowerSeriesOnBall_zero (a : Complex) : HasFPowerSeriesOnBall (fun x =>
 1 / (1 - x) ^ a) (.ofScalars Complex fun n =…
-/
theorem one_div_one_sub_pow_hasFPowerSeriesOnBall_zero (a : ℕ) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x) ^ (a + 1))
      (.ofScalars ℂ (𝕜 := ℂ) fun n ↦ ↑(Nat.choose (a + n) a)) 0 1 := by
  convert one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a + 1) with z n
  · norm_cast
  · rw [eq_comm, add_right_comm, add_sub_cancel_right, ← Nat.cast_add,
      Ring.choose_natCast, Nat.choose_symm_add]
/-
**Complex.one_div_sub_pow_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Complex`。
形式化陈述：one_div_sub_pow_hasFPowerSeriesOnBall_zero (a : Nat) {z : Complex} (hz : z
 != 0) : HasFPowerSeriesOnBall (fun x => 1 / (z - x) ^ (a + 1)) (.ofScalars Comp
lex (𝕜
参数：a : Nat；hz : z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.one_div_one_sub_pow_hasFPowerSeriesOnBall_zero`：one_div_one_sub_
pow_hasFPowerSeriesOnBall_zero (a : Nat) : HasFPowerSeriesOnBall (fun x => 1 / (
1 - x) ^ (a + 1)) (.ofScalars Complex (𝕜
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesOnBall.compContinuousLinearMap`：HasFPowerSeriesOnBall.com
pContinuousLinearMap (hf : HasFPowerSeriesOnBall f pf (u x) r) : HasFPowerSeries
OnBall (f ∘ u) (pf.compContinuousLi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `enorm_smul`：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α 
β] (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
· 使用定理 `instENormSMulClass`：∀ {α : Type u_1} {β : Type u_2} [inst : SeminormedRi
ng α] [inst_1 : SeminormedAddGroup β] [inst_2 : SMul α β]   [NormSMulClass α β],
 ENormSM…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `enorm_inv`：enorm_inv {a : α} (ha : a != 0) : ‖a⁻¹‖ₑ = ‖a‖ₑ⁻¹
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
（共 66 条，此处仅展示前 30 条）
-/
theorem one_div_sub_pow_hasFPowerSeriesOnBall_zero (a : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (z - x) ^ (a + 1))
      (.ofScalars ℂ (𝕜 := ℂ) fun n ↦ (z ^ (n + a + 1))⁻¹ * ↑(Nat.choose (a + n) a)) 0 ‖z‖ₑ := by
  have := one_div_one_sub_pow_hasFPowerSeriesOnBall_zero a
  rw [← map_zero (z⁻¹ • 1 : ℂ →L[ℂ] ℂ)] at this
  have := this.compContinuousLinearMap
  have H : 1 / ‖(z⁻¹ • 1 : ℂ →L[ℂ] ℂ)‖ₑ = ‖z‖ₑ := by simp [enorm_smul, enorm_inv, hz]
  simp only [one_div, FunLike.coe_smul, H, Function.comp_def] at this
  convert (this.const_smul (c := (z ^ (a + 1))⁻¹)).congr ?_
  · ext n
    simp only [FormalMultilinearSeries.smul_apply, smul_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp [add_assoc, pow_add _ _ (a + 1), mul_assoc]
  · intro w hw
    simp [← mul_inv_rev, ← mul_pow, sub_mul, mul_right_comm _ w, hz]
/-
**Complex.one_div_sub_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex`。
形式化陈述：one_div_sub_hasFPowerSeriesOnBall_zero {z : Complex} (hz : z != 0) : HasFP
owerSeriesOnBall (fun x => 1 / (z - x)) (.ofScalars Complex fun n => (z ^ (n + 1
))⁻¹) 0 ‖z‖ₑ
参数：hz : z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.one_div_sub_pow_hasFPowerSeriesOnBall_zero`：one_div_sub_pow_hasF
PowerSeriesOnBall_zero (a : Nat) {z : Complex} (hz : z != 0) : HasFPowerSeriesOn
Ball (fun x => 1 / (z - x) ^ (a + 1)) (.…
-/
theorem one_div_sub_hasFPowerSeriesOnBall_zero {z : ℂ} (hz : z ≠ 0) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (z - x)) (.ofScalars ℂ fun n ↦ (z ^ (n + 1))⁻¹) 0 ‖z‖ₑ := by
  simpa using one_div_sub_pow_hasFPowerSeriesOnBall_zero (a := 0) hz
/-
**Complex.one_div_sub_sq_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `C
omplex`。
形式化陈述：one_div_sub_sq_hasFPowerSeriesOnBall_zero {z : Complex} (hz : z != 0) : Ha
sFPowerSeriesOnBall (fun x => 1 / (z - x) ^ 2) (.ofScalars Complex fun n => (z ^
 (n + 2))⁻¹ * (n + 1)) 0 ‖z‖ₑ
参数：hz : z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.one_div_sub_pow_hasFPowerSeriesOnBall_zero`：one_div_sub_pow_hasF
PowerSeriesOnBall_zero (a : Nat) {z : Complex} (hz : z != 0) : HasFPowerSeriesOn
Ball (fun x => 1 / (z - x) ^ (a + 1)) (.…
-/
theorem one_div_sub_sq_hasFPowerSeriesOnBall_zero {z : ℂ} (hz : z ≠ 0) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (z - x) ^ 2)
      (.ofScalars ℂ fun n ↦ (z ^ (n + 2))⁻¹ * (n + 1)) 0 ‖z‖ₑ := by
  simpa [add_comm 1] using one_div_sub_pow_hasFPowerSeriesOnBall_zero 1 hz
/-
**Complex.one_div_one_sub_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Complex`。
形式化陈述：one_div_one_sub_hasFPowerSeriesOnBall_zero : HasFPowerSeriesOnBall (fun x 
=> 1 / (1 - x : Complex)) (.ofScalars (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Complex.one_div_sub_hasFPowerSeriesOnBall_zero`：one_div_sub_hasFPowerSer
iesOnBall_zero {z : Complex} (hz : z != 0) : HasFPowerSeriesOnBall (fun x => 1 /
 (z - x)) (.ofScalars Complex fun n …
-/
theorem one_div_one_sub_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x : ℂ)) (.ofScalars (𝕜 := ℂ) ℂ 1) 0 1 := by
  simpa using! one_div_sub_hasFPowerSeriesOnBall_zero (z := 1)
/-
**Complex.one_div_one_sub_sq_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空
间 `Complex`。
形式化陈述：one_div_one_sub_sq_hasFPowerSeriesOnBall_zero : HasFPowerSeriesOnBall (fun
 x => 1 / (1 - x : Complex) ^ 2) (.ofScalars Complex fun n => (n + 1 : Complex))
 0 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Complex.one_div_sub_sq_hasFPowerSeriesOnBall_zero`：one_div_sub_sq_hasFPo
werSeriesOnBall_zero {z : Complex} (hz : z != 0) : HasFPowerSeriesOnBall (fun x 
=> 1 / (z - x) ^ 2) (.ofScalars Complex…
-/
theorem one_div_one_sub_sq_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x : ℂ) ^ 2) (.ofScalars ℂ fun n ↦ (n + 1 : ℂ)) 0 1 := by
  simpa using one_div_sub_sq_hasFPowerSeriesOnBall_zero (z := 1)

/-- `∑ (ai + b) zⁱ = (b - a) / (1 - z) + a / (1 - z)²` -/
/-
**Complex.hasFPowerSeriesOnBall_ofScalars_mul_add_zero** 是 Mathlib 中的一个定理，位于命名空间
 `Complex`。
形式化陈述：hasFPowerSeriesOnBall_ofScalars_mul_add_zero (a b : Complex) : HasFPowerSe
riesOnBall (fun x => (b - a) / (1 - x) + a / (1 - x) ^ 2) (.ofScalars Complex fu
n n => a * n + b) 0 1
参数：a b : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
`∑ (ai + b) zⁱ = (b - a) / (1 - z) + a / (1 - z)²`
-/
theorem hasFPowerSeriesOnBall_ofScalars_mul_add_zero (a b : ℂ) :
    HasFPowerSeriesOnBall (fun x ↦ (b - a) / (1 - x) + a / (1 - x) ^ 2)
      (.ofScalars ℂ fun n ↦ a * n + b) 0 1 := by
  convert
    (one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul (c := b - a)).add
      (one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul (c := a))
  · simp [div_eq_mul_inv]
  · ext; simp; ring
/-
**Complex.one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero** 是 Mathlib 中
的一个引理，位于命名空间 `Complex`。
形式化陈述：one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero (w x : Complex) (
hw : w != x) : HasFPowerSeriesOnBall (fun z => 1 / (z - w) ^ 2 - 1 / w ^ 2) (.of
Scalars Complex fun i => (i + 1) * (w - x) ^ (-↑(i + 2) : Int) - i.casesOn (w ^ 
(-2 : Int)) 0) x ‖w - x‖ₑ
参数：w x : Complex；hw : w != x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.sub_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub (G
 i)] (f g : (i : ι) → G i), f - g = fun i => f i - g i
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用引理 `FormalMultilinearSeries.ofScalars_sub`：ofScalars_sub (c' : Nat -> 𝕜) : o
fScalars E (c - c') = ofScalars E c - ofScalars E c'
· 使用定理 `HasFPowerSeriesOnBall.sub`：HasFPowerSeriesOnBall.sub (hf : HasFPowerSeri
esOnBall f pf x r) (hg : HasFPowerSeriesOnBall g pg x r) : HasFPowerSeriesOnBall
 (f - g) (pf - …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用引理 `sub_sq_comm`：sub_sq_comm (a b : R) : (a - b) ^ 2 = (b - a) ^ 2
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasFPowerSeriesOnBall.comp_sub`：HasFPowerSeriesOnBall.comp_sub (hf : Has
FPowerSeriesOnBall f p x r) (y : E) : HasFPowerSeriesOnBall (fun z => f (z - y))
 p (x + y) r
· 使用定理 `Complex.one_div_sub_sq_hasFPowerSeriesOnBall_zero`：one_div_sub_sq_hasFPo
werSeriesOnBall_zero {z : Complex} (hz : z != 0) : HasFPowerSeriesOnBall (fun x 
=> 1 / (z - x) ^ 2) (.ofScalars Complex…
（共 55 条，此处仅展示前 30 条）
-/
lemma one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero (w x : ℂ) (hw : w ≠ x) :
    HasFPowerSeriesOnBall (fun z ↦ 1 / (z - w) ^ 2 - 1 / w ^ 2) (.ofScalars ℂ
      fun i ↦ (i + 1) * (w - x) ^ (-↑(i + 2) : ℤ) - i.casesOn (w ^ (-2 : ℤ)) 0) x ‖w - x‖ₑ := by
  rw [← Pi.sub_def, ← Pi.sub_def, FormalMultilinearSeries.ofScalars_sub]
  refine .sub ?_ ?_
  · simpa only [sub_sub_sub_cancel_right, zero_add, sub_sq_comm w, zpow_neg, zpow_natCast, mul_comm]
      using (one_div_sub_sq_hasFPowerSeriesOnBall_zero
        (z := w - x) (by simp [sub_eq_zero, hw])).comp_sub x
  · convert! hasFPowerSeriesOnBall_const.mono _ le_top
    · ext (_ | _) <;> simp [zpow_ofNat]
    · simpa [sub_eq_zero]

end Complex

namespace Real

attribute [local simp← ] Complex.ofReal_choose in
attribute [-simp] FormalMultilinearSeries.apply_eq_prod_smul_coeff in
/-
**Real.one_add_rpow_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_add_rpow_hasFPowerSeriesOnBall_zero {a : Real} : HasFPowerSeriesOnBall
 (fun x => (1 + x) ^ a) (binomialSeries Real a) 0 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `binomialSeries_apply`：binomialSeries_apply {𝕂 : Type u} [Field 𝕂] [CharZ
ero 𝕂] (𝔸 : Type v) [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRi
ng 𝔸] (a :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HasFPowerSeriesOnBall.restrictScalars`：HasFPowerSeriesOnBall.restrictSca
lars (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesOnBall f (p.restrictS
calars 𝕜) x r
· 使用定理 `Complex.one_add_cpow_hasFPowerSeriesOnBall_zero`：one_add_cpow_hasFPowerS
eriesOnBall_zero {a : Complex} : HasFPowerSeriesOnBall (fun x => (1 + x) ^ a) (b
inomialSeries Complex a) 0 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.map_zero`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : 
Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 
: TopologicalSpace…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
（共 43 条，此处仅展示前 30 条）
-/
theorem one_add_rpow_hasFPowerSeriesOnBall_zero {a : ℝ} :
    HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ a) (binomialSeries ℝ a) 0 1 := by
  have H : binomialSeries ℂ a = (binomialSeries ℂ (a : ℂ)).restrictScalars (𝕜 := ℝ) := by aesop
  have : HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ (a : ℂ)) (binomialSeries ℂ a) (.ofRealCLM 0) 1 :=
    Complex.ofRealCLM.map_zero ▸ H ▸ Complex.one_add_cpow_hasFPowerSeriesOnBall_zero.restrictScalars
  convert! (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap).congr ?_
  · ext; simp [Function.comp_def]
  · simp
  · intro x hx; simp_all; norm_cast
/-
**Real.one_add_rpow_hasFPowerSeriesAt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_add_rpow_hasFPowerSeriesAt_zero {a : Real} : HasFPowerSeriesAt (fun x 
=> (1 + x) ^ a) (binomialSeries Real a) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Real.one_add_rpow_hasFPowerSeriesOnBall_zero`：one_add_rpow_hasFPowerSeri
esOnBall_zero {a : Real} : HasFPowerSeriesOnBall (fun x => (1 + x) ^ a) (binomia
lSeries Real a) 0 1
-/
theorem one_add_rpow_hasFPowerSeriesAt_zero {a : ℝ} :
    HasFPowerSeriesAt (fun x ↦ (1 + x) ^ a) (binomialSeries ℝ a) 0 :=
  one_add_rpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt
/-
**Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空间
 `Real`。
形式化陈述：one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (a : Real) : HasFPowerSeri
esOnBall (fun x => 1 / (1 - x) ^ a) (.ofScalars Real fun n => Ring.choose (a + n
 - 1) n) 0 1
参数：a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `HasFPowerSeriesOnBall.restrictScalars`：HasFPowerSeriesOnBall.restrictSca
lars (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesOnBall f (p.restrictS
calars 𝕜) x r
· 使用定理 `Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`：one_div_one_sub
_cpow_hasFPowerSeriesOnBall_zero (a : Complex) : HasFPowerSeriesOnBall (fun x =>
 1 / (1 - x) ^ a) (.ofScalars Complex fun n =…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
（共 46 条，此处仅展示前 30 条）
-/
theorem one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (a : ℝ) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x) ^ a)
      (.ofScalars ℝ fun n ↦ Ring.choose (a + n - 1) n) 0 1 := by
  have := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).restrictScalars (𝕜 := ℝ)
  rw [← Complex.ofRealCLM.map_zero] at this
  convert (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap).congr ?_
  · ext n
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp
    norm_cast
  · simp
  · intro x hx
    have : |x| < 1 := by simpa [enorm_eq_nnnorm] using! hx
    have : 0 ≤ 1 - x := by grind
    simp [-Complex.inv_re, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow this]
/-
**Real.one_div_sub_pow_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rea
l`。
形式化陈述：one_div_sub_pow_hasFPowerSeriesOnBall_zero (a : Nat) {r : Real} (hr : r !=
 0) : HasFPowerSeriesOnBall (fun x => 1 / (r - x) ^ (a + 1)) (.ofScalars Real (𝕜
参数：a : Nat；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `HasFPowerSeriesOnBall.restrictScalars`：HasFPowerSeriesOnBall.restrictSca
lars (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesOnBall f (p.restrictS
calars 𝕜) x r
· 使用定理 `Complex.one_div_sub_pow_hasFPowerSeriesOnBall_zero`：one_div_sub_pow_hasF
PowerSeriesOnBall_zero (a : Nat) {z : Complex} (hz : z != 0) : HasFPowerSeriesOn
Ball (fun x => 1 / (z - x) ^ (a + 1)) (.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
（共 46 条，此处仅展示前 30 条）
-/
theorem one_div_sub_pow_hasFPowerSeriesOnBall_zero (a : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (r - x) ^ (a + 1))
      (.ofScalars ℝ (𝕜 := ℝ) fun n ↦ (r ^ (n + a + 1))⁻¹ * ↑(Nat.choose (a + n) a)) 0 ‖r‖ₑ := by
  have := (Complex.one_div_sub_pow_hasFPowerSeriesOnBall_zero a (z := r)
    (by simpa)).restrictScalars (𝕜 := ℝ)
  rw [← Complex.ofRealCLM.map_zero] at this
  convert (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap)
  · simp [-Complex.inv_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_sub]
  · ext n
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp [-Complex.inv_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
  · simp [enorm_eq_nnnorm]
/-
**Real.one_div_sub_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_div_sub_hasFPowerSeriesOnBall_zero {r : Real} (hr : r != 0) : HasFPowe
rSeriesOnBall (fun x => 1 / (r - x)) (.ofScalars Real fun n => (r ^ (n + 1))⁻¹) 
0 ‖r‖ₑ
参数：hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.one_div_sub_pow_hasFPowerSeriesOnBall_zero`：one_div_sub_pow_hasFPow
erSeriesOnBall_zero (a : Nat) {r : Real} (hr : r != 0) : HasFPowerSeriesOnBall (
fun x => 1 / (r - x) ^ (a + 1)) (.ofS…
-/
theorem one_div_sub_hasFPowerSeriesOnBall_zero {r : ℝ} (hr : r ≠ 0) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (r - x)) (.ofScalars ℝ fun n ↦ (r ^ (n + 1))⁻¹) 0 ‖r‖ₑ := by
  simpa using one_div_sub_pow_hasFPowerSeriesOnBall_zero (a := 0) hr
/-
**Real.one_div_sub_sq_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real
`。
形式化陈述：one_div_sub_sq_hasFPowerSeriesOnBall_zero {r : Real} (hr : r != 0) : HasFP
owerSeriesOnBall (fun x => 1 / (r - x) ^ 2) (.ofScalars Real fun n => (r ^ (n + 
2))⁻¹ * (n + 1)) 0 ‖r‖ₑ
参数：hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.one_div_sub_pow_hasFPowerSeriesOnBall_zero`：one_div_sub_pow_hasFPow
erSeriesOnBall_zero (a : Nat) {r : Real} (hr : r != 0) : HasFPowerSeriesOnBall (
fun x => 1 / (r - x) ^ (a + 1)) (.ofS…
-/
theorem one_div_sub_sq_hasFPowerSeriesOnBall_zero {r : ℝ} (hr : r ≠ 0) :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (r - x) ^ 2)
      (.ofScalars ℝ fun n ↦ (r ^ (n + 2))⁻¹ * (n + 1)) 0 ‖r‖ₑ := by
  simpa [add_comm 1] using one_div_sub_pow_hasFPowerSeriesOnBall_zero 1 hr
/-
**Real.one_div_one_sub_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rea
l`。
形式化陈述：one_div_one_sub_hasFPowerSeriesOnBall_zero : HasFPowerSeriesOnBall (fun x 
=> 1 / (1 - x)) (.ofScalars (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Real.one_div_sub_hasFPowerSeriesOnBall_zero`：one_div_sub_hasFPowerSeries
OnBall_zero {r : Real} (hr : r != 0) : HasFPowerSeriesOnBall (fun x => 1 / (r - 
x)) (.ofScalars Real fun n => (r …
-/
theorem one_div_one_sub_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x)) (.ofScalars (𝕜 := ℝ) ℝ 1) 0 1 := by
  simpa using! one_div_sub_hasFPowerSeriesOnBall_zero (r := 1)
/-
**Real.one_div_one_sub_sq_hasFPowerSeriesOnBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Real`。
形式化陈述：one_div_one_sub_sq_hasFPowerSeriesOnBall_zero : HasFPowerSeriesOnBall (fun
 x => 1 / (1 - x) ^ 2) (.ofScalars Real fun n => (n + 1 : Real)) 0 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Real.one_div_sub_sq_hasFPowerSeriesOnBall_zero`：one_div_sub_sq_hasFPower
SeriesOnBall_zero {r : Real} (hr : r != 0) : HasFPowerSeriesOnBall (fun x => 1 /
 (r - x) ^ 2) (.ofScalars Real fun n…
-/
theorem one_div_one_sub_sq_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x ↦ 1 / (1 - x) ^ 2) (.ofScalars ℝ fun n ↦ (n + 1 : ℝ)) 0 1 := by
  simpa using one_div_sub_sq_hasFPowerSeriesOnBall_zero (r := 1)

/-- `∑ (ai + b) zⁱ = (b - a) / (1 - z) + a / (1 - z)²` -/
/-
**Real.hasFPowerSeriesOnBall_ofScalars_mul_add_zero** 是 Mathlib 中的一个定理，位于命名空间 `R
eal`。
形式化陈述：hasFPowerSeriesOnBall_ofScalars_mul_add_zero (a b : Real) : HasFPowerSerie
sOnBall (fun x => (b - a) / (1 - x) + a / (1 - x) ^ 2) (.ofScalars Real (a * · +
 b)) 0 1
参数：a b : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
（共 70 条，此处仅展示前 30 条）

--- 原说明 ---
`∑ (ai + b) zⁱ = (b - a) / (1 - z) + a / (1 - z)²`
-/
theorem hasFPowerSeriesOnBall_ofScalars_mul_add_zero (a b : ℝ) :
    HasFPowerSeriesOnBall (fun x ↦ (b - a) / (1 - x) + a / (1 - x) ^ 2)
      (.ofScalars ℝ (a * · + b)) 0 1 := by
  convert!
    (one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul (c := b - a)).add
      (one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul (c := a)) using 2
  · simp [div_eq_mul_inv]
  · ext; simp; ring

end Real

