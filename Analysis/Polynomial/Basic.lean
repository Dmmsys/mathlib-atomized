/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Limits related to polynomial and rational functions

This file proves basic facts about limits of polynomial and rational functions.
The main result is `Polynomial.isEquivalent_atTop_lead`, which states that for
any polynomial `P` of degree `n` with leading coefficient `a`, the corresponding
polynomial function is equivalent to `a * x^n` as `x` goes to +∞.

We can then use this result to prove various limits for polynomial and rational
functions, depending on the degrees and leading coefficients of the considered
polynomials.
-/

public section


open Filter Finset Asymptotics

open Asymptotics Polynomial Topology

namespace Polynomial

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (P Q : 𝕜[X])

/-
**Polynomial.eventually_atTop_not_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eventually_atTop_not_isRoot (hP : P != 0) : forallᶠ x in atTop, ¬P.IsRoot 
x
参数：hP : P != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.atTop_le_cofinite`：atTop_le_cofinite [Preorder α] [NoTopOrder α] 
: (atTop : Filter α) <= cofinite
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
· 使用定理 `Polynomial.finite_setOfPred_isRoot`：finite_setOfPred_isRoot {p : R[X]} (
hp : p != 0) : Set.Finite { x | IsRoot p x }
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem eventually_atTop_not_isRoot (hP : P ≠ 0) : ∀ᶠ x in atTop, ¬P.IsRoot x :=
  atTop_le_cofinite <| (finite_setOfPred_isRoot hP).compl_mem_cofinite

@[deprecated (since := "2026-02-05")] alias eventually_no_roots := eventually_atTop_not_isRoot
/-
**Polynomial.eventually_atBot_not_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eventually_atBot_not_isRoot (hP : P != 0) : forallᶠ x in atBot, ¬P.IsRoot 
x
参数：hP : P != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.atBot_le_cofinite`：atBot_le_cofinite [Preorder α] [NoBotOrder α] 
: (atBot : Filter α) <= cofinite
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
· 使用定理 `Polynomial.finite_setOfPred_isRoot`：finite_setOfPred_isRoot {p : R[X]} (
hp : p != 0) : Set.Finite { x | IsRoot p x }
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem eventually_atBot_not_isRoot (hP : P ≠ 0) : ∀ᶠ x in atBot, ¬P.IsRoot x :=
  atBot_le_cofinite <| (finite_setOfPred_isRoot hP).compl_mem_cofinite

variable [OrderTopology 𝕜]

section PolynomialAtTop

/-
**Polynomial.isEquivalent_atTop_lead** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isEquivalent_atTop_lead : (fun x => eval x P) ~[atTop] fun x => P.leadingC
oeff * x ^ P.natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_eq_sum_range`：eval_eq_sum_range {p : R[X]} (x : R) : p.e
val x = ∑ i in Finset.range (p.natDegree + 1), p.coeff i * x ^ i
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Asymptotics.IsLittleO.add_isEquivalent`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   u =o[l] w → Asym
ptotics.IsEquivalent l v w →…
· 使用定理 `Asymptotics.IsLittleO.fun_sum`：∀ {α : Type u_1} {E' : Type u_6} {F' : Ty
pe u_7} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F'] 
  {g' : α → F'} {l …
· 使用定理 `Asymptotics.IsLittleO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R
 : Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filte
r α}   {f : α → R}, f =o[l…
· 使用定理 `Asymptotics.IsLittleO.const_mul_right`：∀ {α : Type u_1} {E : Type u_3} [
inst : Norm E] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S] {f : α →
 E}   {l : Filter α} {g : α…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Asymptotics.isLittleO_pow_pow_atTop_of_lt`：Asymptotics.isLittleO_pow_pow
_atTop_of_lt [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] {p q : Na
t} (hpq : p < q) : (fun x : 𝕜 =…
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u
-/
theorem isEquivalent_atTop_lead :
    (fun x => eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree := by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [Polynomial.eval_eq_sum_range, sum_range_succ]
    exact
      IsLittleO.add_isEquivalent
        (IsLittleO.fun_sum fun i hi =>
          IsLittleO.const_mul_left
            ((IsLittleO.const_mul_right fun hz => h <| leadingCoeff_eq_zero.mp hz) <|
              isLittleO_pow_pow_atTop_of_lt (mem_range.mp hi))
            _)
        IsEquivalent.refl
/-
**Polynomial.tendsto_atTop_of_leadingCoeff_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 <= P.
leadingCoeff) : Tendsto (fun x => eval x P) atTop atTop
参数：hdeg : 0 < P.degree；hnng : 0 <= P.leadingCoeff。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.tendsto_atTop`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v : α
 → β}   {l : Filter α} [Orde…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Polynomial.isEquivalent_atTop_lead`：isEquivalent_atTop_lead : (fun x => 
eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree
· 使用定理 `Filter.tendsto_const_mul_pow_atTop`：tendsto_const_mul_pow_atTop (hn : n 
!= 0) (hc : 0 < c) : Tendsto (fun x => c * x ^ n) atTop atTop
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Polynomial.ne_zero_of_degree_gt`：ne_zero_of_degree_gt {n : WithBot Nat} 
(h : n < degree p) : p != 0
-/
theorem tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 ≤ P.leadingCoeff) :
    Tendsto (fun x => eval x P) atTop atTop :=
  P.isEquivalent_atTop_lead.symm.tendsto_atTop <|
    tendsto_const_mul_pow_atTop (natDegree_pos_iff_degree_pos.2 hdeg).ne' <|
      hnng.lt_of_ne' <| leadingCoeff_ne_zero.mpr <| ne_zero_of_degree_gt hdeg
/-
**Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：tendsto_atTop_iff_leadingCoeff_nonneg : Tendsto (fun x => eval x P) atTop 
atTop ↔ 0 < P.degree ∧ 0 <= P.leadingCoeff
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.tendsto_atTop`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v : α
 → β}   {l : Filter α} [Orde…
· 使用定理 `Polynomial.isEquivalent_atTop_lead`：isEquivalent_atTop_lead : (fun x => 
eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Filter.tendsto_const_mul_pow_atTop_iff`：tendsto_const_mul_pow_atTop_iff 
: Tendsto (fun x => c * x ^ n) atTop atTop ↔ n != 0 ∧ 0 < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg`：tendsto_atTop_of_leadin
gCoeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 <= P.leadingCoeff) : Tendsto (fun 
x => eval x P) atTop atTop
-/
theorem tendsto_atTop_iff_leadingCoeff_nonneg :
    Tendsto (fun x => eval x P) atTop atTop ↔ 0 < P.degree ∧ 0 ≤ P.leadingCoeff := by
  refine ⟨fun h => ?_, fun h => tendsto_atTop_of_leadingCoeff_nonneg P h.1 h.2⟩
  have : Tendsto (fun x => P.leadingCoeff * x ^ P.natDegree) atTop atTop :=
    (isEquivalent_atTop_lead P).tendsto_atTop h
  rw [tendsto_const_mul_pow_atTop_iff, ← pos_iff_ne_zero, natDegree_pos_iff_degree_pos] at this
  exact ⟨this.1, this.2.le⟩
/-
**Polynomial.tendsto_atBot_iff_leadingCoeff_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：tendsto_atBot_iff_leadingCoeff_nonpos : Tendsto (fun x => eval x P) atTop 
atBot ↔ 0 < P.degree ∧ P.leadingCoeff <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
· 使用定理 `Polynomial.leadingCoeff_neg`：leadingCoeff_neg (p : R[X]) : (-p).leadingC
oeff = -p.leadingCoeff
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_atBot_iff_leadingCoeff_nonpos :
    Tendsto (fun x => eval x P) atTop atBot ↔ 0 < P.degree ∧ P.leadingCoeff ≤ 0 := by
  simp only [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg,
    degree_neg, leadingCoeff_neg, neg_nonneg]
/-
**Polynomial.tendsto_atBot_of_leadingCoeff_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadi
ngCoeff <= 0) : Tendsto (fun x => eval x P) atTop atBot
参数：hdeg : 0 < P.degree；hnps : P.leadingCoeff <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.tendsto_atBot_iff_leadingCoeff_nonpos`：tendsto_atBot_iff_lead
ingCoeff_nonpos : Tendsto (fun x => eval x P) atTop atBot ↔ 0 < P.degree ∧ P.lea
dingCoeff <= 0
-/
theorem tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff ≤ 0) :
    Tendsto (fun x => eval x P) atTop atBot :=
  P.tendsto_atBot_iff_leadingCoeff_nonpos.2 ⟨hdeg, hnps⟩
/-
**Polynomial.abs_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：abs_tendsto_atTop (hdeg : 0 < P.degree) : Tendsto (fun x => abs <| eval x 
P) atTop atTop
参数：hdeg : 0 < P.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_abs_atTop_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G], Filter.Tendsto abs Filter.atTop Filter.atTop
· 使用定理 `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg`：tendsto_atTop_of_leadin
gCoeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 <= P.leadingCoeff) : Tendsto (fun 
x => eval x P) atTop atTop
· 使用定理 `Filter.tendsto_abs_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto abs Filter.at
Bot Filter.atTop
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Polynomial.tendsto_atBot_of_leadingCoeff_nonpos`：tendsto_atBot_of_leadin
gCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff <= 0) : Tendsto (fun 
x => eval x P) atTop atBot
-/
theorem abs_tendsto_atTop (hdeg : 0 < P.degree) :
    Tendsto (fun x => abs <| eval x P) atTop atTop := by
  rcases le_total 0 P.leadingCoeff with hP | hP
  · exact tendsto_abs_atTop_atTop.comp (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
  · exact tendsto_abs_atBot_atTop.comp (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)
/-
**Polynomial.isBoundedUnder_abs_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：isBoundedUnder_abs_atTop_iff : (IsBoundedUnder (· <= ·) atTop fun x => |ev
al x P|) ↔ P.degree <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.not_isBoundedUnder_of_tendsto_atTop`：not_isBoundedUnder_of_tendst
o_atTop [Preorder β] [NoMaxOrder β] {f : α -> β} {l : Filter α} [l.NeBot] (hf : 
Tendsto f l atTop) : ¬IsBoundedU…
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Polynomial.abs_tendsto_atTop`：abs_tendsto_atTop (hdeg : 0 < P.degree) : 
Tendsto (fun x => abs <| eval x P) atTop atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
-/
theorem isBoundedUnder_abs_atTop_iff :
    (IsBoundedUnder (· ≤ ·) atTop fun x => |eval x P|) ↔ P.degree ≤ 0 := by
  refine ⟨fun h => ?_, fun h => ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ => le_of_eq) fun x => congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop P h)

@[deprecated (since := "2026-02-05")] alias abs_isBoundedUnder_iff := isBoundedUnder_abs_atTop_iff
/-
**Polynomial.abs_tendsto_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：abs_tendsto_atTop_iff : Tendsto (fun x => abs <| eval x P) atTop atTop ↔ 0
 < P.degree
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isBoundedUnder_abs_atTop_iff`：isBoundedUnder_abs_atTop_iff : 
(IsBoundedUnder (· <= ·) atTop fun x => |eval x P|) ↔ P.degree <= 0
· 使用定理 `Filter.not_isBoundedUnder_of_tendsto_atTop`：not_isBoundedUnder_of_tendst
o_atTop [Preorder β] [NoMaxOrder β] {f : α -> β} {l : Filter α} [l.NeBot] (hf : 
Tendsto f l atTop) : ¬IsBoundedU…
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Polynomial.abs_tendsto_atTop`：abs_tendsto_atTop (hdeg : 0 < P.degree) : 
Tendsto (fun x => abs <| eval x P) atTop atTop
-/
theorem abs_tendsto_atTop_iff : Tendsto (fun x => abs <| eval x P) atTop atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt (isBoundedUnder_abs_atTop_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atTop P⟩
/-
**Polynomial.tendsto_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：tendsto_nhds_iff {c : 𝕜} : Tendsto (fun x => eval x P) atTop (𝓝 c) ↔ P.lea
dingCoeff = c ∧ P.degree <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.tendsto_nhds`：∀ {α : Type u_1} {β : Type u_2} [
inst : NormedAddCommGroup β] {u v : α → β} {l : Filter α} {c : β},   Asymptotics
.IsEquivalent l u v → Filte…
· 使用定理 `Polynomial.isEquivalent_atTop_lead`：isEquivalent_atTop_lead : (fun x => 
eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
· 使用定理 `Polynomial.natDegree_eq_zero_iff_degree_le_zero`：natDegree_eq_zero_iff_d
egree_le_zero : p.natDegree = 0 ↔ p.degree <= 0
· 使用定理 `tendsto_const_mul_pow_nhds_iff`：tendsto_const_mul_pow_nhds_iff {n : Nat}
 {c d : 𝕜} (hc : c != 0) : Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 
∧ c = d
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem tendsto_nhds_iff {c : 𝕜} :
    Tendsto (fun x => eval x P) atTop (𝓝 c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := P.isEquivalent_atTop_lead.tendsto_nhds h
    by_cases hP : P.leadingCoeff = 0
    · simp only [hP, zero_mul, tendsto_const_nhds_iff] at this
      exact ⟨_root_.trans hP this, by simp [leadingCoeff_eq_zero.1 hP]⟩
    · rw [tendsto_const_mul_pow_nhds_iff hP, natDegree_eq_zero_iff_degree_le_zero] at this
      exact this.symm
  · refine P.isEquivalent_atTop_lead.symm.tendsto_nhds ?_
    have : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h.2
    simp only [h.1, this, pow_zero, mul_one]
    exact tendsto_const_nhds

end PolynomialAtTop

section PolynomialAtBot

/-
**Polynomial.isEquivalent_atBot_lead** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isEquivalent_atBot_lead : P.eval ~[atBot] (P.leadingCoeff * · ^ P.natDegre
e)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Polynomial.comp_neg_X_leadingCoeff_eq`：∀ {R : Type u} [inst : Ring R] (p
 : Polynomial R),   (p.comp (-Polynomial.X)).leadingCoeff = (-1) ^ p.natDegree *
 p.leadingCoeff
· 使用定理 `mul_rotate`：mul_rotate (a b c : G) : a * b * c = b * c * a
· 使用定理 `Polynomial.natDegree_comp`：natDegree_comp : natDegree (p.comp q) = natDe
gree p * natDegree q
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Asymptotics.IsEquivalent.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} [
inst : NormedAddCommGroup β] {l : Filter α} {α₂ : Type u_4} {f g : α₂ → β}   {l'
 : Filter α₂},   Asymptotic…
· 使用定理 `Polynomial.isEquivalent_atTop_lead`：isEquivalent_atTop_lead : (fun x => 
eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem isEquivalent_atBot_lead : P.eval ~[atBot] (P.leadingCoeff * · ^ P.natDegree) := by
  convert! (P.comp (-X)).isEquivalent_atTop_lead.comp_tendsto tendsto_neg_atBot_atTop using 2
  · simp
  · rw [Function.comp_apply, comp_neg_X_leadingCoeff_eq, ← mul_rotate]
    simp [natDegree_comp, ← mul_pow, mul_comm]
/-
**Polynomial.abs_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：abs_tendsto_atBot (hdeg : 0 < P.degree) : Tendsto (|P.eval ·|) atBot atTop
参数：hdeg : 0 < P.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Polynomial.abs_tendsto_atTop`：abs_tendsto_atTop (hdeg : 0 < P.degree) : 
Tendsto (fun x => abs <| eval x P) atTop atTop
· 使用定理 `Polynomial.degree_comp_neg_X`：∀ {R : Type u} [inst : Ring R] {p : Polyno
mial R}, (p.comp (-Polynomial.X)).degree = p.degree
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem abs_tendsto_atBot (hdeg : 0 < P.degree) : Tendsto (|P.eval ·|) atBot atTop := by
  convert! ((P.comp (-X)).abs_tendsto_atTop (by simp [hdeg])).comp tendsto_neg_atBot_atTop using 2
  simp
/-
**Polynomial.isBoundedUnder_abs_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：isBoundedUnder_abs_atBot_iff : (IsBoundedUnder (· <= ·) atBot (|P.eval ·|)
) ↔ P.degree <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.not_isBoundedUnder_of_tendsto_atTop`：not_isBoundedUnder_of_tendst
o_atTop [Preorder β] [NoMaxOrder β] {f : α -> β} {l : Filter α} [l.NeBot] (hf : 
Tendsto f l atTop) : ¬IsBoundedU…
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Filter.atBot_neBot`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirectedOr
der α] [Nonempty α], Filter.atBot.NeBot
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Polynomial.abs_tendsto_atBot`：abs_tendsto_atBot (hdeg : 0 < P.degree) : 
Tendsto (|P.eval ·|) atBot atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
-/
theorem isBoundedUnder_abs_atBot_iff :
    (IsBoundedUnder (· ≤ ·) atBot (|P.eval ·|)) ↔ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ ↦ le_of_eq) fun x ↦ congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atBot P h)
/-
**Polynomial.abs_tendsto_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：abs_tendsto_atBot_iff : Tendsto (|P.eval ·|) atBot atTop ↔ 0 < P.degree
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isBoundedUnder_abs_atBot_iff`：isBoundedUnder_abs_atBot_iff : 
(IsBoundedUnder (· <= ·) atBot (|P.eval ·|)) ↔ P.degree <= 0
· 使用定理 `Filter.not_isBoundedUnder_of_tendsto_atTop`：not_isBoundedUnder_of_tendst
o_atTop [Preorder β] [NoMaxOrder β] {f : α -> β} {l : Filter α} [l.NeBot] (hf : 
Tendsto f l atTop) : ¬IsBoundedU…
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Filter.atBot_neBot`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirectedOr
der α] [Nonempty α], Filter.atBot.NeBot
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Polynomial.abs_tendsto_atBot`：abs_tendsto_atBot (hdeg : 0 < P.degree) : 
Tendsto (|P.eval ·|) atBot atTop
-/
theorem abs_tendsto_atBot_iff : Tendsto (|P.eval ·|) atBot atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt (isBoundedUnder_abs_atBot_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atBot P⟩

end PolynomialAtBot

section PolynomialDivAtTop

/-
**Polynomial.isEquivalent_atTop_div** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isEquivalent_atTop_div : (fun x => eval x P / eval x Q) ~[atTop] fun x => 
P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : Int)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Asymptotics.IsEquivalent.trans`：∀ {α : Type u_1} {β : Type u_2} [inst : 
NormedAddCommGroup β] {l : Filter α} {u v w : α → β},   Asymptotics.IsEquivalent
 l u v → Asymptotics…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Asymptotics.IsEquivalent.div`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {t u v w : α → β} {l : Filter α},   Asymptotics.IsEquivalent l t u 
→ Asymptotics.IsEq…
· 使用定理 `Polynomial.isEquivalent_atTop_lead`：isEquivalent_atTop_lead : (fun x => 
eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree
· 使用定理 `Filter.EventuallyEq.isEquivalent`：Filter.EventuallyEq.isEquivalent {u v 
: α -> β} (h : u =ᶠ[l] v) : u ~[l] v
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `zpow_sub₀`：zpow_sub₀ (ha : a != 0) (m n : Int) : a ^ (m - n) = a ^ m / a
 ^ n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
（共 31 条，此处仅展示前 30 条）
-/
theorem isEquivalent_atTop_div :
    (fun x => eval x P / eval x Q) ~[atTop] fun x =>
      P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : ℤ) := by
  by_cases hP : P = 0
  · simp [hP, IsEquivalent.refl]
  by_cases hQ : Q = 0
  · simp [hQ, IsEquivalent.refl]
  refine
    (P.isEquivalent_atTop_lead.symm.div Q.isEquivalent_atTop_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_gt_atTop 0).mono fun x hx => ?_))
  simp [← div_mul_div_comm, zpow_sub₀ hx.ne.symm]
/-
**Polynomial.div_tendsto_atTop_zero_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：div_tendsto_atTop_zero_of_degree_lt (hdeg : P.degree < Q.degree) : Tendsto
 (fun x => eval x P / eval x Q) atTop (𝓝 0)
参数：hdeg : P.degree < Q.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsEquivalent.tendsto_nhds`：∀ {α : Type u_1} {β : Type u_2} [
inst : NormedAddCommGroup β] {u v : α → β} {l : Filter α} {c : β},   Asymptotics
.IsEquivalent l u v → Filte…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Polynomial.isEquivalent_atTop_div`：isEquivalent_atTop_div : (fun x => ev
al x P / eval x Q) ~[atTop] fun x => P.leadingCoeff / Q.leadingCoeff * x ^ (P.na
tDegree - Q.natDegree :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `tendsto_zpow_atTop_zero`：tendsto_zpow_atTop_zero {n : Int} (hn : n < 0) 
: Tendsto (fun x : 𝕜 => x ^ n) atTop (𝓝 0)
· 使用定理 `Polynomial.natDegree_lt_natDegree_iff`：natDegree_lt_natDegree_iff (hp : 
p != 0) : natDegree p < natDegree q ↔ degree p < degree q
-/
theorem div_tendsto_atTop_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0) := by
  by_cases hP : P = 0
  · simp [hP]
  rw [← natDegree_lt_natDegree_iff hP] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_nhds ?_
  rw [← mul_zero]
  refine (tendsto_zpow_atTop_zero ?_).const_mul _
  lia

@[deprecated (since := "2026-02-05")]
alias div_tendsto_zero_of_degree_lt := div_tendsto_atTop_zero_of_degree_lt
/-
**Polynomial.div_tendsto_atTop_zero_iff_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：div_tendsto_atTop_zero_iff_degree_lt (hQ : Q != 0) : Tendsto (fun x => eva
l x P / eval x Q) atTop (𝓝 0) ↔ P.degree < Q.degree
参数：hQ : Q != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Asymptotics.IsEquivalent.tendsto_nhds`：∀ {α : Type u_1} {β : Type u_2} [
inst : NormedAddCommGroup β] {u v : α → β} {l : Filter α} {c : β},   Asymptotics
.IsEquivalent l u v → Filte…
· 使用定理 `Polynomial.isEquivalent_atTop_div`：isEquivalent_atTop_div : (fun x => ev
al x P / eval x Q) ~[atTop] fun x => P.leadingCoeff / Q.leadingCoeff * x ^ (P.na
tDegree - Q.natDegree :…
· 使用定理 `tendsto_const_mul_zpow_atTop_nhds_iff`：tendsto_const_mul_zpow_atTop_nhds
_iff {n : Int} {c d : 𝕜} (hc : c != 0) : Tendsto (fun x : 𝕜 => c * x ^ n) atTop 
(𝓝 d) ↔ n = 0 ∧ c = d ∨ n <…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.degree_lt_degree`：degree_lt_degree (h : natDegree p < natDegr
ee q) : degree p < degree q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Polynomial.div_tendsto_atTop_zero_of_degree_lt`：div_tendsto_atTop_zero_o
f_degree_lt (hdeg : P.degree < Q.degree) : Tendsto (fun x => eval x P / eval x Q
) atTop (𝓝 0)
-/
theorem div_tendsto_atTop_zero_iff_degree_lt (hQ : Q ≠ 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h => ?_, div_tendsto_atTop_zero_of_degree_lt P Q⟩
  by_cases hPQ : P.leadingCoeff / Q.leadingCoeff = 0
  · simp only [div_eq_mul_inv, inv_eq_zero, mul_eq_zero] at hPQ
    rcases hPQ with hP0 | hQ0
    · rw [leadingCoeff_eq_zero.1 hP0, degree_zero]
      exact bot_lt_iff_ne_bot.2 fun hQ' => hQ (degree_eq_bot.1 hQ')
    · exact absurd (leadingCoeff_eq_zero.1 hQ0) hQ
  · have := (isEquivalent_atTop_div P Q).tendsto_nhds h
    rw [tendsto_const_mul_zpow_atTop_nhds_iff hPQ] at this
    rcases this with h | h
    · exact absurd h.2 hPQ
    · rw [sub_lt_iff_lt_add, zero_add, Int.ofNat_lt] at h
      exact degree_lt_degree h.1

@[deprecated (since := "2026-02-05")]
alias div_tendsto_zero_iff_degree_lt := div_tendsto_atTop_zero_iff_degree_lt
/-
**Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq** 是 Mathlib 中的一个定理，
位于命名空间 `Polynomial`。
形式化陈述：div_tendsto_atTop_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degre
e) : Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 <| P.leadingCoeff / Q.leadi
ngCoeff)
参数：hdeg : P.degree = Q.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.tendsto_nhds`：∀ {α : Type u_1} {β : Type u_2} [
inst : NormedAddCommGroup β] {u v : α → β} {l : Filter α} {c : β},   Asymptotics
.IsEquivalent l u v → Filte…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Polynomial.isEquivalent_atTop_div`：isEquivalent_atTop_div : (fun x => ev
al x P / eval x Q) ~[atTop] fun x => P.leadingCoeff / Q.leadingCoeff * x ^ (P.na
tDegree - Q.natDegree :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
theorem div_tendsto_atTop_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 <| P.leadingCoeff / Q.leadingCoeff) := by
  refine (isEquivalent_atTop_div P Q).symm.tendsto_nhds ?_
  rw [show (P.natDegree : ℤ) = Q.natDegree by simp [hdeg, natDegree]]
  simp

@[deprecated (since := "2026-02-05")]
alias div_tendsto_leadingCoeff_div_of_degree_eq := div_tendsto_atTop_leadingCoeff_div_of_degree_eq
/-
**Polynomial.div_tendsto_atTop_of_degree_gt'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree) (hpos : 0 < P
.leadingCoeff / Q.leadingCoeff) : Tendsto (fun x => eval x P / eval x Q) atTop a
tTop
参数：hdeg : Q.degree < P.degree；hpos : 0 < P.leadingCoeff / Q.leadingCoeff。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Asymptotics.IsEquivalent.tendsto_atTop`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v : α
 → β}   {l : Filter α} [Orde…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Polynomial.isEquivalent_atTop_div`：isEquivalent_atTop_div : (fun x => ev
al x P / eval x Q) ~[atTop] fun x => P.leadingCoeff / Q.leadingCoeff * x ^ (P.na
tDegree - Q.natDegree :…
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用引理 `Filter.tendsto_zpow_atTop_atTop`：tendsto_zpow_atTop_atTop {n : Int} (hn 
: 0 < n) : Tendsto (fun x : α => x ^ n) atTop atTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_lt_natDegree_iff`：natDegree_lt_natDegree_iff (hp : 
p != 0) : natDegree p < natDegree q ↔ degree p < degree q
-/
theorem div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x => eval x P / eval x Q) atTop atTop := by
  have hQ : Q ≠ 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hpos
    exact hpos.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_atTop ?_
  apply Tendsto.const_mul_atTop hpos
  apply tendsto_zpow_atTop_atTop
  lia
/-
**Polynomial.div_tendsto_atTop_of_degree_gt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q != 0) 
(hnng : 0 <= P.leadingCoeff / Q.leadingCoeff) : Tendsto (fun x => eval x P / eva
l x Q) atTop atTop
参数：hdeg : Q.degree < P.degree；hQ : Q != 0；hnng : 0 <= P.leadingCoeff / Q.leading
Coeff。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `Polynomial.ne_zero_of_degree_gt`：ne_zero_of_degree_gt {n : WithBot Nat} 
(h : n < degree p) : p != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.div_tendsto_atTop_of_degree_gt'`：div_tendsto_atTop_of_degree_
gt' (hdeg : Q.degree < P.degree) (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) : 
Tendsto (fun x => eval x P / eva…
-/
theorem div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnng : 0 ≤ P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x => eval x P / eval x Q) atTop atTop :=
  have ratio_pos : 0 < P.leadingCoeff / Q.leadingCoeff :=
    lt_of_le_of_ne hnng
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
          hQ <| leadingCoeff_eq_zero.mp h).symm
  div_tendsto_atTop_of_degree_gt' P Q hdeg ratio_pos
/-
**Polynomial.div_tendsto_atBot_of_degree_gt'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：div_tendsto_atBot_of_degree_gt' (hdeg : Q.degree < P.degree) (hneg : P.lea
dingCoeff / Q.leadingCoeff < 0) : Tendsto (fun x => eval x P / eval x Q) atTop a
tBot
参数：hdeg : Q.degree < P.degree；hneg : P.leadingCoeff / Q.leadingCoeff < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Asymptotics.IsEquivalent.tendsto_atBot`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v : α
 → β}   {l : Filter α} [Orde…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Polynomial.isEquivalent_atTop_div`：isEquivalent_atTop_div : (fun x => ev
al x P / eval x Q) ~[atTop] fun x => P.leadingCoeff / Q.leadingCoeff * x ^ (P.na
tDegree - Q.natDegree :…
· 使用定理 `Filter.Tendsto.const_mul_atTop_of_neg`：∀ {α : Type u_1} {β : Type u_2} [
inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} 
  {f : β → α} {r : α}, r < …
· 使用引理 `Filter.tendsto_zpow_atTop_atTop`：tendsto_zpow_atTop_atTop {n : Int} (hn 
: 0 < n) : Tendsto (fun x : α => x ^ n) atTop atTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_lt_natDegree_iff`：natDegree_lt_natDegree_iff (hp : 
p != 0) : natDegree p < natDegree q ↔ degree p < degree q
-/
theorem div_tendsto_atBot_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hneg : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop atBot := by
  have hQ : Q ≠ 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hneg
    exact hneg.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_atBot ?_
  apply Tendsto.const_mul_atTop_of_neg hneg
  apply tendsto_zpow_atTop_atTop
  lia
/-
**Polynomial.div_tendsto_atBot_of_degree_gt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：div_tendsto_atBot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q != 0) 
(hnps : P.leadingCoeff / Q.leadingCoeff <= 0) : Tendsto (fun x => eval x P / eva
l x Q) atTop atBot
参数：hdeg : Q.degree < P.degree；hQ : Q != 0；hnps : P.leadingCoeff / Q.leadingCoeff
 <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `Polynomial.ne_zero_of_degree_gt`：ne_zero_of_degree_gt {n : WithBot Nat} 
(h : n < degree p) : p != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.div_tendsto_atBot_of_degree_gt'`：div_tendsto_atBot_of_degree_
gt' (hdeg : Q.degree < P.degree) (hneg : P.leadingCoeff / Q.leadingCoeff < 0) : 
Tendsto (fun x => eval x P / eva…
-/
theorem div_tendsto_atBot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnps : P.leadingCoeff / Q.leadingCoeff ≤ 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop atBot :=
  have ratio_neg : P.leadingCoeff / Q.leadingCoeff < 0 :=
    lt_of_le_of_ne hnps
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
        hQ <| leadingCoeff_eq_zero.mp h)
  div_tendsto_atBot_of_degree_gt' P Q hdeg ratio_neg
/-
**Polynomial.abs_div_tendsto_atTop_atTop_of_degree_gt** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：abs_div_tendsto_atTop_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ 
: Q != 0) : Tendsto (fun x => |eval x P / eval x Q|) atTop atTop
参数：hdeg : Q.degree < P.degree；hQ : Q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_abs_atTop_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G], Filter.Tendsto abs Filter.atTop Filter.atTop
· 使用定理 `Polynomial.div_tendsto_atTop_of_degree_gt`：div_tendsto_atTop_of_degree_g
t (hdeg : Q.degree < P.degree) (hQ : Q != 0) (hnng : 0 <= P.leadingCoeff / Q.lea
dingCoeff) : Tendsto (fun x => …
· 使用定理 `Filter.tendsto_abs_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto abs Filter.at
Bot Filter.atTop
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Polynomial.div_tendsto_atBot_of_degree_gt`：div_tendsto_atBot_of_degree_g
t (hdeg : Q.degree < P.degree) (hQ : Q != 0) (hnps : P.leadingCoeff / Q.leadingC
oeff <= 0) : Tendsto (fun x => …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem abs_div_tendsto_atTop_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x => |eval x P / eval x Q|) atTop atTop := by
  by_cases! h : 0 ≤ P.leadingCoeff / Q.leadingCoeff
  · exact tendsto_abs_atTop_atTop.comp (P.div_tendsto_atTop_of_degree_gt Q hdeg hQ h)
  · exact tendsto_abs_atBot_atTop.comp (P.div_tendsto_atBot_of_degree_gt Q hdeg hQ h.le)

@[deprecated (since := "2026-02-05")]
alias abs_div_tendsto_atTop_of_degree_gt := abs_div_tendsto_atTop_atTop_of_degree_gt

end PolynomialDivAtTop

section PolynomialDivAtBot

/-
**Polynomial.isEquivalent_atBot_div** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isEquivalent_atBot_div : (fun x => P.eval x / Q.eval x) ~[atBot] fun x => 
P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : Int)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Asymptotics.IsEquivalent.trans`：∀ {α : Type u_1} {β : Type u_2} [inst : 
NormedAddCommGroup β] {l : Filter α} {u v w : α → β},   Asymptotics.IsEquivalent
 l u v → Asymptotics…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Asymptotics.IsEquivalent.div`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {t u v w : α → β} {l : Filter α},   Asymptotics.IsEquivalent l t u 
→ Asymptotics.IsEq…
· 使用定理 `Polynomial.isEquivalent_atBot_lead`：isEquivalent_atBot_lead : P.eval ~[a
tBot] (P.leadingCoeff * · ^ P.natDegree)
· 使用定理 `Filter.EventuallyEq.isEquivalent`：Filter.EventuallyEq.isEquivalent {u v 
: α -> β} (h : u =ᶠ[l] v) : u ~[l] v
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_lt_atBot`：∀ {α : Type u_3} [inst : Preorder α] [NoBotO
rder α] (a : α), ∀ᶠ (x : α) in Filter.atBot, x < a
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `zpow_sub₀`：zpow_sub₀ (ha : a != 0) (m n : Int) : a ^ (m - n) = a ^ m / a
 ^ n
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isEquivalent_atBot_div :
    (fun x ↦ P.eval x / Q.eval x) ~[atBot] fun x ↦
      P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : ℤ) := by
  by_cases hP : P = 0
  · simp [hP, IsEquivalent.refl]
  by_cases hQ : Q = 0
  · simp [hQ, IsEquivalent.refl]
  refine
    (P.isEquivalent_atBot_lead.symm.div Q.isEquivalent_atBot_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_lt_atBot 0).mono fun x hx => ?_))
  simp [← div_mul_div_comm, zpow_sub₀ hx.ne]
/-
**Polynomial.div_tendsto_atBot_zero_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：div_tendsto_atBot_zero_of_degree_lt (hdeg : P.degree < Q.degree) : Tendsto
 (fun x => eval x P / eval x Q) atBot (𝓝 0)
参数：hdeg : P.degree < Q.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Polynomial.div_tendsto_atTop_zero_of_degree_lt`：div_tendsto_atTop_zero_o
f_degree_lt (hdeg : P.degree < Q.degree) : Tendsto (fun x => eval x P / eval x Q
) atTop (𝓝 0)
· 使用定理 `Polynomial.degree_comp_neg_X`：∀ {R : Type u} [inst : Ring R] {p : Polyno
mial R}, (p.comp (-Polynomial.X)).degree = p.degree
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem div_tendsto_atBot_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 0) := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
  convert! (div_tendsto_atTop_zero_of_degree_lt _ _ hdeg).comp tendsto_neg_atBot_atTop using 2
  simp
/-
**Polynomial.div_tendsto_atBot_zero_iff_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：div_tendsto_atBot_zero_iff_degree_lt (hQ : Q != 0) : Tendsto (fun x => eva
l x P / eval x Q) atBot (𝓝 0) ↔ P.degree < Q.degree
参数：hQ : Q != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_comp_neg_X`：∀ {R : Type u} [inst : Ring R] {p : Polyno
mial R}, (p.comp (-Polynomial.X)).degree = p.degree
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Polynomial.comp_eq_zero_iff`：comp_eq_zero_iff [Semiring R] [NoZeroDiviso
rs R] {p q : R[X]} : p.comp q = 0 ↔ p = 0 ∨ p.eval (q.coeff 0) = 0 ∧ q = C (q.co
eff 0)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_neg`：coeff_neg (p : R[X]) (n : Nat) : coeff (-p) n = -c
oeff p n
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.div_tendsto_atTop_zero_iff_degree_lt`：div_tendsto_atTop_zero_
iff_degree_lt (hQ : Q != 0) : Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0)
 ↔ P.degree < Q.degree
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
（共 34 条，此处仅展示前 30 条）
-/
theorem div_tendsto_atBot_zero_iff_degree_lt (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h ↦ ?_, div_tendsto_atBot_zero_of_degree_lt P Q⟩
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X]
  replace hQ : Q.comp (-X) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    simp [hQ]
  rw [← div_tendsto_atTop_zero_iff_degree_lt _ _ hQ]
  convert! h.comp tendsto_neg_atTop_atBot using 2
  simp
/-
**Polynomial.div_tendsto_atBot_leadingCoeff_div_of_degree_eq** 是 Mathlib 中的一个定理，
位于命名空间 `Polynomial`。
形式化陈述：div_tendsto_atBot_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degre
e) : Tendsto (fun x => eval x P / eval x Q) atBot (𝓝 (P.leadingCoeff / Q.leading
Coeff))
参数：hdeg : P.degree = Q.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.tendsto_nhds`：∀ {α : Type u_1} {β : Type u_2} [
inst : NormedAddCommGroup β] {u v : α → β} {l : Filter α} {c : β},   Asymptotics
.IsEquivalent l u v → Filte…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Polynomial.isEquivalent_atBot_div`：isEquivalent_atBot_div : (fun x => P.
eval x / Q.eval x) ~[atBot] fun x => P.leadingCoeff / Q.leadingCoeff * x ^ (P.na
tDegree - Q.natDegree :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Polynomial.natDegree_eq_natDegree`：natDegree_eq_natDegree {q : S[X]} (hp
q : p.degree = q.degree) : p.natDegree = q.natDegree
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `Filter.atBot_neBot`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirectedOr
der α] [Nonempty α], Filter.atBot.NeBot
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_tendsto_atBot_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  refine (isEquivalent_atBot_div P Q).symm.tendsto_nhds ?_
  simp [natDegree_eq_natDegree hdeg]
/-
**Polynomial.abs_div_tendsto_atBot_atTop_of_degree_gt** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：abs_div_tendsto_atBot_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ 
: Q != 0) : Tendsto (fun x => |eval x P / eval x Q|) atBot atTop
参数：hdeg : Q.degree < P.degree；hQ : Q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Polynomial.comp_eq_zero_iff`：comp_eq_zero_iff [Semiring R] [NoZeroDiviso
rs R] {p q : R[X]} : p.comp q = 0 ↔ p = 0 ∨ p.eval (q.coeff 0) = 0 ∧ q = C (q.co
eff 0)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_neg`：coeff_neg (p : R[X]) (n : Nat) : coeff (-p) n = -c
oeff p n
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Polynomial.abs_div_tendsto_atTop_atTop_of_degree_gt`：abs_div_tendsto_atT
op_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q != 0) : Tendsto (fun 
x => |eval x P / eval x Q|) atTop atTop
（共 34 条，此处仅展示前 30 条）
-/
theorem abs_div_tendsto_atBot_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |eval x P / eval x Q|) atBot atTop := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
  replace hQ : Q.comp (-X) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    simp [hQ]
  convert! (abs_div_tendsto_atTop_atTop_of_degree_gt _ _ hdeg hQ).comp tendsto_neg_atBot_atTop
    using 2
  simp

end PolynomialDivAtBot

/-
**Polynomial.isLittleO_atTop_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：isLittleO_atTop_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atTop] 
Q.eval
参数：h : P.degree < Q.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Polynomial.ne_zero_of_degree_ge_degree`：ne_zero_of_degree_ge_degree (hpq
 : p.degree <= q.degree) (hp : p != 0) : q != 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Polynomial.eventually_atTop_not_isRoot`：eventually_atTop_not_isRoot (hP 
: P != 0) : forallᶠ x in atTop, ¬P.IsRoot x
· 使用定理 `Asymptotics.isLittleO_of_tendsto'`：∀ {α : Type u_1} {𝕜 : Type u_15} [ins
t : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   (∀ᶠ (x : α) in l, g x 
= 0 → f x = 0) → Filter…
· 使用定理 `Polynomial.div_tendsto_atTop_zero_of_degree_lt`：div_tendsto_atTop_zero_o
f_degree_lt (hdeg : P.degree < Q.degree) : Tendsto (fun x => eval x P / eval x Q
) atTop (𝓝 0)
-/
theorem isLittleO_atTop_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atTop] Q.eval := by
  by_cases hp : P = 0
  · simp [hp]
  · have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h.le hp
    have hPQ : ∀ᶠ x in atTop, Q.eval x = 0 → P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot Q hq) fun x h h' ↦ absurd h' h
    exact isLittleO_of_tendsto' hPQ (div_tendsto_atTop_zero_of_degree_lt P Q h)
/-
**Polynomial.isLittleO_atBot_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：isLittleO_atBot_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atBot] 
Q.eval
参数：h : P.degree < Q.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `Polynomial.isLittleO_atTop_of_degree_lt`：isLittleO_atTop_of_degree_lt (h
 : P.degree < Q.degree) : P.eval =o[atTop] Q.eval
· 使用定理 `Polynomial.degree_comp_neg_X`：∀ {R : Type u} [inst : Ring R] {p : Polyno
mial R}, (p.comp (-Polynomial.X)).degree = p.degree
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem isLittleO_atBot_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atBot] Q.eval := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at h
  convert! (isLittleO_atTop_of_degree_lt _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp
/-
**Polynomial.isBigO_atTop_of_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isBigO_atTop_of_degree_le (h : P.degree <= Q.degree) : P.eval =O[atTop] Q.
eval
参数：h : P.degree <= Q.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `Asymptotics.isBigO_zero`：isBigO_zero : (fun _x => (0 : E')) =O[l] g
· 使用定理 `Polynomial.ne_zero_of_degree_ge_degree`：ne_zero_of_degree_ge_degree (hpq
 : p.degree <= q.degree) (hp : p != 0) : q != 0
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Polynomial.eventually_atTop_not_isRoot`：eventually_atTop_not_isRoot (hP 
: P != 0) : forallᶠ x in atTop, ¬P.IsRoot x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `Asymptotics.isBigO_of_div_tendsto_nhds`：isBigO_of_div_tendsto_nhds {α : 
Type*} {l : Filter α} {f g : α -> 𝕜} (hgf : forallᶠ x in l, g x = 0 -> f x = 0) 
(c : 𝕜) (H : Filter.Tendsto …
· 使用定理 `Polynomial.div_tendsto_atTop_zero_of_degree_lt`：div_tendsto_atTop_zero_o
f_degree_lt (hdeg : P.degree < Q.degree) : Tendsto (fun x => eval x P / eval x Q
) atTop (𝓝 0)
· 使用定理 `Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq`：div_tendsto_
atTop_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree) : Tendsto (fun 
x => eval x P / eval x Q) atTop (𝓝 <| P.leadingC…
-/
theorem isBigO_atTop_of_degree_le (h : P.degree ≤ Q.degree) : P.eval =O[atTop] Q.eval := by
  by_cases hp : P = 0
  · simpa [hp] using isBigO_zero Q.eval atTop
  · have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h hp
    have hPQ : ∀ᶠ x in atTop, Q.eval x = 0 → P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot Q hq) fun x h h' ↦ absurd h' h
    rcases le_iff_lt_or_eq.mp h with h | h
    · exact isBigO_of_div_tendsto_nhds hPQ 0 (div_tendsto_atTop_zero_of_degree_lt P Q h)
    · exact isBigO_of_div_tendsto_nhds hPQ _ (div_tendsto_atTop_leadingCoeff_div_of_degree_eq P Q h)
/-
**Polynomial.isBigO_atBot_of_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isBigO_atBot_of_degree_le (h : P.degree <= Q.degree) : P.eval =O[atBot] Q.
eval
参数：h : P.degree <= Q.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Polynomial.isBigO_atTop_of_degree_le`：isBigO_atTop_of_degree_le (h : P.d
egree <= Q.degree) : P.eval =O[atTop] Q.eval
· 使用定理 `Polynomial.degree_comp_neg_X`：∀ {R : Type u} [inst : Ring R] {p : Polyno
mial R}, (p.comp (-Polynomial.X)).degree = p.degree
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem isBigO_atBot_of_degree_le (h : P.degree ≤ Q.degree) : P.eval =O[atBot] Q.eval := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at h
  convert! (isBigO_atTop_of_degree_le _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

@[deprecated (since := "2026-02-05")] alias isBigO_of_degree_le := isBigO_atTop_of_degree_le

section Cobounded

/-
**Polynomial.eventually_cofinite_not_isRoot** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l`。
形式化陈述：eventually_cofinite_not_isRoot {R : Type*} [CommRing R] [IsDomain R] {P : 
R[X]} (hP : P != 0) : forallᶠ x in cofinite, ¬P.IsRoot x
参数：hP : P != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.compl_mem_cofinite`：∀ {α : Type u_2} {s : Set α}, s.Finite → 
sᶜ ∈ Filter.cofinite
· 使用定理 `Polynomial.finite_setOfPred_isRoot`：finite_setOfPred_isRoot {p : R[X]} (
hp : p != 0) : Set.Finite { x | IsRoot p x }
-/
lemma eventually_cofinite_not_isRoot {R : Type*} [CommRing R] [IsDomain R] {P : R[X]} (hP : P ≠ 0) :
    ∀ᶠ x in cofinite, ¬P.IsRoot x :=
  (finite_setOfPred_isRoot hP).compl_mem_cofinite

open Bornology

variable {R : Type*} [NormedRing R] [NormMulClass R] {P Q : R[X]}
/-
**Polynomial.isEquivalent_cobounded_leading_monomial** 是 Mathlib 中的一个引理，位于命名空间 `
Polynomial`。
形式化陈述：isEquivalent_cobounded_leading_monomial : P.eval ~[cobounded R] (P.leading
Coeff * · ^ P.natDegree)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_eq_sum_range`：eval_eq_sum_range {p : R[X]} (x : R) : p.e
val x = ∑ i in Finset.range (p.natDegree + 1), p.coeff i * x ^ i
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Asymptotics.IsLittleO.add_isEquivalent`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   u =o[l] w → Asym
ptotics.IsEquivalent l v w →…
· 使用定理 `Asymptotics.IsLittleO.fun_sum`：∀ {α : Type u_1} {E' : Type u_6} {F' : Ty
pe u_7} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F'] 
  {g' : α → F'} {l …
· 使用定理 `Asymptotics.IsLittleO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R
 : Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filte
r α}   {f : α → R}, f =o[l…
· 使用定理 `Asymptotics.IsLittleO.const_mul_right`：∀ {α : Type u_1} {E : Type u_3} [
inst : Norm E] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S] {f : α →
 E}   {l : Filter α} {g : α…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Asymptotics.isLittleO_pow_pow_cobounded_of_lt`：Asymptotics.isLittleO_pow
_pow_cobounded_of_lt (hpq : p < q) : (· ^ p) =o[cobounded R] (· ^ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u
-/
lemma isEquivalent_cobounded_leading_monomial :
    P.eval ~[cobounded R] (P.leadingCoeff * · ^ P.natDegree) := by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [eval_eq_sum_range, sum_range_succ]
    exact (IsLittleO.fun_sum fun i hi ↦
      ((isLittleO_pow_pow_cobounded_of_lt (mem_range.mp hi)).const_mul_right
        (leadingCoeff_ne_zero.mpr h)).const_mul_left _).add_isEquivalent .refl
/-
**Polynomial.isLittleO_cobounded_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：isLittleO_cobounded_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[cob
ounded R] Q.eval
参数：h : P.degree < Q.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Asymptotics.IsEquivalent.trans_isLittleO`：∀ {α : Type u_1} {β : Type u_2
} {β₂ : Type u_3} [inst : NormedAddCommGroup β] [inst_1 : Norm β₂] {l : Filter α
}   {f g₁ : α → β} {g₂ : α → β…
· 使用引理 `Polynomial.isEquivalent_cobounded_leading_monomial`：isEquivalent_cobound
ed_leading_monomial : P.eval ~[cobounded R] (P.leadingCoeff * · ^ P.natDegree)
· 使用定理 `Asymptotics.IsLittleO.trans_isEquivalent`：∀ {α : Type u_1} {β : Type u_2
} {β₂ : Type u_3} [inst : NormedAddCommGroup β] [inst_1 : Norm β₂] {l : Filter α
}   {f : α → β₂} {g₁ g₂ : α → …
· 使用定理 `Asymptotics.IsLittleO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R
 : Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filte
r α}   {f : α → R}, f =o[l…
· 使用定理 `Asymptotics.IsLittleO.const_mul_right`：∀ {α : Type u_1} {E : Type u_3} [
inst : Norm E] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S] {f : α →
 E}   {l : Filter α} {g : α…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Polynomial.ne_zero_of_degree_gt`：ne_zero_of_degree_gt {n : WithBot Nat} 
(h : n < degree p) : p != 0
· 使用定理 `Asymptotics.isLittleO_pow_pow_cobounded_of_lt`：Asymptotics.isLittleO_pow
_pow_cobounded_of_lt (hpq : p < q) : (· ^ p) =o[cobounded R] (· ^ q)
· 使用定理 `Polynomial.natDegree_lt_natDegree`：natDegree_lt_natDegree {q : S[X]} (hp
 : p != 0) (hpq : p.degree < q.degree) : p.natDegree < q.natDegree
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
-/
theorem isLittleO_cobounded_of_degree_lt (h : P.degree < Q.degree) :
    P.eval =o[cobounded R] Q.eval := by
  by_cases hP : P = 0
  · simp [hP]
  · refine isEquivalent_cobounded_leading_monomial.trans_isLittleO <|
      ((IsLittleO.const_mul_right ?_ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    · exact leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt h)
    · exact isLittleO_pow_pow_cobounded_of_lt (natDegree_lt_natDegree hP h)
/-
**Polynomial.isBigO_cobounded_of_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：isBigO_cobounded_of_degree_le (h : P.degree <= Q.degree) : P.eval =O[cobou
nded R] Q.eval
参数：h : P.degree <= Q.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Asymptotics.IsEquivalent.trans_isBigO`：∀ {α : Type u_1} {β : Type u_2} {
β₂ : Type u_3} [inst : NormedAddCommGroup β] [inst_1 : Norm β₂] {l : Filter α}  
 {f g₁ : α → β} {g₂ : α → β…
· 使用引理 `Polynomial.isEquivalent_cobounded_leading_monomial`：isEquivalent_cobound
ed_leading_monomial : P.eval ~[cobounded R] (P.leadingCoeff * · ^ P.natDegree)
· 使用定理 `Asymptotics.IsBigO.trans_isEquivalent`：∀ {α : Type u_1} {β : Type u_2} {
β₂ : Type u_3} [inst : NormedAddCommGroup β] [inst_1 : Norm β₂] {l : Filter α}  
 {f : α → β₂} {g₁ g₂ : α → …
· 使用定理 `Asymptotics.IsBigO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R : 
Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filter α
}   {f : α → R}, f =O[l…
· 使用定理 `Asymptotics.IsBigO.const_mul_right`：∀ {α : Type u_1} {E : Type u_3} [ins
t : Norm E] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S] {f : α → E}
   {l : Filter α} {g : α…
· 使用定理 `Asymptotics.isBigO_pow_pow_cobounded_of_le`：Asymptotics.isBigO_pow_pow_c
obounded_of_le (hpq : p <= q) : (· ^ p) =O[cobounded R] (· ^ q)
· 使用定理 `Polynomial.natDegree_le_natDegree`：natDegree_le_natDegree [Semiring S] {
q : S[X]} (hpq : p.degree <= q.degree) : p.natDegree <= q.natDegree
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
-/
theorem isBigO_cobounded_of_degree_le (h : P.degree ≤ Q.degree) :
    P.eval =O[cobounded R] Q.eval := by
  by_cases hQ : Q.leadingCoeff = 0
  · aesop
  · refine isEquivalent_cobounded_leading_monomial.trans_isBigO <|
      ((IsBigO.const_mul_right hQ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    exact isBigO_pow_pow_cobounded_of_le (natDegree_le_natDegree h)

end Cobounded

/-- If `deg Q < deg P`, there are only finitely many integers `x` where `|P(x)| ≤ |Q(x)|`. -/
/-
**Polynomial.finite_abs_eval_le_of_degree_lt** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al`。
形式化陈述：finite_abs_eval_le_of_degree_lt {P Q : Int[X]} (h : Q.degree < P.degree) :
 {x | |P.eval x| <= |Q.eval x|}.Finite
参数：h : Q.degree < P.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.isLittleO_cobounded_of_degree_lt`：isLittleO_cobounded_of_degr
ee_lt (h : P.degree < Q.degree) : P.eval =o[cobounded R] Q.eval
· 使用引理 `Polynomial.eventually_cofinite_not_isRoot`：eventually_cofinite_not_isRoo
t {R : Type*} [CommRing R] [IsDomain R] {P : R[X]} (hP : P != 0) : forallᶠ x in 
cofinite, ¬P.IsRoot x
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Polynomial.ne_zero_of_degree_gt`：ne_zero_of_degree_gt {n : WithBot Nat} 
(h : n < degree p) : p != 0
· 使用定理 `Asymptotics.IsLittleO.eventuallyLT_norm_of_eventually_pos`：∀ {α : Type u
_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} 
{g : α → F} {l : Filter α},   f =o[l] g → (∀ᶠ (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cofinite_eq`：cofinite_eq : (cofinite : Filter Int) = atBot ⊔ atTop
· 使用引理 `IsOrderBornology.cobounded_eq`：IsOrderBornology.cobounded_eq [NoMaxOrder
 α] [NoMinOrder α] : Bornology.cobounded α = .atBot ⊔ .atTop
· 使用定理 `Int.instIsOrderBornology`：IsOrderBornology ℤ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Filter.Eventually.congr`：∀ {α : Type u} {f : Filter α} {p q : α → Prop},
   (∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x ↔ q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
If `deg Q < deg P`, there are only finitely many integers `x` where `|P(x)| ≤ |Q
(x)|`.
-/
lemma finite_abs_eval_le_of_degree_lt {P Q : ℤ[X]} (h : Q.degree < P.degree) :
    {x | |P.eval x| ≤ |Q.eval x|}.Finite := by
  have o := isLittleO_cobounded_of_degree_lt h
  rw [IsOrderBornology.cobounded_eq, ← Int.cofinite_eq] at o
  have nr := eventually_cofinite_not_isRoot (ne_zero_of_degree_gt h)
  have key := o.eventuallyLT_norm_of_eventually_pos (nr.congr (.of_forall (by simp)))
  simp_rw [eventually_cofinite, not_lt, Int.norm_eq_abs] at key
  norm_cast at key

/-- If `Q(x) ∣ P(x)` at infinitely many integers `x` and `Q` is monic, `Q ∣ P`. -/
/-
**Polynomial.dvd_of_infinite_eval_dvd_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：dvd_of_infinite_eval_dvd_eval {P Q : Int[X]} (mQ : Q.Monic) (h : {a | Q.ev
al a ∣ P.eval a}.Infinite) : Q ∣ P
参数：mQ : Q.Monic；h : {a | Q.eval a ∣ P.eval a}.Infinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用定理 `Polynomial.eq_zero_of_infinite_isRoot`：eq_zero_of_infinite_isRoot (p : R
[X]) (h : Set.Infinite { x | IsRoot p x }) : p = 0
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用引理 `Int.eq_zero_of_abs_lt_dvd`：eq_zero_of_abs_lt_dvd {m x : Int} (h1 : m ∣ x
) (h2 : |x| < m) : x = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `abs_dvd`：abs_dvd (a b : α) : |a| ∣ b ↔ a ∣ b
· 使用定理 `Int.dvd_add_self_mul`：∀ {a b c : ℤ}, a ∣ b + a * c ↔ a ∣ b
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Infinite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Infinite → t.Finite 
→ (s \ t).Infinite
· 使用引理 `Polynomial.finite_abs_eval_le_of_degree_lt`：finite_abs_eval_le_of_degree
_lt {P Q : Int[X]} (h : Q.degree < P.degree) : {x | |P.eval x| <= |Q.eval x|}.Fi
nite

--- 原说明 ---
If `Q(x) ∣ P(x)` at infinitely many integers `x` and `Q` is monic, `Q ∣ P`.
-/
theorem dvd_of_infinite_eval_dvd_eval
    {P Q : ℤ[X]} (mQ : Q.Monic) (h : {a | Q.eval a ∣ P.eval a}.Infinite) : Q ∣ P := by
  have eqR := modByMonic_add_div P Q
  have degR := degree_modByMonic_lt P mQ
  rw [← modByMonic_eq_zero_iff_dvd mQ]
  set R := P %ₘ Q
  apply eq_zero_of_infinite_isRoot
  refine (h.sdiff (finite_abs_eval_le_of_degree_lt degR)).mono fun x mx ↦ ?_
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_le] at mx
  rw [← eqR, eval_add, eval_mul, Int.dvd_add_self_mul, ← abs_dvd] at mx
  exact Int.eq_zero_of_abs_lt_dvd mx.1 mx.2

end Polynomial

