/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-! # C⋆-algebraic facts about `a⁺` and `a⁻`. -/

public section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace CStarAlgebra

section SpanNonneg

open Submodule

/-- A C⋆-algebra is spanned by nonnegative elements of norm at most `r` -/
/-
**CStarAlgebra.span_nonneg_inter_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlge
bra`。
形式化陈述：span_nonneg_inter_closedBall {r : Real} (hr : 0 < r) : span Complex ({x : 
A | 0 <= x} inter Metric.closedBall 0 r) = ⊤
参数：hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CStarAlgebra.span_nonneg`：CStarAlgebra.span_nonneg : Submodule.span Comp
lex {a : A | 0 <= a} = ⊤
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
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
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `eq_zero_or_norm_pos`：∀ {E : Type u_5} [inst : NormedAddGroup E] (a : E),
 a = 0 ∨ 0 < ‖a‖
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
A C⋆-algebra is spanned by nonnegative elements of norm at most `r`
-/
lemma span_nonneg_inter_closedBall {r : ℝ} (hr : 0 < r) :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.closedBall 0 r) = ⊤ := by
  rw [eq_top_iff, ← span_nonneg, span_le]
  intro x hx
  obtain (rfl | hx_pos) := eq_zero_or_norm_pos x
  · exact zero_mem _
  · suffices (r * ‖x‖⁻¹ : ℂ)⁻¹ • ((r * ‖x‖⁻¹ : ℂ) • x) = x by
      rw [← this]
      refine smul_mem _ _ (subset_span <| Set.mem_inter ?_ ?_)
      · norm_cast
        exact smul_nonneg (by positivity) hx
      · simp [mul_smul, norm_smul, abs_of_pos hr, inv_mul_cancel₀ hx_pos.ne']
    apply inv_smul_smul₀
    norm_cast
    positivity

/-- A C⋆-algebra is spanned by nonnegative elements of norm less than `r`. -/
/-
**CStarAlgebra.span_nonneg_inter_ball** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：span_nonneg_inter_ball {r : Real} (hr : 0 < r) : span Complex ({x : A | 0 
<= x} inter Metric.ball 0 r) = ⊤
参数：hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CStarAlgebra.span_nonneg_inter_closedBall`：span_nonneg_inter_closedBall 
{r : Real} (hr : 0 < r) : span Complex ({x : A | 0 <= x} inter Metric.closedBall
 0 r) = ⊤
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Metric.closedBall_subset_ball`：closedBall_subset_ball (h : ε₁ < ε₂) : cl
osedBall x ε₁ subseteq ball x ε₂
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a

--- 原说明 ---
A C⋆-algebra is spanned by nonnegative elements of norm less than `r`.
-/
lemma span_nonneg_inter_ball {r : ℝ} (hr : 0 < r) :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.ball 0 r) = ⊤ := by
  rw [eq_top_iff, ← span_nonneg_inter_closedBall (half_pos hr)]
  gcongr
  exact Metric.closedBall_subset_ball <| half_lt_self hr

/-- A C⋆-algebra is spanned by nonnegative contractions. -/
/-
**CStarAlgebra.span_nonneg_inter_unitClosedBall** 是 Mathlib 中的一个引理，位于命名空间 `CStar
Algebra`。
形式化陈述：span_nonneg_inter_unitClosedBall : span Complex ({x : A | 0 <= x} inter Me
tric.closedBall 0 1) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarAlgebra.span_nonneg_inter_closedBall`：span_nonneg_inter_closedBall 
{r : Real} (hr : 0 < r) : span Complex ({x : A | 0 <= x} inter Metric.closedBall
 0 r) = ⊤
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
A C⋆-algebra is spanned by nonnegative contractions.
-/
lemma span_nonneg_inter_unitClosedBall :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.closedBall 0 1) = ⊤ :=
  span_nonneg_inter_closedBall zero_lt_one

/-- A C⋆-algebra is spanned by nonnegative strict contractions. -/
/-
**CStarAlgebra.span_nonneg_inter_unitBall** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebr
a`。
形式化陈述：span_nonneg_inter_unitBall : span Complex ({x : A | 0 <= x} inter Metric.b
all 0 1) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarAlgebra.span_nonneg_inter_ball`：span_nonneg_inter_ball {r : Real} (
hr : 0 < r) : span Complex ({x : A | 0 <= x} inter Metric.ball 0 r) = ⊤
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
A C⋆-algebra is spanned by nonnegative strict contractions.
-/
lemma span_nonneg_inter_unitBall :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.ball 0 1) = ⊤ :=
  span_nonneg_inter_ball zero_lt_one

end SpanNonneg

open Complex in
/-
**CStarAlgebra.exists_sum_four_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：exists_sum_four_nonneg {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder
 A] [StarOrderedRing A] (a : A) : exists x : Fin 4 -> A, (forall i, 0 <= x i) ∧ 
(forall i, ‖x i‖ <= ‖a‖) ∧ a = ∑ i : Fin 4, I ^ (i : Nat) • x i
参数：a : A。
该定理/引理给出了一组等式。
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
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用引理 `CFC.posPart_nonneg`：posPart_nonneg (a : A) : 0 <= a⁺
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CStarAlgebra.norm_posPart_le`：CStarAlgebra.norm_posPart_le (a : A) : ‖a⁺
‖ <= ‖a‖
· 使用引理 `realPart.norm_le`：realPart.norm_le (x : A) : ‖realPart x‖ <= ‖x‖
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `imaginaryPart.norm_le`：imaginaryPart.norm_le (x : A) : ‖imaginaryPart x‖
 <= ‖x‖
· 使用引理 `CFC.negPart_nonneg`：negPart_nonneg (a : A) : 0 <= a⁻
（共 86 条，此处仅展示前 30 条）
-/
lemma exists_sum_four_nonneg {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (a : A) :
    ∃ x : Fin 4 → A, (∀ i, 0 ≤ x i) ∧ (∀ i, ‖x i‖ ≤ ‖a‖) ∧ a = ∑ i : Fin 4, I ^ (i : ℕ) • x i := by
  use ![(realPart a)⁺, (imaginaryPart a)⁺, (realPart a)⁻, (imaginaryPart a)⁻]
  rw [← and_assoc, ← forall_and]
  constructor
  · intro i
    fin_cases i
    all_goals
      constructor
      · simp
        cfc_tac
    · exact CStarAlgebra.norm_posPart_le _ |>.trans <| realPart.norm_le a
    · exact CStarAlgebra.norm_posPart_le _ |>.trans <| imaginaryPart.norm_le a
    · exact CStarAlgebra.norm_negPart_le _ |>.trans <| realPart.norm_le a
    · exact CStarAlgebra.norm_negPart_le _ |>.trans <| imaginaryPart.norm_le a
  · nth_rw 1 [← CStarAlgebra.linear_combination_nonneg a]
    simp only [Fin.sum_univ_four, Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod, I_sq,
      I_pow_three]
    module

end CStarAlgebra

