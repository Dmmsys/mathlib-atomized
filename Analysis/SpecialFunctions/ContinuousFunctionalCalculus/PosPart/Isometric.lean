/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! # Facts about `CFC.posPart` and `CFC.negPart` involving norms

This file collects various facts about the positive and negative parts of elements of a
C⋆-algebra that involve the norm.

## Main results

* `CFC.norm_eq_max_norm_posPart_negPart`: states that `‖a‖ = max ‖a⁺‖ ‖a⁻‖`
* `CFC.norm_posPart_le` and `CFC.norm_negPart_le`: state that `‖a⁺‖ ≤ ‖a‖` and `‖a⁻‖ ≤ ‖a‖`
  respectively.
-/

public section

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A] [SMulCommClass ℝ A A]
  [IsScalarTower ℝ A A] [StarRing A]
  [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

@[simp]
/-
**CStarAlgebra.norm_posPart_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CStarAlgebra.norm_posPart_le (a : A) : ‖a⁺‖ <= ‖a‖
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用引理 `norm_cfcₙ_le`：norm_cfcₙ_le {f : 𝕜 -> 𝕜} {a : A} {c : Real} (h : forall x
 in σₙ 𝕜 a, ‖f x‖ <= c) : ‖cfcₙ f a‖ <= c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le`：no
rm_quasispectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x in σₙ 𝕜 a) (ha : p a
· 使用引理 `cfcₙ_apply_of_not_predicate`：cfcₙ_apply_of_not_predicate {f : R -> R} (a
 : A) (ha : ¬ p a) : cfcₙ f a = 0
-/
lemma CStarAlgebra.norm_posPart_le (a : A) : ‖a⁺‖ ≤ ‖a‖ := by
  by_cases ha : IsSelfAdjoint a
  case neg => simp [CFC.posPart_def, cfcₙ_apply_of_not_predicate a ha]
  refine norm_cfcₙ_le fun x hx ↦ ?_
  obtain (h | h) := le_or_gt x 0
  · simp [posPart_def, max_eq_right h]
  · simp only [posPart_def, max_eq_left h.le]
    exact NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a hx ha

@[simp]
/-
**CStarAlgebra.norm_negPart_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CStarAlgebra.norm_negPart_le (a : A) : ‖a⁻‖ <= ‖a‖
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.posPart_neg`：posPart_neg (a : A) : (-a)⁺ = a⁻
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `CStarAlgebra.norm_posPart_le`：CStarAlgebra.norm_posPart_le (a : A) : ‖a⁺
‖ <= ‖a‖
-/
lemma CStarAlgebra.norm_negPart_le (a : A) : ‖a⁻‖ ≤ ‖a‖ := by
  simpa [CFC.negPart_neg] using norm_posPart_le (-a)

open CStarAlgebra in
/-
**IsSelfAdjoint.norm_eq_max_norm_posPart_negPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.norm_eq_max_norm_posPart_negPart (a : A) (ha : IsSelfAdjoint
 a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_id'`：cfcₙ_id' : cfcₙ (fun x : R => x) a = a
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用引理 `norm_cfcₙ_le_iff`：norm_cfcₙ_le_iff (f : 𝕜 -> 𝕜) (a : A) (c : Real) (hf :
 ContinuousOn f (σₙ 𝕜 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `posPart_eq_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMon
oid α] {a : α}, a⁺ = a ↔ 0 ≤ a
· 使用引理 `norm_apply_le_norm_cfcₙ`：norm_apply_le_norm_cfcₙ (f : 𝕜 -> 𝕜) (a : A) ⦃x
 : 𝕜⦄ (hx : x in σₙ 𝕜 a) (hf : ContinuousOn f (σₙ 𝕜 a)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `continuous_posPart`：continuous_posPart : Continuous (posPart : α -> α)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `posPart_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid
 α], 0⁺ = 0
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
（共 39 条，此处仅展示前 30 条）
-/
lemma IsSelfAdjoint.norm_eq_max_norm_posPart_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    ‖a‖ = max ‖a⁺‖ ‖a⁻‖ := by
  refine le_antisymm ?_ <| max_le (norm_posPart_le a) (norm_negPart_le a)
  conv_lhs => rw [← cfcₙ_id' ℝ a]
  rw [norm_cfcₙ_le_iff ..]
  intro x hx
  obtain (hx' | hx') := le_total 0 x
  · apply le_max_of_le_left
    refine le_of_eq_of_le ?_ <| norm_apply_le_norm_cfcₙ _ a hx
    rw [posPart_eq_self.mpr hx']
  · apply le_max_of_le_right
    refine le_of_eq_of_le ?_ <| norm_apply_le_norm_cfcₙ _ a hx
    rw [negPart_eq_neg.mpr hx', norm_neg]
