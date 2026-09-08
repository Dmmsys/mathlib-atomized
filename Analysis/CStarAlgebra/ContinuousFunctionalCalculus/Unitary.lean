/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Tactic.Peel
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.Complex.Basic

/-! # Conditions on unitary elements imposed by the continuous functional calculus

## Main theorems

* `unitary_iff_isStarNormal_and_spectrum_subset_unitary`: An element is unitary if and only if it is
  star-normal and its spectrum lies on the unit circle.

-/

public section

section Generic

variable {R A : Type*} {p : A → Prop} [CommRing R] [StarRing R] [MetricSpace R]
variable [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-
**cfc_unitary_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_unitary_iff (f : R -> R) (a : A) (ha : p a
参数：f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `IsStarNormal.star_comm_self`：∀ {R : Type u_1} {inst : Mul R} {inst_1 : S
tar R} {x : R} [self : IsStarNormal x], Commute (star x) x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `cfc_one`：cfc_one : cfc (1 : R -> R) a = 1
· 使用引理 `cfc_star`：cfc_star (f : R -> R) (a : A) : cfc (fun x => star (f x)) a = 
star (cfc f a)
· 使用引理 `cfc_mul`：cfc_mul (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R
 a)
· 使用定理 `ContinuousOn.star`：ContinuousOn.star (hf : ContinuousOn f s) : Continuou
sOn (fun x => star (f x)) s
· 使用引理 `cfc_eq_cfc_iff_eqOn`：cfc_eq_cfc_iff_eqOn : cfc f a = cfc g a ↔ (spectrum
 R a).EqOn f g
· 使用定理 `ContinuousOn.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_one`：continuous_one [TopologicalSpace M] [One M] : Continuous
 (1 : X -> M)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cfc_unitary_iff (f : R → R) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc f a ∈ unitary A ↔ ∀ x ∈ spectrum R a, star (f x) * f x = 1 := by
  simp only [unitary, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  rw [← IsStarNormal.cfc_map (p := p) f a |>.star_comm_self |>.eq, and_self, ← cfc_one R a,
    ← cfc_star, ← cfc_mul .., cfc_eq_cfc_iff_eqOn]
  exact Iff.rfl

end Generic

section Complex

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal]

/-
**unitary_iff_isStarNormal_and_spectrum_subset_unitary** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：unitary_iff_isStarNormal_and_spectrum_subset_unitary {u : A} : u in unitar
y A ↔ IsStarNormal u ∧ spectrum Complex u subseteq unitary Complex
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `isStarNormal_of_mem_unitary`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 
: StarMul R] {u : R}, u ∈ unitary R → IsStarNormal u
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `cfc_unitary_iff`：cfc_unitary_iff (f : R -> R) (a : A) (ha : p a
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `Set.subset_def`：subset_def : (s subseteq t) = forall x, x in s -> x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma unitary_iff_isStarNormal_and_spectrum_subset_unitary {u : A} :
    u ∈ unitary A ↔ IsStarNormal u ∧ spectrum ℂ u ⊆ unitary ℂ := by
  rw [← and_iff_right_of_imp isStarNormal_of_mem_unitary]
  refine and_congr_right fun hu ↦ ?_
  nth_rw 1 [← cfc_id ℂ u]
  rw [cfc_unitary_iff id u, Set.subset_def]
  simp only [id_eq, RCLike.star_def, SetLike.mem_coe, Unitary.mem_iff_star_mul_self]
/-
**mem_unitary_of_spectrum_subset_unitary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_unitary_of_spectrum_subset_unitary {u : A} [IsStarNormal u] (hu : spec
trum Complex u subseteq unitary Complex) : u in unitary A
参数：hu : spectrum Complex u subseteq unitary Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `unitary_iff_isStarNormal_and_spectrum_subset_unitary`：unitary_iff_isStar
Normal_and_spectrum_subset_unitary {u : A} : u in unitary A ↔ IsStarNormal u ∧ s
pectrum Complex u subseteq unitary Complex
-/
lemma mem_unitary_of_spectrum_subset_unitary {u : A}
    [IsStarNormal u] (hu : spectrum ℂ u ⊆ unitary ℂ) : u ∈ unitary A :=
  unitary_iff_isStarNormal_and_spectrum_subset_unitary.mpr ⟨‹_›, hu⟩
/-
**spectrum_subset_unitary_of_mem_unitary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：spectrum_subset_unitary_of_mem_unitary {u : A} (hu : u in unitary A) : spe
ctrum Complex u subseteq unitary Complex
参数：hu : u in unitary A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `unitary_iff_isStarNormal_and_spectrum_subset_unitary`：unitary_iff_isStar
Normal_and_spectrum_subset_unitary {u : A} : u in unitary A ↔ IsStarNormal u ∧ s
pectrum Complex u subseteq unitary Complex
-/
lemma spectrum_subset_unitary_of_mem_unitary {u : A} (hu : u ∈ unitary A) :
    spectrum ℂ u ⊆ unitary ℂ :=
  unitary_iff_isStarNormal_and_spectrum_subset_unitary.mp hu |>.right

end Complex

