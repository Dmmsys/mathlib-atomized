/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar, Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!

# Projections in C⋆-algebras

Here we collect results about projections specific to C⋆-algebras.

## Main results

+ `isStarProjection_iff_isIdempotentElem_and_isStarNormal`: star projections are precisely
  idempotent normal elements.
+ `IsStarProjection.le_tfae`: for star projections `p` and `q`, the following are equivalent:
  - `p ≤ q`
  - `q * p = p`
  - `p * q = p`
  - `q - p` is a star projection
  - `q - p` is an idempotent element

-/

public section

open scoped CStarAlgebra

section NonUnital
variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A]

/-
**isStarProjection_iff_quasispectrum_subset_and_isSelfAdjoint** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：isStarProjection_iff_quasispectrum_subset_and_isSelfAdjoint [Module Real A
] [IsScalarTower Real A A] [SMulCommClass Real A A] [NonUnitalContinuousFunction
alCalculus Real A IsSelfAdjoint] {p : A} : IsStarProjection p ↔ quasispectrum Re
al p subseteq {0, 1} ∧ IsSelfAdjoint p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `isIdempotentElem_iff_quasispectrum_subset`：isIdempotentElem_iff_quasispe
ctrum_subset [NonUnitalRing A] [StarRing A] [Module R A] [IsScalarTower R A A] [
SMulCommClass R A A] [NonUnital…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isStarProjection_iff`：∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] 
(p : R), IsStarProjection p ↔ IsIdempotentElem p ∧ IsSelfAdjoint p
-/
lemma isStarProjection_iff_quasispectrum_subset_and_isSelfAdjoint [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {p : A} :
    IsStarProjection p ↔ quasispectrum ℝ p ⊆ {0, 1} ∧ IsSelfAdjoint p :=
  (isStarProjection_iff p).eq ▸
    and_congr_left_iff.mpr fun h ↦ isIdempotentElem_iff_quasispectrum_subset ℝ p h

section Normal
variable [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

/-- An idempotent element in a non-unital C⋆-algebra is self-adjoint iff it is normal. -/
/-
**IsIdempotentElem.isSelfAdjoint_iff_isStarNormal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIdempotentElem.isSelfAdjoint_iff_isStarNormal {p : A} (hp : IsIdempotent
Elem p) : IsSelfAdjoint p ↔ IsStarNormal p
参数：hp : IsIdempotentElem p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIdempotentElem.quasispectrum_subset`：IsIdempotentElem.quasispectrum_su
bset (𝕜 : Type*) {A : Type*} [Field 𝕜] [NonUnitalRing A] [Module 𝕜 A] [IsScalarT
ower 𝕜 A A] [SMulCommClass …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An idempotent element in a non-unital C⋆-algebra is self-adjoint iff it is norma
l.
-/
theorem IsIdempotentElem.isSelfAdjoint_iff_isStarNormal {p : A} (hp : IsIdempotentElem p) :
    IsSelfAdjoint p ↔ IsStarNormal p := by
  simp only [isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts,
    QuasispectrumRestricts.real_iff, and_iff_left_iff_imp]
  intro h x hx
  rcases hp.quasispectrum_subset _ hx with (hx | hx) <;> simp [Set.mem_singleton_iff.mp hx]

/-- An element in a non-unital C⋆-algebra is a star projection
if and only if it is idempotent and normal. -/
/-
**isStarProjection_iff_isIdempotentElem_and_isStarNormal** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：isStarProjection_iff_isIdempotentElem_and_isStarNormal {p : A} : IsStarPro
jection p ↔ IsIdempotentElem p ∧ IsStarNormal p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsIdempotentElem.isSelfAdjoint_iff_isStarNormal`：IsIdempotentElem.isSelf
Adjoint_iff_isStarNormal {p : A} (hp : IsIdempotentElem p) : IsSelfAdjoint p ↔ I
sStarNormal p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `isStarProjection_iff`：∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] 
(p : R), IsStarProjection p ↔ IsIdempotentElem p ∧ IsSelfAdjoint p

--- 原说明 ---
An element in a non-unital C⋆-algebra is a star projection
if and only if it is idempotent and normal.
-/
theorem isStarProjection_iff_isIdempotentElem_and_isStarNormal {p : A} :
    IsStarProjection p ↔ IsIdempotentElem p ∧ IsStarNormal p :=
  (isStarProjection_iff p).eq ▸ and_congr_right_iff.eq ▸ fun h => h.isSelfAdjoint_iff_isStarNormal
/-
**isStarProjection_iff_quasispectrum_subset_and_isStarNormal** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：isStarProjection_iff_quasispectrum_subset_and_isStarNormal {p : A} : IsSta
rProjection p ↔ quasispectrum Complex p subseteq {0, 1} ∧ IsStarNormal p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `isIdempotentElem_iff_quasispectrum_subset`：isIdempotentElem_iff_quasispe
ctrum_subset [NonUnitalRing A] [StarRing A] [Module R A] [IsScalarTower R A A] [
SMulCommClass R A A] [NonUnital…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isStarProjection_iff_isIdempotentElem_and_isStarNormal`：isStarProjection
_iff_isIdempotentElem_and_isStarNormal {p : A} : IsStarProjection p ↔ IsIdempote
ntElem p ∧ IsStarNormal p
-/
theorem isStarProjection_iff_quasispectrum_subset_and_isStarNormal {p : A} :
    IsStarProjection p ↔ quasispectrum ℂ p ⊆ {0, 1} ∧ IsStarNormal p :=
  isStarProjection_iff_isIdempotentElem_and_isStarNormal (p := p).eq ▸
    and_congr_left_iff.mpr fun h ↦ isIdempotentElem_iff_quasispectrum_subset ℂ p h

end Normal
end NonUnital

section Unital
variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A]

/-
**isStarProjection_iff_spectrum_subset_and_isSelfAdjoint** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：isStarProjection_iff_spectrum_subset_and_isSelfAdjoint [Algebra Real A] [N
onUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint] {p : A} : IsStarProje
ction p ↔ spectrum Real p subseteq {0, 1} ∧ IsSelfAdjoint p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `isIdempotentElem_iff_spectrum_subset`：isIdempotentElem_iff_spectrum_subs
et [Ring A] [StarRing A] [Algebra R A] [NonUnitalContinuousFunctionalCalculus R 
A p] (a : A) (ha : p a) : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isStarProjection_iff`：∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] 
(p : R), IsStarProjection p ↔ IsIdempotentElem p ∧ IsSelfAdjoint p
-/
lemma isStarProjection_iff_spectrum_subset_and_isSelfAdjoint [Algebra ℝ A]
    [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {p : A} :
    IsStarProjection p ↔ spectrum ℝ p ⊆ {0, 1} ∧ IsSelfAdjoint p :=
  (isStarProjection_iff p).eq ▸
    and_congr_left_iff.mpr fun h ↦ isIdempotentElem_iff_spectrum_subset ℝ p h
/-
**isStarProjection_iff_spectrum_subset_and_isStarNormal** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：isStarProjection_iff_spectrum_subset_and_isStarNormal [Algebra Complex A] 
[NonUnitalContinuousFunctionalCalculus Complex A IsStarNormal] {p : A} : IsStarP
rojection p ↔ spectrum Complex p subseteq {0, 1} ∧ IsStarNormal p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `isIdempotentElem_iff_spectrum_subset`：isIdempotentElem_iff_spectrum_subs
et [Ring A] [StarRing A] [Algebra R A] [NonUnitalContinuousFunctionalCalculus R 
A p] (a : A) (ha : p a) : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isStarProjection_iff_isIdempotentElem_and_isStarNormal`：isStarProjection
_iff_isIdempotentElem_and_isStarNormal {p : A} : IsStarProjection p ↔ IsIdempote
ntElem p ∧ IsStarNormal p
-/
theorem isStarProjection_iff_spectrum_subset_and_isStarNormal [Algebra ℂ A]
    [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal] {p : A} :
    IsStarProjection p ↔ spectrum ℂ p ⊆ {0, 1} ∧ IsStarNormal p :=
  isStarProjection_iff_isIdempotentElem_and_isStarNormal (p := p).eq ▸
    and_congr_left_iff.mpr fun h ↦ isIdempotentElem_iff_spectrum_subset ℂ p h

end Unital

namespace IsStarProjection

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {p q : A}

open CFC in
/-
**IsStarProjection.le_tfae** 是 Mathlib 中的一个引理，位于命名空间 `IsStarProjection`。
形式化陈述：le_tfae (hp : IsStarProjection p) (hq : IsStarProjection q) : List.TFAE [p
 <= q, q * p = p, p * q = p, IsStarProjection (q - p), IsIdempotentElem (q - p)]
参数：hp : IsStarProjection p；hq : IsStarProjection q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `IsStarProjection.mul_right_and_mul_left_of_nonneg_of_le`：IsStarProjectio
n.mul_right_and_mul_left_of_nonneg_of_le {a e : A} (he : IsStarProjection e) (ha
 : 0 <= a) (hae : a <= e) : a * e = a ∧ e * a…
· 使用定理 `IsStarProjection.nonneg`：IsStarProjection.nonneg {p : R} (hp : IsStarPro
jection p) : 0 <= p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p
· 使用定理 `IsStarProjection.sub_of_mul_eq_left`：sub_of_mul_eq_left [NonUnitalNonAss
ocRing R] [StarRing R] (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq 
: p * q = p) : IsStarProj…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsSelfAdjoint.sub`：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x - y)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma le_tfae (hp : IsStarProjection p) (hq : IsStarProjection q) :
  List.TFAE
    [p ≤ q,
    q * p = p,
    p * q = p,
    IsStarProjection (q - p),
    IsIdempotentElem (q - p)] := by
  tfae_have 1 → 2 := fun h ↦ (hq.mul_right_and_mul_left_of_nonneg_of_le hp.nonneg h).2
  tfae_have 2 → 3 := fun h ↦ by
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $h)
  tfae_have 3 → 4 := hp.sub_of_mul_eq_left hq
  tfae_have 4 → 1 := fun h ↦ by simpa using h.nonneg
  tfae_have 4 ↔ 5 := by simp [isStarProjection_iff, hq.isSelfAdjoint.sub hp.isSelfAdjoint]
  tfae_finish
/-
**IsStarProjection.le_iff_mul_eq_right** 是 Mathlib 中的一个引理，位于命名空间 `IsStarProjecti
on`。
形式化陈述：le_iff_mul_eq_right (hp : IsStarProjection p) (hq : IsStarProjection q) : 
p <= q ↔ q * p = p
参数：hp : IsStarProjection p；hq : IsStarProjection q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `IsStarProjection.le_tfae`：le_tfae (hp : IsStarProjection p) (hq : IsStar
Projection q) : List.TFAE [p <= q, q * p = p, p * q = p, IsStarProjection (q - p
), IsIdempoten…
-/
lemma le_iff_mul_eq_right (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ q * p = p :=
  hp.le_tfae hq |>.out 0 1
/-
**IsStarProjection.le_iff_mul_eq_left** 是 Mathlib 中的一个引理，位于命名空间 `IsStarProjectio
n`。
形式化陈述：le_iff_mul_eq_left (hp : IsStarProjection p) (hq : IsStarProjection q) : p
 <= q ↔ p * q = p
参数：hp : IsStarProjection p；hq : IsStarProjection q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `IsStarProjection.le_tfae`：le_tfae (hp : IsStarProjection p) (hq : IsStar
Projection q) : List.TFAE [p <= q, q * p = p, p * q = p, IsStarProjection (q - p
), IsIdempoten…
-/
lemma le_iff_mul_eq_left (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ p * q = p :=
  hp.le_tfae hq |>.out 0 2
/-
**IsStarProjection.le_iff_sub** 是 Mathlib 中的一个引理，位于命名空间 `IsStarProjection`。
形式化陈述：le_iff_sub (hp : IsStarProjection p) (hq : IsStarProjection q) : p <= q ↔ 
IsStarProjection (q - p)
参数：hp : IsStarProjection p；hq : IsStarProjection q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `IsStarProjection.le_tfae`：le_tfae (hp : IsStarProjection p) (hq : IsStar
Projection q) : List.TFAE [p <= q, q * p = p, p * q = p, IsStarProjection (q - p
), IsIdempoten…
-/
lemma le_iff_sub (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ IsStarProjection (q - p) :=
  hp.le_tfae hq |>.out 0 3
/-
**IsStarProjection.le_iff_idempotent_sub** 是 Mathlib 中的一个引理，位于命名空间 `IsStarProjec
tion`。
形式化陈述：le_iff_idempotent_sub (hp : IsStarProjection p) (hq : IsStarProjection q) 
: p <= q ↔ IsIdempotentElem (q - p)
参数：hp : IsStarProjection p；hq : IsStarProjection q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `IsStarProjection.le_tfae`：le_tfae (hp : IsStarProjection p) (hq : IsStar
Projection q) : List.TFAE [p <= q, q * p = p, p * q = p, IsStarProjection (q - p
), IsIdempoten…
-/
lemma le_iff_idempotent_sub (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ IsIdempotentElem (q - p) :=
  hp.le_tfae hq |>.out 0 4
/-
**IsStarProjection.commute_of_le** 是 Mathlib 中的一个引理，位于命名空间 `IsStarProjection`。
形式化陈述：commute_of_le (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p <
= q) : Commute p q
参数：hp : IsStarProjection p；hq : IsStarProjection q；h : p <= q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsStarProjection.le_iff_mul_eq_right`：le_iff_mul_eq_right (hp : IsStarPr
ojection p) (hq : IsStarProjection q) : p <= q ↔ q * p = p
· 使用引理 `IsStarProjection.le_iff_mul_eq_left`：le_iff_mul_eq_left (hp : IsStarProj
ection p) (hq : IsStarProjection q) : p <= q ↔ p * q = p
-/
lemma commute_of_le (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p ≤ q) :
    Commute p q := by
  rw [commute_iff_eq, hp.le_iff_mul_eq_right hq |>.mp h, hp.le_iff_mul_eq_left hq |>.mp h]

end IsStarProjection

