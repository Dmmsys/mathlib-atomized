/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Refinements

In order to prove injectivity/surjectivity/exactness properties for diagrams
in the category of abelian groups, we often need to do diagram chases.
Some of these can be carried out in more general abelian categories:
for example, a morphism `X ⟶ Y` in an abelian category `C` is a
monomorphism if and only if for all `A : C`, the induced map
`(A ⟶ X) → (A ⟶ Y)` of abelian groups is a monomorphism, i.e. injective.
Alternatively, the Yoneda presheaf functor which sends `X` to the
presheaf of maps `A ⟶ X` for all `A : C` preserves and reflects
monomorphisms.

However, if `p : X ⟶ Y` is an epimorphism in `C` and `A : C`,
`(A ⟶ X) → (A ⟶ Y)` may fail to be surjective (unless `p` is a split
epimorphism).

In this file, the basic result is `epi_iff_surjective_up_to_refinements`
which states that if `f : X ⟶ Y` is a morphism in an abelian category,
then it is an epimorphism if and only if for all `y : A ⟶ Y`,
there exists an epimorphism `π : A' ⟶ A` and `x : A' ⟶ X` such
that `π ≫ y = x ≫ f`. In other words, if we allow a precomposition
with an epimorphism, we may lift a morphism to `Y` to a morphism to `X`.
Following unpublished notes by George Bergman, we shall say that the
precomposition by an epimorphism `π ≫ y` is a refinement of `y`. Then,
we get that an epimorphism is a morphism that is "surjective up to refinements".
(This result is similar to the fact that a morphism of sheaves on
a topological space or a site is epi iff sections can be lifted
locally. Then, arguing "up to refinements" is very similar to
arguing locally for a Grothendieck topology (TODO: indeed,
show that it corresponds to the "refinements" topology on an
abelian category `C` that is defined by saying that
a sieve is covering if it contains an epimorphism)).

Similarly, it is possible to show that a short complex in an abelian
category is exact if and only if it is exact up to refinements
(see `ShortComplex.exact_iff_exact_up_to_refinements`).

As it is outlined in the documentation of the file
`Mathlib/CategoryTheory/Abelian/Pseudoelements.lean`, the Freyd-Mitchell
embedding theorem implies the existence of a faithful and exact functor `ι`
from an abelian category `C` to the category of abelian groups. If we
define a pseudo-element of `X : C` to be an element in `ι.obj X`, one
may do diagram chases in any abelian category using these pseudo-elements.
However, using this approach would require proving this embedding theorem!
Currently, mathlib contains a weaker notion of pseudo-elements
`Mathlib/CategoryTheory/Abelian/Pseudoelements.lean`. Some theorems can be obtained
using this notion, but there is the issue that for this notion
of pseudo-elements a morphism `X ⟶ Y` in `C` is not determined by
its action on pseudo-elements (see also `Counterexamples/Pseudoelement.lean`).
On the contrary, the approach consisting of working up to refinements
does not require the introduction of other types: we only need to work
with morphisms `A ⟶ X` in `C` which we may consider as being
"sort of elements of `X`". One may carry diagram-chasing by tracking
these morphisms and sometimes introducing an auxiliary epimorphism `A' ⟶ A`.

## References
* George Bergman, A note on abelian categories – translating element-chasing proofs,
  and exact embedding in abelian groups (1974)
  http://math.berkeley.edu/~gbergman/papers/unpub/elem-chase.pdf

-/

public section

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type*} [Category* C] [Abelian C] {X Y : C} (S : ShortComplex C)
  {S₁ S₂ : ShortComplex C}

/-
**CategoryTheory.epi_iff_surjective_up_to_refinements** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory`。
形式化陈述：epi_iff_surjective_up_to_refinements (f : X ⟶ Y) : Epi f ↔ forall ⦃A : C⦄ 
(y : A ⟶ Y), exists (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ 
f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma epi_iff_surjective_up_to_refinements (f : X ⟶ Y) :
    Epi f ↔ ∀ ⦃A : C⦄ (y : A ⟶ Y),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ f := by
  constructor
  · intro _ A a
    exact ⟨pullback a f, pullback.fst a f, inferInstance, pullback.snd a f, pullback.condition⟩
  · intro hf
    obtain ⟨A, π, hπ, a', fac⟩ := hf (𝟙 Y)
    rw [comp_id] at fac
    exact epi_of_epi_fac fac.symm
/-
**CategoryTheory.surjective_up_to_refinements_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory`。
形式化陈述：surjective_up_to_refinements_of_epi (f : X ⟶ Y) [Epi f] {A : C} (y : A ⟶ Y
) : exists (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ f
参数：f : X ⟶ Y；y : A ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.epi_iff_surjective_up_to_refinements`：epi_iff_surjective_
up_to_refinements (f : X ⟶ Y) : Epi f ↔ forall ⦃A : C⦄ (y : A ⟶ Y), exists (A' :
 C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X)…
-/
lemma surjective_up_to_refinements_of_epi (f : X ⟶ Y) [Epi f] {A : C} (y : A ⟶ Y) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ f :=
  (epi_iff_surjective_up_to_refinements f).1 inferInstance y
/-
**CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C]   (S : CategoryTheory.ShortComplex C),   S.Exact ↔     
∀ ⦃A : C⦄ (x₂ : A ⟶ S.X₂),       CategoryTheory.CategoryStruct.comp x₂ S.g = 0 →
         ∃ A' π,           ∃ (_ : CategoryTheory.Epi π),             ∃ x₁, Categ
oryTheory.CategoryStruct.comp π x₂ = CategoryTheory.CategoryStruct.comp x₁ S.f
参数：S : CategoryTheory.ShortComplex C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi_toCycles`：exact_iff_epi_toCycl
es [S.HasHomology] : S.Exact ↔ Epi S.toCycles
· 使用引理 `CategoryTheory.epi_iff_surjective_up_to_refinements`：epi_iff_surjective_
up_to_refinements (f : X ⟶ Y) : Epi f ↔ forall ⦃A : C⦄ (y : A ⟶ Y), exists (A' :
 C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
· 使用引理 `CategoryTheory.ShortComplex.toCycles_i`：toCycles_i : S.toCycles ≫ S.iCyc
les = S.f
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ShortComplex.iCycles_g`：iCycles_g : S.iCycles ≫ S.g = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.instMonoICycles`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   (S : CategoryTheory.Sho…
-/
lemma ShortComplex.exact_iff_exact_up_to_refinements :
    S.Exact ↔ ∀ ⦃A : C⦄ (x₂ : A ⟶ S.X₂) (_ : x₂ ≫ S.g = 0),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := by
  rw [S.exact_iff_epi_toCycles, epi_iff_surjective_up_to_refinements]
  constructor
  · intro hS A a ha
    obtain ⟨A', π, hπ, x₁, fac⟩ := hS (S.liftCycles a ha)
    exact ⟨A', π, hπ, x₁, by simpa only [assoc, liftCycles_i, toCycles_i] using fac =≫ S.iCycles⟩
  · intro hS A a
    obtain ⟨A', π, hπ, x₁, fac⟩ := hS (a ≫ S.iCycles) (by simp)
    exact ⟨A', π, hπ, x₁, by simp only [← cancel_mono S.iCycles, assoc, toCycles_i, fac]⟩

variable {S}
/-
**CategoryTheory.ShortComplex.Exact.exact_up_to_refinements** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C]   {S : CategoryTheory.ShortComplex C},   S.Exact →     
∀ {A : C} (x₂ : A ⟶ S.X₂),       CategoryTheory.CategoryStruct.comp x₂ S.g = 0 →
         ∃ A' π,           ∃ (_ : CategoryTheory.Epi π),             ∃ x₁, Categ
oryTheory.CategoryStruct.comp π x₂ = CategoryTheory.CategoryStruct.comp x₁ S.f
参数：x₂ : A ⟶ S.X₂；_ : CategoryTheory.Epi π。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.A
belian C]   (S : CategoryTheory.ShortComplex C),   …
-/
lemma ShortComplex.Exact.exact_up_to_refinements
    (hS : S.Exact) {A : C} (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at hS
  exact hS x₂ hx₂
/-
**CategoryTheory.ShortComplex.eq_liftCycles_homology** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ShortComplex.eq_liftCycles_homologyπ_up_to_refinements {A : C} (γ : A ⟶ S.homology) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (z : A' ⟶ S.X₂) (hz : z ≫ S.g = 0),
      π ≫ γ = S.liftCycles z hz ≫ S.homologyπ := by
  obtain ⟨A', π, hπ, z, hz⟩ := surjective_up_to_refinements_of_epi S.homologyπ γ
  refine ⟨A', π, hπ, z ≫ S.iCycles, by simp, ?_⟩
  rw [hz]
  congr 1
  rw [← cancel_mono S.iCycles, liftCycles_i]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.CokernelCofork.IsColimit.comp_** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Limits.CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements {f : X ⟶ Y}
    {c : CokernelCofork f} (hc : IsColimit c) {A : C} (y : A ⟶ Y) :
    y ≫ c.π = 0 ↔ ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ f := by
  refine ⟨fun hy ↦ ?_, ?_⟩
  · have h := (ShortComplex.mk _ _ c.condition).exact_of_g_is_cokernel
      (IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by simp)))
    rw [ShortComplex.exact_iff_exact_up_to_refinements] at h
    obtain ⟨A', π, hπ, x₁, fac⟩ := h y hy
    exact ⟨A', π, hπ, x₁, fac⟩
  · rintro ⟨A', π, hπ, x, fac⟩
    simp [← cancel_epi π, reassoc_of% fac, condition]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.liftCycles_comp_homology** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ShortComplex.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
    {A : C} (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) :
    S.liftCycles x₂ hx₂ ≫ S.homologyπ = 0 ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := by
  have := CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
        S.homologyIsCokernel (S.liftCycles x₂ hx₂)
  dsimp at this
  simp [this, ← cancel_mono S.iCycles]
/-
**CategoryTheory.ShortComplex.liftCycles_comp_homology** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ShortComplex.liftCycles_comp_homologyπ_eq_iff_up_to_refinements
    {A : C} (x₂ x₂' : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) (hx₂' : x₂' ≫ S.g = 0) :
    S.liftCycles x₂ hx₂ ≫ S.homologyπ = S.liftCycles x₂' hx₂' ≫ S.homologyπ ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = π ≫ x₂' + x₁ ≫ S.f := by
  suffices S.liftCycles x₂ hx₂ ≫ S.homologyπ = S.liftCycles x₂' hx₂' ≫ S.homologyπ ↔
      S.liftCycles (x₂ - x₂') (by simp [hx₂, hx₂']) ≫ S.homologyπ = 0 by
    simp [this, S.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements,
      sub_eq_iff_eq_add']
  rw [← sub_eq_zero, ← sub_comp, sub_liftCycles]
/-
**CategoryTheory.ShortComplex.comp_homology** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ShortComplex.comp_homologyπ_eq_zero_iff_up_to_refinements
    {A : C} (z₂ : A ⟶ S.cycles) :
    z₂ ≫ S.homologyπ = 0 ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ z₂ = x₁ ≫ S.toCycles := by
  obtain ⟨x₂, hx₂, rfl⟩ : ∃ (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0), z₂ = S.liftCycles x₂ hx₂ :=
    ⟨z₂ ≫ S.iCycles, by simp, by simp [← cancel_mono S.iCycles, liftCycles_i]⟩
  simp [liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements, ← cancel_mono S.iCycles]
/-
**CategoryTheory.ShortComplex.comp_homology** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ShortComplex.comp_homologyπ_eq_iff_up_to_refinements
    {A : C} (z₂ z₂' : A ⟶ S.cycles) :
    z₂ ≫ S.homologyπ = z₂' ≫ S.homologyπ ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁),
        π ≫ z₂ = π ≫ z₂' + x₁ ≫ S.toCycles := by
  obtain ⟨x₂, hx₂, rfl⟩ : ∃ (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0), z₂ = S.liftCycles x₂ hx₂ :=
    ⟨z₂ ≫ S.iCycles, by simp, by simp [← cancel_mono S.iCycles]⟩
  obtain ⟨x₂', hx₂', rfl⟩ : ∃ (x₂' : A ⟶ S.X₂) (hx₂' : x₂' ≫ S.g = 0), z₂' =
    S.liftCycles x₂' hx₂' := ⟨z₂' ≫ S.iCycles, by simp,
      by simp [← cancel_mono S.iCycles]⟩
  simp [liftCycles_comp_homologyπ_eq_iff_up_to_refinements, ← cancel_mono S.iCycles]
/-
**CategoryTheory.ShortComplex.comp_pOpcycles_eq_zero_iff_up_to_refinements** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C]   {S : CategoryTheory.ShortComplex C} {A : C} (x₂ : A ⟶
 S.X₂),   CategoryTheory.CategoryStruct.comp x₂ S.pOpcycles = 0 ↔     ∃ A' π,   
    ∃ (_ : CategoryTheory.Epi π),         ∃ x₁, CategoryTheory.CategoryStruct.co
mp π x₂ = CategoryTheory.CategoryStruct.comp x₁ S.f
参数：x₂ : A ⟶ S.X₂；_ : CategoryTheory.Epi π。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_
refinements`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [ins
t_1 : CategoryTheory.Abelian C] {X Y : C} {f : X ⟶ Y}   {c : CategoryTheo…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `CategoryTheory.ShortComplex.f_pOpcycles`：f_pOpcycles : S.f ≫ S.pOpcycles
 = 0
-/
lemma ShortComplex.comp_pOpcycles_eq_zero_iff_up_to_refinements
    {A : C} (x₂ : A ⟶ S.X₂) :
    x₂ ≫ S.pOpcycles = 0 ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f :=
  CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
    S.opcyclesIsCokernel x₂

variable {K L} in
/-
**CategoryTheory.ShortComplex.mono_homologyMap_iff_up_to_refinements** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C]   {S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂)
,   CategoryTheory.Mono (CategoryTheory.ShortComplex.homologyMap φ) ↔     ∀ ⦃A :
 C⦄ (x₂ : A ⟶ S₁.X₂),       CategoryTheory.CategoryStruct.comp x₂ S₁.g = 0 →    
     ∀ (y₁ : A ⟶ S₂.X₁),           CategoryTheory.CategoryStruct.comp x₂ φ.τ₂ = 
CategoryTheory.CategoryStruct.comp y₁ S₂.f →             ∃ A' π,               ∃
 (_ : CategoryTheory.Epi π),                 ∃ x₁, CategoryTheory.CategoryStruct
.comp π x₂ = CategoryTheory.CategoryStruct.comp x₁ S₁.f
参数：φ : S₁ ⟶ S₂；CategoryTheory.ShortComplex.homologyMap φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.homologyπ_naturality`：homologyπ_naturality (
φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] : S₁.homologyπ ≫ homologyMap φ = 
cyclesMap φ ≫ S₂.homologyπ
· 使用定理 `CategoryTheory.ShortComplex.liftCycles_comp_cyclesMap_assoc`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Lim
its.HasZeroMorphisms C]   (S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.ShortComplex.liftCycles_comp_homologyπ_eq_zero_iff_up_to_
refinements`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [ins
t_1 : CategoryTheory.Abelian C]   {S : CategoryTheory.ShortComplex C} {A …
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Preadditive.mono_iff_cancel_zero`：mono_iff_cancel_zero {Q
 R : C} (f : Q ⟶ R) : Mono f ↔ forall (P : C) (g : P ⟶ Q), g ≫ f = 0 -> g = 0
· 使用定理 `CategoryTheory.ShortComplex.eq_liftCycles_homologyπ_up_to_refinements`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Category
Theory.Abelian C]   {S : CategoryTheory.ShortComplex C} {A …
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
· 使用引理 `CategoryTheory.ShortComplex.toCycles_i`：toCycles_i : S.toCycles ≫ S.iCyc
les = S.f
-/
lemma ShortComplex.mono_homologyMap_iff_up_to_refinements (φ : S₁ ⟶ S₂) :
    Mono (homologyMap φ) ↔
      ∀ ⦃A : C⦄ (x₂ : A ⟶ S₁.X₂) (_ : x₂ ≫ S₁.g = 0) (y₁ : A ⟶ S₂.X₁)
          (_ : x₂ ≫ φ.τ₂ = y₁ ≫ S₂.f),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S₁.X₁),
          π ≫ x₂ = x₁ ≫ S₁.f := by
  refine ⟨fun h A x₂ hx₂ y₁ fac ↦ ?_, fun h ↦ ?_⟩
  · suffices S₁.liftCycles x₂ hx₂ ≫ S₁.homologyπ = 0 by
      rwa [← S₁.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements]
    simp only [← cancel_mono (homologyMap φ), zero_comp, assoc,
      homologyπ_naturality, liftCycles_comp_cyclesMap_assoc,
      S₂.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements]
    exact ⟨A, 𝟙 A, inferInstance, y₁, by simpa using fac⟩
  · rw [Preadditive.mono_iff_cancel_zero]
    intro A γ hγ
    obtain ⟨A₁, π₁, hπ₁, z, hz, fac⟩ := S₁.eq_liftCycles_homologyπ_up_to_refinements γ
    rw [← cancel_epi π₁, fac, comp_zero]
    replace hγ := π₁ ≫= hγ
    simp only [reassoc_of% fac, homologyπ_naturality, liftCycles_comp_cyclesMap_assoc,
      comp_zero, comp_homologyπ_eq_zero_iff_up_to_refinements] at hγ
    obtain ⟨A₂, π₂, hπ₂, y, hy⟩ := hγ
    replace hy := hy =≫ S₂.iCycles
    simp only [assoc, liftCycles_i, toCycles_i] at hy
    obtain ⟨A₃, π₃, hπ₃, x₁, hx₁⟩ :=
      h (π₂ ≫ z) (by rw [assoc, hz, comp_zero]) y (by simpa)
    rw [liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements]
    exact ⟨A₃, π₃ ≫ π₂, epi_comp _ _, x₁, by simpa⟩

variable {K L} in
/-
**CategoryTheory.ShortComplex.epi_homologyMap_iff_up_to_refinements** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C]   {S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂)
,   CategoryTheory.Epi (CategoryTheory.ShortComplex.homologyMap φ) ↔     ∀ ⦃A : 
C⦄ (y₂ : A ⟶ S₂.X₂),       CategoryTheory.CategoryStruct.comp y₂ S₂.g = 0 →     
    ∃ A' π,           ∃ (_ : CategoryTheory.Epi π),             ∃ x₂,           
    ∃ (_ : CategoryTheory.CategoryStruct.comp x₂ S₁.g = 0),                 ∃ y₁
,                   CategoryTheory.CategoryStruct.comp π y₂ =                   
  CategoryTheory.CategoryStruct.comp x₂ φ.τ₂ + CategoryTheory.CategoryStruct.com
p y₁ S₂.f
参数：φ : S₁ ⟶ S₂；CategoryTheory.ShortComplex.homologyMap φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.epi_iff_surjective_up_to_refinements`：epi_iff_surjective_
up_to_refinements (f : X ⟶ Y) : Epi f ↔ forall ⦃A : C⦄ (y : A ⟶ Y), exists (A' :
 C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X)…
· 使用定理 `CategoryTheory.ShortComplex.eq_liftCycles_homologyπ_up_to_refinements`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Category
Theory.Abelian C]   {S : CategoryTheory.ShortComplex C} {A …
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.ShortComplex.comp_liftCycles_assoc`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   (S : CategoryTheory.Sho…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.ShortComplex.homologyπ_naturality`：homologyπ_naturality (
φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] : S₁.homologyπ ≫ homologyMap φ = 
cyclesMap φ ≫ S₂.homologyπ
· 使用定理 `CategoryTheory.ShortComplex.liftCycles_comp_cyclesMap_assoc`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Lim
its.HasZeroMorphisms C]   (S : CategoryTheory.Sho…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma ShortComplex.epi_homologyMap_iff_up_to_refinements (φ : S₁ ⟶ S₂) :
    Epi (homologyMap φ) ↔
      ∀ ⦃A : C⦄ (y₂ : A ⟶ S₂.X₂) (_ : y₂ ≫ S₂.g = 0),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₂ : A' ⟶ S₁.X₂) (_ : x₂ ≫ S₁.g = 0)
          (y₁ : A' ⟶ S₂.X₁), π ≫ y₂ = x₂ ≫ φ.τ₂ + y₁ ≫ S₂.f := by
  rw [epi_iff_surjective_up_to_refinements]
  constructor
  · intro h A y₂ hy₂
    obtain ⟨A₁, π₁, hπ₁, γ, hγ⟩ := h (S₂.liftCycles y₂ hy₂ ≫ S₂.homologyπ)
    obtain ⟨A₂, π₂, hπ₂, x₂, hx₂, fac⟩ := S₁.eq_liftCycles_homologyπ_up_to_refinements γ
    replace hγ := π₂ ≫= hγ
    simp only [reassoc_of% fac, homologyπ_naturality, liftCycles_comp_cyclesMap_assoc,
      comp_liftCycles_assoc, liftCycles_comp_homologyπ_eq_iff_up_to_refinements] at hγ
    obtain ⟨A₃, π₃, hπ₃, x₁, hx₁⟩ := hγ
    exact ⟨A₃, π₃ ≫ π₂ ≫ π₁, inferInstance, π₃ ≫ x₂, by simp only [assoc, hx₂, comp_zero],
      x₁, by simpa only [assoc] using hx₁⟩
  · intro h A γ
    obtain ⟨A₁, π₁, hπ₁, y₂, hy₂, fac⟩ := S₂.eq_liftCycles_homologyπ_up_to_refinements γ
    obtain ⟨A₂, π₂, hπ₂, x₂, hx₂, y₁, hy₁⟩ := h y₂ hy₂
    refine ⟨A₂, π₂ ≫ π₁, inferInstance, S₁.liftCycles x₂ hx₂ ≫ S₁.homologyπ, ?_⟩
    simp only [assoc, fac, homologyπ_naturality, liftCycles_comp_cyclesMap_assoc,
      comp_liftCycles_assoc, liftCycles_comp_homologyπ_eq_iff_up_to_refinements]
    exact ⟨A₂, 𝟙 _, inferInstance, y₁, by simpa only [id_comp] using hy₁⟩

end CategoryTheory

