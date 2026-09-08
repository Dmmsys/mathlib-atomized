/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.EpiMono

/-!
# The homology of the differentials of a spectral object

Let `X` be a spectral object indexed by a category `ι` in an abelian
category `C`. Assume we have seven composable arrows
`f₁`, `f₂`, `f₃`, `f₄`, `f₅`, `f₆`, `f₇` in `ι`. In this file,
we compute the homology of the differentials, i.e. the homology of the short complex
`E^{n - 1}(f₅, f₆, f₇) ⟶ E^n(f₃, f₄, f₅) ⟶ E^{n + 1}(f₁, f₂, f₃)`.
The main definition for this is `dHomologyData` which is a homology data
for this short complex where:
* the cycles are `E^n(f₂ ≫ f₃, f₄, f₅)`;
* the opcycles are `E^n(f₃, f₄, f₅ ≫ f₆)`;
* the homology is `E^n(f₂ ≫ f₃, f₄, f₅ ≫ f₆)`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ComposableArrows Preadditive

namespace Abelian

variable {C ι : Type*} [Category* C] [Abelian C] [Category* ι]

namespace SpectralObject

variable (X : SpectralObject C ι)

section ExactSequences

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (n₀ n₁ n₂ n₃ : ℤ)

/-- The exact sequence expressing `E^n(f₁, f₂, f₃ ≫ f₄)` as the cokernel
of the differential `E^{n-1}(f₃, f₄, f₅) ⟶ E^n(f₁, f₂, f₃)` -/
@[simps!]
/-
**CategoryTheory.Abelian.SpectralObject.dCokernelSequence** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：dCokernelSequence (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exact sequence expressing `E^n(f₁, f₂, f₃ ≫ f₄)` as the cokernel
of the differential `E^{n-1}(f₃, f₄, f₅) ⟶ E^n(f₁, f₂, f₃)`
-/
noncomputable def dCokernelSequence
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.d_map_fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄ n₀ n₁ n₂ n₃)
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (_ : n₀ + 1 = n₁) (_ : n₁ + 1 = n₂) (_ : n₂ + 1 = n₃) :
    Epi (X.dCokernelSequence f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄ n₀ n₁ n₂ n₃ ‹_› ‹_› ‹_›).g :=
  inferInstanceAs (Epi (X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) ..))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.dCokernelSequence_exact** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：dCokernelSequence_exact (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.A
belian C]   (S : CategoryTheory.ShortComplex C),   …
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.sequenceΨ_exact`：sequenceΨ_exact (
hn₁ : n₀ + 1 = n₁
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_up_to_refinements`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   {S : CategoryTheory.ShortComplex C},   …
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.Abelian.SpectralObject.map_ιE`：map_ιE (γ : mk₂ f₂ f₃ ⟶ mk
₂ f₂' f₃') (n₀ n₁ n₂ : Int) (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (natu
rality' α 1 2) (naturality' α 2 3)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoιE`：∀ {C : Type u_2} {ι : 
Type u_4} [inst : CategoryTheory.Category.{u_1, u_2} C]   [inst_1 : CategoryTheo
ry.Category.{u_3, u_4} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.πE_d_ιE`：πE_d_ιE {i₀ i₁ i₂ i₃ i₄ i
₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃) (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅
) (n₀ n₁ n₂ n₃ : Int) (hn₁ : n₀ + 1…
-/
lemma dCokernelSequence_exact
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    (X.dCokernelSequence f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄ n₀ n₁ n₂ n₃).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at hx₂ ⊢
  have hx₂' := hx₂ =≫ X.ιE ..
  rw [assoc, zero_comp, X.map_ιE f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄)
    (threeδ₃Toδ₂ f₂ f₃ f₄ f₃₄) n₁ n₂ n₃] at hx₂'
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    ((X.sequenceΨ_exact f₂ f₃ f₄ _ rfl f₃₄ h₃₄ n₁ n₂).exact 1).exact_up_to_refinements
      (x₂ ≫ X.ιE ..) (by simp [sequenceΨ, Precomp.map, hx₂'])
  dsimp [sequenceΨ, Precomp.map] at hx₁
  refine ⟨A₁, π₁, inferInstance, x₁ ≫ X.πE f₃ f₄ f₅ n₀ n₁ n₂, ?_⟩
  rw [← cancel_mono (X.ιE ..), assoc, assoc, assoc, hx₁, πE_d_ιE ..]

/-- The exact sequence expressing `E^n(f₂ ≫ f₃, f₄, f₅)` as the kernel
of the differential `E^n(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)` -/
@[simps!]
/-
**CategoryTheory.Abelian.SpectralObject.dKernelSequence** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：dKernelSequence (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exact sequence expressing `E^n(f₂ ≫ f₃, f₄, f₅)` as the kernel
of the differential `E^n(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)`
-/
noncomputable def dKernelSequence
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.map_fourδ₁Toδ₀_d f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ n₀ n₁ n₂ n₃)
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (_ : n₀ + 1 = n₁) (_ : n₁ + 1 = n₂) (_ : n₂ + 1 = n₃) :
    Mono (X.dKernelSequence f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ n₀ n₁ n₂ n₃ ‹_› ‹_› ‹_›).f :=
  inferInstanceAs (Mono (X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃) ..))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.dKernelSequence_exact** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：dKernelSequence_exact (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.A
belian C]   (S : CategoryTheory.ShortComplex C),   …
· 使用引理 `CategoryTheory.surjective_up_to_refinements_of_epi`：surjective_up_to_ref
inements_of_epi (f : X ⟶ Y) [Epi f] {A : C} (y : A ⟶ Y) : exists (A' : C) (π : A
' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y =…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiπE`：∀ {C : Type u_2} {ι : T
ype u_4} [inst : CategoryTheory.Category.{u_1, u_2} C]   [inst_1 : CategoryTheor
y.Category.{u_3, u_4} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.sequenceΨ_exact`：sequenceΨ_exact (
hn₁ : n₀ + 1 = n₁
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_up_to_refinements`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   {S : CategoryTheory.ShortComplex C},   …
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.Abelian.SpectralObject.πE_d_ιE`：πE_d_ιE {i₀ i₁ i₂ i₃ i₄ i
₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃) (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅
) (n₀ n₁ n₂ n₃ : Int) (hn₁ : n₀ + 1…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Abelian.SpectralObject.πE_map`：πE_map (β : mk₂ f₁ f₂ ⟶ mk
₂ f₁' f₂') (n₀ n₁ n₂ : Int) (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (natu
rality' α 0 1 (by lia) (by lia)) (…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
-/
lemma dKernelSequence_exact
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    (X.dKernelSequence f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ n₀ n₁ n₂ n₃).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at hx₂ ⊢
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂) x₂
  have hy₂' := hy₂ =≫ X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ ≫ X.ιE ..
  simp only [assoc, reassoc_of% hx₂, zero_comp, comp_zero, πE_d_ιE] at hy₂'
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    ((X.sequenceΨ_exact f₂ f₃ f₄ f₂₃ h₂₃ _ rfl n₁ n₂).exact 0).exact_up_to_refinements y₂ hy₂'.symm
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, y₁ ≫ X.πE f₂₃ f₄ f₅ n₀ n₁ n₂, ?_⟩
  simp [sequenceΨ, hy₂, reassoc_of% hy₁, X.πE_map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃)
    (threeδ₁Toδ₀ f₂ f₃ f₄ f₂₃) n₀ n₁ n₂]

end ExactSequences

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₆ : i₅ ⟶ i₆) (f₇ : i₆ ⟶ i₇)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₅₆ : i₄ ⟶ i₆) (h₅₆ : f₅ ≫ f₆ = f₅₆)
  (n₀ n₁ n₂ n₃ n₄ : ℤ)

/-- The short complex `E^{n-1}(f₅, f₆, f₇) ⟶ E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)`
given by the differentials of a spectral object. -/
@[simps!]
/-
**CategoryTheory.Abelian.SpectralObject.dShortComplex** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Abelian.SpectralObject`。
形式化陈述：dShortComplex (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex `E^{n-1}(f₅, f₆, f₇) ⟶ E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)
`
given by the differentials of a spectral object.
-/
noncomputable def dShortComplex
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) (hn₄ : n₃ + 1 = n₄ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.d_d f₁ f₂ f₃ f₄ f₅ f₆ f₇ n₀ n₁ n₂ n₃ n₄)

@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.map_four** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_fourδ₁Toδ₀_EMap_fourδ₄Toδ₃
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃) n₁ n₂ n₃ ≫
      X.map f₃ f₄ f₅ f₃ f₄ f₅₆ (fourδ₄Toδ₃ f₃ f₄ f₅ f₆ f₅₆) n₁ n₂ n₃ =
    X.map f₂₃ f₄ f₅ f₂₃ f₄ f₅₆ (fourδ₄Toδ₃ f₂₃ f₄ f₅ f₆ f₅₆) n₁ n₂ n₃ ≫
      X.map f₂₃ f₄ f₅₆ f₃ f₄ f₅₆ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅₆ f₂₃) n₁ n₂ n₃ := by
  simp only [← map_comp]
  cat_disch

set_option backward.isDefEq.respectTransparency false in
/-- The homology data of the short complex
`E^{n-1}(f₅, f₆, f₇) ⟶ E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)` for which
* the cycles are `E^n(f₂ ≫ f₃, f₄, f₅)`;
* the opcycles are `E^n(f₃, f₄, f₅ ≫ f₆)`;
* the homology is `E^n(f₂ ≫ f₃, f₄, f₅ ≫ f₆)`. -/
@[simps!]
/-
**CategoryTheory.Abelian.SpectralObject.dHomologyData** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Abelian.SpectralObject`。
形式化陈述：dHomologyData (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology data of the short complex
`E^{n-1}(f₅, f₆, f₇) ⟶ E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)` for which
* the cycles are `E^n(f₂ ≫ f₃, f₄, f₅)`;
* the opcycles are `E^n(f₃, f₄, f₅ ≫ f₆)`;
* the homology is `E^n(f₂ ≫ f₃, f₄, f₅ ≫ f₆)`.
-/
noncomputable def dHomologyData
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) (hn₄ : n₃ + 1 = n₄ := by lia) :
    (X.dShortComplex f₁ f₂ f₃ f₄ f₅ f₆ f₇ n₀ n₁ n₂ n₃ n₄).HomologyData :=
  ShortComplex.HomologyData.ofEpiMonoFactorisation
    (X.dShortComplex f₁ f₂ f₃ f₄ f₅ f₆ f₇ n₀ n₁ n₂ n₃ n₄)
    (X.dKernelSequence_exact f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ n₁ n₂ n₃ n₄).fIsKernel
    (X.dCokernelSequence_exact f₃ f₄ f₅ f₆ f₇ f₅₆ h₅₆ n₀ n₁ n₂ n₃).gIsCokernel
    (X.map_fourδ₁Toδ₀_EMap_fourδ₄Toδ₃ f₂ f₃ f₄ f₅ f₆ f₂₃ h₂₃ f₅₆ h₅₆ n₁ n₂ n₃)

/-- The homology of the short complex
`E^{n-1}(f₅, f₆, f₇) ⟶ E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)` identifies to
`E^n(f₂ ≫ f₃, f₄, f₅ ≫ f₆)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.dHomologyIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Abelian.SpectralObject`。
形式化陈述：dHomologyIso (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology of the short complex
`E^{n-1}(f₅, f₆, f₇) ⟶ E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)` identifies to
`E^n(f₂ ≫ f₃, f₄, f₅ ≫ f₆)`.
-/
noncomputable def dHomologyIso
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) (hn₄ : n₃ + 1 = n₄ := by lia) :
    (X.dShortComplex f₁ f₂ f₃ f₄ f₅ f₆ f₇ n₀ n₁ n₂ n₃ n₄).homology ≅
      X.E f₂₃ f₄ f₅₆ n₁ n₂ n₃ :=
  (X.dHomologyData f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₂₃ h₂₃ f₅₆ h₅₆ ..).left.homologyIso

end SpectralObject

end Abelian

end CategoryTheory

