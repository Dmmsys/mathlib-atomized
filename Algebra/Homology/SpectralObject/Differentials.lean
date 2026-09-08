/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Page

/-!
# Differentials of a spectral object

Let `X` be a spectral object in an abelian category `C` indexed by a category `ι`.
In this file, we construct the differentials `d : E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)`
that are attached to families of five composable morphisms `f₁`, `f₂`, `f₃`, `f₄`, `f₅`
in `ι`. We show that `d ≫ d = 0`. The homology of these differentials is computed in the
file `Mathlib/Algebra/Homology/SpectralObject/Homology.lean`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

open Category ComposableArrows Limits Preadditive

namespace Abelian

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (f₄₅ : i₃ ⟶ i₅) (h₄₅ : f₄ ≫ f₅ = f₄₅)
  (n₀ n₁ n₂ n₃ : ℤ)

/-- The differential `E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)` that is
attached to a family of five composable morphisms `f₁`, `f₂`, `f₃`, `f₄`, `f₅`. -/
/-
**CategoryTheory.Abelian.SpectralObject.d** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Abelian.SpectralObject`。
形式化陈述：d (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential `E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)` that is
attached to a family of five composable morphisms `f₁`, `f₂`, `f₃`, `f₄`, `f₅`.
-/
noncomputable def d
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.E f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ⟶ X.E f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ :=
  X.descE f₃ f₄ f₅ _ rfl n₀ n₁ n₂ (X.δ (f₁ ≫ f₂) (f₃ ≫ f₄) n₁ n₂ hn₂ ≫
    X.toCycles f₁ f₂ _ rfl n₂ ≫ X.πE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃) (by
      rw [X.δ_naturality_assoc (f₁ ≫ f₂) f₃ (f₁ ≫ f₂) (f₃ ≫ f₄)
        (𝟙 _) (twoδ₂Toδ₁ f₃ f₄ _ rfl) n₁ n₂ rfl hn₂, Functor.map_id, id_comp,
        δ_toCycles_assoc .., δToCycles_πE ..]) hn₁
          (by rw [δ_δ_assoc .., zero_comp])

@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.toCycles_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCycles_πE_d
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.toCycles f₃ f₄ f₃₄ h₃₄ n₁ ≫ X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫
      X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ =
        X.δ f₁₂ f₃₄ n₁ n₂ hn₂ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₂ ≫
          X.πE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ := by
  subst h₁₂ h₃₄
  simp only [d, δ_toCycles_assoc, toCycles_πE_descE]

set_option backward.defeqAttrib.useBackward true in
include h₃₄ in
@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.d_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d_ιE_fromOpcycles
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫ X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ ≫
      X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₂ =
      X.ιE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₄ f₅ f₄₅ h₄₅ n₁ ≫
        X.δ f₂₃ f₄₅ n₁ n₂ hn₂ := by
  rw [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂),
    ← cancel_epi (X.toCycles f₃ f₄ f₃₄ h₃₄ n₁),
    X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃,
    πE_ιE_assoc .., p_fromOpcycles, toCycles_i_assoc, fromOpcyles_δ ..,
    πE_ιE_assoc .., pOpcycles_δFromOpcycles, toCycles_i_assoc, ← Functor.map_comp, Eq.comm]
  apply δ_naturality
  simp

end

section

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₆ : i₅ ⟶ i₆) (f₇ : i₆ ⟶ i₇)
  (n₀ n₁ n₂ n₃ n₄ : ℤ)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.d_d** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Abelian.SpectralObject`。
形式化陈述：d_d (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiπE`：∀ {C : Type u_2} {ι : T
ype u_4} [inst : CategoryTheory.Category.{u_1, u_2} C]   [inst_1 : CategoryTheor
y.Category.{u_3, u_4} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiToCycles`：∀ {C : Type u_1} 
{ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Abelian.SpectralObject.toCycles_πE_d_assoc`：∀ {C : Type u
_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.toCycles_πE_d`：toCycles_πE_d (hn₁ 
: n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Abelian.SpectralObject.δ_δ_assoc`：∀ {C : Type u_1} {ι : T
ype u_2} [inst : CategoryTheory.Category.{u_4, u_1} C]   [inst_1 : CategoryTheor
y.Category.{u_3, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma d_d (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) (hn₄ : n₃ + 1 = n₄ := by lia) :
    X.d f₃ f₄ f₅ f₆ f₇ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      X.d f₁ f₂ f₃ f₄ f₅ n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄ = 0 := by
  rw [← cancel_epi (X.πE f₅ f₆ f₇ n₀ n₁ n₂ hn₁ hn₂),
    ← cancel_epi (X.toCycles f₅ f₆ _ rfl n₁), comp_zero, comp_zero,
    X.toCycles_πE_d_assoc f₃ f₄ f₅ f₆ f₇ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃,
    X.toCycles_πE_d f₁ f₂ f₃ f₄ f₅ _ rfl _ rfl n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄,
    δ_δ_assoc .., zero_comp]

end

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)

/-- When `f₁`, `f₂` and `f₃` are composable morphisms, this is the canonical
morphism `Z^n(f₂, f₃) ⟶ opZ^{n+1}(f₁, f₂)` that is induced both
by `δ : H^n(f₂ ≫ f₃) ⟶ H^{n+1}(f₁)` (see `toCycles_Ψ`) and
by `δ : H^n(f₃) ⟶ H^{n+1}(f₁ ≫ f₂)` (see `Ψ_fromOpcycles`).
See the lemma `πE_d_ιE` for the relation between this definition
and the differentials `d`. -/
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f₁`, `f₂` and `f₃` are composable morphisms, this is the canonical
morphism `Z^n(f₂, f₃) ⟶ opZ^{n+1}(f₁, f₂)` that is induced both
by `δ : H^n(f₂ ≫ f₃) ⟶ H^{n+1}(f₁)` (see `toCycles_Ψ`) and
by `δ : H^n(f₃) ⟶ H^{n+1}(f₁ ≫ f₂)` (see `Ψ_fromOpcycles`).
See the lemma `πE_d_ιE` for the relation between this definition
and the differentials `d`.
-/
noncomputable def Ψ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.cycles f₂ f₃ n₀ ⟶ X.opcycles f₁ f₂ n₁ :=
  X.descCycles f₂ f₃ _ rfl
    (X.δ f₁ (f₂ ≫ f₃) n₀ n₁ hn₁ ≫ X.pOpcycles f₁ f₂ n₁) (by
      rw [X.δ_naturality_assoc f₁ f₂ f₁ (f₂ ≫ f₃) (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ _ rfl) _ _ rfl,
        Functor.map_id, id_comp, δ_pOpcycles ..])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.toCycles_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCycles_Ψ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.toCycles f₂ f₃ f₂₃ h₂₃ n₀ ≫ X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ =
      X.δ f₁ f₂₃ n₀ n₁ hn₁ ≫ X.pOpcycles f₁ f₂ n₁ := by
  subst h₂₃
  simp only [Ψ, toCycles_descCycles]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ψ_fromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫ X.fromOpcycles f₁ f₂ f₁₂ h₁₂ n₁ =
      X.iCycles f₂ f₃ n₀ ≫ X.δ f₁₂ f₃ n₀ n₁ hn₁ := by
  rw [← cancel_epi (X.toCycles f₂ f₃ _ rfl n₀),
    toCycles_Ψ_assoc .., p_fromOpcycles, toCycles_i_assoc]
  exact (X.δ_naturality _ _ _ _ _ _ _ _ rfl).symm

include h₂₃ in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.cyclesMap_** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cyclesMap_Ψ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.cyclesMap _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) n₀ ≫
      X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ = 0 := by
  rw [← cancel_epi (X.toCycles f₁₂ f₃ (f₁ ≫ f₂ ≫ f₃)
    (by rw [reassoc_of% h₁₂]) n₀), comp_zero,
    X.toCycles_cyclesMap_assoc f₁₂ f₃ f₂ f₃ (f₁ ≫ f₂ ≫ f₃)
    (by rw [reassoc_of% h₁₂]) f₂₃ h₂₃ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂)
    (twoδ₁Toδ₀ f₁ f₂₃ (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃])) n₀ rfl rfl,
    toCycles_Ψ .., zero₃_assoc .., zero_comp]

include h₁₂ in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ψ_opcyclesMap (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫
      X.opcyclesMap _ _ _ _ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) n₁ = 0 := by
  rw [← cancel_mono (X.fromOpcycles f₁ f₂₃ (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃]) n₁),
    zero_comp, assoc, X.opcyclesMap_fromOpcycles f₁ f₂ f₁ f₂₃ f₁₂ h₁₂
    (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃]) (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃)
    (twoδ₂Toδ₁ f₁₂ f₃ (f₁ ≫ f₂ ≫ f₃) (by rw [reassoc_of% h₁₂])) n₁ rfl rfl,
    Ψ_fromOpcycles_assoc .., zero₁ .., comp_zero]

/-- When `f₁`, `f₂` and `f₃` are composable morphisms, this is the exact sequence
`Z^n(f₁ ≫ f₂, f₃) ⟶ Z^n(f₂, f₃) ⟶ opZ^{n+1}(f₁, f₂) ⟶ opZ^{n+1}(f₁, f₂ ≫ f₃)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.sequence** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f₁`, `f₂` and `f₃` are composable morphisms, this is the exact sequence
`Z^n(f₁ ≫ f₂, f₃) ⟶ Z^n(f₂, f₃) ⟶ opZ^{n+1}(f₁, f₂) ⟶ opZ^{n+1}(f₁, f₂ ≫ f₃)`.
-/
noncomputable def sequenceΨ (hn₁ : n₀ + 1 = n₁ := by lia) :
    ComposableArrows C 3 :=
  mk₃ (X.cyclesMap _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) n₀)
    (X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁)
    (X.opcyclesMap _ _ _ _ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) n₁)
/-
**CategoryTheory.Abelian.SpectralObject.cyclesMap_** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cyclesMap_Ψ_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (X.cyclesMap_Ψ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A z hz
  refine ⟨A, 𝟙 _, inferInstance,
    X.liftCycles f₁₂ f₃ n₀ n₁ hn₁ (z ≫ X.iCycles f₂ f₃ n₀) ?_, ?_⟩ <;> dsimp
  · rw [assoc, ← X.Ψ_fromOpcycles f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ hn₁, reassoc_of% hz, zero_comp]
  · rw [← cancel_mono (X.iCycles f₂ f₃ n₀), id_comp, assoc,
      X.cyclesMap_i _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) (𝟙 _) n₀ (by cat_disch),
      Functor.map_id, comp_id, liftCycles_i]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Ψ_opcyclesMap_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (X.Ψ_opcyclesMap f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro _ z₀ hz₀
  obtain ⟨A₁, π₁, _, z₁, hz₁⟩ := surjective_up_to_refinements_of_epi (X.pOpcycles f₁ f₂ n₁) z₀
  obtain ⟨A₂, π₂, _, z₂, hz₂⟩ :=
      (X.cokernelSequenceOpcycles_exact f₁ f₂₃ n₀ n₁ hn₁).exact_up_to_refinements z₁ (by
    dsimp
    have H := X.p_opcyclesMap f₁ f₂ f₁ f₂₃ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) (𝟙 _) n₁ (by cat_disch)
    rw [Functor.map_id, id_comp] at H
    rw [← H, ← reassoc_of% hz₁, hz₀, comp_zero])
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, z₂ ≫ X.toCycles f₂ f₃ f₂₃ h₂₃ n₀, ?_⟩
  rw [← cancel_mono (X.fromOpcycles f₁ f₂ f₁₂ h₁₂ n₁), assoc, assoc,
    assoc, assoc, toCycles_Ψ_assoc .., p_fromOpcycles, ← reassoc_of% dsimp% hz₂,
    reassoc_of% hz₁, p_fromOpcycles]
/-
**CategoryTheory.Abelian.SpectralObject.sequence** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sequenceΨ_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.sequenceΨ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).Exact :=
  exact_of_δ₀ (X.cyclesMap_Ψ_exact f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).exact_toComposableArrows
    (X.Ψ_opcyclesMap_exact f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).exact_toComposableArrows

end

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma πE_d_ιE
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (n₀ n₁ n₂ n₃ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫ X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ = X.Ψ f₂ f₃ f₄ n₁ n₂ hn₂ := by
  rw [← cancel_epi (X.toCycles f₃ f₄ _ rfl n₁), toCycles_Ψ ..,
    X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃,
    πE_ιE .., toCycles_i_assoc, ← X.δ_naturality_assoc (f₁ ≫ f₂) (f₃ ≫ f₄) f₂ (f₃ ≫ f₄)
      (twoδ₁Toδ₀ f₁ f₂ _ rfl) (𝟙 _) n₁ n₂ rfl hn₂, Functor.map_id, id_comp]

section

variable {i₀ i₁ i₂ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂)
  (n₀ n₁ n₂ n₃ : ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma πE_EIsoH_hom (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE (𝟙 i₀) f₁ (𝟙 i₁) n₀ n₁ n₂ hn₁ hn₂ ≫ (X.EIsoH f₁ n₀ n₁ n₂ hn₁ hn₂).hom =
      (X.cyclesIsoH f₁ n₁ n₂ hn₂).hom := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [πE, cyclesIsoH, EIsoH]

@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.d_EIsoH_hom** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Abelian.SpectralObject`。
形式化陈述：d_EIsoH_hom (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiπE`：∀ {C : Type u_2} {ι : T
ype u_4} [inst : CategoryTheory.Category.{u_1, u_2} C]   [inst_1 : CategoryTheor
y.Category.{u_3, u_4} ι] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiToCycles`：∀ {C : Type u_1} 
{ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.toCycles_πE_d_assoc`：∀ {C : Type u
_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.πE_EIsoH_hom`：πE_EIsoH_hom (hn₁ : 
n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Abelian.SpectralObject.πE_EIsoH_hom_assoc`：∀ {C : Type u_
1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cyclesIsoH_inv_hom_id`：cyclesIsoH_
inv_hom_id (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.cyclesIsoH_inv_hom_id_assoc`：∀ {C 
: Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
-/
lemma d_EIsoH_hom (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d (𝟙 i₀) f₁ (𝟙 i₁) f₂ (𝟙 i₂) n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      (X.EIsoH f₁ n₁ n₂ n₃ hn₂ hn₃).hom =
    (X.EIsoH f₂ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.δ f₁ f₂ n₁ n₂ hn₂ := by
  rw [← cancel_epi (X.πE (𝟙 i₁) f₂ (𝟙 i₂) n₀ n₁ n₂ hn₁ hn₂),
    ← cancel_epi (X.toCycles (𝟙 i₁) f₂ f₂ (by simp) n₁),
    X.toCycles_πE_d_assoc (𝟙 i₀) f₁ (𝟙 i₁) f₂ (𝟙 i₂) f₁ (by simp) _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃,
    πE_EIsoH_hom .., πE_EIsoH_hom_assoc .., cyclesIsoH_inv_hom_id ..,
    comp_id, cyclesIsoH_inv_hom_id_assoc ..]

end

end SpectralObject

end Abelian

end CategoryTheory

