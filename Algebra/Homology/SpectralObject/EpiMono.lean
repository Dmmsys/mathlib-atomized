/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Differentials
public import Mathlib.CategoryTheory.ComposableArrows.Four

/-!
# Induced morphisms that are epi or mono

Given a spectral object in an abelian category, we show that certain
morphisms `E^n(f₁, f₂, f₃) ⟶ E^n(f₁', f₂', f₃')` are monomorphisms,
epimorphisms or isomorphisms.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι ι' κ : Type*} [Category* C] [Abelian C] [Category* ι] [Preorder ι']
  (X : SpectralObject C ι) (X' : SpectralObject C ι')

section

variable
  {i₀' i₀ i₁ i₂ i₃ i₃' : ι} (f₁ : i₀ ⟶ i₁)
  (f₁' : i₀' ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃) (f₃' : i₂ ⟶ i₃')
  (n₀ n₁ n₂ n₃ : ℤ)

/-
**CategoryTheory.Abelian.SpectralObject.epi_map** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Abelian.SpectralObject`。
形式化陈述：epi_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃') (n₀ n₁ n₂ n₃ : Int) (hα₀ : α.ap
p 0 = 𝟙 _
参数：α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃'；n₀ n₁ n₂ n₃ : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cyclesMap_id`：cyclesMap_id (n : In
t) : X.cyclesMap f g f g (𝟙 _) n = 𝟙 _
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiπE`：∀ {C : Type u_2} {ι : T
ype u_4} [inst : CategoryTheory.Category.{u_1, u_2} C]   [inst_1 : CategoryTheor
y.Category.{u_3, u_4} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.πE_map`：πE_map (β : mk₂ f₁ f₂ ⟶ mk
₂ f₁' f₂') (n₀ n₁ n₂ : Int) (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (natu
rality' α 0 1 (by lia) (by lia)) (…
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `CategoryTheory.ComposableArrows.homMk₂.congr_simp`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {f g : CategoryTheory.ComposableArrows
 C 2}   (app₀ app₀_1 : f.obj' 0 _proof_…
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₂`：hom_ext₂ {f g : ComposableArro
ws C 2} {φ φ' : f ⟶ g} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (
h₂ : app' φ 2 = app' φ' 2) : φ…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma epi_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃') (n₀ n₁ n₂ n₃ : ℤ)
    (hα₀ : α.app 0 = 𝟙 _ := by cat_disch) (hα₁ : α.app 1 = 𝟙 _ := by cat_disch)
    (hα₂ : α.app 2 = 𝟙 _ := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    Epi (X.map f₁ f₂ f₃ f₁ f₂ f₃' α n₀ n₁ n₂ hn₁ hn₂) :=
  have : Epi (X.cyclesMap f₁ f₂ f₁ f₂ (𝟙 (mk₂ f₁ f₂)) n₁) := by rw [X.cyclesMap_id]; infer_instance
  epi_of_epi_fac (X.πE_map _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂ (by cat_disch) _ _)
/-
**CategoryTheory.Abelian.SpectralObject.mono_map** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Abelian.SpectralObject`。
形式化陈述：mono_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂ f₃) (n₀ n₁ n₂ n₃ : Int) (hα₁ : α.a
pp 1 = 𝟙 _
参数：α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂ f₃；n₀ n₁ n₂ n₃ : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.Abelian.SpectralObject.map_ιE`：map_ιE (γ : mk₂ f₂ f₃ ⟶ mk
₂ f₂' f₃') (n₀ n₁ n₂ : Int) (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (natu
rality' α 1 2) (naturality' α 2 3)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ComposableArrows.homMk₂.congr_simp`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {f g : CategoryTheory.ComposableArrows
 C 2}   (app₀ app₀_1 : f.obj' 0 _proof_…
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₂`：hom_ext₂ {f g : ComposableArro
ws C 2} {φ φ' : f ⟶ g} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (
h₂ : app' φ 2 = app' φ' 2) : φ…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoιE`：∀ {C : Type u_2} {ι : 
Type u_4} [inst : CategoryTheory.Category.{u_1, u_2} C]   [inst_1 : CategoryTheo
ry.Category.{u_3, u_4} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.opcyclesMap_id`：opcyclesMap_id (n 
: Int) : X.opcyclesMap f g f g (𝟙 _) n = 𝟙 _
-/
lemma mono_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂ f₃) (n₀ n₁ n₂ n₃ : ℤ)
    (hα₁ : α.app 1 = 𝟙 _ := by cat_disch) (hα₂ : α.app 2 = 𝟙 _ := by cat_disch)
    (hα₃ : α.app 3 = 𝟙 _ := by cat_disch) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    Mono (X.map f₁ f₂ f₃ f₁' f₂ f₃ α n₀ n₁ n₂ hn₁ hn₂) := by
  have := X.map_ιE _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂
  rw [opcyclesMap_id, comp_id] at this
  exact mono_of_mono_fac this

end

section

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (n₀ n₁ n₂ n₃ : ℤ)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.d_map_four** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d_map_fourδ₄Toδ₃ (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃ = 0 := by
  simp [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂), ← cancel_epi (X.toCycles f₃ f₄ f₃₄ h₃₄ n₁),
    X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl f₃₄ h₃₄ n₀ n₁ n₂ n₃,
    X.πE_map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) (𝟙 _) n₁ n₂ n₃]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) :
    Epi (X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃) :=
  X.epi_map _ _ _ _ _ _ _ _ _ rfl rfl rfl hn₂ hn₃ rfl

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.isIso_map_four** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_map_fourδ₄Toδ₃ (h : (X.H n₁).map (twoδ₁Toδ₀ f₃ f₄ f₃₄ h₃₄) = 0 := by cat_disch)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    IsIso (X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · exact (X.exact₂ f₃ f₄ f₃₄ h₃₄ _).epi_f h
  · dsimp
    convert! (inferInstance : IsIso ((X.H n₂).map (𝟙 _)))
    cat_disch
  · dsimp
    convert! (inferInstance : Mono ((X.H n₃).map (𝟙 (mk₁ f₁))))
    cat_disch
/-
**CategoryTheory.Abelian.SpectralObject.isIso_map_four** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_map_fourδ₄Toδ₃_of_isZero (h : IsZero ((X.H n₁).obj (mk₁ f₄)) := by cat_disch)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    IsIso (X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃) :=
  X.isIso_map_fourδ₄Toδ₃ _ _ _ _ _ _ _ _ _ (h.eq_of_tgt _ _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.map_four** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_fourδ₁Toδ₀_d (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂ ≫
      X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ = 0 := by
  simp [← cancel_mono (X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃),
    ← cancel_mono (X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₂),
    X.d_ιE_fromOpcycles f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃, X.map_ιE_assoc
    f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) (𝟙 _) n₀ n₁ n₂ (by cat_disch) hn₁ hn₂]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) :=
  X.mono_map _ _ _ _ _ _ _ _ _ rfl rfl rfl _ _ rfl

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.isIso_map_four** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_map_fourδ₁Toδ₀ (h : (X.H n₂).map (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) = 0 := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · dsimp
    convert! (inferInstance : Epi ((X.H n₀).map (𝟙 _)))
    cat_disch
  · dsimp
    convert! (inferInstance : IsIso ((X.H n₁).map (𝟙 _)))
    cat_disch
  · exact (X.exact₂ f₂ f₃ f₂₃ h₂₃ n₂).mono_g h
/-
**CategoryTheory.Abelian.SpectralObject.isIso_map_four** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_map_fourδ₁Toδ₀_of_isZero (h : IsZero ((X.H n₂).obj (mk₁ f₂)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) :=
  X.isIso_map_fourδ₁Toδ₀ _ _ _ _ _ _ _ _ _ (h.eq_of_src _ _)

end

section

variable (i₀ i₁ i₂ i₃ i₄ i₅ : ι') (hi₀₁ : i₀ ≤ i₁)
  (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (hi₃₄ : i₃ ≤ i₄) (hi₄₅ : i₄ ≤ i₅)

/-- For a spectral object indexed by a preorder, this is the map
`E^{n₁}(i₀ ≤ i₂ ≤ i₃ ≤ i₄) ⟶ E^{n₁}(i₁ ≤ i₂ ≤ i₃ ≤ i₄)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.mapFour** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a spectral object indexed by a preorder, this is the map
`E^{n₁}(i₀ ≤ i₂ ≤ i₃ ≤ i₄) ⟶ E^{n₁}(i₁ ≤ i₂ ≤ i₃ ≤ i₄)`.
-/
noncomputable abbrev mapFourδ₁Toδ₀' (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :=
  X'.map _ _ _ _ _ _ (fourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

/-- For a spectral object indexed by a preorder, this is the map
`E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₄)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.mapFour** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a spectral object indexed by a preorder, this is the map
`E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₄)`.
-/
noncomputable abbrev mapFourδ₄Toδ₃' (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :=
  X'.map _ _ _ _ _ _ (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.mapFour** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapFourδ₁Toδ₀'_comp (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₁Toδ₀' i₀ i₁ i₃ i₄ i₅ hi₀₁ (hi₁₂.trans hi₂₃) hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₁Toδ₀' i₁ i₂ i₃ i₄ i₅ hi₁₂ hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
    X'.mapFourδ₁Toδ₀' i₀ i₂ i₃ i₄ i₅ (hi₀₁.trans hi₁₂) hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ :=
  (X'.map_comp (hn₁ := hn₁) (hn₂ := hn₂) ..).symm

@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.mapFour** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapFourδ₄Toδ₃'_comp (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₄ i₅ hi₀₁ hi₁₂ (hi₂₃.trans hi₃₄) hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
    X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₅ hi₀₁ hi₁₂ hi₂₃ (hi₃₄.trans hi₄₅) n₀ n₁ n₂ hn₁ hn₂ :=
  (X'.map_comp (hn₁ := hn₁) (hn₂ := hn₂) ..).symm

@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.mapFour** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃' (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₄Toδ₃' i₁ i₂ i₃ i₄ i₅ hi₁₂ hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
    X'.mapFourδ₄Toδ₃' i₀ i₂ i₃ i₄ i₅ _ _ _ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₅ hi₀₁ _ _ _ n₀ n₁ n₂ hn₁ hn₂ := by
  rw [← map_comp .., ← map_comp ..]
  rfl

section

variable (n₀ n₁ n₂ : ℤ) (h : IsZero ((X'.H n₂).obj (mk₁ (homOfLE hi₀₁))))

include h in
/-
**CategoryTheory.Abelian.SpectralObject.isIso_mapFour** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_mapFourδ₁Toδ₀' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_map_fourδ₁Toδ₀_of_isZero _ _ _ _ _ _ _ _ _ h

/-- For a spectral object indexed by a preorder, this is the isomorphism
`E^{n₁}(i₀ ≤ i₂ ≤ i₃ ≤ i₄) ≅ E^{n₁}(i₁ ≤ i₂ ≤ i₃ ≤ i₄)`
when `H^{n₁ + 1}(i₀ ≤ i₁)` is a zero object. -/
@[simps! hom]
/-
**CategoryTheory.Abelian.SpectralObject.isoMapFour** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a spectral object indexed by a preorder, this is the isomorphism
`E^{n₁}(i₀ ≤ i₂ ≤ i₃ ≤ i₄) ≅ E^{n₁}(i₁ ≤ i₂ ≤ i₃ ≤ i₄)`
when `H^{n₁ + 1}(i₀ ≤ i₁)` is a zero object.
-/
noncomputable def isoMapFourδ₁Toδ₀' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.E (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) (homOfLE hi₃₄) n₀ n₁ n₂ hn₁ hn₂ ≅
      X'.E (homOfLE hi₁₂) (homOfLE hi₂₃) (homOfLE hi₃₄) n₀ n₁ n₂ hn₁ hn₂ :=
  have := X'.isIso_mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂
  asIso (X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.isoMapFour** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoMapFourδ₁Toδ₀'_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv = 𝟙 _ :=
  (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.isoMapFour** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoMapFourδ₁Toδ₀'_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
      X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ :=
  (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv_hom_id

end

section

variable (n₀ n₁ n₂ : ℤ) (h : IsZero ((X'.H n₀).obj (mk₁ (homOfLE hi₃₄))))

include h in
/-
**CategoryTheory.Abelian.SpectralObject.isIso_mapFour** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_mapFourδ₄Toδ₃' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_map_fourδ₄Toδ₃_of_isZero (h := h) ..

/-- For a spectral object indexed by a preorder, this is the isomorphism
`E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ≅ E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₄)`
when `H^{n₁-1}(i₃ ≤ i₄)` is a zero object. -/
@[simps! hom]
/-
**CategoryTheory.Abelian.SpectralObject.isoMapFour** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a spectral object indexed by a preorder, this is the isomorphism
`E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ≅ E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₄)`
when `H^{n₁-1}(i₃ ≤ i₄)` is a zero object.
-/
noncomputable def isoMapFourδ₄Toδ₃' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃) n₀ n₁ n₂ hn₁ hn₂ ≅
      X'.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE (hi₂₃.trans hi₃₄)) n₀ n₁ n₂ hn₁ hn₂ :=
  have := X'.isIso_mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂
  asIso (X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.isoMapFour** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoMapFourδ₄Toδ₄'_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv = 𝟙 _ :=
  (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.isoMapFour** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoMapFourδ₄Toδ₄'_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
      X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ :=
  (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv_hom_id

end

section

variable (i₀ i₁ i₂ i₃ i₄ i₅ : ι') (hi₀₁ : i₀ ≤ i₁)
  (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (hi₃₄ : i₃ ≤ i₄) (hi₄₅ : i₄ ≤ i₅)

/-- For a spectral object indexed by a preorder, this is the map
`E^{n₁}(i₀ ≤ i₁ ≤ i₃ ≤ i₄) ⟶ E^{n₁}(i₀ ≤ i₂ ≤ i₃ ≤ i₄)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.mapFour** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a spectral object indexed by a preorder, this is the map
`E^{n₁}(i₀ ≤ i₁ ≤ i₃ ≤ i₄) ⟶ E^{n₁}(i₀ ≤ i₂ ≤ i₃ ≤ i₄)`.
-/
noncomputable abbrev mapFourδ₂Toδ₁' (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :=
  X'.map _ _ _ _ _ _ (fourδ₂Toδ₁' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂
/-
**CategoryTheory.Abelian.SpectralObject.isIso_mapFour** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_mapFourδ₂Toδ₁' (n₀ n₁ n₂ : ℤ)
    (h₁ : IsIso ((X'.H n₁).map (twoδ₁Toδ₀' i₁ i₂ i₃ hi₁₂ hi₂₃)))
    (h₂ : IsIso ((X'.H n₂).map (twoδ₂Toδ₁' i₀ i₁ i₂ hi₀₁ hi₁₂)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.mapFourδ₂Toδ₁' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_map _ _ _ _ _ _ _ _ _ _
    (by exact (inferInstanceAs (IsIso ((X'.H n₀).map (𝟙 _))))) h₁ h₂

end

end

end SpectralObject

end Abelian

end CategoryTheory

