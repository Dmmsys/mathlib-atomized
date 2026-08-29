/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.ComposableArrows.One
public import Mathlib.CategoryTheory.ComposableArrows.Two

/-!
# Spectral objects in abelian categories

In this file, we introduce the category `SpectralObject C ι` of spectral
objects in an abelian category `C` indexed by the category `ι`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Abelian

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

open ComposableArrows

/--
Definition of `SpectralObject` / `SpectralObject` 的定义

English:
structure SpectralObject
  parameters: where
  axioms and operations (5):
    - H((n : Int)) : ComposableArrows ι 1 ⥤ C
    - δ'((n₀ n₁ : Int) (h : n₀ + 1 = n₁)) : functorArrows ι 1 2 2 ⋙ H n₀ ⟶ functorArrows ι 0 1 2 ⋙ H n₁
    - exact₁'((n₀ n₁ : Int) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2)) : (mk₂ ((δ' n₀ n₁ h).app D) ((H n₁).map ((mapFunctorArrows ι 0 1 0 2 2).app D))).Exact
    - exact₂'((n : Int) (D : ComposableArrows ι 2)) : (mk₂ ((H n).map ((mapFunctorArrows ι 0 1 0 2 2).app D)) ((H n).map ((mapFunctorArrows ι 0 2 1 2 2).app D))).Exact
    - exact₃'((n₀ n₁ : Int) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2)) : (mk₂ ((H n₀).map ((mapFunctorArrows ι 0 2 1 2 2).app D)) ((δ' n₀ n₁ h).app D)).Exact

中文:
结构 SpectralObject
  参数: where
  公理与运算 (5 个):
    - H((n : 整数)) : ComposableArrows ι 1 ⥤ C
    - δ'((n₀ n₁ : 整数) (h : n₀ + 1 = n₁)) : functorArrows ι 1 2 2 ⋙ H n₀ ⟶ functorArrows ι 0 1 2 ⋙ H n₁
    - exact₁'((n₀ n₁ : 整数) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2)) : (mk₂ ((δ' n₀ n₁ h).app D) ((H n₁).map ((mapFunctorArrows ι 0 1 0 2 2).app D))).Exact
    - exact₂'((n : 整数) (D : ComposableArrows ι 2)) : (mk₂ ((H n).map ((mapFunctorArrows ι 0 1 0 2 2).app D)) ((H n).map ((mapFunctorArrows ι 0 2 1 2 2).app D))).Exact
    - exact₃'((n₀ n₁ : 整数) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2)) : (mk₂ ((H n₀).map ((mapFunctorArrows ι 0 2 1 2 2).app D)) ((δ' n₀ n₁ h).app D)).Exact
-/
structure SpectralObject where
  /-- A sequence of functors from `ComposableArrows ι 1` to the abelian category.
  The image of `mk₁ f` will be referred to as `H^n(f)` in the documentation. -/
  H (n : Int) : ComposableArrows ι 1 ⥤ C
  /-- The connecting homomorphism of the spectral object. (Use `δ` instead.) -/
  δ' (n₀ n₁ : Int) (h : n₀ + 1 = n₁) :
    functorArrows ι 1 2 2 ⋙ H n₀ ⟶ functorArrows ι 0 1 2 ⋙ H n₁
  exact₁' (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    (mk₂ ((δ' n₀ n₁ h).app D) ((H n₁).map ((mapFunctorArrows ι 0 1 0 2 2).app D))).Exact
  exact₂' (n : Int) (D : ComposableArrows ι 2) :
    (mk₂ ((H n).map ((mapFunctorArrows ι 0 1 0 2 2).app D))
      ((H n).map ((mapFunctorArrows ι 0 2 1 2 2).app D))).Exact
  exact₃' (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    (mk₂ ((H n₀).map ((mapFunctorArrows ι 0 2 1 2 2).app D)) ((δ' n₀ n₁ h).app D)).Exact

namespace SpectralObject

variable {C ι} (X : SpectralObject C ι)

section

/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia)
  body: (X.δ' n₀ n₁ hn₁).app (mk₂ f g)

中文:
定义 δ
  签名: {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : 整数) (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: (X.δ' n₀ n₁ hn₁).app (mk₂ f g)
-/
def δ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.H n₀).obj (mk₁ g) ⟶ (X.H n₁).obj (mk₁ f) :=
  (X.δ' n₀ n₁ hn₁).app (mk₂ f g)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `δ_naturality` / 引理 `δ_naturality`

English:
lemma δ_naturality
  statement: {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  proof: by
  have h := (X.δ' n₀ n₁ hn₁).naturality
    (homMk₂ (α.app 0) (α.app 1) (β.app 1) (naturality' α 0 1)
      (by simpa only [hαβ] using! naturality' β 0 1) : mk₂ f g ⟶ mk₂ f' g')
  dsimp at h
  convert! h <;> cat_disch

中文:
引理 δ_naturality
  结论: {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  证明: by
  have h := (X.δ' n₀ n₁ hn₁).naturality
    (homMk₂ (α.app 0) (α.app 1) (β.app 1) (naturality' α 0 1)
      (by simpa only [hαβ] using! naturality' β 0 1) : mk₂ f g ⟶ mk₂ f' g')
  dsimp at h
  convert! h <;> cat_disch

Depends on / 依赖: cat_disch, convert, naturality
-/
lemma δ_naturality {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
    {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
    (α : mk₁ f ⟶ mk₁ f') (β : mk₁ g ⟶ mk₁ g')
    (n₀ n₁ : Int) (hαβ : α.app 1 = β.app 0 := by cat_disch) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.H n₀).map β ≫ X.δ f' g' n₀ n₁ hn₁ = X.δ f g n₀ n₁ hn₁ ≫ (X.H n₁).map α := by
  have h := (X.δ' n₀ n₁ hn₁).naturality
    (homMk₂ (α.app 0) (α.app 1) (β.app 1) (naturality' α 0 1)
      (by simpa only [hαβ] using! naturality' β 0 1) : mk₂ f g ⟶ mk₂ f' g')
  dsimp at h
  convert! h <;> cat_disch

end

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  (fg : i ⟶ k) (h : f ≫ g = fg)

@[reassoc (attr := simp)]
/--
lemma `zero₁` / 引理 `zero₁`

English:
lemma zero₁
  given: (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  subst h
  exact (X.exact₁' n₀ n₁ hn₁ (mk₂ f g)).zero 0

@[reassoc (attr := simp)]

中文:
引理 zero₁
  条件: (n₀ n₁ : 整数) (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  subst h
  exact (X.exact₁' n₀ n₁ hn₁ (mk₂ f g)).zero 0

@[reassoc (attr := simp)]

Depends on / 依赖: X.exact
-/
lemma zero₁ (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ ≫ (X.H n₁).map (twoδ₂Toδ₁ f g fg h) = 0 := by
  subst h
  exact (X.exact₁' n₀ n₁ hn₁ (mk₂ f g)).zero 0

@[reassoc (attr := simp)]
/--
lemma `zero₂` / 引理 `zero₂`

English:
lemma zero₂
  given: (fg : i ⟶ k) (h : f ≫ g = fg) (n₀ : Int)
  proof: by
  subst h
  exact (X.exact₂' n₀ (mk₂ f g)).zero 0

@[reassoc (attr := simp)]

中文:
引理 zero₂
  条件: (fg : i ⟶ k) (h : f ≫ g = fg) (n₀ : 整数)
  证明: by
  subst h
  exact (X.exact₂' n₀ (mk₂ f g)).zero 0

@[reassoc (attr := simp)]

Depends on / 依赖: X.exact
-/
lemma zero₂ (fg : i ⟶ k) (h : f ≫ g = fg) (n₀ : Int) :
    (X.H n₀).map (twoδ₂Toδ₁ f g fg h) ≫ (X.H n₀).map (twoδ₁Toδ₀ f g fg h) = 0 := by
  subst h
  exact (X.exact₂' n₀ (mk₂ f g)).zero 0

@[reassoc (attr := simp)]
/--
lemma `zero₃` / 引理 `zero₃`

English:
lemma zero₃
  given: (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  subst h
  exact (X.exact₃' n₀ n₁ hn₁ (mk₂ f g)).zero 0

中文:
引理 zero₃
  条件: (n₀ n₁ : 整数) (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  subst h
  exact (X.exact₃' n₀ n₁ hn₁ (mk₂ f g)).zero 0

Depends on / 依赖: X.exact
-/
lemma zero₃ (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.H n₀).map (twoδ₁Toδ₀ f g fg h) ≫ X.δ f g n₀ n₁ hn₁ = 0 := by
  subst h
  exact (X.exact₃' n₀ n₁ hn₁ (mk₂ f g)).zero 0

/-- The (exact) short complex `H^n₀(g) ⟶ H^n₁(f) ⟶ H^n₁(fg)` of a
spectral object, when `f ≫ g = fg` and `n₀ + 1 = n₁`. -/
@[simps]
/--
Definition of `sc₁` / `sc₁` 的定义

English:
definition sc₁
  signature: (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia)
  body: ShortComplex.mk _ _ (X.zero₁ f g fg h n₀ n₁ hn₁)

中文:
定义 sc₁
  签名: (n₀ n₁ : 整数) (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: ShortComplex.mk _ _ (X.zero₁ f g fg h n₀ n₁ hn₁)

Depends on / 依赖: ShortComplex, ShortComplex.mk, X.zero
-/
def sc₁ (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₁ f g fg h n₀ n₁ hn₁)

/-- The (exact) short complex `H^n₀(f) ⟶ H^n₀(fg) ⟶ H^n₀(g)` of a
spectral object, when `f ≫ g = fg`. -/
@[simps]
/--
Definition of `sc₂` / `sc₂` 的定义

English:
definition sc₂
  signature: (n₀ : Int)
  body: ShortComplex.mk _ _ (X.zero₂ f g fg h n₀)

中文:
定义 sc₂
  签名: (n₀ : 整数)
  定义体: ShortComplex.mk _ _ (X.zero₂ f g fg h n₀)

Depends on / 依赖: ShortComplex, ShortComplex.mk, X.zero
-/
def sc₂ (n₀ : Int) : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₂ f g fg h n₀)

/-- The (exact) short complex `H^n₀(fg) ⟶ H^n₀(g) ⟶ H^n₁(f)`
of a spectral object, when `f ≫ g = fg` and `n₀ + 1 = n₁`. -/
@[simps]
/--
Definition of `sc₃` / `sc₃` 的定义

English:
definition sc₃
  signature: (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia)
  body: ShortComplex.mk _ _ (X.zero₃ f g fg h n₀ n₁ hn₁)

中文:
定义 sc₃
  签名: (n₀ n₁ : 整数) (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: ShortComplex.mk _ _ (X.zero₃ f g fg h n₀ n₁ hn₁)

Depends on / 依赖: ShortComplex, ShortComplex.mk, X.zero
-/
def sc₃ (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₃ f g fg h n₀ n₁ hn₁)

/--
lemma `exact₁` / 引理 `exact₁`

English:
lemma exact₁
  given: (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  subst h
  exact (X.exact₁' n₀ n₁ hn₁ (mk₂ f g)).exact 0

中文:
引理 exact₁
  条件: (n₀ n₁ : 整数) (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  subst h
  exact (X.exact₁' n₀ n₁ hn₁ (mk₂ f g)).exact 0

Depends on / 依赖: X.exact, X.sc
-/
lemma exact₁ (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.sc₁ f g fg h n₀ n₁ hn₁).Exact := by
  subst h
  exact (X.exact₁' n₀ n₁ hn₁ (mk₂ f g)).exact 0

/--
lemma `exact₂` / 引理 `exact₂`

English:
lemma exact₂
  given: (n₀ : Int)
  proof: by
  subst h
  exact (X.exact₂' n₀ (mk₂ f g)).exact 0

中文:
引理 exact₂
  条件: (n₀ : 整数)
  证明: by
  subst h
  exact (X.exact₂' n₀ (mk₂ f g)).exact 0

Depends on / 依赖: X.exact
-/
lemma exact₂ (n₀ : Int) :
    (X.sc₂ f g fg h n₀).Exact := by
  subst h
  exact (X.exact₂' n₀ (mk₂ f g)).exact 0

/--
lemma `exact₃` / 引理 `exact₃`

English:
lemma exact₃
  given: (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  subst h
  exact ((X.exact₃' n₀ n₁ hn₁ (mk₂ f g))).exact 0

中文:
引理 exact₃
  条件: (n₀ n₁ : 整数) (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  subst h
  exact ((X.exact₃' n₀ n₁ hn₁ (mk₂ f g))).exact 0

Depends on / 依赖: X.exact, X.sc
-/
lemma exact₃ (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.sc₃ f g fg h n₀ n₁ hn₁).Exact := by
  subst h
  exact ((X.exact₃' n₀ n₁ hn₁ (mk₂ f g))).exact 0

/--
Definition of `composableArrows₅` / `composableArrows₅` 的定义

English:
abbreviation composableArrows₅
  signature: (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia)
  body: mk₅ ((X.H n₀).map (twoδ₂Toδ₁ f g fg h)) ((X.H n₀).map (twoδ₁Toδ₀ f g fg h))
    (X.δ f g n₀ n₁ hn₁) ((X.H n₁).map (twoδ₂Toδ₁ f g fg h))
    ((X.H n₁).map (twoδ₁Toδ₀ f g fg h))

中文:
缩写 composableArrows₅
  签名: (n₀ n₁ : 整数) (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: mk₅ ((X.H n₀).map (twoδ₂Toδ₁ f g fg h)) ((X.H n₀).map (twoδ₁Toδ₀ f g fg h))
    (X.δ f g n₀ n₁ hn₁) ((X.H n₁).map (twoδ₂Toδ₁ f g fg h))
    ((X.H n₁).map (twoδ₁Toδ₀ f g fg h))

Depends on / 依赖: ComposableArrows
-/
abbrev composableArrows₅ (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) :
    ComposableArrows C 5 :=
  mk₅ ((X.H n₀).map (twoδ₂Toδ₁ f g fg h)) ((X.H n₀).map (twoδ₁Toδ₀ f g fg h))
    (X.δ f g n₀ n₁ hn₁) ((X.H n₁).map (twoδ₂Toδ₁ f g fg h))
    ((X.H n₁).map (twoδ₁Toδ₀ f g fg h))

/--
lemma `composableArrows₅_exact` / 引理 `composableArrows₅_exact`

English:
lemma composableArrows₅_exact
  given: (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: exact_of_δ₀ (X.exact₂ _ _ _ h n₀).exact_toComposableArrows
    (exact_of_δ₀ (X.exact₃ _ _ _ h n₀ n₁ hn₁).exact_toComposableArrows
      (exact_of_δ₀ (X.exact₁ _ _ _ h n₀ n₁ hn₁).exact_toComposableArrows
        ((X.exact₂ _ _ _ h n₁).exact_toComposableArrows)))

中文:
引理 composableArrows₅_exact
  条件: (n₀ n₁ : 整数) (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: exact_of_δ₀ (X.exact₂ _ _ _ h n₀).exact_toComposableArrows
    (exact_of_δ₀ (X.exact₃ _ _ _ h n₀ n₁ hn₁).exact_toComposableArrows
      (exact_of_δ₀ (X.exact₁ _ _ _ h n₀ n₁ hn₁).exact_toComposableArrows
        ((X.exact₂ _ _ _ h n₁).exact_toComposableArrows)))

Depends on / 依赖: X.composableArrows, X.exact, exact_toComposableArrows
-/
lemma composableArrows₅_exact (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.composableArrows₅ f g fg h n₀ n₁ hn₁).Exact :=
  exact_of_δ₀ (X.exact₂ _ _ _ h n₀).exact_toComposableArrows
    (exact_of_δ₀ (X.exact₃ _ _ _ h n₀ n₁ hn₁).exact_toComposableArrows
      (exact_of_δ₀ (X.exact₁ _ _ _ h n₀ n₁ hn₁).exact_toComposableArrows
        ((X.exact₂ _ _ _ h n₁).exact_toComposableArrows)))

end

@[reassoc (attr := simp)]
/--
lemma `δ_δ` / 引理 `δ_δ`

English:
lemma δ_δ
  statement: {i j k l : ι} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
  proof: by
  have eq := X.δ_naturality f g f (g ≫ h) (𝟙 _) (twoδ₂Toδ₁ g h _ rfl) n₁ n₂
  rw [Functor.map_id]; rw [comp_id] at eq
  rw [← eq]; rw [X.zero₁_assoc g h _ rfl n₀ n₁ hn₁]; rw [zero_comp]

中文:
引理 δ_δ
  结论: {i j k l : ι} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
  证明: by
  have eq := X.δ_naturality f g f (g ≫ h) (𝟙 _) (twoδ₂Toδ₁ g h _ rfl) n₁ n₂
  rw [Functor.map_id]; rw [comp_id] at eq
  rw [← eq]; rw [X.zero₁_assoc g h _ rfl n₀ n₁ hn₁]; rw [zero_comp]

Depends on / 依赖: Functor, Functor.map_id, X.zero, comp_id, map_id, zero_comp
-/
lemma δ_δ {i j k l : ι} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
    (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.δ g h n₀ n₁ hn₁ ≫ X.δ f g n₁ n₂ hn₂ = 0 := by
  have eq := X.δ_naturality f g f (g ≫ h) (𝟙 _) (twoδ₂Toδ₁ g h _ rfl) n₁ n₂
  rw [Functor.map_id]; rw [comp_id] at eq
  rw [← eq]; rw [X.zero₁_assoc g h _ rfl n₀ n₁ hn₁]; rw [zero_comp]

/-- The type of morphisms between spectral objects in abelian categories. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X' : SpectralObject C ι)
  axioms and operations (2):
    - hom((n : Int)) : X.H n ⟶ X'.H n
    - comm((n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)) : X.δ f g n₀ n₁ hn₁ ≫ (hom n₁).app (mk₁ f) = (hom n₀).app (mk₁ g) ≫ X'.δ f g n₀ n₁ hn₁  [default: by cat_disch]

中文:
结构 Hom
  参数: (X' : SpectralObject C ι)
  公理与运算 (2 个):
    - hom((n : 整数)) : X.H n ⟶ X'.H n
    - comm((n₀ n₁ : 整数) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)) : X.δ f g n₀ n₁ hn₁ ≫ (hom n₁).app (mk₁ f) = (hom n₀).app (mk₁ g) ≫ X'.δ f g n₀ n₁ hn₁  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (X' : SpectralObject C ι) where
  /-- The natural transformation that is part of a morphism between spectral objects. -/
  hom (n : Int) : X.H n ⟶ X'.H n
  comm (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) :
    X.δ f g n₀ n₁ hn₁ ≫ (hom n₁).app (mk₁ f) =
    (hom n₀).app (mk₁ g) ≫ X'.δ f g n₀ n₁ hn₁ := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (SpectralObject C ι)
  body: Hom
  id X := { hom _ := 𝟙 _ }
  comp f g := { hom n := f.hom n ≫ g.hom n }

中文:
实例 :
  签名: Category (SpectralObject C ι)
  定义体: Hom
  id X := { hom _ := 𝟙 _ }
  comp f g := { hom n := f.hom n ≫ g.hom n }
-/
instance : Category (SpectralObject C ι) where
  Hom := Hom
  id X := { hom _ := 𝟙 _ }
  comp f g := { hom n := f.hom n ≫ g.hom n }

attribute [simp] id_hom
attribute [reassoc, simp] comp_hom

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isZero_H_map_mk₁_of_isIso` / 引理 `isZero_H_map_mk₁_of_isIso`

English:
lemma isZero_H_map_mk₁_of_isIso
  given: (n : Int) {i₀ i₁ : ι} (f : i₀ ⟶ i₁) [IsIso f]
  proof: by
  let φ := twoδ₂Toδ₁ f (inv f) (𝟙 i₀) (by simp) ≫ twoδ₁Toδ₀ f (inv f) (𝟙 i₀)
  have : IsIso φ := by
    rw [isIso_iff₁]
    constructor <;> dsimp [φ] <;> infer_instance
  rw [IsZero.iff_id_eq_zero]
  rw [← cancel_mono ((X.H n).map φ)]; rw [Category.id_comp]; rw [zero_comp]; rw [← X.zero₂ f (inv f

中文:
引理 isZero_H_map_mk₁_of_isIso
  条件: (n : 整数) {i₀ i₁ : ι} (f : i₀ ⟶ i₁) [IsIso f]
  证明: by
  let φ := twoδ₂Toδ₁ f (inv f) (𝟙 i₀) (by simp) ≫ twoδ₁Toδ₀ f (inv f) (𝟙 i₀)
  have : IsIso φ := by
    rw [isIso_iff₁]
    constructor <;> dsimp [φ] <;> infer_instance
  rw [IsZero.iff_id_eq_zero]
  rw [← cancel_mono ((X.H n).map φ)]; rw [Category.id_comp]; rw [zero_comp]; rw [← X.zero₂ f (inv f

Depends on / 依赖: Category, Category.id_comp, Functor, Functor.map_comp, IsZero, IsZero.iff_id_eq_zero, X.zero, cancel_mono, id_comp, iff_id_eq_zero, infer_instance, map_comp, zero_comp
-/
lemma isZero_H_map_mk₁_of_isIso (n : Int) {i₀ i₁ : ι} (f : i₀ ⟶ i₁) [IsIso f] :
    IsZero ((X.H n).obj (mk₁ f)) := by
  let φ := twoδ₂Toδ₁ f (inv f) (𝟙 i₀) (by simp) ≫ twoδ₁Toδ₀ f (inv f) (𝟙 i₀)
  have : IsIso φ := by
    rw [isIso_iff₁]
    constructor <;> dsimp [φ] <;> infer_instance
  rw [IsZero.iff_id_eq_zero]
  rw [← cancel_mono ((X.H n).map φ)]; rw [Category.id_comp]; rw [zero_comp]; rw [← X.zero₂ f (inv f) (𝟙 _) (by simp)]; rw [← Functor.map_comp]

section

variable (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁) {i₀ i₁ i₂ : ι}
  (f : i₀ ⟶ i₁) (g : i₁ ⟶ i₂) (fg : i₀ ⟶ i₂) (hfg : f ≫ g = fg)
  (h₁ : IsZero ((X.H n₀).obj (mk₁ f))) (h₂ : IsZero ((X.H n₁).obj (mk₁ f)))

include h₁ in
/--
lemma `mono_H_map_twoδ₁Toδ₀` / 引理 `mono_H_map_twoδ₁Toδ₀`

English:
lemma mono_H_map_twoδ₁Toδ₀
  statement: Mono ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg))
  proof: (X.exact₂ f g fg hfg n₀).mono_g (h₁.eq_of_src _ _)

include h₂ hn₁ in

中文:
引理 mono_H_map_twoδ₁Toδ₀
  结论: Mono ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg))
  证明: (X.exact₂ f g fg hfg n₀).mono_g (h₁.eq_of_src _ _)

include h₂ hn₁ in

Depends on / 依赖: X.exact, eq_of_src, mono_g
-/
lemma mono_H_map_twoδ₁Toδ₀ : Mono ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg)) :=
  (X.exact₂ f g fg hfg n₀).mono_g (h₁.eq_of_src _ _)

include h₂ hn₁ in
/--
lemma `epi_H_map_twoδ₁Toδ₀` / 引理 `epi_H_map_twoδ₁Toδ₀`

English:
lemma epi_H_map_twoδ₁Toδ₀
  statement: Epi ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg))
  proof: (X.exact₃ f g fg hfg n₀ n₁ hn₁).epi_f (h₂.eq_of_tgt _ _)

include h₁ h₂ hn₁ in

中文:
引理 epi_H_map_twoδ₁Toδ₀
  结论: Epi ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg))
  证明: (X.exact₃ f g fg hfg n₀ n₁ hn₁).epi_f (h₂.eq_of_tgt _ _)

include h₁ h₂ hn₁ in

Depends on / 依赖: X.exact, epi_f, eq_of_tgt
-/
lemma epi_H_map_twoδ₁Toδ₀ : Epi ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg)) :=
  (X.exact₃ f g fg hfg n₀ n₁ hn₁).epi_f (h₂.eq_of_tgt _ _)

include h₁ h₂ hn₁ in
/--
lemma `isIso_H_map_twoδ₁Toδ₀` / 引理 `isIso_H_map_twoδ₁Toδ₀`

English:
lemma isIso_H_map_twoδ₁Toδ₀
  statement: IsIso ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg))
  proof: by
  have := X.mono_H_map_twoδ₁Toδ₀ n₀ f g fg hfg h₁
  have := X.epi_H_map_twoδ₁Toδ₀ n₀ n₁ hn₁ f g fg hfg h₂
  apply isIso_of_mono_of_epi

中文:
引理 isIso_H_map_twoδ₁Toδ₀
  结论: IsIso ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg))
  证明: by
  have := X.mono_H_map_twoδ₁Toδ₀ n₀ f g fg hfg h₁
  have := X.epi_H_map_twoδ₁Toδ₀ n₀ n₁ hn₁ f g fg hfg h₂
  apply isIso_of_mono_of_epi

Depends on / 依赖: X.epi_H_map_two, X.mono_H_map_two, isIso_of_mono_of_epi
-/
lemma isIso_H_map_twoδ₁Toδ₀ : IsIso ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg)) := by
  have := X.mono_H_map_twoδ₁Toδ₀ n₀ f g fg hfg h₁
  have := X.epi_H_map_twoδ₁Toδ₀ n₀ n₁ hn₁ f g fg hfg h₂
  apply isIso_of_mono_of_epi

end

section

variable {ι' : Type*} [Preorder ι'] (X' : SpectralObject C ι')
  (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁) (i₀ i₁ i₂ : ι') (h₀₁ : i₀ <= i₁) (h₁₂ : i₁ <= i₂)
  (h₁ : IsZero ((X'.H n₀).obj (mk₁ (homOfLE h₀₁))))
  (h₂ : IsZero ((X'.H n₁).obj (mk₁ (homOfLE h₀₁))))

include h₁ in
/--
lemma `mono_H_map_twoδ₁Toδ₀'` / 引理 `mono_H_map_twoδ₁Toδ₀'`

English:
lemma mono_H_map_twoδ₁Toδ₀'
  statement: Mono ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂))
  proof: X'.mono_H_map_twoδ₁Toδ₀ _ _ _ _ _ h₁

include h₂ hn₁ in

中文:
引理 mono_H_map_twoδ₁Toδ₀'
  结论: Mono ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂))
  证明: X'.mono_H_map_twoδ₁Toδ₀ _ _ _ _ _ h₁

include h₂ hn₁ in
-/
lemma mono_H_map_twoδ₁Toδ₀' : Mono ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂)) :=
  X'.mono_H_map_twoδ₁Toδ₀ _ _ _ _ _ h₁

include h₂ hn₁ in
/--
lemma `epi_H_map_twoδ₁Toδ₀'` / 引理 `epi_H_map_twoδ₁Toδ₀'`

English:
lemma epi_H_map_twoδ₁Toδ₀'
  statement: Epi ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂))
  proof: X'.epi_H_map_twoδ₁Toδ₀ _ _ hn₁ _ _ _ _ h₂

include h₁ h₂ hn₁ in

中文:
引理 epi_H_map_twoδ₁Toδ₀'
  结论: Epi ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂))
  证明: X'.epi_H_map_twoδ₁Toδ₀ _ _ hn₁ _ _ _ _ h₂

include h₁ h₂ hn₁ in
-/
lemma epi_H_map_twoδ₁Toδ₀' : Epi ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂)) :=
  X'.epi_H_map_twoδ₁Toδ₀ _ _ hn₁ _ _ _ _ h₂

include h₁ h₂ hn₁ in
/--
lemma `isIso_H_map_twoδ₁Toδ₀'` / 引理 `isIso_H_map_twoδ₁Toδ₀'`

English:
lemma isIso_H_map_twoδ₁Toδ₀'
  statement: IsIso ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂))
  proof: X'.isIso_H_map_twoδ₁Toδ₀ _ _ hn₁ _ _ _ _ h₁ h₂

中文:
引理 isIso_H_map_twoδ₁Toδ₀'
  结论: IsIso ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂))
  证明: X'.isIso_H_map_twoδ₁Toδ₀ _ _ hn₁ _ _ _ _ h₁ h₂
-/
lemma isIso_H_map_twoδ₁Toδ₀' : IsIso ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂)) :=
  X'.isIso_H_map_twoδ₁Toδ₀ _ _ hn₁ _ _ _ _ h₁ h₂

end

end SpectralObject

end Abelian

end CategoryTheory
