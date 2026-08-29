/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# The adjunction between the nerve and the homotopy category functor

We define an adjunction `nerveAdjunction : hoFunctor ⊣ nerveFunctor` between the functor that
takes a simplicial set to its homotopy category and the functor that takes a category to its nerve.

Up to natural isomorphism, this is constructed as the composite of two other adjunctions,
namely `nerve₂Adj : hoFunctor₂ ⊣ nerveFunctor₂` between analogously-defined functors involving
the category of 2-truncated simplicial sets and `coskAdj 2 : truncation 2 ⊣ Truncated.cosk 2`. The
aforementioned natural isomorphism

`cosk₂Iso : nerveFunctor ≅ nerveFunctor₂ ⋙ Truncated.cosk 2`

exists because nerves of categories are 2-coskeletal.

We also prove that `nerveFunctor` is fully faithful, demonstrating that `nerveAdjunction` is
reflective. Since the category of simplicial sets is cocomplete, we conclude in
`Mathlib/CategoryTheory/Category/Cat/Colimit.lean` that the category of categories has colimits.

Finally we show that `hoFunctor : SSet.{u} ⥤ Cat.{u, u}` preserves finite cartesian products; note
that it fails to preserve infinite products.

-/

@[expose] public section

universe u

open CategoryTheory Nerve Simplicial SimplicialObject.Truncated
  SimplexCategory.Truncated Opposite Limits

namespace SSet

namespace Truncated

section liftOfStrictSegal
/-! The goal of this section is to define `SSet.Truncated.liftOfStrictSegal`
which allows to construct of morphism `X ⟶ Y` of `2`-truncated simplicial sets
from the data of maps on `0`- and `1`-simplices when `Y` is strict Segal.
-/

variable {n : Nat} {X Y : Truncated.{u} 2} (f₀ : X _⦋0⦌₂ -> Y _⦋0⦌₂) (f₁ : X _⦋1⦌₂ -> Y _⦋1⦌₂)
  (hδ₁ : forall (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op (f₁ x))
  (hδ₀ : forall (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op (f₁ x))
  (H : forall (x : X _⦋2⦌₂) (y : Y _⦋2⦌₂), f₁ (X.map (δ₂ 2).op x) = Y.map (δ₂ 2).op y ->
    f₁ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op y ->
      f₁ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op y)
  (hσ : forall (x : X _⦋0⦌₂), f₁ (X.map (σ₂ 0).op x) = Y.map (σ₂ 0).op (f₀ x))
  (hY : Y.StrictSegal)

namespace liftOfStrictSegal

/--
Definition of `f₂` / `f₂` 的定义

English:
definition f₂
  signature: (x : X _⦋2⦌₂)
  body: (hY.spineEquiv 2).symm
    (.mk₂ (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 2).op x)))
      (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 0).op x))) (by
        simp only [spine_vertex]
        rw [← δ₂_one_eq_const]; rw [← δ₂_zero_eq_const]; rw [← hδ₁]; rw [← hδ₀]
        simp only [← Functor.map_comp_apply, ← op_

中文:
定义 f₂
  签名: (x : X _⦋2⦌₂)
  定义体: (hY.spineEquiv 2).symm
    (.mk₂ (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 2).op x)))
      (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 0).op x))) (by
        simp only [spine_vertex]
        rw [← δ₂_one_eq_const]; rw [← δ₂_zero_eq_const]; rw [← hδ₁]; rw [← hδ₀]
        simp only [← Functor.map_comp_apply, ← op_

Depends on / 依赖: Functor, Functor.map_comp_apply, X.map, Y.spine, hY.spineEquiv, map_comp_apply, op_comp, spineEquiv, spine_vertex
-/
def f₂ (x : X _⦋2⦌₂) : Y _⦋2⦌₂ :=
  (hY.spineEquiv 2).symm
    (.mk₂ (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 2).op x)))
      (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 0).op x))) (by
        simp only [spine_vertex]
        rw [← δ₂_one_eq_const]; rw [← δ₂_zero_eq_const]; rw [← hδ₁]; rw [← hδ₀]
        simp only [← Functor.map_comp_apply, ← op_comp, δ₂_zero_comp_δ₂_two]))

@[simp]
/--
lemma `spineEquiv_f₂_arrow_zero` / 引理 `spineEquiv_f₂_arrow_zero`

English:
lemma spineEquiv_f₂_arrow_zero
  given: (x : X _⦋2⦌₂)
  proof: by
  simp [f₂]

@[simp]

中文:
引理 spineEquiv_f₂_arrow_zero
  条件: (x : X _⦋2⦌₂)
  证明: by
  simp [f₂]

@[simp]
-/
lemma spineEquiv_f₂_arrow_zero (x : X _⦋2⦌₂) :
    ((hY.spineEquiv 2) (f₂ f₀ f₁ hδ₁ hδ₀ hY x)).arrow 0 = f₁ (X.map (δ₂ 2).op x) := by
  simp [f₂]

@[simp]
/--
lemma `spineEquiv_f₂_arrow_one` / 引理 `spineEquiv_f₂_arrow_one`

English:
lemma spineEquiv_f₂_arrow_one
  given: (x : X _⦋2⦌₂)
  proof: by
  simp [f₂]

中文:
引理 spineEquiv_f₂_arrow_one
  条件: (x : X _⦋2⦌₂)
  证明: by
  simp [f₂]
-/
lemma spineEquiv_f₂_arrow_one (x : X _⦋2⦌₂) :
    ((hY.spineEquiv 2) (f₂ f₀ f₁ hδ₁ hδ₀ hY x)).arrow 1 = f₁ (X.map (δ₂ 0).op x) := by
  simp [f₂]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `hδ'₀` / 引理 `hδ'₀`

English:
lemma hδ'₀
  given: (x : X _⦋2⦌₂)
  proof: by
  simp [← spineEquiv_f₂_arrow_one f₀ f₁ hδ₁ hδ₀ hY, StrictSegal.spineEquiv,
    SimplexCategory.mkOfSucc_one_eq_δ]

中文:
引理 hδ'₀
  条件: (x : X _⦋2⦌₂)
  证明: by
  simp [← spineEquiv_f₂_arrow_one f₀ f₁ hδ₁ hδ₀ hY, StrictSegal.spineEquiv,
    SimplexCategory.mkOfSucc_one_eq_δ]

Depends on / 依赖: SimplexCategory, SimplexCategory.mkOfSucc_one_eq_, StrictSegal, StrictSegal.spineEquiv, spineEquiv
-/
lemma hδ'₀ (x : X _⦋2⦌₂) :
    f₁ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x) := by
  simp [← spineEquiv_f₂_arrow_one f₀ f₁ hδ₁ hδ₀ hY, StrictSegal.spineEquiv,
    SimplexCategory.mkOfSucc_one_eq_δ]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `hδ'₂` / 引理 `hδ'₂`

English:
lemma hδ'₂
  given: (x : X _⦋2⦌₂)
  proof: by
  simp [← spineEquiv_f₂_arrow_zero f₀ f₁ hδ₁ hδ₀ hY, StrictSegal.spineEquiv,
    SimplexCategory.mkOfSucc_zero_eq_δ]

include H in

中文:
引理 hδ'₂
  条件: (x : X _⦋2⦌₂)
  证明: by
  simp [← spineEquiv_f₂_arrow_zero f₀ f₁ hδ₁ hδ₀ hY, StrictSegal.spineEquiv,
    SimplexCategory.mkOfSucc_zero_eq_δ]

include H in
-/
lemma hδ'₂ (x : X _⦋2⦌₂) :
    f₁ (X.map (δ₂ 2).op x) = Y.map (δ₂ 2).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x) := by
  simp [← spineEquiv_f₂_arrow_zero f₀ f₁ hδ₁ hδ₀ hY, StrictSegal.spineEquiv,
    SimplexCategory.mkOfSucc_zero_eq_δ]

include H in
/--
lemma `hδ'₁` / 引理 `hδ'₁`

English:
lemma hδ'₁
  given: (x : X _⦋2⦌₂)
  proof: H x (f₂ f₀ f₁ hδ₁ hδ₀ hY x) (hδ'₂ f₀ f₁ hδ₁ hδ₀ hY x) (hδ'₀ f₀ f₁ hδ₁ hδ₀ hY x)

中文:
引理 hδ'₁
  条件: (x : X _⦋2⦌₂)
  证明: H x (f₂ f₀ f₁ hδ₁ hδ₀ hY x) (hδ'₂ f₀ f₁ hδ₁ hδ₀ hY x) (hδ'₀ f₀ f₁ hδ₁ hδ₀ hY x)
-/
lemma hδ'₁ (x : X _⦋2⦌₂) :
    f₁ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x) :=
  H x (f₂ f₀ f₁ hδ₁ hδ₀ hY x) (hδ'₂ f₀ f₁ hδ₁ hδ₀ hY x) (hδ'₀ f₀ f₁ hδ₁ hδ₀ hY x)

set_option backward.isDefEq.respectTransparency.types false in
include hσ in
/--
lemma `hσ'₀` / 引理 `hσ'₀`

English:
lemma hσ'₀
  given: (x : X _⦋1⦌₂)
  proof: by
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    dsimp [StrictSegal.spineEquiv]
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_two_comp_σ₂_zero]; rw [op_comp]; rw [Functor.map_comp_apply]; rw [hσ]; rw [SimplexCategory.mkOfSucc_ze

中文:
引理 hσ'₀
  条件: (x : X _⦋1⦌₂)
  证明: by
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    dsimp [StrictSegal.spineEquiv]
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_two_comp_σ₂_zero]; rw [op_comp]; rw [Functor.map_comp_apply]; rw [hσ]; rw [SimplexCategory.mkOfSucc_ze

Depends on / 依赖: Functor, Functor.map_comp_apply, SimplexCategory, SimplexCategory.mk, SimplexCategory.mkOfSucc_zero_eq_, StrictSegal, StrictSegal.spineEquiv, fin_cases, hY.spineEquiv, injective, map_comp_apply, op_comp, spineEquiv
-/
lemma hσ'₀ (x : X _⦋1⦌₂) :
    f₂ f₀ f₁ hδ₁ hδ₀ hY (X.map (σ₂ 0).op x) = Y.map (σ₂ 0).op (f₁ x) := by
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    dsimp [StrictSegal.spineEquiv]
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_two_comp_σ₂_zero]; rw [op_comp]; rw [Functor.map_comp_apply]; rw [hσ]; rw [SimplexCategory.mkOfSucc_zero_eq_δ]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_two_comp_σ₂_zero]; rw [op_comp]; rw [Functor.map_comp_apply]; rw [hδ₁]
  · dsimp
    rw [spineEquiv_f₂_arrow_one]
    simp [StrictSegal.spineEquiv, SimplexCategory.mkOfSucc_one_eq_δ,
      ← Functor.map_comp_apply, ← op_comp]

set_option backward.isDefEq.respectTransparency.types false in
include hσ in
/--
lemma `hσ'₁` / 引理 `hσ'₁`

English:
lemma hσ'₁
  given: (x : X _⦋1⦌₂)
  proof: by
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    simp [StrictSegal.spineEquiv, SimplexCategory.mkOfSucc_zero_eq_δ,
      ← Functor.map_comp_apply, ← op_comp]
  · dsimp
    rw [spineEquiv_f₂_arrow_one]
    dsimp [StrictSegal.spineEquiv]
    

中文:
引理 hσ'₁
  条件: (x : X _⦋1⦌₂)
  证明: by
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    simp [StrictSegal.spineEquiv, SimplexCategory.mkOfSucc_zero_eq_δ,
      ← Functor.map_comp_apply, ← op_comp]
  · dsimp
    rw [spineEquiv_f₂_arrow_one]
    dsimp [StrictSegal.spineEquiv]
    
-/
lemma hσ'₁ (x : X _⦋1⦌₂) :
    f₂ f₀ f₁ hδ₁ hδ₀ hY (X.map (σ₂ 1).op x) = Y.map (σ₂ 1).op (f₁ x) := by
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    simp [StrictSegal.spineEquiv, SimplexCategory.mkOfSucc_zero_eq_δ,
      ← Functor.map_comp_apply, ← op_comp]
  · dsimp
    rw [spineEquiv_f₂_arrow_one]
    dsimp [StrictSegal.spineEquiv]
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_zero_comp_σ₂_one]; rw [op_comp]; rw [Functor.map_comp_apply]; rw [hσ]; rw [SimplexCategory.mkOfSucc_one_eq_δ]; rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_zero_comp_σ₂_one]; rw [op_comp]; rw [Functor.map_comp_apply]; rw [hδ₀]

/--
Definition of `app` / `app` 的定义

English:
definition app
  signature: (n : (SimplexCategory.Truncated 2)ᵒᵖ)
  body: by
  obtain ⟨⟨n⟩, hn⟩ := n
  match n with
  | 0 => exact ↾f₀
  | 1 => exact ↾f₁
  | 2 => exact ↾(f₂ f₀ f₁ hδ₁ hδ₀ hY)

中文:
定义 app
  签名: (n : (单纯形范畴.Truncated 2)ᵒᵖ)
  定义体: by
  obtain ⟨⟨n⟩, hn⟩ := n
  match n with
  | 0 => exact ↾f₀
  | 1 => exact ↾f₁
  | 2 => exact ↾(f₂ f₀ f₁ hδ₁ hδ₀ hY)
-/
def app (n : (SimplexCategory.Truncated 2)ᵒᵖ) : X.obj n ⟶ Y.obj n := by
  obtain ⟨⟨n⟩, hn⟩ := n
  match n with
  | 0 => exact ↾f₀
  | 1 => exact ↾f₁
  | 2 => exact ↾(f₂ f₀ f₁ hδ₁ hδ₀ hY)

/--
Definition of `naturalityProperty` / `naturalityProperty` 的定义

English:
abbreviation naturalityProperty
  signature: : MorphismProperty (SimplexCategory.Truncated 2)
  body: (MorphismProperty.naturalityProperty (app f₀ f₁ hδ₁ hδ₀ hY)).unop

include H hσ in

中文:
缩写 naturalityProperty
  签名: : MorphismProperty (单纯形范畴.Truncated 2)
  定义体: (MorphismProperty.naturalityProperty (app f₀ f₁ hδ₁ hδ₀ hY)).unop

include H hσ in

Depends on / 依赖: MorphismProperty, MorphismProperty.naturalityProperty, naturalityProperty
-/
abbrev naturalityProperty : MorphismProperty (SimplexCategory.Truncated 2) :=
  (MorphismProperty.naturalityProperty (app f₀ f₁ hδ₁ hδ₀ hY)).unop

include H hσ in
/--
lemma `naturalityProperty_eq_top` / 引理 `naturalityProperty_eq_top`

English:
lemma naturalityProperty_eq_top
  proof: by
  refine SimplexCategory.Truncated.morphismProperty_eq_top _
    (fun n hn i => ?_) (fun n hn i => ?_)
  · obtain _ | _ | n := n
    · fin_cases i
      · ext; apply hδ₀
      · ext; apply hδ₁
    · fin_cases i
      · ext; apply hδ'₀ f₀ f₁ hδ₁ hδ₀ hY
      · ext; apply hδ'₁ f₀ f₁ hδ₁ hδ₀ H hY
  

中文:
引理 naturalityProperty_eq_top
  证明: by
  refine SimplexCategory.Truncated.morphismProperty_eq_top _
    (fun n hn i => ?_) (fun n hn i => ?_)
  · obtain _ | _ | n := n
    · fin_cases i
      · ext; apply hδ₀
      · ext; apply hδ₁
    · fin_cases i
      · ext; apply hδ'₀ f₀ f₁ hδ₁ hδ₀ hY
      · ext; apply hδ'₁ f₀ f₁ hδ₁ hδ₀ H hY
  

Depends on / 依赖: SimplexCategory, SimplexCategory.Truncated.morphismProperty_eq_top, Truncated, fin_cases, morphismProperty_eq_top
-/
lemma naturalityProperty_eq_top :
    naturalityProperty f₀ f₁ hδ₁ hδ₀ hY = ⊤ := by
  refine SimplexCategory.Truncated.morphismProperty_eq_top _
    (fun n hn i => ?_) (fun n hn i => ?_)
  · obtain _ | _ | n := n
    · fin_cases i
      · ext; apply hδ₀
      · ext; apply hδ₁
    · fin_cases i
      · ext; apply hδ'₀ f₀ f₁ hδ₁ hδ₀ hY
      · ext; apply hδ'₁ f₀ f₁ hδ₁ hδ₀ H hY
      · ext; apply hδ'₂ f₀ f₁ hδ₁ hδ₀ hY
    · lia
  · obtain _ | _ | n := n
    · fin_cases i
      ext; apply hσ
    · fin_cases i
      · ext; apply hσ'₀ f₀ f₁ hδ₁ hδ₀ hσ hY
      · ext; apply hσ'₁ f₀ f₁ hδ₁ hδ₀ hσ hY
    · lia

end liftOfStrictSegal

open liftOfStrictSegal in
/--
Definition of `liftOfStrictSegal` / `liftOfStrictSegal` 的定义

English:
definition liftOfStrictSegal
  signature: : X ⟶ Y where
  body: liftOfStrictSegal.app f₀ f₁ hδ₁ hδ₀ hY
  naturality _ _ φ :=
    (liftOfStrictSegal.naturalityProperty_eq_top f₀ f₁ hδ₁ hδ₀ H hσ hY).symm.le
      φ.unop (by simp)

@[simp]

中文:
定义 liftOfStrictSegal
  签名: : X ⟶ Y where
  定义体: liftOfStrictSegal.app f₀ f₁ hδ₁ hδ₀ hY
  naturality _ _ φ :=
    (liftOfStrictSegal.naturalityProperty_eq_top f₀ f₁ hδ₁ hδ₀ H hσ hY).symm.le
      φ.unop (by simp)

@[simp]

Depends on / 依赖: liftOfStrictSegal, liftOfStrictSegal.app
-/
def liftOfStrictSegal : X ⟶ Y where
  app := liftOfStrictSegal.app f₀ f₁ hδ₁ hδ₀ hY
  naturality _ _ φ :=
    (liftOfStrictSegal.naturalityProperty_eq_top f₀ f₁ hδ₁ hδ₀ H hσ hY).symm.le
      φ.unop (by simp)

@[simp]
/--
lemma `liftOfStrictSegal_app_0` / 引理 `liftOfStrictSegal_app_0`

English:
lemma liftOfStrictSegal_app_0
  proof: rfl

@[simp]

中文:
引理 liftOfStrictSegal_app_0
  证明: rfl

@[simp]
-/
lemma liftOfStrictSegal_app_0 :
    (liftOfStrictSegal f₀ f₁ hδ₁ hδ₀ H hσ hY).app (op ⦋0⦌₂) = ↾f₀ := rfl

@[simp]
/--
lemma `liftOfStrictSegal_app_1` / 引理 `liftOfStrictSegal_app_1`

English:
lemma liftOfStrictSegal_app_1
  proof: rfl

中文:
引理 liftOfStrictSegal_app_1
  证明: rfl
-/
lemma liftOfStrictSegal_app_1 :
    (liftOfStrictSegal f₀ f₁ hδ₁ hδ₀ H hσ hY).app (op ⦋1⦌₂) = ↾f₁ := rfl

end liftOfStrictSegal

namespace HomotopyCategory

variable {X : Truncated.{u} 2} {C D : Type u} [SmallCategory C] [SmallCategory D]

/--
Definition of `descOfTruncation` / `descOfTruncation` 的定义

English:
definition descOfTruncation
  signature: (φ : X ⟶ (truncation 2).obj (nerve C))
  body: lift (fun x => nerveEquiv (φ.app _ x)) (fun e => nerve.homEquiv (e.map φ))
    (fun x => by simpa using! nerve.homEquiv_id (φ.app _ x))
      (fun h => nerve.homEquiv_comp (h.map φ))

@[simp]

中文:
定义 descOfTruncation
  签名: (φ : X ⟶ (truncation 2).obj (nerve C))
  定义体: lift (fun x => nerveEquiv (φ.app _ x)) (fun e => nerve.homEquiv (e.map φ))
    (fun x => by simpa using! nerve.homEquiv_id (φ.app _ x))
      (fun h => nerve.homEquiv_comp (h.map φ))

@[simp]

Depends on / 依赖: e.map, h.map, homEquiv, homEquiv_comp, homEquiv_id, nerve.homEquiv, nerve.homEquiv_comp, nerve.homEquiv_id, nerveEquiv
-/
def descOfTruncation (φ : X ⟶ (truncation 2).obj (nerve C)) :
    X.HomotopyCategory ⥤ C :=
  lift (fun x => nerveEquiv (φ.app _ x)) (fun e => nerve.homEquiv (e.map φ))
    (fun x => by simpa using! nerve.homEquiv_id (φ.app _ x))
      (fun h => nerve.homEquiv_comp (h.map φ))

@[simp]
/--
lemma `descOfTruncation_obj_mk` / 引理 `descOfTruncation_obj_mk`

English:
lemma descOfTruncation_obj_mk
  given: (φ : X ⟶ (truncation 2).obj (nerve C)) (x : X _⦋0⦌₂)
  proof: rfl

@[simp]

中文:
引理 descOfTruncation_obj_mk
  条件: (φ : X ⟶ (truncation 2).obj (nerve C)) (x : X _⦋0⦌₂)
  证明: rfl

@[simp]
-/
lemma descOfTruncation_obj_mk (φ : X ⟶ (truncation 2).obj (nerve C)) (x : X _⦋0⦌₂) :
    (descOfTruncation φ).obj (mk x) = nerveEquiv (φ.app _ x) := rfl

@[simp]
/--
lemma `descOfTruncation_map_homMk` / 引理 `descOfTruncation_map_homMk`

English:
lemma descOfTruncation_map_homMk
  statement: (φ : X ⟶ (truncation 2).obj (nerve C))
  proof: Category.id_comp _

中文:
引理 descOfTruncation_map_homMk
  结论: (φ : X ⟶ (truncation 2).obj (nerve C))
  证明: Category.id_comp _

Depends on / 依赖: Category, Category.id_comp, id_comp
-/
lemma descOfTruncation_map_homMk (φ : X ⟶ (truncation 2).obj (nerve C))
    {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) :
    (descOfTruncation φ).map (homMk e) = nerve.homEquiv (e.map φ) :=
  Category.id_comp _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `descOfTruncation_comp` / 引理 `descOfTruncation_comp`

English:
lemma descOfTruncation_comp
  statement: {X' : Truncated.{u} 2} (ψ : X ⟶ X')
  proof: functor_ext (fun _ => by simp) (by cat_disch)

中文:
引理 descOfTruncation_comp
  结论: {X' : Truncated.{u} 2} (ψ : X ⟶ X')
  证明: functor_ext (fun _ => by simp) (by cat_disch)

Depends on / 依赖: cat_disch, functor_ext
-/
lemma descOfTruncation_comp {X' : Truncated.{u} 2} (ψ : X ⟶ X')
    (φ : X' ⟶ (truncation 2).obj (nerve C)) :
    descOfTruncation (ψ ≫ φ) = mapHomotopyCategory ψ ⋙ descOfTruncation φ :=
  functor_ext (fun _ => by simp) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `homToNerveMk` / `homToNerveMk` 的定义

English:
definition homToNerveMk
  signature: (F : X.HomotopyCategory ⥤ C)
  body: liftOfStrictSegal (fun x => nerveEquiv.symm (F.obj (mk x)))
    (fun f => ComposableArrows.mk₁ (F.map (homMk (Truncated.Edge.mk' f))))
    (fun f => ComposableArrows.ext₀ rfl)
    (fun f => ComposableArrows.ext₀ rfl)
    (fun x y h₂ h₀ => by
      have h' {a b : X _⦋0⦌₂} (e : Edge a b) :
          C

中文:
定义 homToNerveMk
  签名: (F : X.HomotopyCategory ⥤ C)
  定义体: liftOfStrictSegal (fun x => nerveEquiv.symm (F.obj (mk x)))
    (fun f => ComposableArrows.mk₁ (F.map (homMk (Truncated.Edge.mk' f))))
    (fun f => ComposableArrows.ext₀ rfl)
    (fun f => ComposableArrows.ext₀ rfl)
    (fun x y h₂ h₀ => by
      have h' {a b : X _⦋0⦌₂} (e : Edge a b) :
          C

Depends on / 依赖: ComposableArrows, ComposableArrows.arrowEquiv.injective, ComposableArrows.ext, ComposableArrows.mk, Edge.mk, F.map, F.mapArrow.obj, F.obj, Truncated, Truncated.Edge.mk, arrowEquiv, congr_arg, congr_arrowMk_homMk, e.edge, injective, liftOfStrictSegal, mapArrow, nerveEquiv, nerveEquiv.symm
-/
def homToNerveMk (F : X.HomotopyCategory ⥤ C) : X ⟶ (truncation 2).obj (nerve C) :=
  liftOfStrictSegal (fun x => nerveEquiv.symm (F.obj (mk x)))
    (fun f => ComposableArrows.mk₁ (F.map (homMk (Truncated.Edge.mk' f))))
    (fun f => ComposableArrows.ext₀ rfl)
    (fun f => ComposableArrows.ext₀ rfl)
    (fun x y h₂ h₀ => by
      have h' {a b : X _⦋0⦌₂} (e : Edge a b) :
          ComposableArrows.mk₁ (F.map (homMk (Edge.mk' e.edge))) =
            ComposableArrows.mk₁ (F.map (homMk e)) :=
        ComposableArrows.arrowEquiv.injective
          (congr_arg F.mapArrow.obj (congr_arrowMk_homMk (Edge.mk' e.edge) e rfl))
      obtain ⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, h, rfl⟩ := Edge.CompStruct.exists_of_simplex x
      dsimp at h₀ h₂ ⊢
      have : ComposableArrows.mk₂ (F.map (homMk e₀₁)) (F.map (homMk e₁₂)) = y := by
        rw [h.d₂]; rw [h'] at h₂
        rw [h.d₀]; rw [h'] at h₀
        refine (spine_bijective (X := (truncation 2).obj (nerve C)) _ _).injective ?_
        ext i
        fin_cases i
        · dsimp
          simp only [SimplexCategory.mkOfSucc_zero_eq_δ, ← h₂]
          apply nerve.δ₂_mk₂_eq
        · dsimp
          simp only [SimplexCategory.mkOfSucc_one_eq_δ, ← h₀]
          apply nerve.δ₀_mk₂_eq
      rw [h.d₁]; rw [← this]
      have := (nerve.δ₁_mk₂_eq (F.map (homMk e₀₁)) (F.map (homMk e₁₂))).symm
      rwa [← Functor.map_comp, homMk_comp_homMk h, ← h'] at this)
    (fun x => ComposableArrows.arrowEquiv.injective
      ((congr_arg F.mapArrow.obj
        (congr_arrowMk_homMk (Edge.mk' (X.map (σ₂ 0).op x)) (Edge.id x) rfl)).trans (by aesop)))
    ((Nerve.strictSegal C).truncation 1)

@[simp]
/--
lemma `homToNerveMk_app_zero` / 引理 `homToNerveMk_app_zero`

English:
lemma homToNerveMk_app_zero
  given: (F : X.HomotopyCategory ⥤ C) (x : X _⦋0⦌₂)
  proof: rfl

中文:
引理 homToNerveMk_app_zero
  条件: (F : X.HomotopyCategory ⥤ C) (x : X _⦋0⦌₂)
  证明: rfl
-/
lemma homToNerveMk_app_zero (F : X.HomotopyCategory ⥤ C) (x : X _⦋0⦌₂) :
    (homToNerveMk F).app _ x = nerveEquiv.symm (F.obj (mk x)) := rfl

/--
lemma `homToNerveMk_app_one` / 引理 `homToNerveMk_app_one`

English:
lemma homToNerveMk_app_one
  given: (F : X.HomotopyCategory ⥤ C) (f : X _⦋1⦌₂)
  proof: rfl

@[simp]

中文:
引理 homToNerveMk_app_one
  条件: (F : X.HomotopyCategory ⥤ C) (f : X _⦋1⦌₂)
  证明: rfl

@[simp]
-/
lemma homToNerveMk_app_one (F : X.HomotopyCategory ⥤ C) (f : X _⦋1⦌₂) :
    (homToNerveMk F).app _ f =
      ComposableArrows.mk₁ (F.map (homMk (Truncated.Edge.mk' f))) :=
  rfl

@[simp]
/--
lemma `homToNerveMk_app_edge` / 引理 `homToNerveMk_app_edge`

English:
lemma homToNerveMk_app_edge
  given: (F : X.HomotopyCategory ⥤ C) {x y : X _⦋0⦌₂} (e : Edge x y)
  proof: by
  rw [homToNerveMk_app_one]
  exact ComposableArrows.arrowEquiv.injective
    (congr_arg F.mapArrow.obj (congr_arrowMk_homMk (Edge.mk' e.edge) e rfl))

中文:
引理 homToNerveMk_app_edge
  条件: (F : X.HomotopyCategory ⥤ C) {x y : X _⦋0⦌₂} (e : 边 x y)
  证明: by
  rw [homToNerveMk_app_one]
  exact ComposableArrows.arrowEquiv.injective
    (congr_arg F.mapArrow.obj (congr_arrowMk_homMk (Edge.mk' e.edge) e rfl))

Depends on / 依赖: ComposableArrows, ComposableArrows.arrowEquiv.injective, Edge.mk, F.mapArrow.obj, arrowEquiv, congr_arg, congr_arrowMk_homMk, e.edge, homToNerveMk_app_one, injective, mapArrow
-/
lemma homToNerveMk_app_edge (F : X.HomotopyCategory ⥤ C) {x y : X _⦋0⦌₂} (e : Edge x y) :
    (homToNerveMk F).app _ e.edge =
      ComposableArrows.mk₁ (F.map (homMk e)) := by
  rw [homToNerveMk_app_one]
  exact ComposableArrows.arrowEquiv.injective
    (congr_arg F.mapArrow.obj (congr_arrowMk_homMk (Edge.mk' e.edge) e rfl))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `functorEquiv` / `functorEquiv` 的定义

English:
definition functorEquiv
  signature: :
  body: homToNerveMk
  invFun := descOfTruncation
  left_inv F :=
    functor_ext (fun x => by simp) (fun x y f => by
      dsimp
      simp only [Category.comp_id, Category.id_comp, descOfTruncation_map_homMk,
        homToNerveMk_app_zero]
      exact nerve.homEquiv.symm.injective (Edge.ext (by cat_disch)

中文:
定义 functorEquiv
  签名: :
  定义体: homToNerveMk
  invFun := descOfTruncation
  left_inv F :=
    functor_ext (fun x => by simp) (fun x y f => by
      dsimp
      simp only [Category.comp_id, Category.id_comp, descOfTruncation_map_homMk,
        homToNerveMk_app_zero]
      exact nerve.homEquiv.symm.injective (Edge.ext (by cat_disch)

Depends on / 依赖: homToNerveMk
-/
def functorEquiv :
    (X.HomotopyCategory ⥤ C) ≃ (X ⟶ (truncation 2).obj (nerve C)) where
  toFun := homToNerveMk
  invFun := descOfTruncation
  left_inv F :=
    functor_ext (fun x => by simp) (fun x y f => by
      dsimp
      simp only [Category.comp_id, Category.id_comp, descOfTruncation_map_homMk,
        homToNerveMk_app_zero]
      exact nerve.homEquiv.symm.injective (Edge.ext (by cat_disch)))
  right_inv φ :=
    IsStrictSegal.hom_ext (fun s => by
      obtain ⟨x₀, x₁, f, rfl⟩ := Edge.exists_of_simplex s
      dsimp [nerve.homEquiv]
      simp only [homToNerveMk_app_edge, descOfTruncation_obj_mk,
        descOfTruncation_map_homMk]
      refine ComposableArrows.ext₁ ?_ ?_ rfl
      · dsimp [nerveEquiv, ComposableArrows.right]
        simp only [← f.src_eq, NatTrans.naturality_apply]
        rfl
      · dsimp [nerveEquiv, ComposableArrows.right]
        simp only [← f.tgt_eq, NatTrans.naturality_apply]
        rfl)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `homToNerveMk_comp` / 引理 `homToNerveMk_comp`

English:
lemma homToNerveMk_comp
  statement: {D : Type u} [SmallCategory D]
  proof: IsStrictSegal.hom_ext (fun s => by
    obtain ⟨x₀, x₁, f, rfl⟩ := Edge.exists_of_simplex s
    dsimp
    simp only [homToNerveMk_app_edge, Functor.comp_map]
    exact ComposableArrows.ext₁ rfl rfl (by aesop))

中文:
引理 homToNerveMk_comp
  结论: {D : 类型u} [小范畴 D]
  证明: IsStrictSegal.hom_ext (fun s => by
    obtain ⟨x₀, x₁, f, rfl⟩ := Edge.exists_of_simplex s
    dsimp
    simp only [homToNerveMk_app_edge, Functor.comp_map]
    exact ComposableArrows.ext₁ rfl rfl (by aesop))

Depends on / 依赖: ComposableArrows, ComposableArrows.ext, Edge.exists_of_simplex, Functor, Functor.comp_map, IsStrictSegal, IsStrictSegal.hom_ext, comp_map, exists_of_simplex, homToNerveMk_app_edge, hom_ext
-/
lemma homToNerveMk_comp {D : Type u} [SmallCategory D]
    (F : X.HomotopyCategory ⥤ C) (G : C ⥤ D) :
    homToNerveMk (F ⋙ G) = homToNerveMk F ≫ (truncation 2).map (nerveMap G) :=
  IsStrictSegal.hom_ext (fun s => by
    obtain ⟨x₀, x₁, f, rfl⟩ := Edge.exists_of_simplex s
    dsimp
    simp only [homToNerveMk_app_edge, Functor.comp_map]
    exact ComposableArrows.ext₁ rfl rfl (by aesop))

end HomotopyCategory

/--
Definition of `nerve₂Adj` / `nerve₂Adj` 的定义

English:
definition nerve₂Adj
  signature: : hoFunctor₂.{u} ⊣ nerveFunctor₂
  body: Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (Cat.Hom.equivFunctor _ _).trans HomotopyCategory.functorEquiv
      homEquiv_naturality_left_symm _ _ := by ext1; exact HomotopyCategory.descOfTruncation_comp _ _
      homEquiv_naturality_right _ _ := HomotopyCategory.homToNerveMk_comp _ _ }

中文:
定义 nerve₂Adj
  签名: : hoFunctor₂.{u} ⊣ nerveFunctor₂
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (Cat.Hom.equivFunctor _ _).trans HomotopyCategory.functorEquiv
      homEquiv_naturality_left_symm _ _ := by ext1; exact HomotopyCategory.descOfTruncation_comp _ _
      homEquiv_naturality_right _ _ := HomotopyCategory.homToNerveMk_comp _ _ }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Cat.Hom.equivFunctor, HomotopyCategory, HomotopyCategory.descOfTruncation_comp, HomotopyCategory.functorEquiv, HomotopyCategory.homToNerveMk_comp, descOfTruncation_comp, equivFunctor, functorEquiv, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, homToNerveMk_comp, mkOfHomEquiv
-/
def nerve₂Adj : hoFunctor₂.{u} ⊣ nerveFunctor₂ :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (Cat.Hom.equivFunctor _ _).trans HomotopyCategory.functorEquiv
      homEquiv_naturality_left_symm _ _ := by ext1; exact HomotopyCategory.descOfTruncation_comp _ _
      homEquiv_naturality_right _ _ := HomotopyCategory.homToNerveMk_comp _ _ }

end Truncated

end SSet

namespace CategoryTheory

namespace nerve

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `C ⥤ D` that is reconstructed for a morphism
between the `2`-truncated nerves. -/
@[simps]
/--
Definition of `functorOfNerveMap` / `functorOfNerveMap` 的定义

English:
definition functorOfNerveMap
  signature: (φ : nerveFunctor₂.obj (.of C) ⟶ nerveFunctor₂.obj (.of D))
  body: nerveEquiv (φ.app (op ⟨⦋0⦌, by simp⟩) (nerveEquiv.symm x))
  map f := nerve.homEquiv ((nerve.edgeMk f).toTruncated.map φ)
  map_id x := by
    rw [edgeMk_id]; rw [SSet.Edge.toTruncated_id]; rw [SSet.Truncated.Edge.map_id]
    exact nerve.homEquiv_id _
  map_comp f g := by
    obtain ⟨h⟩ := (nerve.no

中文:
定义 functorOfNerveMap
  签名: (φ : nerveFunctor₂.obj (.of C) ⟶ nerveFunctor₂.obj (.of D))
  定义体: nerveEquiv (φ.app (op ⟨⦋0⦌, by simp⟩) (nerveEquiv.symm x))
  map f := nerve.homEquiv ((nerve.edgeMk f).toTruncated.map φ)
  map_id x := by
    rw [edgeMk_id]; rw [SSet.Edge.toTruncated_id]; rw [SSet.Truncated.Edge.map_id]
    exact nerve.homEquiv_id _
  map_comp f g := by
    obtain ⟨h⟩ := (nerve.no

Depends on / 依赖: nerveEquiv, nerveEquiv.symm
-/
def functorOfNerveMap (φ : nerveFunctor₂.obj (.of C) ⟶ nerveFunctor₂.obj (.of D)) :
    C ⥤ D where
  obj x := nerveEquiv (φ.app (op ⟨⦋0⦌, by simp⟩) (nerveEquiv.symm x))
  map f := nerve.homEquiv ((nerve.edgeMk f).toTruncated.map φ)
  map_id x := by
    rw [edgeMk_id]; rw [SSet.Edge.toTruncated_id]; rw [SSet.Truncated.Edge.map_id]
    exact nerve.homEquiv_id _
  map_comp f g := by
    obtain ⟨h⟩ := (nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl
    exact (nerve.homEquiv_comp (h.toTruncated.map φ)).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `nerveFunctor₂_map_functorOfNerveMap` / 引理 `nerveFunctor₂_map_functorOfNerveMap`

English:
lemma nerveFunctor₂_map_functorOfNerveMap
  proof: SSet.Truncated.IsStrictSegal.hom_ext (fun f => by
    obtain ⟨x, y, f, rfl⟩ := ComposableArrows.mk₁_surjective f
    exact (nerveMap_app_mk₁ _ _).trans ((nerve.mk₁_homEquiv_apply _).trans
      (ComposableArrows.mk₁_hom _)))

中文:
引理 nerveFunctor₂_map_functorOfNerveMap
  证明: SSet.Truncated.IsStrictSegal.hom_ext (fun f => by
    obtain ⟨x, y, f, rfl⟩ := ComposableArrows.mk₁_surjective f
    exact (nerveMap_app_mk₁ _ _).trans ((nerve.mk₁_homEquiv_apply _).trans
      (ComposableArrows.mk₁_hom _)))

Depends on / 依赖: ComposableArrows, ComposableArrows.mk, IsStrictSegal, SSet.Truncated.IsStrictSegal.hom_ext, Truncated, hom_ext, nerve.mk
-/
lemma nerveFunctor₂_map_functorOfNerveMap
    (φ : nerveFunctor₂.obj (.of C) ⟶ nerveFunctor₂.obj (.of D)) :
    nerveFunctor₂.map (functorOfNerveMap φ).toCatHom = φ :=
  SSet.Truncated.IsStrictSegal.hom_ext (fun f => by
    obtain ⟨x, y, f, rfl⟩ := ComposableArrows.mk₁_surjective f
    exact (nerveMap_app_mk₁ _ _).trans ((nerve.mk₁_homEquiv_apply _).trans
      (ComposableArrows.mk₁_hom _)))

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `functorOfNerveMap_nerveFunctor₂_map` / 引理 `functorOfNerveMap_nerveFunctor₂_map`

English:
lemma functorOfNerveMap_nerveFunctor₂_map
  given: (F : C ⥤ D)
  proof: Functor.ext (fun x => by cat_disch) (fun x y f => by cat_disch)

中文:
引理 functorOfNerveMap_nerveFunctor₂_map
  条件: (F : C ⥤ D)
  证明: Functor.ext (fun x => by cat_disch) (fun x y f => by cat_disch)

Depends on / 依赖: Functor, Functor.ext, cat_disch
-/
lemma functorOfNerveMap_nerveFunctor₂_map (F : C ⥤ D) :
    functorOfNerveMap ((SSet.truncation 2).map (nerveMap F)) = F :=
  Functor.ext (fun x => by cat_disch) (fun x y f => by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `fullyFaithfulNerveFunctor₂` / `fullyFaithfulNerveFunctor₂` 的定义

English:
definition fullyFaithfulNerveFunctor₂
  signature: : nerveFunctor₂.{u, u}.FullyFaithful where
  body: (functorOfNerveMap φ).toCatHom
  map_preimage _ := nerveFunctor₂_map_functorOfNerveMap _
  preimage_map _ := by ext1; exact functorOfNerveMap_nerveFunctor₂_map _

中文:
定义 fullyFaithfulNerveFunctor₂
  签名: : nerveFunctor₂.{u, u}.满忠实 where
  定义体: (functorOfNerveMap φ).toCatHom
  map_preimage _ := nerveFunctor₂_map_functorOfNerveMap _
  preimage_map _ := by ext1; exact functorOfNerveMap_nerveFunctor₂_map _

Depends on / 依赖: functorOfNerveMap, toCatHom
-/
def fullyFaithfulNerveFunctor₂ : nerveFunctor₂.{u, u}.FullyFaithful where
  preimage φ := (functorOfNerveMap φ).toCatHom
  map_preimage _ := nerveFunctor₂_map_functorOfNerveMap _
  preimage_map _ := by ext1; exact functorOfNerveMap_nerveFunctor₂_map _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: nerveFunctor₂.{u, u}.Faithful
  body: (fullyFaithfulNerveFunctor₂).faithful

中文:
实例 :
  签名: nerveFunctor₂.{u, u}.忠实
  定义体: (fullyFaithfulNerveFunctor₂).faithful

Depends on / 依赖: faithful
-/
instance : nerveFunctor₂.{u, u}.Faithful :=
  (fullyFaithfulNerveFunctor₂).faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: nerveFunctor₂.{u, u}.Full
  body: (fullyFaithfulNerveFunctor₂).full

中文:
实例 :
  签名: nerveFunctor₂.{u, u}.满
  定义体: (fullyFaithfulNerveFunctor₂).full
-/
instance : nerveFunctor₂.{u, u}.Full :=
  (fullyFaithfulNerveFunctor₂).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Reflective nerveFunctor₂.{u, u}
  body: Reflective.mk _ SSet.Truncated.nerve₂Adj

中文:
实例 :
  签名: 反射 nerveFunctor₂.{u, u}
  定义体: Reflective.mk _ SSet.Truncated.nerve₂Adj

Depends on / 依赖: Reflective, Reflective.mk, SSet.Truncated.nerve, Truncated
-/
instance : Reflective nerveFunctor₂.{u, u} := Reflective.mk _ SSet.Truncated.nerve₂Adj

end nerve

open SSet

/--
Definition of `nerveAdjunction` / `nerveAdjunction` 的定义

English:
definition nerveAdjunction
  signature: : hoFunctor ⊣ nerveFunctor
  body: Adjunction.ofNatIsoRight ((SSet.coskAdj 2).comp Truncated.nerve₂Adj) Nerve.cosk₂Iso.symm

中文:
定义 nerveAdjunction
  签名: : hoFunctor ⊣ nerveFunctor
  定义体: Adjunction.ofNatIsoRight ((SSet.coskAdj 2).comp Truncated.nerve₂Adj) Nerve.cosk₂Iso.symm

Depends on / 依赖: Adjunction, Adjunction.ofNatIsoRight, Iso.symm, Nerve.cosk, SSet.coskAdj, Truncated, Truncated.nerve, coskAdj, ofNatIsoRight
-/
noncomputable def nerveAdjunction : hoFunctor ⊣ nerveFunctor :=
  Adjunction.ofNatIsoRight ((SSet.coskAdj 2).comp Truncated.nerve₂Adj) Nerve.cosk₂Iso.symm


/--
Instance `nerveFunctor.faithful` / 实例 `nerveFunctor.faithful`

English:
instance nerveFunctor.faithful
  signature: : nerveFunctor.{u, u}.Faithful
  body: Functor.Faithful.of_iso Nerve.cosk₂Iso.symm

中文:
实例 nerveFunctor.faithful
  签名: : nerveFunctor.{u, u}.忠实
  定义体: Functor.Faithful.of_iso Nerve.cosk₂Iso.symm

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_iso, Iso.symm, Nerve.cosk, of_iso
-/
instance nerveFunctor.faithful : nerveFunctor.{u, u}.Faithful :=
  Functor.Faithful.of_iso Nerve.cosk₂Iso.symm

/--
Instance `nerveFunctor.full` / 实例 `nerveFunctor.full`

English:
instance nerveFunctor.full
  signature: : nerveFunctor.{u, u}.Full
  body: Functor.Full.of_iso Nerve.cosk₂Iso.symm

中文:
实例 nerveFunctor.full
  签名: : nerveFunctor.{u, u}.满
  定义体: Functor.Full.of_iso Nerve.cosk₂Iso.symm

Depends on / 依赖: Functor, Functor.Full.of_iso, Iso.symm, Nerve.cosk, of_iso
-/
instance nerveFunctor.full : nerveFunctor.{u, u}.Full :=
  Functor.Full.of_iso Nerve.cosk₂Iso.symm

/--
Definition of `nerveFunctor.fullyfaithful` / `nerveFunctor.fullyfaithful` 的定义

English:
definition nerveFunctor.fullyfaithful
  signature: : nerveFunctor.FullyFaithful
  body: Functor.FullyFaithful.ofFullyFaithful _

中文:
定义 nerveFunctor.fullyfaithful
  签名: : nerveFunctor.满忠实
  定义体: Functor.FullyFaithful.ofFullyFaithful _

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.ofFullyFaithful, ofFullyFaithful
-/
noncomputable def nerveFunctor.fullyfaithful : nerveFunctor.FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/--
Instance `nerveAdjunction.isIso_counit` / 实例 `nerveAdjunction.isIso_counit`

English:
instance nerveAdjunction.isIso_counit
  signature: : IsIso nerveAdjunction.counit
  body: Adjunction.counit_isIso_of_R_fully_faithful _

中文:
实例 nerveAdjunction.isIso_counit
  签名: : 是同构 nerveAdjunction.counit
  定义体: Adjunction.counit_isIso_of_R_fully_faithful _

Depends on / 依赖: Adjunction, Adjunction.counit_isIso_of_R_fully_faithful, counit_isIso_of_R_fully_faithful
-/
instance nerveAdjunction.isIso_counit : IsIso nerveAdjunction.counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

/--
Definition of `nerveFunctorCompHoFunctorIso` / `nerveFunctorCompHoFunctorIso` 的定义

English:
definition nerveFunctorCompHoFunctorIso
  signature: : nerveFunctor.{u, u} ⋙ hoFunctor ≅ 𝟭 Cat
  body: asIso (nerveAdjunction.counit)

中文:
定义 nerveFunctorCompHoFunctorIso
  签名: : nerveFunctor.{u, u} ⋙ hoFunctor ≅ 𝟭 Cat
  定义体: asIso (nerveAdjunction.counit)

Depends on / 依赖: counit, nerveAdjunction, nerveAdjunction.counit
-/
noncomputable def nerveFunctorCompHoFunctorIso : nerveFunctor.{u, u} ⋙ hoFunctor ≅ 𝟭 Cat :=
  asIso (nerveAdjunction.counit)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Reflective nerveFunctor
  body: hoFunctor
  adj := nerveAdjunction

中文:
实例 :
  签名: 反射 nerveFunctor
  定义体: hoFunctor
  adj := nerveAdjunction

Depends on / 依赖: hoFunctor
-/
noncomputable instance : Reflective nerveFunctor where
  L := hoFunctor
  adj := nerveAdjunction

section

instance (C D : Type u) [Category.{u} C] [Category.{u} D] :
    IsIso (prodComparison (nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor)
      (Cat.of C) (Cat.of D)) := by
  let iso : nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor ≅ nerveFunctor :=
    (nerveFunctor.associator hoFunctor nerveFunctor).symm ≪≫
      Functor.isoWhiskerRight nerveFunctorCompHoFunctorIso nerveFunctor ≪≫
        nerveFunctor.leftUnitor
  exact IsIso.of_isIso_fac_right (prodComparison_natural_of_natTrans iso.hom).symm

namespace hoFunctor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: hoFunctor.IsLeftAdjoint
  body: nerveAdjunction.isLeftAdjoint

中文:
实例 :
  签名: hoFunctor.是左伴随
  定义体: nerveAdjunction.isLeftAdjoint

Depends on / 依赖: isLeftAdjoint, nerveAdjunction, nerveAdjunction.isLeftAdjoint
-/
instance : hoFunctor.IsLeftAdjoint := nerveAdjunction.isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
instance (C D : Type u) [Category.{u} C] [Category.{u} D] :
    IsIso (prodComparison hoFunctor (nerve C) (nerve D)) := by
  have : IsIso (nerveFunctor.map (prodComparison hoFunctor (nerve C) (nerve D))) := by
    have : IsIso (prodComparison (hoFunctor ⋙ nerveFunctor) (nerve C) (nerve D)) :=
      IsIso.of_isIso_fac_left
        (prodComparison_comp nerveFunctor (hoFunctor ⋙ nerveFunctor)
          (A := Cat.of C) (B := Cat.of D)).symm
    exact IsIso.of_isIso_fac_right (prodComparison_comp hoFunctor nerveFunctor).symm
  exact isIso_of_fully_faithful nerveFunctor _

/--
Instance `isIso_prodComparison_stdSimplex.` / 实例 `isIso_prodComparison_stdSimplex.`

English:
instance isIso_prodComparison_stdSimplex.{w}
  signature: (n m : Nat)
  body: IsIso.of_isIso_fac_right (prodComparison_natural.{w}
    hoFunctor (stdSimplex.isoNerve n).hom (stdSimplex.isoNerve m).hom).symm

中文:
实例 isIso_prodComparison_stdSimplex.{w}
  签名: (n m : 自然数)
  定义体: IsIso.of_isIso_fac_right (prodComparison_natural.{w}
    hoFunctor (stdSimplex.isoNerve n).hom (stdSimplex.isoNerve m).hom).symm

Depends on / 依赖: IsIso.of_isIso_fac_right, hoFunctor, isoNerve, of_isIso_fac_right, prodComparison_natural, stdSimplex, stdSimplex.isoNerve
-/
instance isIso_prodComparison_stdSimplex.{w} (n m : Nat) :
    IsIso (prodComparison hoFunctor (Δ[n] : SSet.{w}) Δ[m]) :=
  IsIso.of_isIso_fac_right (prodComparison_natural.{w}
    hoFunctor (stdSimplex.isoNerve n).hom (stdSimplex.isoNerve m).hom).symm

/--
lemma `isIso_prodComparison_of_stdSimplex` / 引理 `isIso_prodComparison_of_stdSimplex`

English:
lemma isIso_prodComparison_of_stdSimplex
  statement: {D : SSet.{u}} (X : SSet.{u})
  proof: by
  have : IsIso (Functor.whiskerLeft (CostructuredArrow.proj uliftYoneda X ⋙ uliftYoneda)
      (prodComparisonNatTrans hoFunctor.{u} D)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun x => H (x.left).len
  exact isIso_app_coconePt_of_preservesColimit _ (prodComparisonNatTrans hoFunctor

中文:
引理 isIso_prodComparison_of_stdSimplex
  结论: {D : SSet.{u}} (X : SSet.{u})
  证明: by
  have : IsIso (Functor.whiskerLeft (CostructuredArrow.proj uliftYoneda X ⋙ uliftYoneda)
      (prodComparisonNatTrans hoFunctor.{u} D)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun x => H (x.left).len
  exact isIso_app_coconePt_of_preservesColimit _ (prodComparisonNatTrans hoFunctor

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, Functor, Functor.whiskerLeft, NatTrans, NatTrans.isIso_iff_isIso_app, Presheaf, Presheaf.isColimitTautologicalCocone, hoFunctor, isColimitTautologicalCocone, isIso_app_coconePt_of_preservesColimit, isIso_iff_isIso_app, prodComparisonNatTrans, uliftYoneda, whiskerLeft, x.left
-/
lemma isIso_prodComparison_of_stdSimplex {D : SSet.{u}} (X : SSet.{u})
    (H : forall m, IsIso (prodComparison hoFunctor D Δ[m])) :
    IsIso (prodComparison hoFunctor D X) := by
  have : IsIso (Functor.whiskerLeft (CostructuredArrow.proj uliftYoneda X ⋙ uliftYoneda)
      (prodComparisonNatTrans hoFunctor.{u} D)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun x => H (x.left).len
  exact isIso_app_coconePt_of_preservesColimit _ (prodComparisonNatTrans hoFunctor _) _
    (Presheaf.isColimitTautologicalCocone' X)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isIso_prodComparison` / 实例 `isIso_prodComparison`

English:
instance isIso_prodComparison
  signature: (X Y : SSet)
  body: isIso_prodComparison_of_stdSimplex _ fun m => by
  convert_to IsIso (hoFunctor.map (prod.braiding _ _).hom ≫
    prodComparison hoFunctor Δ[m] X ≫ (prod.braiding _ _).hom)
  · ext <;> simp [← Functor.map_comp]
  suffices IsIso (prodComparison hoFunctor Δ[m] X) by infer_instance
  exact isIso_prodCom

中文:
实例 isIso_prodComparison
  签名: (X Y : SSet)
  定义体: isIso_prodComparison_of_stdSimplex _ fun m => by
  convert_to IsIso (hoFunctor.map (prod.braiding _ _).hom ≫
    prodComparison hoFunctor Δ[m] X ≫ (prod.braiding _ _).hom)
  · ext <;> simp [← Functor.map_comp]
  suffices IsIso (prodComparison hoFunctor Δ[m] X) by infer_instance
  exact isIso_prodCom

Depends on / 依赖: Functor, Functor.map_comp, braiding, convert_to, hoFunctor, hoFunctor.map, infer_instance, isIso_prodComparison_of_stdSimplex, isIso_prodComparison_stdSimplex, map_comp, prod.braiding, prodComparison
-/
instance isIso_prodComparison (X Y : SSet) :
    IsIso (prodComparison hoFunctor.{u} X Y) := isIso_prodComparison_of_stdSimplex _ fun m => by
  convert_to IsIso (hoFunctor.map (prod.braiding _ _).hom ≫
    prodComparison hoFunctor Δ[m] X ≫ (prod.braiding _ _).hom)
  · ext <;> simp [← Functor.map_comp]
  suffices IsIso (prodComparison hoFunctor Δ[m] X) by infer_instance
  exact isIso_prodComparison_of_stdSimplex _ (isIso_prodComparison_stdSimplex _)

/--
Instance `preservesBinaryProduct` / 实例 `preservesBinaryProduct`

English:
instance preservesBinaryProduct
  signature: (X Y : SSet)
  body: PreservesLimitPair.of_iso_prod_comparison hoFunctor X Y

中文:
实例 preservesBinaryProduct
  签名: (X Y : SSet)
  定义体: PreservesLimitPair.of_iso_prod_comparison hoFunctor X Y

Depends on / 依赖: PreservesLimitPair, PreservesLimitPair.of_iso_prod_comparison, hoFunctor, of_iso_prod_comparison
-/
instance preservesBinaryProduct (X Y : SSet) :
    PreservesLimit (pair X Y) hoFunctor :=
  PreservesLimitPair.of_iso_prod_comparison hoFunctor X Y

/--
Instance `preservesBinaryProducts` / 实例 `preservesBinaryProducts`

English:
instance preservesBinaryProducts
  signature: :
  body: preservesLimit_of_iso_diagram hoFunctor (diagramIsoPair F).symm

中文:
实例 preservesBinaryProducts
  签名: :
  定义体: preservesLimit_of_iso_diagram hoFunctor (diagramIsoPair F).symm

Depends on / 依赖: diagramIsoPair, hoFunctor, preservesLimit_of_iso_diagram
-/
instance preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) hoFunctor where
  preservesLimit {F} := preservesLimit_of_iso_diagram hoFunctor (diagramIsoPair F).symm

/--
Instance `preservesFiniteProducts` / 实例 `preservesFiniteProducts`

English:
instance preservesFiniteProducts
  signature: : PreservesFiniteProducts hoFunctor
  body: PreservesFiniteProducts.of_preserves_binary_and_terminal _

中文:
实例 preservesFiniteProducts
  签名: : 保持FiniteProducts hoFunctor
  定义体: PreservesFiniteProducts.of_preserves_binary_and_terminal _

Depends on / 依赖: PreservesFiniteProducts, PreservesFiniteProducts.of_preserves_binary_and_terminal, of_preserves_binary_and_terminal
-/
instance preservesFiniteProducts : PreservesFiniteProducts hoFunctor :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

end hoFunctor

end

end CategoryTheory
