/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.UnitInterval
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The cartesian monoidal structure on `TopCat`

We define the cartesian monoidal category structure on `TopCat`.
We also introduce the unit interval as an object `TopCat.I` of `TopCat`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace TopCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CartesianMonoidalCategory TopCat.{u}
  body: .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun X Y => ⟨prodBinaryFan X Y, X.prodBinaryFanIsLimit Y⟩)

中文:
实例 :
  签名: CartesianMonoidal范畴 顶元素范畴.{u}
  定义体: .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun X Y => ⟨prodBinaryFan X Y, X.prodBinaryFanIsLimit Y⟩)

Depends on / 依赖: X.prodBinaryFanIsLimit, isTerminalPUnit, ofChosenFiniteProducts, prodBinaryFan, prodBinaryFanIsLimit
-/
instance : CartesianMonoidalCategory TopCat.{u} :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun X Y => ⟨prodBinaryFan X Y, X.prodBinaryFanIsLimit Y⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory TopCat.{u}
  body: .ofCartesianMonoidalCategory

@[simp]

中文:
实例 :
  签名: 辫范畴 顶元素范畴.{u}
  定义体: .ofCartesianMonoidalCategory

@[simp]

Depends on / 依赖: ofCartesianMonoidalCategory
-/
instance : BraidedCategory TopCat.{u} := .ofCartesianMonoidalCategory

@[simp]
/--
theorem `tensor_apply` / 定理 `tensor_apply`

English:
theorem tensor_apply
  given: {W X Y Z : TopCat.{u}} (f : W ⟶ X) (g : Y ⟶ Z) (p : ↑(W otimes Y))
  proof: rfl

@[simp]

中文:
定理 tensor_apply
  条件: {W X Y Z : 顶元素范畴.{u}} (f : W ⟶ X) (g : Y ⟶ Z) (p : ↑(W otimes Y))
  证明: rfl

@[simp]
-/
theorem tensor_apply {W X Y Z : TopCat.{u}} (f : W ⟶ X) (g : Y ⟶ Z) (p : ↑(W otimes Y)) :
    (f otimesₘ g).hom p = (f p.1, g p.2) :=
  rfl

@[simp]
/--
theorem `whiskerLeft_apply` / 定理 `whiskerLeft_apply`

English:
theorem whiskerLeft_apply
  given: (X : TopCat.{u}) {Y Z : TopCat.{u}} (f : Y ⟶ Z) (p : ↑(X otimes Y))
  proof: rfl

@[simp]

中文:
定理 whiskerLeft_apply
  条件: (X : 顶元素范畴.{u}) {Y Z : 顶元素范畴.{u}} (f : Y ⟶ Z) (p : ↑(X otimes Y))
  证明: rfl

@[simp]
-/
theorem whiskerLeft_apply (X : TopCat.{u}) {Y Z : TopCat.{u}} (f : Y ⟶ Z) (p : ↑(X otimes Y)) :
    (X ◁ f) p = (p.1, f p.2) :=
  rfl

@[simp]
/--
theorem `whiskerRight_apply` / 定理 `whiskerRight_apply`

English:
theorem whiskerRight_apply
  given: {Y Z : TopCat.{u}} (f : Y ⟶ Z) (X : TopCat.{u}) (p : ↑(Y otimes X))
  proof: rfl

@[simp]

中文:
定理 whiskerRight_apply
  条件: {Y Z : 顶元素范畴.{u}} (f : Y ⟶ Z) (X : 顶元素范畴.{u}) (p : ↑(Y otimes X))
  证明: rfl

@[simp]
-/
theorem whiskerRight_apply {Y Z : TopCat.{u}} (f : Y ⟶ Z) (X : TopCat.{u}) (p : ↑(Y otimes X)) :
    (f ▷ X) p = (f p.1, p.2) :=
  rfl

@[simp]
/--
theorem `leftUnitor_hom_apply` / 定理 `leftUnitor_hom_apply`

English:
theorem leftUnitor_hom_apply
  given: {X : TopCat.{u}} {x : X} {p : PUnit.{u + 1}}
  proof: rfl

@[simp]

中文:
定理 leftUnitor_hom_apply
  条件: {X : 顶元素范畴.{u}} {x : X} {p : 命题单元.{u + 1}}
  证明: rfl

@[simp]
-/
theorem leftUnitor_hom_apply {X : TopCat.{u}} {x : X} {p : PUnit.{u + 1}} :
    (fun_ X).hom (p, x) = x :=
  rfl

@[simp]
/--
theorem `leftUnitor_inv_apply` / 定理 `leftUnitor_inv_apply`

English:
theorem leftUnitor_inv_apply
  given: {X : TopCat.{u}} {x : X}
  proof: rfl

@[simp]

中文:
定理 leftUnitor_inv_apply
  条件: {X : 顶元素范畴.{u}} {x : X}
  证明: rfl

@[simp]
-/
theorem leftUnitor_inv_apply {X : TopCat.{u}} {x : X} :
    (fun_ X).inv x = (PUnit.unit, x) :=
  rfl

@[simp]
/--
theorem `rightUnitor_hom_apply` / 定理 `rightUnitor_hom_apply`

English:
theorem rightUnitor_hom_apply
  given: {X : TopCat.{u}} {x : X} {p : PUnit.{u + 1}}
  proof: rfl

@[simp]

中文:
定理 rightUnitor_hom_apply
  条件: {X : 顶元素范畴.{u}} {x : X} {p : 命题单元.{u + 1}}
  证明: rfl

@[simp]
-/
theorem rightUnitor_hom_apply {X : TopCat.{u}} {x : X} {p : PUnit.{u + 1}} :
    (ρ_ X).hom (x, p) = x :=
  rfl

@[simp]
/--
theorem `rightUnitor_inv_apply` / 定理 `rightUnitor_inv_apply`

English:
theorem rightUnitor_inv_apply
  given: {X : TopCat.{u}} {x : X}
  proof: rfl

@[simp]

中文:
定理 rightUnitor_inv_apply
  条件: {X : 顶元素范畴.{u}} {x : X}
  证明: rfl

@[simp]
-/
theorem rightUnitor_inv_apply {X : TopCat.{u}} {x : X} :
    (ρ_ X).inv x = (x, .unit) :=
  rfl

@[simp]
/--
theorem `associator_hom_apply` / 定理 `associator_hom_apply`

English:
theorem associator_hom_apply
  given: {X Y Z : TopCat.{u}} {x : X} {y : Y} {z : Z}
  proof: rfl

@[simp]

中文:
定理 associator_hom_apply
  条件: {X Y Z : 顶元素范畴.{u}} {x : X} {y : Y} {z : Z}
  证明: rfl

@[simp]
-/
theorem associator_hom_apply {X Y Z : TopCat.{u}} {x : X} {y : Y} {z : Z} :
    (α_ X Y Z).hom ((x, y), z) = (x, (y, z)) :=
  rfl

@[simp]
/--
theorem `associator_inv_apply` / 定理 `associator_inv_apply`

English:
theorem associator_inv_apply
  given: {X Y Z : TopCat.{u}} {x : X} {y : Y} {z : Z}
  proof: rfl

中文:
定理 associator_inv_apply
  条件: {X Y Z : 顶元素范畴.{u}} {x : X} {y : Y} {z : Z}
  证明: rfl
-/
theorem associator_inv_apply {X Y Z : TopCat.{u}} {x : X} {y : Y} {z : Z} :
    (α_ X Y Z).inv (x, (y, z)) = ((x, y), z) :=
  rfl

/--
theorem `associator_hom_apply_1` / 定理 `associator_hom_apply_1`

English:
theorem associator_hom_apply_1
  given: {X Y Z : TopCat.{u}} {x}
  proof: rfl

中文:
定理 associator_hom_apply_1
  条件: {X Y Z : 顶元素范畴.{u}} {x}
  证明: rfl
-/
@[simp] theorem associator_hom_apply_1 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).hom x).1 = x.1.1 :=
  rfl

/--
theorem `associator_hom_apply_2_1` / 定理 `associator_hom_apply_2_1`

English:
theorem associator_hom_apply_2_1
  given: {X Y Z : TopCat.{u}} {x}
  proof: rfl

中文:
定理 associator_hom_apply_2_1
  条件: {X Y Z : 顶元素范畴.{u}} {x}
  证明: rfl
-/
@[simp] theorem associator_hom_apply_2_1 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).hom x).2.1 = x.1.2 :=
  rfl

/--
theorem `associator_hom_apply_2_2` / 定理 `associator_hom_apply_2_2`

English:
theorem associator_hom_apply_2_2
  given: {X Y Z : TopCat.{u}} {x}
  proof: rfl

中文:
定理 associator_hom_apply_2_2
  条件: {X Y Z : 顶元素范畴.{u}} {x}
  证明: rfl
-/
@[simp] theorem associator_hom_apply_2_2 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).hom x).2.2 = x.2 :=
  rfl

/--
theorem `associator_inv_apply_1_1` / 定理 `associator_inv_apply_1_1`

English:
theorem associator_inv_apply_1_1
  given: {X Y Z : TopCat.{u}} {x}
  proof: rfl

中文:
定理 associator_inv_apply_1_1
  条件: {X Y Z : 顶元素范畴.{u}} {x}
  证明: rfl
-/
@[simp] theorem associator_inv_apply_1_1 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).inv x).1.1 = x.1 :=
  rfl

/--
theorem `associator_inv_apply_1_2` / 定理 `associator_inv_apply_1_2`

English:
theorem associator_inv_apply_1_2
  given: {X Y Z : TopCat.{u}} {x}
  proof: rfl

中文:
定理 associator_inv_apply_1_2
  条件: {X Y Z : 顶元素范畴.{u}} {x}
  证明: rfl
-/
@[simp] theorem associator_inv_apply_1_2 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).inv x).1.2 = x.2.1 :=
  rfl

/--
theorem `associator_inv_apply_2` / 定理 `associator_inv_apply_2`

English:
theorem associator_inv_apply_2
  given: {X Y Z : TopCat.{u}} {x}
  proof: rfl

@[simp]

中文:
定理 associator_inv_apply_2
  条件: {X Y Z : 顶元素范畴.{u}} {x}
  证明: rfl

@[simp]
-/
@[simp] theorem associator_inv_apply_2 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).inv x).2 = x.2.2 :=
  rfl

@[simp]
/--
theorem `braiding_hom_apply` / 定理 `braiding_hom_apply`

English:
theorem braiding_hom_apply
  given: {X Y : TopCat.{u}} {x : X} {y : Y}
  proof: rfl

@[simp]

中文:
定理 braiding_hom_apply
  条件: {X Y : 顶元素范畴.{u}} {x : X} {y : Y}
  证明: rfl

@[simp]
-/
theorem braiding_hom_apply {X Y : TopCat.{u}} {x : X} {y : Y} :
    (β_ X Y).hom (x, y) = (y, x) :=
  rfl

@[simp]
/--
theorem `braiding_inv_apply` / 定理 `braiding_inv_apply`

English:
theorem braiding_inv_apply
  given: {X Y : TopCat.{u}} {x : X} {y : Y}
  proof: rfl

@[simp]

中文:
定理 braiding_inv_apply
  条件: {X Y : 顶元素范畴.{u}} {x : X} {y : Y}
  证明: rfl

@[simp]
-/
theorem braiding_inv_apply {X Y : TopCat.{u}} {x : X} {y : Y} :
    (β_ X Y).inv (y, x) = (x, y) :=
  rfl

@[simp]
/--
theorem `lift_apply` / 定理 `lift_apply`

English:
theorem lift_apply
  given: {X Y Z : TopCat.{u}} {f : X ⟶ Y} {g : X ⟶ Z} {x : X}
  proof: rfl

中文:
定理 lift_apply
  条件: {X Y Z : 顶元素范畴.{u}} {f : X ⟶ Y} {g : X ⟶ Z} {x : X}
  证明: rfl
-/
protected theorem lift_apply {X Y Z : TopCat.{u}} {f : X ⟶ Y} {g : X ⟶ Z} {x : X} :
    CartesianMonoidalCategory.lift f g x = (f x, g x) :=
  rfl

/--
Definition of `I` / `I` 的定义

English:
definition I
  signature: : TopCat.{u}
  body: TopCat.of (ULift unitInterval)

中文:
定义 I
  签名: : 顶元素范畴.{u}
  定义体: TopCat.of (ULift unitInterval)

Depends on / 依赖: TopCat, TopCat.of, unitInterval
-/
def I : TopCat.{u} := TopCat.of (ULift unitInterval)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyCompactSpace I
  body: inferInstanceAs (LocallyCompactSpace (ULift unitInterval))

中文:
实例 :
  签名: 局部紧空间 I
  定义体: inferInstanceAs (LocallyCompactSpace (ULift unitInterval))

Depends on / 依赖: LocallyCompactSpace, unitInterval
-/
instance : LocallyCompactSpace I :=
  inferInstanceAs (LocallyCompactSpace (ULift unitInterval))

namespace I

/--
Definition of `homeomorph` / `homeomorph` 的定义

English:
definition homeomorph
  signature: : I ≃ₜ unitInterval
  body: Homeomorph.ulift

@[ext]

中文:
定义 homeomorph
  签名: : I ≃ₜ unit整数erval
  定义体: Homeomorph.ulift

@[ext]

Depends on / 依赖: Homeomorph, Homeomorph.ulift
-/
def homeomorph : I ≃ₜ unitInterval := Homeomorph.ulift

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {x y : I.{u}} (h : homeomorph x = homeomorph y)
  statement: x = y
  proof: homeomorph.injective h

中文:
引理 ext
  条件: {x y : I.{u}} (h : homeomorph x = homeomorph y)
  结论: x = y
  证明: homeomorph.injective h

Depends on / 依赖: homeomorph, homeomorph.injective, injective
-/
lemma ext {x y : I.{u}} (h : homeomorph x = homeomorph y) : x = y :=
  homeomorph.injective h

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : I.{u} ⟶ I
  body: ofHom ⟨homeomorph.symm ∘ unitInterval.symm ∘ homeomorph, by fun_prop⟩

@[simp]

中文:
定义 symm
  签名: : I.{u} ⟶ I
  定义体: ofHom ⟨homeomorph.symm ∘ unitInterval.symm ∘ homeomorph, by fun_prop⟩

@[simp]

Depends on / 依赖: fun_prop, homeomorph, homeomorph.symm, unitInterval, unitInterval.symm
-/
def symm : I.{u} ⟶ I :=
  ofHom ⟨homeomorph.symm ∘ unitInterval.symm ∘ homeomorph, by fun_prop⟩

@[simp]
/--
lemma `homeomorph_symm` / 引理 `homeomorph_symm`

English:
lemma homeomorph_symm
  given: (x : I)
  proof: rfl

中文:
引理 homeomorph_symm
  条件: (x : I)
  证明: rfl
-/
lemma homeomorph_symm (x : I) :
    homeomorph (symm x) = unitInterval.symm (homeomorph x) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OfNat I.{u} 0
  body: ⟨homeomorph.symm 0⟩

中文:
实例 :
  签名: Of自然数 I.{u} 0
  定义体: ⟨homeomorph.symm 0⟩

Depends on / 依赖: homeomorph, homeomorph.symm
-/
instance : OfNat I.{u} 0 := ⟨homeomorph.symm 0⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OfNat I.{u} 1
  body: ⟨homeomorph.symm 1⟩

中文:
实例 :
  签名: Of自然数 I.{u} 1
  定义体: ⟨homeomorph.symm 1⟩

Depends on / 依赖: homeomorph, homeomorph.symm
-/
instance : OfNat I.{u} 1 := ⟨homeomorph.symm 1⟩

/--
lemma `homeomorph_zero` / 引理 `homeomorph_zero`

English:
lemma homeomorph_zero
  statement: homeomorph (0 : I.{u}) = 0
  proof: by simp [OfNat.ofNat]

中文:
引理 homeomorph_zero
  结论: homeomorph (0 : I.{u}) = 0
  证明: by simp [OfNat.ofNat]
-/
@[simp] lemma homeomorph_zero : homeomorph (0 : I.{u}) = 0 := by simp [OfNat.ofNat]
/--
lemma `homeomorph_one` / 引理 `homeomorph_one`

English:
lemma homeomorph_one
  statement: homeomorph (1 : I.{u}) = 1
  proof: by simp [OfNat.ofNat]

中文:
引理 homeomorph_one
  结论: homeomorph (1 : I.{u}) = 1
  证明: by simp [OfNat.ofNat]
-/
@[simp] lemma homeomorph_one : homeomorph (1 : I.{u}) = 1 := by simp [OfNat.ofNat]
/--
lemma `symm_one` / 引理 `symm_one`

English:
lemma symm_one
  statement: I.symm 1 = 0
  proof: by aesop

中文:
引理 symm_one
  结论: I.symm 1 = 0
  证明: by aesop
-/
@[simp] lemma symm_one : I.symm 1 = 0 := by aesop
/--
lemma `symm_zero` / 引理 `symm_zero`

English:
lemma symm_zero
  statement: I.symm 0 = 1
  proof: by aesop

中文:
引理 symm_zero
  结论: I.symm 0 = 1
  证明: by aesop
-/
@[simp] lemma symm_zero : I.symm 0 = 1 := by aesop

end I

open CartesianMonoidalCategory

/--
Definition of `ι₀` / `ι₀` 的定义

English:
definition ι₀
  signature: {X : TopCat.{u}}
  body: lift (𝟙 X) (const 0)

@[reassoc (attr := simp)]

中文:
定义 ι₀
  签名: {X : 顶元素范畴.{u}}
  定义体: lift (𝟙 X) (const 0)

@[reassoc (attr := simp)]
-/
noncomputable def ι₀ {X : TopCat.{u}} : X ⟶ X otimes I :=
  lift (𝟙 X) (const 0)

@[reassoc (attr := simp)]
/--
lemma `ι₀_comp` / 引理 `ι₀_comp`

English:
lemma ι₀_comp
  given: {X Y : TopCat.{u}} (f : X ⟶ Y)
  statement: ι₀ ≫ f ▷ _ = f ≫ ι₀
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 ι₀_comp
  条件: {X Y : 顶元素范畴.{u}} (f : X ⟶ Y)
  结论: ι₀ ≫ f ▷ _ = f ≫ ι₀
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma ι₀_comp {X Y : TopCat.{u}} (f : X ⟶ Y) : ι₀ ≫ f ▷ _ = f ≫ ι₀ := rfl

@[reassoc (attr := simp)]
/--
lemma `ι₀_fst` / 引理 `ι₀_fst`

English:
lemma ι₀_fst
  given: (X : TopCat.{u})
  statement: ι₀ ≫ fst X _ = 𝟙 X
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 ι₀_fst
  条件: (X : 顶元素范畴.{u})
  结论: ι₀ ≫ fst X _ = 𝟙 X
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma ι₀_fst (X : TopCat.{u}) : ι₀ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
/--
lemma `ι₀_snd` / 引理 `ι₀_snd`

English:
lemma ι₀_snd
  given: (X : TopCat.{u})
  statement: ι₀ ≫ snd X _ = TopCat.const 0
  proof: rfl

中文:
引理 ι₀_snd
  条件: (X : 顶元素范畴.{u})
  结论: ι₀ ≫ snd X _ = 顶元素范畴.const 0
  证明: rfl
-/
lemma ι₀_snd (X : TopCat.{u}) : ι₀ ≫ snd X _ = TopCat.const 0 := rfl

/--
lemma `ι₀_apply` / 引理 `ι₀_apply`

English:
lemma ι₀_apply
  given: {X : TopCat.{u}} (x : X)
  statement: ι₀ x = ⟨x, 0⟩
  proof: rfl

中文:
引理 ι₀_apply
  条件: {X : 顶元素范畴.{u}} (x : X)
  结论: ι₀ x = ⟨x, 0⟩
  证明: rfl
-/
@[simp] lemma ι₀_apply {X : TopCat.{u}} (x : X) : ι₀ x = ⟨x, 0⟩ := rfl

/--
Definition of `ι₁` / `ι₁` 的定义

English:
definition ι₁
  signature: {X : TopCat.{u}}
  body: lift (𝟙 X) (const 1)

@[reassoc (attr := simp)]

中文:
定义 ι₁
  签名: {X : 顶元素范畴.{u}}
  定义体: lift (𝟙 X) (const 1)

@[reassoc (attr := simp)]
-/
noncomputable def ι₁ {X : TopCat.{u}} : X ⟶ X otimes I :=
  lift (𝟙 X) (const 1)

@[reassoc (attr := simp)]
/--
lemma `ι₁_comp` / 引理 `ι₁_comp`

English:
lemma ι₁_comp
  given: {X Y : TopCat.{u}} (f : X ⟶ Y)
  statement: ι₁ ≫ f ▷ _ = f ≫ ι₁
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 ι₁_comp
  条件: {X Y : 顶元素范畴.{u}} (f : X ⟶ Y)
  结论: ι₁ ≫ f ▷ _ = f ≫ ι₁
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma ι₁_comp {X Y : TopCat.{u}} (f : X ⟶ Y) : ι₁ ≫ f ▷ _ = f ≫ ι₁ := rfl

@[reassoc (attr := simp)]
/--
lemma `ι₁_fst` / 引理 `ι₁_fst`

English:
lemma ι₁_fst
  given: (X : TopCat.{u})
  statement: ι₁ ≫ fst X _ = 𝟙 X
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 ι₁_fst
  条件: (X : 顶元素范畴.{u})
  结论: ι₁ ≫ fst X _ = 𝟙 X
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma ι₁_fst (X : TopCat.{u}) : ι₁ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
/--
lemma `ι₁_snd` / 引理 `ι₁_snd`

English:
lemma ι₁_snd
  given: (X : TopCat.{u})
  statement: ι₁ ≫ snd X _ = const 1
  proof: rfl

@[simp]

中文:
引理 ι₁_snd
  条件: (X : 顶元素范畴.{u})
  结论: ι₁ ≫ snd X _ = const 1
  证明: rfl

@[simp]
-/
lemma ι₁_snd (X : TopCat.{u}) : ι₁ ≫ snd X _ = const 1 := rfl

@[simp]
/--
lemma `ι₁_apply` / 引理 `ι₁_apply`

English:
lemma ι₁_apply
  given: {X : TopCat.{u}} (x : X)
  statement: ι₁ x = ⟨x, 1⟩
  proof: rfl

中文:
引理 ι₁_apply
  条件: {X : 顶元素范畴.{u}} (x : X)
  结论: ι₁ x = ⟨x, 1⟩
  证明: rfl
-/
lemma ι₁_apply {X : TopCat.{u}} (x : X) : ι₁ x = ⟨x, 1⟩ := rfl

end TopCat
