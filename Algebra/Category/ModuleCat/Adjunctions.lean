/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
The functor of forming finitely supported functions on a type with values in a `[Ring R]`
is the left adjoint of
the forgetful functor from `R`-modules to types.
-/

@[expose] public noncomputable section

assert_not_exists Cardinal

open CategoryTheory
open scoped MonoidAlgebra

namespace ModuleCat

universe u

variable (R : Type u)

section

variable [Ring R]

/-- The free functor `Type u ⥤ ModuleCat R` sending a type `X` to the
free `R`-module with generators `x : X`, implemented as the type `X →₀ R`.
-/
/-
**ModuleCat.free** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：free : Type u ⥤ ModuleCat R where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free functor `Type u ⥤ ModuleCat R` sending a type `X` to the
free `R`-module with generators `x : X`, implemented as the type `X →₀ R`.
-/
def free : Type u ⥤ ModuleCat R where
  obj X := ModuleCat.of R (X →₀ R)
  map {_ _} f := ofHom <| Finsupp.lmapDomain _ _ (f : _ → _)

/-- The free functor `Type u ⥤ ModuleCat R` sending a type `X` to the
free `R`-module with generators `x : X`, implemented as the monoid algebra `R[X]`.
-/
@[simps]
/-
**ModuleCat.monoidAlgebraFree** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：monoidAlgebraFree : Type u ⥤ ModuleCat.{u} R where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free functor `Type u ⥤ ModuleCat R` sending a type `X` to the
free `R`-module with generators `x : X`, implemented as the monoid algebra `R[X]
`.
-/
def monoidAlgebraFree : Type u ⥤ ModuleCat.{u} R where
  obj X := .of R R[X]
  map f := ofHom (MonoidAlgebra.mapDomainLinearMap R R f)

variable {R}

/-- Constructor for elements in the module `(free R).obj X`. -/
/-
**ModuleCat.freeMk** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：freeMk {X : Type u} (x : X) : (free R).obj X
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for elements in the module `(free R).obj X`.
-/
noncomputable def freeMk {X : Type u} (x : X) : (free R).obj X := Finsupp.single x 1

@[ext 1200]
/-
**ModuleCat.free_hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：free_hom_ext {X : Type u} {M : ModuleCat.{u} R} {f g : (free R).obj X ⟶ M}
 (h : forall (x : X), f (freeMk x) = g (freeMk x)) : f = g
参数：free R；h : forall (x : X), f (freeMk x) = g (freeMk x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
-/
lemma free_hom_ext {X : Type u} {M : ModuleCat.{u} R} {f g : (free R).obj X ⟶ M}
    (h : ∀ (x : X), f (freeMk x) = g (freeMk x)) :
    f = g :=
  ModuleCat.hom_ext (Finsupp.lhom_ext' (fun x ↦ LinearMap.ext_ring (h x)))

/-- The morphism of modules `(free R).obj X ⟶ M` corresponding
to a map `f : X ⟶ M`. -/
/-
**ModuleCat.freeDesc** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：freeDesc {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) : (free R).obj X ⟶
 M
参数：f : X ⟶ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism of modules `(free R).obj X ⟶ M` corresponding
to a map `f : X ⟶ M`.
-/
noncomputable def freeDesc {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) :
    (free R).obj X ⟶ M :=
  ofHom <| Finsupp.lift M R X f

@[simp]
/-
**ModuleCat.freeDesc_apply** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：freeDesc_apply {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) (x : X) : fr
eeDesc f (freeMk x) = f x
参数：f : X ⟶ M；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.lift_apply`：lift_apply (f) (g) : ((lift M R X) f) g = g.sum fun 
x r => r • f x
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma freeDesc_apply {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) (x : X) :
    freeDesc f (freeMk x) = f x := by
  dsimp [freeDesc]
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  all_goals simp

@[simp]
/-
**ModuleCat.free_map_apply** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：free_map_apply {X Y : Type u} (f : X ⟶ Y) (x : X) : (free R).map f (freeMk
 x) = freeMk (f x)
参数：f : X ⟶ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
-/
lemma free_map_apply {X Y : Type u} (f : X ⟶ Y) (x : X) :
    (free R).map f (freeMk x) = freeMk (f x) := by
  apply Finsupp.mapDomain_single

/-- The bijection `((free R).obj X ⟶ M) ≃ (X → M)` when `X` is a type and `M` a module. -/
@[simps]
/-
**ModuleCat.freeHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：freeHomEquiv {X : Type u} {M : ModuleCat.{u} R} : ((free R).obj X ⟶ M) ≃ (
X ⟶ M) where toFun φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `((free R).obj X ⟶ M) ≃ (X → M)` when `X` is a type and `M` a modu
le.
-/
def freeHomEquiv {X : Type u} {M : ModuleCat.{u} R} :
    ((free R).obj X ⟶ M) ≃ (X ⟶ M) where
  toFun φ := ↾fun x ↦ φ (freeMk x)
  invFun ψ := freeDesc (↾ψ)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

variable (R)

set_option backward.isDefEq.respectTransparency.types false in
/-- The free-forgetful adjunction for R-modules. -/
/-
**ModuleCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：adj : free R ⊣ forget (ModuleCat.{u} R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free-forgetful adjunction for R-modules.
-/
def adj : free R ⊣ forget (ModuleCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => freeHomEquiv
      homEquiv_naturality_left_symm := fun {X Y M} f g ↦ by ext; simp [freeHomEquiv] }

@[simp]
/-
**ModuleCat.adj_homEquiv** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：adj_homEquiv (X : Type u) (M : ModuleCat.{u} R) : (adj R).homEquiv X M = f
reeHomEquiv
参数：X : Type u；M : ModuleCat.{u} R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma adj_homEquiv (X : Type u) (M : ModuleCat.{u} R) :
    (adj R).homEquiv X M = freeHomEquiv := by
  simp only [adj, Adjunction.mkOfHomEquiv_homEquiv]
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget (ModuleCat.{u} R)).IsRightAdjoint :=
  (adj R).isRightAdjoint

end

section Free

open MonoidalCategory

variable [CommRing R]

namespace FreeMonoidal

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical isomorphism `𝟙_ (ModuleCat R) ≅ (free R).obj (𝟙_ (Type u))`.
(This should not be used directly: it is part of the implementation of the
monoidal structure on the functor `free R`.) -/
/-
**ModuleCat.FreeMonoidal.** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.FreeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `𝟙_ (ModuleCat R) ≅ (free R).obj (𝟙_ (Type u))`.
(This should not be used directly: it is part of the implementation of the
monoidal structure on the functor `free R`.)
-/
def εIso : 𝟙_ (ModuleCat R) ≅ (free R).obj (𝟙_ (Type u)) where
  hom := ofHom <| Finsupp.lsingle PUnit.unit
  inv := ofHom <| Finsupp.lapply PUnit.unit
  hom_inv_id := by
    ext
    simp [free]
  inv_hom_id := by
    ext ⟨⟩
    dsimp [freeMk]
    erw [Finsupp.lapply_apply, Finsupp.lsingle_apply]
    rw [Finsupp.single_eq_same]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ModuleCat.FreeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.FreeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma εIso_hom_one : (εIso R).hom 1 = freeMk PUnit.unit := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ModuleCat.FreeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.FreeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma εIso_inv_freeMk (x : PUnit) : (εIso R).inv (freeMk x) = 1 := by
  dsimp [εIso, freeMk]
  erw [Finsupp.lapply_apply]
  rw [Finsupp.single_eq_same]

/-- The canonical isomorphism `(free R).obj X ⊗ (free R).obj Y ≅ (free R).obj (X ⊗ Y)`
for two types `X` and `Y`.
(This should not be used directly: it is part of the implementation of the
monoidal structure on the functor `free R`.) -/
/-
**ModuleCat.FreeMonoidal.** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.FreeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(free R).obj X ⊗ (free R).obj Y ≅ (free R).obj (X ⊗ Y
)`
for two types `X` and `Y`.
(This should not be used directly: it is part of the implementation of the
monoidal structure on the functor `free R`.)
-/
def μIso (X Y : Type u) :
    (free R).obj X ⊗ (free R).obj Y ≅ (free R).obj (X ⊗ Y) :=
  (finsuppTensorFinsupp' R _ _).toModuleIso

@[simp]
/-
**ModuleCat.FreeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.FreeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μIso_hom_freeMk_tmul_freeMk {X Y : Type u} (x : X) (y : Y) :
    (μIso R X Y).hom (freeMk x ⊗ₜ freeMk y) = freeMk (x, y) := by
  dsimp [μIso, freeMk]
  erw [finsuppTensorFinsupp'_single_tmul_single]
  rw [mul_one]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ModuleCat.FreeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.FreeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μIso_inv_freeMk {X Y : Type u} (z : X ⊗ Y) :
    (μIso R X Y).inv (freeMk z) = freeMk z.1 ⊗ₜ freeMk z.2 := by
  dsimp [μIso, freeMk]
  erw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

end FreeMonoidal
set_option backward.isDefEq.respectTransparency.types false in
open FreeMonoidal in
/-- The free functor `Type u ⥤ ModuleCat R` is a monoidal functor. -/
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free functor `Type u ⥤ ModuleCat R` is a monoidal functor.
-/
instance : (free R).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := εIso R
      μIso := μIso R
      μIso_hom_natural_left := fun {X Y} f X' ↦ by
        rw [← cancel_epi (μIso R X X').inv]
        aesop
      μIso_hom_natural_right := fun {X Y} X' f ↦ by
        rw [← cancel_epi (μIso R X' X).inv]
        aesop
      associativity := fun X Y Z ↦ by
        rw [← cancel_epi ((μIso R X Y).inv ▷ _), ← cancel_epi (μIso R _ _).inv]
        ext ⟨⟨x, y⟩, z⟩
        dsimp
        rw [μIso_inv_freeMk, MonoidalCategory.whiskerRight_apply, μIso_inv_freeMk,
          MonoidalCategory.whiskerRight_apply, μIso_hom_freeMk_tmul_freeMk,
          μIso_hom_freeMk_tmul_freeMk, free_map_apply,
          CategoryTheory.associator_hom_apply, MonoidalCategory.associator_hom_apply,
          MonoidalCategory.whiskerLeft_apply, μIso_hom_freeMk_tmul_freeMk,
          μIso_hom_freeMk_tmul_freeMk]
      left_unitality := fun X ↦ by
        rw [← cancel_epi (λ_ _).inv, Iso.inv_hom_id]
        aesop
      right_unitality := fun X ↦ by
        rw [← cancel_epi (ρ_ _).inv, Iso.inv_hom_id]
        aesop }

open Functor.LaxMonoidal Functor.OplaxMonoidal

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ModuleCat.free_** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma free_ε_one : ε (free R) 1 = freeMk PUnit.unit := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ModuleCat.free_** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma free_η_freeMk (x : PUnit) : η (free R) (freeMk x) = 1 := by
  apply FreeMonoidal.εIso_inv_freeMk

@[simp]
/-
**ModuleCat.free_** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma free_μ_freeMk_tmul_freeMk {X Y : Type u} (x : X) (y : Y) :
    μ (free R) _ _ (freeMk x ⊗ₜ freeMk y) = freeMk (x, y) := by
  apply FreeMonoidal.μIso_hom_freeMk_tmul_freeMk

@[simp]
/-
**ModuleCat.free_** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma free_δ_freeMk {X Y : Type u} (z : X ⊗ Y) :
    δ (free R) _ _ (freeMk z) = freeMk z.1 ⊗ₜ freeMk z.2 := by
  apply FreeMonoidal.μIso_inv_freeMk

end Free

end ModuleCat

namespace CategoryTheory

universe v u

/-- `Free R C` is a type synonym for `C`, which, given `[CommRing R]` and `[Category* C]`,
we will equip with a category structure where the morphisms are formal `R`-linear combinations
of the morphisms in `C`.
-/
@[nolint unusedArguments]
/-
**CategoryTheory.Free** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Free (_ : Type*) (C : Type u)
参数：_ : Type*；C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Free R C` is a type synonym for `C`, which, given `[CommRing R]` and `[Category
* C]`,
we will equip with a category structure where the morphisms are formal `R`-linea
r combinations
of the morphisms in `C`.
-/
def Free (_ : Type*) (C : Type u) :=
  C

/-- Consider an object of `C` as an object of the `R`-linear completion.

It may be preferable to use `(Free.embedding R C).obj X` instead;
this functor can also be used to lift morphisms.
-/
/-
**CategoryTheory.Free.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Free`。
形式化陈述：(R : Type u_1) → {C : Type u} → C → CategoryTheory.Free R C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider an object of `C` as an object of the `R`-linear completion.

It may be preferable to use `(Free.embedding R C).obj X` instead;
this functor can also be used to lift morphisms.
-/
def Free.of (R : Type*) {C : Type u} (X : C) : Free R C :=
  X

variable (R : Type*) [CommRing R] (C : Type u) [Category.{v} C]

open Finsupp

-- Conceptually, it would be nice to construct this via "transport of enrichment",
-- using the fact that `ModuleCat.Free R : Type ⥤ ModuleCat R` and `ModuleCat.forget` are both lax
-- monoidal. This still seems difficult, so we just do it by hand.
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.categoryFree** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：categoryFree : Category (Free R C) where Hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance categoryFree : Category (Free R C) where
  Hom := fun X Y : C => (X ⟶ Y) →₀ R
  id := fun X : C => Finsupp.single (𝟙 X) 1
  comp {X _ Z : C} f g :=
    (f.sum (fun f' s => g.sum (fun g' t => Finsupp.single (f' ≫ g') (s * t))) : (X ⟶ Z) →₀ R)
  assoc {W X Y Z} f g h := by
    -- This imitates the proof of associativity for `MonoidAlgebra`.
    simp [sum_sum_index, add_mul, mul_add, Category.assoc, mul_assoc]

namespace Free

section

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Free.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Free`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (Free R C) where
  homGroup _ _ := Finsupp.instAddCommGroup
  add_comp X Y Z f f' g := by
    dsimp +instances [CategoryTheory.categoryFree]
    rw [Finsupp.sum_add_index'] <;> · simp [add_mul]
  comp_add X Y Z f g g' := by
    dsimp +instances [CategoryTheory.categoryFree]
    rw [← Finsupp.sum_add]
    congr; ext r h
    rw [Finsupp.sum_add_index'] <;> · simp [mul_add]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Free.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Free`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Linear R (Free R C) where
  homModule _ _ := Finsupp.module _ R
  smul_comp X Y Z r f g := by
    dsimp +instances [CategoryTheory.categoryFree]
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_assoc]
  comp_smul X Y Z f r g := by
    dsimp +instances [CategoryTheory.categoryFree]
    simp_rw [Finsupp.smul_sum]
    congr; ext h s
    rw [Finsupp.sum_smul_index] <;> simp [mul_left_comm]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Free.single_comp_single** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Free`。
形式化陈述：single_comp_single {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : R) : (single
 f r ≫ single g s : Free.of R X ⟶ Free.of R Z) = single (f ≫ g) (r * s)
参数：f : X ⟶ Y；g : Y ⟶ Z；r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem single_comp_single {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : R) :
    (single f r ≫ single g s : Free.of R X ⟶ Free.of R Z) = single (f ≫ g) (r * s) := by
  dsimp +instances [CategoryTheory.categoryFree]
  simp

end

attribute [local simp] single_comp_single

set_option backward.isDefEq.respectTransparency false in
/-- A category embeds into its `R`-linear completion.
-/
@[simps]
/-
**CategoryTheory.Free.embedding** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Free`。
形式化陈述：embedding : C ⥤ Free R C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category embeds into its `R`-linear completion.
-/
def embedding : C ⥤ Free R C where
  obj X := X
  map {_ _} f := Finsupp.single f 1
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10959): simp used to be able to close this goal
    rw [single_comp_single, one_mul]

variable {C} {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D]

open Preadditive Linear

set_option backward.isDefEq.respectTransparency false in
/-- A functor to an `R`-linear category lifts to a functor from its `R`-linear completion.
-/
@[simps]
/-
**CategoryTheory.Free.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Free`。
形式化陈述：lift (F : C ⥤ D) : Free R C ⥤ D where obj X
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor to an `R`-linear category lifts to a functor from its `R`-linear compl
etion.
-/
def lift (F : C ⥤ D) : Free R C ⥤ D where
  obj X := F.obj X
  map {_ _} f := f.sum fun f' r => r • F.map f'
  map_id := by
    dsimp +instances [CategoryTheory.categoryFree]
    simp
  map_comp {X Y Z} f g := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ w₁ w₂ =>
      rw [add_comp]
      rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
      · simp only [w₁, w₂, add_comp]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
    | single f' r =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [comp_add]
        rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
        · simp only [w₁, w₂, comp_add]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
      | single g' s =>
        rw [single_comp_single _ _ f' g' r s]
        simp [mul_comm r s, mul_smul]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Free.lift_map_single** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Free`。
形式化陈述：lift_map_single (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (r : R) : (lift R F).map
 (single f r) = r • F.map f
参数：F : C ⥤ D；f : X ⟶ Y；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Free.lift_map`：∀ (R : Type u_1) [inst : CommRing R] {C : 
Type u} [inst_1 : CategoryTheory.Category.{v, u} C] {D : Type u}   [inst_2 : Cat
egoryTheory.Catego…
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_map_single (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (r : R) :
    (lift R F).map (single f r) = r • F.map f := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Free.lift_additive** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fr
ee`。
形式化陈述：lift_additive (F : C ⥤ D) : (lift R F).Additive where map_add {X Y} f g
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_add_index'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : AddZeroClass M] [inst_1 : AddCommMonoid N] {f g : α →₀ M}   {h : α → M →
 N},   (∀ (a…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
instance lift_additive (F : C ⥤ D) : (lift R F).Additive where
  map_add {X Y} f g := by
    dsimp
    rw [Finsupp.sum_add_index'] <;> simp [add_smul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Free.lift_linear** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Free
`。
形式化陈述：lift_linear (F : C ⥤ D) : (lift R F).Linear R where map_smul {X Y} f r
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_smul_index`：sum_smul_index [MulZeroClass R] [AddCommMonoid M
] {g : α ->₀ R} {b : R} {h : α -> R -> M} (h0 : forall i, h i 0 = 0) : (b • g).s
um h = g.sum…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Finsupp.smul_sum`：smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] 
{v : α ->₀ β} {c : R} {h : α -> β -> M} : c • v.sum h = v.sum fun a b => c • h a
 b
-/
instance lift_linear (F : C ⥤ D) : (lift R F).Linear R where
  map_smul {X Y} f r := by
    dsimp
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_smul]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The embedding into the `R`-linear completion, followed by the lift,
is isomorphic to the original functor.
-/
/-
**CategoryTheory.Free.embeddingLiftIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Free`。
形式化陈述：embeddingLiftIso (F : C ⥤ D) : embedding R C ⋙ lift R F ≅ F
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding into the `R`-linear completion, followed by the lift,
is isomorphic to the original functor.
-/
def embeddingLiftIso (F : C ⥤ D) : embedding R C ⋙ lift R F ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- Two `R`-linear functors out of the `R`-linear completion are isomorphic iff their
compositions with the embedding functor are isomorphic.
-/
/-
**CategoryTheory.Free.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Free`。
形式化陈述：ext {F G : Free R C ⥤ D} [F.Additive] [F.Linear R] [G.Additive] [G.Linear 
R] (α : embedding R C ⋙ F ≅ embedding R C ⋙ G) : F ≅ G
参数：α : embedding R C ⋙ F ≅ embedding R C ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two `R`-linear functors out of the `R`-linear completion are isomorphic iff thei
r
compositions with the embedding functor are isomorphic.
-/
def ext {F G : Free R C ⥤ D} [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
    (α : embedding R C ⋙ F ≅ embedding R C ⋙ G) : F ≅ G :=
  NatIso.ofComponents (fun X => α.app X)
    (by
      intro X Y f
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [Functor.map_add, add_comp, w₁, w₂, Functor.map_add, comp_add]
      | single f' r =>
        rw [Iso.app_hom, Iso.app_hom, ← smul_single_one, F.map_smul, G.map_smul, smul_comp,
          comp_smul]
        change r • (embedding R C ⋙ F).map f' ≫ _ = r • _ ≫ (embedding R C ⋙ G).map f'
        rw [α.hom.naturality f'])

/-- `Free.lift` is unique amongst `R`-linear functors `Free R C ⥤ D`
which compose with `embedding ℤ C` to give the original functor.
-/
/-
**CategoryTheory.Free.liftUnique** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Free`
。
形式化陈述：liftUnique (F : C ⥤ D) (L : Free R C ⥤ D) [L.Additive] [L.Linear R] (α : e
mbedding R C ⋙ L ≅ F) : L ≅ lift R F
参数：F : C ⥤ D；L : Free R C ⥤ D；α : embedding R C ⋙ L ≅ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Free.lift` is unique amongst `R`-linear functors `Free R C ⥤ D`
which compose with `embedding ℤ C` to give the original functor.
-/
def liftUnique (F : C ⥤ D) (L : Free R C ⥤ D) [L.Additive] [L.Linear R]
    (α : embedding R C ⋙ L ≅ F) : L ≅ lift R F :=
  ext R (α.trans (embeddingLiftIso R F).symm)

end Free
end CategoryTheory

