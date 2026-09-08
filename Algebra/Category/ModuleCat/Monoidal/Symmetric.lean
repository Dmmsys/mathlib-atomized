/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# The symmetric monoidal structure on `Module R`.
-/

@[expose] public section

universe v w x u

open CategoryTheory MonoidalCategory

namespace SemimoduleCat

variable {R : Type u} [CommSemiring R]

/-- (implementation) the braiding for R-modules -/
/-
**SemimoduleCat.braiding** 是 Mathlib 中的一个定义，位于命名空间 `SemimoduleCat`。
形式化陈述：braiding (M N : SemimoduleCat.{u} R) : M otimes N ≅ N otimes M
参数：M N : SemimoduleCat.{u} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) the braiding for R-modules
-/
def braiding (M N : SemimoduleCat.{u} R) : M ⊗ N ≅ N ⊗ M :=
  LinearEquiv.toModuleIsoₛ (TensorProduct.comm R M N)

namespace MonoidalCategory

@[simp]
/-
**SemimoduleCat.MonoidalCategory.braiding_naturality** 是 Mathlib 中的一个定理，位于命名空间 `
SemimoduleCat.MonoidalCategory`。
形式化陈述：braiding_naturality {X₁ X₂ Y₁ Y₂ : SemimoduleCat.{u} R} (f : X₁ ⟶ Y₁) (g :
 X₂ ⟶ Y₂) : (f otimesₘ g) ≫ (Y₁.braiding Y₂).hom = (X₁.braiding X₂).hom ≫ (g oti
mesₘ f)
参数：f : X₁ ⟶ Y₁；g : X₂ ⟶ Y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
-/
theorem braiding_naturality {X₁ X₂ Y₁ Y₂ : SemimoduleCat.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g) ≫ (Y₁.braiding Y₂).hom = (X₁.braiding X₂).hom ≫ (g ⊗ₘ f) := by
  ext : 1
  apply TensorProduct.ext'
  intro x y
  rfl

@[simp]
/-
**SemimoduleCat.MonoidalCategory.braiding_naturality_left** 是 Mathlib 中的一个定理，位于命
名空间 `SemimoduleCat.MonoidalCategory`。
形式化陈述：braiding_naturality_left {X Y : SemimoduleCat R} (f : X ⟶ Y) (Z : Semimodu
leCat R) : f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f
参数：f : X ⟶ Y；Z : SemimoduleCat R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemimoduleCat.MonoidalCategory.braiding_naturality`：braiding_naturality 
{X₁ X₂ Y₁ Y₂ : SemimoduleCat.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f otimesₘ g) 
≫ (Y₁.braiding Y₂).hom = (X₁.braiding X₂…
-/
theorem braiding_naturality_left {X Y : SemimoduleCat R} (f : X ⟶ Y) (Z : SemimoduleCat R) :
    f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
  simp_rw [← id_tensorHom]
  apply braiding_naturality

@[simp]
/-
**SemimoduleCat.MonoidalCategory.braiding_naturality_right** 是 Mathlib 中的一个定理，位于
命名空间 `SemimoduleCat.MonoidalCategory`。
形式化陈述：braiding_naturality_right (X : SemimoduleCat R) {Y Z : SemimoduleCat R} (f
 : Y ⟶ Z) : X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X
参数：X : SemimoduleCat R；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemimoduleCat.MonoidalCategory.braiding_naturality`：braiding_naturality 
{X₁ X₂ Y₁ Y₂ : SemimoduleCat.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f otimesₘ g) 
≫ (Y₁.braiding Y₂).hom = (X₁.braiding X₂…
-/
theorem braiding_naturality_right (X : SemimoduleCat R) {Y Z : SemimoduleCat R} (f : Y ⟶ Z) :
    X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X := by
  simp_rw [← id_tensorHom]
  apply braiding_naturality

@[simp]
/-
**SemimoduleCat.MonoidalCategory.hexagon_forward** 是 Mathlib 中的一个定理，位于命名空间 `Semi
moduleCat.MonoidalCategory`。
形式化陈述：hexagon_forward (X Y Z : SemimoduleCat.{u} R) : (α_ X Y Z).hom ≫ (braiding
 X _).hom ≫ (α_ Y Z X).hom = (braiding X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (brai
ding X Z).hom
参数：X Y Z : SemimoduleCat.{u} R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext_threefold`：ext_threefold {g h : M otimes[R] N otimes[R
] P ->ₛₗ[σ₁₂] P₂} (H : forall x y z, g (x otimesₜ y otimesₜ z) = h (x otimesₜ y 
otimesₜ z)) : g =…
-/
theorem hexagon_forward (X Y Z : SemimoduleCat.{u} R) :
    (α_ X Y Z).hom ≫ (braiding X _).hom ≫ (α_ Y Z X).hom =
      (braiding X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (braiding X Z).hom := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

@[simp]
/-
**SemimoduleCat.MonoidalCategory.hexagon_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Semi
moduleCat.MonoidalCategory`。
形式化陈述：hexagon_reverse (X Y Z : SemimoduleCat.{u} R) : (α_ X Y Z).inv ≫ (braiding
 _ Z).hom ≫ (α_ Z X Y).inv = X ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).inv ≫ (X.braidi
ng Z).hom ▷ Y
参数：X Y Z : SemimoduleCat.{u} R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext_threefold`：ext_threefold {g h : M otimes[R] N otimes[R
] P ->ₛₗ[σ₁₂] P₂} (H : forall x y z, g (x otimesₜ y otimesₜ z) = h (x otimesₜ y 
otimesₜ z)) : g =…
-/
theorem hexagon_reverse (X Y Z : SemimoduleCat.{u} R) :
    (α_ X Y Z).inv ≫ (braiding _ Z).hom ≫ (α_ Z X Y).inv =
      X ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).inv ≫ (X.braiding Z).hom ▷ Y := by
  apply (cancel_epi (α_ X Y Z).hom).1
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

attribute [local ext] TensorProduct.ext

/-- The symmetric monoidal structure on `Module R`. -/
/-
**SemimoduleCat.MonoidalCategory.symmetricCategory** 是 Mathlib 中的一个实例，位于命名空间 `Se
mimoduleCat.MonoidalCategory`。
形式化陈述：symmetricCategory : SymmetricCategory (SemimoduleCat.{u} R) where braiding
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SemimoduleCat.MonoidalCategory.braiding_naturality_right`：braiding_natur
ality_right (X : SemimoduleCat R) {Y Z : SemimoduleCat R} (f : Y ⟶ Z) : X ◁ f ≫ 
(braiding X Z).hom = (braiding X Y).hom ≫ f ▷ …
· 使用定理 `SemimoduleCat.MonoidalCategory.braiding_naturality_left`：braiding_natura
lity_left {X Y : SemimoduleCat R} (f : X ⟶ Y) (Z : SemimoduleCat R) : f ▷ Z ≫ (b
raiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f
· 使用定理 `SemimoduleCat.MonoidalCategory.hexagon_forward`：hexagon_forward (X Y Z :
 SemimoduleCat.{u} R) : (α_ X Y Z).hom ≫ (braiding X _).hom ≫ (α_ Y Z X).hom = (
braiding X Y).hom ▷ Z ≫ (α_ Y X Z).h…
· 使用定理 `SemimoduleCat.MonoidalCategory.hexagon_reverse`：hexagon_reverse (X Y Z :
 SemimoduleCat.{u} R) : (α_ X Y Z).inv ≫ (braiding _ Z).hom ≫ (α_ Z X Y).inv = X
 ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).i…

--- 原说明 ---
The symmetric monoidal structure on `Module R`.
-/
instance symmetricCategory : SymmetricCategory (SemimoduleCat.{u} R) where
  braiding := braiding
  braiding_naturality_left := braiding_naturality_left
  braiding_naturality_right := braiding_naturality_right
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse
  -- Porting note: this proof was automatic in Lean3
  -- now `aesop` is applying `SemimoduleCat.ext` in favour of `TensorProduct.ext`.
  symmetry _ _ := by
    ext : 1
    apply TensorProduct.ext'
    cat_disch

@[simp]
/-
**SemimoduleCat.MonoidalCategory.braiding_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `S
emimoduleCat.MonoidalCategory`。
形式化陈述：braiding_hom_apply {M N : SemimoduleCat.{u} R} (m : M) (n : N) : ((β_ M N)
.hom : M otimes N ⟶ N otimes M) (m otimesₜ n) = n otimesₜ m
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_hom_apply {M N : SemimoduleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).hom : M ⊗ N ⟶ N ⊗ M) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl

@[simp]
/-
**SemimoduleCat.MonoidalCategory.braiding_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `S
emimoduleCat.MonoidalCategory`。
形式化陈述：braiding_inv_apply {M N : SemimoduleCat.{u} R} (m : M) (n : N) : ((β_ M N)
.inv : N otimes M ⟶ M otimes N) (n otimesₜ m) = m otimesₜ n
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_inv_apply {M N : SemimoduleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).inv : N ⊗ M ⟶ M ⊗ N) (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl
/-
**SemimoduleCat.MonoidalCategory.tensor** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat
.MonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorμ_eq_tensorTensorTensorComm {A B C D : SemimoduleCat R} :
    tensorμ A B C D = ofHom (TensorProduct.tensorTensorTensorComm R A B C D).toLinearMap :=
  SemimoduleCat.hom_ext <| TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext₂ fun _ _ =>
    TensorProduct.ext <| LinearMap.ext₂ fun _ _ => rfl

@[simp]
/-
**SemimoduleCat.MonoidalCategory.tensor** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat
.MonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorμ_apply
    {A B C D : SemimoduleCat R} (x : A) (y : B) (z : C) (w : D) :
    tensorμ A B C D ((x ⊗ₜ y) ⊗ₜ (z ⊗ₜ w)) = (x ⊗ₜ z) ⊗ₜ (y ⊗ₜ w) := rfl

end MonoidalCategory

end SemimoduleCat

namespace ModuleCat.MonoidalCategory

variable {R : Type u} [CommRing R]

/-
**ModuleCat.MonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.MonoidalCateg
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory (ModuleCat.{u} R) :=
  .ofFaithful equivalenceSemimoduleCat.functor (fun M N ↦ (TensorProduct.comm R M N).toModuleIso)
/-
**ModuleCat.MonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.MonoidalCateg
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : equivalenceSemimoduleCat (R := R).functor.Braided where
/-
**ModuleCat.MonoidalCategory.symmetricCategory** 是 Mathlib 中的一个实例，位于命名空间 `Module
Cat.MonoidalCategory`。
形式化陈述：symmetricCategory : SymmetricCategory (ModuleCat.{u} R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance symmetricCategory : SymmetricCategory (ModuleCat.{u} R) :=
  .ofFaithful equivalenceSemimoduleCat.functor

@[simp]
/-
**ModuleCat.MonoidalCategory.braiding_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Modul
eCat.MonoidalCategory`。
形式化陈述：braiding_hom_apply {M N : ModuleCat.{u} R} (m : M) (n : N) : ((β_ M N).hom
 : M otimes N ⟶ N otimes M) (m otimesₜ n) = n otimesₜ m
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_hom_apply {M N : ModuleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).hom : M ⊗ N ⟶ N ⊗ M) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl

@[simp]
/-
**ModuleCat.MonoidalCategory.braiding_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Modul
eCat.MonoidalCategory`。
形式化陈述：braiding_inv_apply {M N : ModuleCat.{u} R} (m : M) (n : N) : ((β_ M N).inv
 : N otimes M ⟶ M otimes N) (n otimesₜ m) = m otimesₜ n
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_inv_apply {M N : ModuleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).inv : N ⊗ M ⟶ M ⊗ N) (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl
/-
**ModuleCat.MonoidalCategory.tensor** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.Monoida
lCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorμ_eq_tensorTensorTensorComm {A B C D : ModuleCat R} :
    tensorμ A B C D = ofHom (TensorProduct.tensorTensorTensorComm R A B C D).toLinearMap :=
  ModuleCat.hom_ext <| TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext₂ fun _ _ =>
    TensorProduct.ext <| LinearMap.ext₂ fun _ _ => rfl

@[simp]
/-
**ModuleCat.MonoidalCategory.tensor** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.Monoida
lCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorμ_apply
    {A B C D : ModuleCat R} (x : A) (y : B) (z : C) (w : D) :
    tensorμ A B C D ((x ⊗ₜ y) ⊗ₜ (z ⊗ₜ w)) = (x ⊗ₜ z) ⊗ₜ (y ⊗ₜ w) := rfl

end ModuleCat.MonoidalCategory

