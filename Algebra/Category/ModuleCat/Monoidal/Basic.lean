/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The monoidal category structure on R-modules

Mostly this uses existing machinery in `LinearAlgebra.TensorProduct`.
We just need to provide a few small missing pieces to build the
`MonoidalCategory` instance.
The `SymmetricCategory` instance is in `Algebra.Category.ModuleCat.Monoidal.Symmetric`
to reduce imports.

Note the universe level of the modules must be at least the universe level of the ring,
so that we have a monoidal unit.
For now, we simplify by insisting both universe levels are the same.

We construct the monoidal closed structure on `ModuleCat R` in
`Algebra.Category.ModuleCat.Monoidal.Closed`.

If you're happy using the bundled `ModuleCat R`, it may be possible to mostly
use this as an interface and not need to interact much with the implementation details.
-/

@[expose] public section

universe v w x u

open CategoryTheory

namespace SemimoduleCat

variable {R : Type u} [CommSemiring R]

namespace MonoidalCategory

-- The definitions inside this namespace are essentially private.
-- After we build the `MonoidalCategory (Module R)` instance,
-- you should use that API.
open TensorProduct

attribute [local ext] TensorProduct.ext

/-- (implementation) tensor product of R-modules -/
/-
**SemimoduleCat.MonoidalCategory.tensorObj** 是 Mathlib 中的一个定义，位于命名空间 `Semimodule
Cat.MonoidalCategory`。
形式化陈述：tensorObj (M N : SemimoduleCat R) : SemimoduleCat R
参数：M N : SemimoduleCat R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) tensor product of R-modules
-/
def tensorObj (M N : SemimoduleCat R) : SemimoduleCat R :=
  SemimoduleCat.of R (M ⊗[R] N)

/-- (implementation) tensor product of morphisms R-modules -/
/-
**SemimoduleCat.MonoidalCategory.tensorHom** 是 Mathlib 中的一个定义，位于命名空间 `Semimodule
Cat.MonoidalCategory`。
形式化陈述：tensorHom {M N M' N' : SemimoduleCat R} (f : M ⟶ N) (g : M' ⟶ N') : tensor
Obj M M' ⟶ tensorObj N N'
参数：f : M ⟶ N；g : M' ⟶ N'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) tensor product of morphisms R-modules
-/
def tensorHom {M N M' N' : SemimoduleCat R} (f : M ⟶ N) (g : M' ⟶ N') :
    tensorObj M M' ⟶ tensorObj N N' :=
  ofHom <| TensorProduct.map f.hom g.hom

/-- (implementation) left whiskering for R-modules -/
/-
**SemimoduleCat.MonoidalCategory.whiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `Semimodu
leCat.MonoidalCategory`。
形式化陈述：whiskerLeft (M : SemimoduleCat R) {N₁ N₂ : SemimoduleCat R} (f : N₁ ⟶ N₂) 
: tensorObj M N₁ ⟶ tensorObj M N₂
参数：M : SemimoduleCat R；f : N₁ ⟶ N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) left whiskering for R-modules
-/
def whiskerLeft (M : SemimoduleCat R) {N₁ N₂ : SemimoduleCat R} (f : N₁ ⟶ N₂) :
    tensorObj M N₁ ⟶ tensorObj M N₂ :=
  ofHom <| f.hom.lTensor M

/-- (implementation) right whiskering for R-modules -/
/-
**SemimoduleCat.MonoidalCategory.whiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `Semimod
uleCat.MonoidalCategory`。
形式化陈述：whiskerRight {M₁ M₂ : SemimoduleCat R} (f : M₁ ⟶ M₂) (N : SemimoduleCat R)
 : tensorObj M₁ N ⟶ tensorObj M₂ N
参数：f : M₁ ⟶ M₂；N : SemimoduleCat R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) right whiskering for R-modules
-/
def whiskerRight {M₁ M₂ : SemimoduleCat R} (f : M₁ ⟶ M₂) (N : SemimoduleCat R) :
    tensorObj M₁ N ⟶ tensorObj M₂ N :=
  ofHom <| f.hom.rTensor N
/-
**SemimoduleCat.MonoidalCategory.id_tensorHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Semi
moduleCat.MonoidalCategory`。
形式化陈述：id_tensorHom_id (M N : SemimoduleCat R) : tensorHom (𝟙 M) (𝟙 N) = 𝟙 (Semim
oduleCat.of R (M otimes N))
参数：M N : SemimoduleCat R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
-/
theorem id_tensorHom_id (M N : SemimoduleCat R) :
    tensorHom (𝟙 M) (𝟙 N) = 𝟙 (SemimoduleCat.of R (M ⊗ N)) := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl
/-
**SemimoduleCat.MonoidalCategory.tensorHom_comp_tensorHom** 是 Mathlib 中的一个定理，位于命
名空间 `SemimoduleCat.MonoidalCategory`。
形式化陈述：tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SemimoduleCat R} (f₁ : X₁ ⟶ 
Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) : tensorHom f₁ f₂ ≫ tensorHom g
₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；g₁ : Y₁ ⟶ Z₁；g₂ : Y₂ ⟶ Z₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
-/
theorem tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

/-- (implementation) the associator for R-modules -/
/-
**SemimoduleCat.MonoidalCategory.associator** 是 Mathlib 中的一个定义，位于命名空间 `Semimodul
eCat.MonoidalCategory`。
形式化陈述：associator (M : SemimoduleCat.{v} R) (N : SemimoduleCat.{w} R) (K : Semimo
duleCat.{x} R) : tensorObj (tensorObj M N) K ≅ tensorObj M (tensorObj N K)
参数：M : SemimoduleCat.{v} R；N : SemimoduleCat.{w} R；K : SemimoduleCat.{x} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) the associator for R-modules
-/
def associator (M : SemimoduleCat.{v} R) (N : SemimoduleCat.{w} R) (K : SemimoduleCat.{x} R) :
    tensorObj (tensorObj M N) K ≅ tensorObj M (tensorObj N K) :=
  (TensorProduct.assoc R M N K).toModuleIsoₛ

/-- (implementation) the left unitor for R-modules -/
/-
**SemimoduleCat.MonoidalCategory.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `Semimodul
eCat.MonoidalCategory`。
形式化陈述：leftUnitor (M : SemimoduleCat.{u} R) : SemimoduleCat.of R (R otimes[R] M) 
≅ M
参数：M : SemimoduleCat.{u} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) the left unitor for R-modules
-/
def leftUnitor (M : SemimoduleCat.{u} R) : SemimoduleCat.of R (R ⊗[R] M) ≅ M :=
  (TensorProduct.lid R M).toModuleIsoₛ

/-- (implementation) the right unitor for R-modules -/
/-
**SemimoduleCat.MonoidalCategory.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `Semimodu
leCat.MonoidalCategory`。
形式化陈述：rightUnitor (M : SemimoduleCat.{u} R) : SemimoduleCat.of R (M otimes[R] R)
 ≅ M
参数：M : SemimoduleCat.{u} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) the right unitor for R-modules
-/
def rightUnitor (M : SemimoduleCat.{u} R) : SemimoduleCat.of R (M ⊗[R] R) ≅ M :=
  (TensorProduct.rid R M).toModuleIsoₛ

@[simps -isSimp]
/-
**SemimoduleCat.MonoidalCategory.instMonoidalCategoryStruct** 是 Mathlib 中的一个实例，位
于命名空间 `SemimoduleCat.MonoidalCategory`。
形式化陈述：instMonoidalCategoryStruct : MonoidalCategoryStruct (SemimoduleCat.{u} R) 
where tensorObj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (SemimoduleCat.{u} R) where
  tensorObj := tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorHom := tensorHom
  tensorUnit := SemimoduleCat.of R R
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
/-
**SemimoduleCat.MonoidalCategory.associator_naturality** 是 Mathlib 中的一个定理，位于命名空间
 `SemimoduleCat.MonoidalCategory`。
形式化陈述：associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁)
 (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) : tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁
 Y₂ Y₃).hom = (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；f₃ : X₃ ⟶ Y₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext_threefold`：ext_threefold {g h : M otimes[R] N otimes[R
] P ->ₛₗ[σ₁₂] P₂} (H : forall x y z, g (x otimesₜ y otimesₜ z) = h (x otimesₜ y 
otimesₜ z)) : g =…
-/
theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl
/-
**SemimoduleCat.MonoidalCategory.pentagon** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleC
at.MonoidalCategory`。
形式化陈述：pentagon (W X Y Z : SemimoduleCat R) : whiskerRight (associator W X Y).hom
 Z ≫ (associator W (tensorObj X Y) Z).hom ≫ whiskerLeft W (associator X Y Z).hom
 = (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom
参数：W X Y Z : SemimoduleCat R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext_fourfold`：ext_fourfold {g h : M otimes[R] N otimes[R] 
P otimes[R] Q ->ₛₗ[σ₁₂] P₂} (H : forall w x y z, g (w otimesₜ x otimesₜ y otimes
ₜ z) = h (w otim…
-/
theorem pentagon (W X Y Z : SemimoduleCat R) :
    whiskerRight (associator W X Y).hom Z ≫
        (associator W (tensorObj X Y) Z).hom ≫ whiskerLeft W (associator X Y Z).hom =
      (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
  ext : 1
  apply TensorProduct.ext_fourfold
  intro w x y z
  rfl
/-
**SemimoduleCat.MonoidalCategory.leftUnitor_naturality** 是 Mathlib 中的一个定理，位于命名空间
 `SemimoduleCat.MonoidalCategory`。
形式化陈述：leftUnitor_naturality {M N : SemimoduleCat R} (f : M ⟶ N) : tensorHom (𝟙 (
SemimoduleCat.of R R)) f ≫ (leftUnitor N).hom = (leftUnitor M).hom ≫ f
参数：f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.compr₂ₛₗ.congr_simp`：∀ {R : Type u_2} [inst : CommSemiring R] 
{R₂ : Type u_14} {R₃ : Type u_15} {R₄ : Type u_16} {M : Type u_17}   {N : Type u
_18} {P : Type u_19…
· 使用定理 `LinearEquiv.toModuleIsoₛ_hom`：∀ {R : Type u} [inst : Semiring R] {X₁ X₂ 
: Type v} {g₁ : AddCommMonoid X₁} {g₂ : AddCommMonoid X₂}   {m₁ : _root_.Module 
R X₁} {m₂ : _root_…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftUnitor_naturality {M N : SemimoduleCat R} (f : M ⟶ N) :
    tensorHom (𝟙 (SemimoduleCat.of R R)) f ≫ (leftUnitor N).hom = (leftUnitor M).hom ≫ f := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [tensorHom, tensorObj, leftUnitor]
/-
**SemimoduleCat.MonoidalCategory.rightUnitor_naturality** 是 Mathlib 中的一个定理，位于命名空
间 `SemimoduleCat.MonoidalCategory`。
形式化陈述：rightUnitor_naturality {M N : SemimoduleCat R} (f : M ⟶ N) : tensorHom f (
𝟙 (SemimoduleCat.of R R)) ≫ (rightUnitor N).hom = (rightUnitor M).hom ≫ f
参数：f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.compr₂ₛₗ.congr_simp`：∀ {R : Type u_2} [inst : CommSemiring R] 
{R₂ : Type u_14} {R₃ : Type u_15} {R₄ : Type u_16} {M : Type u_17}   {N : Type u
_18} {P : Type u_19…
· 使用定理 `LinearEquiv.toModuleIsoₛ_hom`：∀ {R : Type u} [inst : Semiring R] {X₁ X₂ 
: Type v} {g₁ : AddCommMonoid X₁} {g₂ : AddCommMonoid X₂}   {m₁ : _root_.Module 
R X₁} {m₂ : _root_…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightUnitor_naturality {M N : SemimoduleCat R} (f : M ⟶ N) :
    tensorHom f (𝟙 (SemimoduleCat.of R R)) ≫ (rightUnitor N).hom = (rightUnitor M).hom ≫ f := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [tensorHom, tensorObj, rightUnitor]
/-
**SemimoduleCat.MonoidalCategory.triangle** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleC
at.MonoidalCategory`。
形式化陈述：triangle (M N : SemimoduleCat.{u} R) : (associator M (SemimoduleCat.of R R
) N).hom ≫ tensorHom (𝟙 M) (leftUnitor N).hom = tensorHom (rightUnitor M).hom (𝟙
 N)
参数：M N : SemimoduleCat.{u} R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext_threefold`：ext_threefold {g h : M otimes[R] N otimes[R
] P ->ₛₗ[σ₁₂] P₂} (H : forall x y z, g (x otimesₜ y otimesₜ z) = h (x otimesₜ y 
otimesₜ z)) : g =…
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
-/
theorem triangle (M N : SemimoduleCat.{u} R) :
    (associator M (SemimoduleCat.of R R) N).hom ≫ tensorHom (𝟙 M) (leftUnitor N).hom =
      tensorHom (rightUnitor M).hom (𝟙 N) := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y
  exact TensorProduct.tmul_smul _ _

end MonoidalCategory

open MonoidalCategory

/-
**SemimoduleCat.monoidalCategory** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
形式化陈述：monoidalCategory : MonoidalCategory (SemimoduleCat.{u} R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SemimoduleCat.MonoidalCategory.id_tensorHom_id`：id_tensorHom_id (M N : S
emimoduleCat R) : tensorHom (𝟙 M) (𝟙 N) = 𝟙 (SemimoduleCat.of R (M otimes N))
· 使用定理 `SemimoduleCat.MonoidalCategory.tensorHom_comp_tensorHom`：tensorHom_comp_
tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g
₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) : tensorHom f₁ f₂…
· 使用定理 `SemimoduleCat.MonoidalCategory.associator_naturality`：associator_natural
ity {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃
 ⟶ Y₃) : tensorHom (tensorHom f₁ f₂) f₃ ≫ …
· 使用定理 `SemimoduleCat.MonoidalCategory.leftUnitor_naturality`：leftUnitor_natural
ity {M N : SemimoduleCat R} (f : M ⟶ N) : tensorHom (𝟙 (SemimoduleCat.of R R)) f
 ≫ (leftUnitor N).hom = (leftUnitor M).hom…
· 使用定理 `SemimoduleCat.MonoidalCategory.rightUnitor_naturality`：rightUnitor_natur
ality {M N : SemimoduleCat R} (f : M ⟶ N) : tensorHom f (𝟙 (SemimoduleCat.of R R
)) ≫ (rightUnitor N).hom = (rightUnitor M).…
· 使用定理 `SemimoduleCat.MonoidalCategory.pentagon`：pentagon (W X Y Z : SemimoduleC
at R) : whiskerRight (associator W X Y).hom Z ≫ (associator W (tensorObj X Y) Z)
.hom ≫ whiskerLeft W (associa…
· 使用定理 `SemimoduleCat.MonoidalCategory.triangle`：triangle (M N : SemimoduleCat.{
u} R) : (associator M (SemimoduleCat.of R R) N).hom ≫ tensorHom (𝟙 M) (leftUnito
r N).hom = tensorHom (rightUn…
-/
instance monoidalCategory : MonoidalCategory (SemimoduleCat.{u} R) := MonoidalCategory.ofTensorHom
  (id_tensorHom_id := fun M N ↦ id_tensorHom_id M N)
  (tensorHom_comp_tensorHom := fun f g h ↦ MonoidalCategory.tensorHom_comp_tensorHom f g h)
  (associator_naturality := fun f g h ↦ MonoidalCategory.associator_naturality f g h)
  (leftUnitor_naturality := fun f ↦ MonoidalCategory.leftUnitor_naturality f)
  (rightUnitor_naturality := fun f ↦ rightUnitor_naturality f)
  (pentagon := fun M N K L ↦ pentagon M N K L)
  (triangle := fun M N ↦ triangle M N)

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative semiring. -/
/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Remind ourselves that the monoidal unit, being just `R`, is still a commutative 
semiring.
-/
instance : CommSemiring ((𝟙_ (SemimoduleCat.{u} R) : SemimoduleCat.{u} R) : Type u) :=
  inferInstanceAs <| CommSemiring R
/-
**SemimoduleCat.hom_tensorHom** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_tensorHom {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) : (f
 otimesₘ g).hom = TensorProduct.map f.hom g.hom
参数：f : K ⟶ L；g : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_tensorHom {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom :=
  rfl
/-
**SemimoduleCat.hom_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_whiskerLeft (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f :
 M ⟶ N) : (L ◁ f).hom = f.hom.lTensor L
参数：L : SemimoduleCat.{u} R；f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_whiskerLeft (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = f.hom.lTensor L :=
  rfl
/-
**SemimoduleCat.hom_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_whiskerRight {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCa
t.{u} R) : (f ▷ N).hom = f.hom.rTensor N
参数：f : L ⟶ M；N : SemimoduleCat.{u} R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_whiskerRight {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCat.{u} R) :
    (f ▷ N).hom = f.hom.rTensor N :=
  rfl
/-
**SemimoduleCat.hom_hom_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_hom_leftUnitor {M : SemimoduleCat.{u} R} : (fun_ M).hom.hom = (TensorP
roduct.lid _ _).toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_hom_leftUnitor {M : SemimoduleCat.{u} R} :
    (λ_ M).hom.hom = (TensorProduct.lid _ _).toLinearMap :=
  rfl
/-
**SemimoduleCat.hom_inv_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_inv_leftUnitor {M : SemimoduleCat.{u} R} : (fun_ M).inv.hom = (TensorP
roduct.lid _ _).symm.toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_inv_leftUnitor {M : SemimoduleCat.{u} R} :
    (λ_ M).inv.hom = (TensorProduct.lid _ _).symm.toLinearMap :=
  rfl
/-
**SemimoduleCat.hom_hom_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_hom_rightUnitor {M : SemimoduleCat.{u} R} : (ρ_ M).hom.hom = (TensorPr
oduct.rid _ _).toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_hom_rightUnitor {M : SemimoduleCat.{u} R} :
    (ρ_ M).hom.hom = (TensorProduct.rid _ _).toLinearMap :=
  rfl
/-
**SemimoduleCat.hom_inv_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_inv_rightUnitor {M : SemimoduleCat.{u} R} : (ρ_ M).inv.hom = (TensorPr
oduct.rid _ _).symm.toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_inv_rightUnitor {M : SemimoduleCat.{u} R} :
    (ρ_ M).inv.hom = (TensorProduct.rid _ _).symm.toLinearMap :=
  rfl
/-
**SemimoduleCat.hom_hom_associator** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_hom_associator {M N K : SemimoduleCat.{u} R} : (α_ M N K).hom.hom = (T
ensorProduct.assoc _ _ _ _).toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_hom_associator {M N K : SemimoduleCat.{u} R} :
    (α_ M N K).hom.hom = (TensorProduct.assoc _ _ _ _).toLinearMap :=
  rfl
/-
**SemimoduleCat.hom_inv_associator** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_inv_associator {M N K : SemimoduleCat.{u} R} : (α_ M N K).inv.hom = (T
ensorProduct.assoc _ _ _ _).symm.toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_inv_associator {M N K : SemimoduleCat.{u} R} :
    (α_ M N K).inv.hom = (TensorProduct.assoc _ _ _ _).symm.toLinearMap :=
  rfl

namespace MonoidalCategory

@[simp]
/-
**SemimoduleCat.MonoidalCategory.tensorHom_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Semim
oduleCat.MonoidalCategory`。
形式化陈述：tensorHom_tmul {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k 
: K) (m : M) : (f otimesₘ g) (k otimesₜ m) = f k otimesₜ g m
参数：f : K ⟶ L；g : M ⟶ N；k : K；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorHom_tmul {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ₘ g) (k ⊗ₜ m) = f k ⊗ₜ g m :=
  rfl

@[simp]
/-
**SemimoduleCat.MonoidalCategory.whiskerLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `Se
mimoduleCat.MonoidalCategory`。
形式化陈述：whiskerLeft_apply (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f
 : M ⟶ N) (l : L) (m : M) : (L ◁ f) (l otimesₜ m) = l otimesₜ f m
参数：L : SemimoduleCat.{u} R；f : M ⟶ N；l : L；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerLeft_apply (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f : M ⟶ N)
    (l : L) (m : M) :
    (L ◁ f) (l ⊗ₜ m) = l ⊗ₜ f m :=
  rfl

@[simp]
/-
**SemimoduleCat.MonoidalCategory.whiskerRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `S
emimoduleCat.MonoidalCategory`。
形式化陈述：whiskerRight_apply {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : Semimodule
Cat.{u} R) (l : L) (n : N) : (f ▷ N) (l otimesₜ n) = f l otimesₜ n
参数：f : L ⟶ M；N : SemimoduleCat.{u} R；l : L；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerRight_apply {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCat.{u} R)
    (l : L) (n : N) :
    (f ▷ N) (l ⊗ₜ n) = f l ⊗ₜ n :=
  rfl

@[simp]
/-
**SemimoduleCat.MonoidalCategory.leftUnitor_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 
`SemimoduleCat.MonoidalCategory`。
形式化陈述：leftUnitor_hom_apply {M : SemimoduleCat.{u} R} (r : R) (m : M) : ((fun_ M)
.hom : 𝟙_ (SemimoduleCat R) otimes M ⟶ M) (r otimesₜ[R] m) = r • m
参数：r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.lid_tmul`：lid_tmul (m : M) (r : R) : (TensorProduct.lid R 
M : R otimes M -> M) (r otimesₜ m) = r • m
-/
theorem leftUnitor_hom_apply {M : SemimoduleCat.{u} R} (r : R) (m : M) :
    ((λ_ M).hom : 𝟙_ (SemimoduleCat R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

@[simp]
/-
**SemimoduleCat.MonoidalCategory.leftUnitor_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 
`SemimoduleCat.MonoidalCategory`。
形式化陈述：leftUnitor_inv_apply {M : SemimoduleCat.{u} R} (m : M) : ((fun_ M).inv : M
 ⟶ 𝟙_ (SemimoduleCat.{u} R) otimes M) m = 1 otimesₜ[R] m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.lid_symm_apply`：lid_symm_apply (m : M) : (TensorProduct.li
d R M).symm m = 1 otimesₜ m
-/
theorem leftUnitor_inv_apply {M : SemimoduleCat.{u} R} (m : M) :
    ((λ_ M).inv : M ⟶ 𝟙_ (SemimoduleCat.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m

@[simp]
/-
**SemimoduleCat.MonoidalCategory.rightUnitor_hom_apply** 是 Mathlib 中的一个定理，位于命名空间
 `SemimoduleCat.MonoidalCategory`。
形式化陈述：rightUnitor_hom_apply {M : SemimoduleCat.{u} R} (m : M) (r : R) : ((ρ_ M).
hom : M otimes 𝟙_ (SemimoduleCat R) ⟶ M) (m otimesₜ r) = r • m
参数：m : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.rid_tmul`：rid_tmul (m : M) (r : R) : (TensorProduct.rid R 
M) (m otimesₜ r) = r • m
-/
theorem rightUnitor_hom_apply {M : SemimoduleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).hom : M ⊗ 𝟙_ (SemimoduleCat R) ⟶ M) (m ⊗ₜ r) = r • m :=
  TensorProduct.rid_tmul m r

@[simp]
/-
**SemimoduleCat.MonoidalCategory.rightUnitor_inv_apply** 是 Mathlib 中的一个定理，位于命名空间
 `SemimoduleCat.MonoidalCategory`。
形式化陈述：rightUnitor_inv_apply {M : SemimoduleCat.{u} R} (m : M) : ((ρ_ M).inv : M 
⟶ M otimes 𝟙_ (SemimoduleCat.{u} R)) m = m otimesₜ[R] 1
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.rid_symm_apply`：rid_symm_apply (m : M) : (TensorProduct.ri
d R M).symm m = m otimesₜ 1
-/
theorem rightUnitor_inv_apply {M : SemimoduleCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (SemimoduleCat.{u} R)) m = m ⊗ₜ[R] 1 :=
  TensorProduct.rid_symm_apply m

@[simp]
/-
**SemimoduleCat.MonoidalCategory.associator_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 
`SemimoduleCat.MonoidalCategory`。
形式化陈述：associator_hom_apply {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K)
 : ((α_ M N K).hom : (M otimes N) otimes K ⟶ M otimes N otimes K) (m otimesₜ n o
timesₜ k) = m otimesₜ (n otimesₜ k)
参数：m : M；n : N；k : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_hom_apply {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).hom : (M ⊗ N) ⊗ K ⟶ M ⊗ N ⊗ K) (m ⊗ₜ n ⊗ₜ k) = m ⊗ₜ (n ⊗ₜ k) :=
  rfl

@[simp]
/-
**SemimoduleCat.MonoidalCategory.associator_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 
`SemimoduleCat.MonoidalCategory`。
形式化陈述：associator_inv_apply {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K)
 : ((α_ M N K).inv : M otimes N otimes K ⟶ (M otimes N) otimes K) (m otimesₜ (n 
otimesₜ k)) = m otimesₜ n otimesₜ k
参数：m : M；n : N；k : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_inv_apply {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M ⊗ N ⊗ K ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = m ⊗ₜ n ⊗ₜ k :=
  rfl

variable {M₁ M₂ M₃ M₄ : SemimoduleCat.{u} R}

section

variable (f : M₁ → M₂ → M₃) (h₁ : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (h₂ : ∀ (a : R) m n, f (a • m) n = a • f m n)
  (h₃ : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (h₄ : ∀ (a : R) m n, f m (a • n) = a • f m n)

/-- Construct for morphisms from the tensor product of two objects in `SemimoduleCat`. -/
/-
**SemimoduleCat.MonoidalCategory.tensorLift** 是 Mathlib 中的一个定义，位于命名空间 `Semimodul
eCat.MonoidalCategory`。
形式化陈述：tensorLift : M₁ otimes M₂ ⟶ M₃
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct for morphisms from the tensor product of two objects in `SemimoduleCat
`.
-/
def tensorLift : M₁ ⊗ M₂ ⟶ M₃ :=
  ofHom <| TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄)

@[simp]
/-
**SemimoduleCat.MonoidalCategory.tensorLift_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Semi
moduleCat.MonoidalCategory`。
形式化陈述：tensorLift_tmul (m : M₁) (n : M₂) : tensorLift f h₁ h₂ h₃ h₄ (m otimesₜ n)
 = f m n
参数：m : M₁；n : M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorLift_tmul (m : M₁) (n : M₂) :
    tensorLift f h₁ h₂ h₃ h₄ (m ⊗ₜ n) = f m n := rfl

end

/-
**SemimoduleCat.MonoidalCategory.tensor_ext** 是 Mathlib 中的一个引理，位于命名空间 `Semimodul
eCat.MonoidalCategory`。
形式化陈述：tensor_ext {f g : M₁ otimes M₂ ⟶ M₃} (h : forall m n, f.hom (m otimesₜ n) 
= g.hom (m otimesₜ n)) : f = g
参数：h : forall m n, f.hom (m otimesₜ n) = g.hom (m otimesₜ n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma tensor_ext {f g : M₁ ⊗ M₂ ⟶ M₃} (h : ∀ m n, f.hom (m ⊗ₜ n) = g.hom (m ⊗ₜ n)) :
    f = g :=
  hom_ext <| TensorProduct.ext (by ext; apply h)

/-- Extensionality lemma for morphisms from a module of the form `(M₁ ⊗ M₂) ⊗ M₃`. -/
/-
**SemimoduleCat.MonoidalCategory.tensor_ext** 是 Mathlib 中的一个引理，位于命名空间 `Semimodul
eCat.MonoidalCategory`。
形式化陈述：tensor_ext {f g : M₁ otimes M₂ ⟶ M₃} (h : forall m n, f.hom (m otimesₜ n) 
= g.hom (m otimesₜ n)) : f = g
参数：h : forall m n, f.hom (m otimesₜ n) = g.hom (m otimesₜ n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g

--- 原说明 ---
Extensionality lemma for morphisms from a module of the form `(M₁ ⊗ M₂) ⊗ M₃`.
-/
lemma tensor_ext₃' {f g : (M₁ ⊗ M₂) ⊗ M₃ ⟶ M₄}
    (h : ∀ m₁ m₂ m₃, f (m₁ ⊗ₜ m₂ ⊗ₜ m₃) = g (m₁ ⊗ₜ m₂ ⊗ₜ m₃)) :
    f = g :=
  hom_ext <| TensorProduct.ext_threefold h

/-- Extensionality lemma for morphisms from a module of the form `M₁ ⊗ (M₂ ⊗ M₃)`. -/
/-
**SemimoduleCat.MonoidalCategory.tensor_ext** 是 Mathlib 中的一个引理，位于命名空间 `Semimodul
eCat.MonoidalCategory`。
形式化陈述：tensor_ext {f g : M₁ otimes M₂ ⟶ M₃} (h : forall m n, f.hom (m otimesₜ n) 
= g.hom (m otimesₜ n)) : f = g
参数：h : forall m n, f.hom (m otimesₜ n) = g.hom (m otimesₜ n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g

--- 原说明 ---
Extensionality lemma for morphisms from a module of the form `M₁ ⊗ (M₂ ⊗ M₃)`.
-/
lemma tensor_ext₃ {f g : M₁ ⊗ (M₂ ⊗ M₃) ⟶ M₄}
    (h : ∀ m₁ m₂ m₃, f (m₁ ⊗ₜ (m₂ ⊗ₜ m₃)) = g (m₁ ⊗ₜ (m₂ ⊗ₜ m₃))) :
    f = g := by
  rw [← cancel_epi (α_ _ _ _).hom]
  exact tensor_ext₃' h

end MonoidalCategory

end SemimoduleCat

namespace ModuleCat

variable {R : Type u} [CommRing R]

@[simps -isSimp]
/-
**ModuleCat.MonoidalCategory.instMonoidalCategoryStruct** 是 Mathlib 中的一个定义，位于命名空
间 `ModuleCat.MonoidalCategory`。
形式化陈述：{R : Type u} → [inst : CommRing R] → CategoryTheory.MonoidalCategoryStruct
 (ModuleCat R)
参数：ModuleCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MonoidalCategory.instMonoidalCategoryStruct :
    MonoidalCategoryStruct (ModuleCat.{u} R) where
  tensorObj M N := of R (TensorProduct R M N)
  whiskerLeft M _ _ f := ofHom <| f.hom.lTensor M
  whiskerRight f M := ofHom <| f.hom.rTensor M
  tensorHom f g := ofHom <| TensorProduct.map f.hom g.hom
  tensorUnit := of R R
  associator M N K := (TensorProduct.assoc R M N K).toModuleIso
  leftUnitor M := (TensorProduct.lid R M).toModuleIso
  rightUnitor M := (TensorProduct.rid R M).toModuleIso
/-
**ModuleCat.monoidalCategory** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：monoidalCategory : MonoidalCategory (ModuleCat.{u} R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidalCategory : MonoidalCategory (ModuleCat.{u} R) :=
  Monoidal.induced equivalenceSemimoduleCat.functor
  { μIso _ _ := .refl _
    εIso := .refl _
    associator_eq _ _ _ := by ext1; exact TensorProduct.ext (TensorProduct.ext rfl)
    leftUnitor_eq _ := by ext1; exact TensorProduct.ext rfl
    rightUnitor_eq _ := by ext1; exact TensorProduct.ext rfl }

open MonoidalCategory

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative ring. -/
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Remind ourselves that the monoidal unit, being just `R`, is still a commutative 
ring.
-/
instance : CommRing ((𝟙_ (ModuleCat.{u} R) : ModuleCat.{u} R) : Type u) :=
  inferInstanceAs <| CommRing R
/-
**ModuleCat.hom_tensorHom** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：hom_tensorHom {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) : (f oti
mesₘ g).hom = TensorProduct.map f.hom g.hom
参数：f : K ⟶ L；g : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_tensorHom {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom :=
  rfl
/-
**ModuleCat.hom_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：hom_whiskerLeft (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) 
: (L ◁ f).hom = f.hom.lTensor L
参数：L : ModuleCat.{u} R；f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_whiskerLeft (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = f.hom.lTensor L :=
  rfl
/-
**ModuleCat.hom_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：hom_whiskerRight {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R)
 : (f ▷ N).hom = f.hom.rTensor N
参数：f : L ⟶ M；N : ModuleCat.{u} R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_whiskerRight {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R) :
    (f ▷ N).hom = f.hom.rTensor N :=
  rfl
/-
**ModuleCat.hom_hom_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：hom_hom_leftUnitor {M : ModuleCat.{u} R} : (fun_ M).hom.hom = (TensorProdu
ct.lid _ _).toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_hom_leftUnitor {M : ModuleCat.{u} R} :
    (λ_ M).hom.hom = (TensorProduct.lid _ _).toLinearMap :=
  rfl
/-
**ModuleCat.hom_inv_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：hom_inv_leftUnitor {M : ModuleCat.{u} R} : (fun_ M).inv.hom = (TensorProdu
ct.lid _ _).symm.toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_inv_leftUnitor {M : ModuleCat.{u} R} :
    (λ_ M).inv.hom = (TensorProduct.lid _ _).symm.toLinearMap :=
  rfl
/-
**ModuleCat.hom_hom_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：hom_hom_rightUnitor {M : ModuleCat.{u} R} : (ρ_ M).hom.hom = (TensorProduc
t.rid _ _).toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_hom_rightUnitor {M : ModuleCat.{u} R} :
    (ρ_ M).hom.hom = (TensorProduct.rid _ _).toLinearMap :=
  rfl
/-
**ModuleCat.hom_inv_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：hom_inv_rightUnitor {M : ModuleCat.{u} R} : (ρ_ M).inv.hom = (TensorProduc
t.rid _ _).symm.toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_inv_rightUnitor {M : ModuleCat.{u} R} :
    (ρ_ M).inv.hom = (TensorProduct.rid _ _).symm.toLinearMap :=
  rfl
/-
**ModuleCat.hom_hom_associator** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：hom_hom_associator {M N K : ModuleCat.{u} R} : (α_ M N K).hom.hom = (Tenso
rProduct.assoc _ _ _ _).toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_hom_associator {M N K : ModuleCat.{u} R} :
    (α_ M N K).hom.hom = (TensorProduct.assoc _ _ _ _).toLinearMap :=
  rfl
/-
**ModuleCat.hom_inv_associator** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：hom_inv_associator {M N K : ModuleCat.{u} R} : (α_ M N K).inv.hom = (Tenso
rProduct.assoc _ _ _ _).symm.toLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_inv_associator {M N K : ModuleCat.{u} R} :
    (α_ M N K).inv.hom = (TensorProduct.assoc _ _ _ _).symm.toLinearMap :=
  rfl

namespace MonoidalCategory

@[simp]
/-
**ModuleCat.MonoidalCategory.tensorHom_tmul** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat
.MonoidalCategory`。
形式化陈述：tensorHom_tmul {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K)
 (m : M) : (f otimesₘ g) (k otimesₜ m) = f k otimesₜ g m
参数：f : K ⟶ L；g : M ⟶ N；k : K；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorHom_tmul {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ₘ g) (k ⊗ₜ m) = f k ⊗ₜ g m :=
  rfl

@[simp]
/-
**ModuleCat.MonoidalCategory.whiskerLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module
Cat.MonoidalCategory`。
形式化陈述：whiskerLeft_apply (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N
) (l : L) (m : M) : (L ◁ f) (l otimesₜ m) = l otimesₜ f m
参数：L : ModuleCat.{u} R；f : M ⟶ N；l : L；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerLeft_apply (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (l : L) (m : M) :
    (L ◁ f) (l ⊗ₜ m) = l ⊗ₜ f m :=
  rfl

@[simp]
/-
**ModuleCat.MonoidalCategory.whiskerRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Modul
eCat.MonoidalCategory`。
形式化陈述：whiskerRight_apply {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} 
R) (l : L) (n : N) : (f ▷ N) (l otimesₜ n) = f l otimesₜ n
参数：f : L ⟶ M；N : ModuleCat.{u} R；l : L；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerRight_apply {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R)
    (l : L) (n : N) :
    (f ▷ N) (l ⊗ₜ n) = f l ⊗ₜ n :=
  rfl

@[simp]
/-
**ModuleCat.MonoidalCategory.leftUnitor_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mod
uleCat.MonoidalCategory`。
形式化陈述：leftUnitor_hom_apply {M : ModuleCat.{u} R} (r : R) (m : M) : ((fun_ M).hom
 : 𝟙_ (ModuleCat R) otimes M ⟶ M) (r otimesₜ[R] m) = r • m
参数：r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.lid_tmul`：lid_tmul (m : M) (r : R) : (TensorProduct.lid R 
M : R otimes M -> M) (r otimesₜ m) = r • m
-/
theorem leftUnitor_hom_apply {M : ModuleCat.{u} R} (r : R) (m : M) :
    ((λ_ M).hom : 𝟙_ (ModuleCat R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

@[simp]
/-
**ModuleCat.MonoidalCategory.leftUnitor_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mod
uleCat.MonoidalCategory`。
形式化陈述：leftUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) : ((fun_ M).inv : M ⟶ 𝟙
_ (ModuleCat.{u} R) otimes M) m = 1 otimesₜ[R] m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.lid_symm_apply`：lid_symm_apply (m : M) : (TensorProduct.li
d R M).symm m = 1 otimesₜ m
-/
theorem leftUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((λ_ M).inv : M ⟶ 𝟙_ (ModuleCat.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m

@[simp]
/-
**ModuleCat.MonoidalCategory.rightUnitor_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mo
duleCat.MonoidalCategory`。
形式化陈述：rightUnitor_hom_apply {M : ModuleCat.{u} R} (m : M) (r : R) : ((ρ_ M).hom 
: M otimes 𝟙_ (ModuleCat R) ⟶ M) (m otimesₜ r) = r • m
参数：m : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.rid_tmul`：rid_tmul (m : M) (r : R) : (TensorProduct.rid R 
M) (m otimesₜ r) = r • m
-/
theorem rightUnitor_hom_apply {M : ModuleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).hom : M ⊗ 𝟙_ (ModuleCat R) ⟶ M) (m ⊗ₜ r) = r • m :=
  TensorProduct.rid_tmul m r

@[simp]
/-
**ModuleCat.MonoidalCategory.rightUnitor_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mo
duleCat.MonoidalCategory`。
形式化陈述：rightUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) : ((ρ_ M).inv : M ⟶ M 
otimes 𝟙_ (ModuleCat.{u} R)) m = m otimesₜ[R] 1
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.rid_symm_apply`：rid_symm_apply (m : M) : (TensorProduct.ri
d R M).symm m = m otimesₜ 1
-/
theorem rightUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (ModuleCat.{u} R)) m = m ⊗ₜ[R] 1 :=
  TensorProduct.rid_symm_apply m

@[simp]
/-
**ModuleCat.MonoidalCategory.associator_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mod
uleCat.MonoidalCategory`。
形式化陈述：associator_hom_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) : (
(α_ M N K).hom : (M otimes N) otimes K ⟶ M otimes N otimes K) (m otimesₜ n otime
sₜ k) = m otimesₜ (n otimesₜ k)
参数：m : M；n : N；k : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_hom_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).hom : (M ⊗ N) ⊗ K ⟶ M ⊗ N ⊗ K) (m ⊗ₜ n ⊗ₜ k) = m ⊗ₜ (n ⊗ₜ k) :=
  rfl

@[simp]
/-
**ModuleCat.MonoidalCategory.associator_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mod
uleCat.MonoidalCategory`。
形式化陈述：associator_inv_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) : (
(α_ M N K).inv : M otimes N otimes K ⟶ (M otimes N) otimes K) (m otimesₜ (n otim
esₜ k)) = m otimesₜ n otimesₜ k
参数：m : M；n : N；k : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_inv_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M ⊗ N ⊗ K ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = m ⊗ₜ n ⊗ₜ k :=
  rfl

variable {M₁ M₂ M₃ M₄ : ModuleCat.{u} R}

section

variable (f : M₁ → M₂ → M₃) (h₁ : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (h₂ : ∀ (a : R) m n, f (a • m) n = a • f m n)
  (h₃ : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (h₄ : ∀ (a : R) m n, f m (a • n) = a • f m n)

/-- Construct for morphisms from the tensor product of two objects in `ModuleCat`. -/
/-
**ModuleCat.MonoidalCategory.tensorLift** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Mon
oidalCategory`。
形式化陈述：tensorLift : M₁ otimes M₂ ⟶ M₃
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct for morphisms from the tensor product of two objects in `ModuleCat`.
-/
def tensorLift : M₁ ⊗ M₂ ⟶ M₃ :=
  ofHom <| TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄)

@[simp]
/-
**ModuleCat.MonoidalCategory.tensorLift_tmul** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCa
t.MonoidalCategory`。
形式化陈述：tensorLift_tmul (m : M₁) (n : M₂) : tensorLift f h₁ h₂ h₃ h₄ (m otimesₜ n)
 = f m n
参数：m : M₁；n : M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorLift_tmul (m : M₁) (n : M₂) :
    tensorLift f h₁ h₂ h₃ h₄ (m ⊗ₜ n) = f m n := rfl

end

/-
**ModuleCat.MonoidalCategory.tensor_ext** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.Mon
oidalCategory`。
形式化陈述：tensor_ext {f g : M₁ otimes M₂ ⟶ M₃} (h : forall m n, f.hom (m otimesₜ n) 
= g.hom (m otimesₜ n)) : f = g
参数：h : forall m n, f.hom (m otimesₜ n) = g.hom (m otimesₜ n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma tensor_ext {f g : M₁ ⊗ M₂ ⟶ M₃} (h : ∀ m n, f.hom (m ⊗ₜ n) = g.hom (m ⊗ₜ n)) :
    f = g :=
  hom_ext <| TensorProduct.ext (by ext; apply h)

/-- Extensionality lemma for morphisms from a module of the form `(M₁ ⊗ M₂) ⊗ M₃`. -/
/-
**ModuleCat.MonoidalCategory.tensor_ext** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.Mon
oidalCategory`。
形式化陈述：tensor_ext {f g : M₁ otimes M₂ ⟶ M₃} (h : forall m n, f.hom (m otimesₜ n) 
= g.hom (m otimesₜ n)) : f = g
参数：h : forall m n, f.hom (m otimesₜ n) = g.hom (m otimesₜ n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g

--- 原说明 ---
Extensionality lemma for morphisms from a module of the form `(M₁ ⊗ M₂) ⊗ M₃`.
-/
lemma tensor_ext₃' {f g : (M₁ ⊗ M₂) ⊗ M₃ ⟶ M₄}
    (h : ∀ m₁ m₂ m₃, f (m₁ ⊗ₜ m₂ ⊗ₜ m₃) = g (m₁ ⊗ₜ m₂ ⊗ₜ m₃)) :
    f = g :=
  hom_ext <| TensorProduct.ext_threefold h

/-- Extensionality lemma for morphisms from a module of the form `M₁ ⊗ (M₂ ⊗ M₃)`. -/
/-
**ModuleCat.MonoidalCategory.tensor_ext** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.Mon
oidalCategory`。
形式化陈述：tensor_ext {f g : M₁ otimes M₂ ⟶ M₃} (h : forall m n, f.hom (m otimesₜ n) 
= g.hom (m otimesₜ n)) : f = g
参数：h : forall m n, f.hom (m otimesₜ n) = g.hom (m otimesₜ n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g

--- 原说明 ---
Extensionality lemma for morphisms from a module of the form `M₁ ⊗ (M₂ ⊗ M₃)`.
-/
lemma tensor_ext₃ {f g : M₁ ⊗ (M₂ ⊗ M₃) ⟶ M₄}
    (h : ∀ m₁ m₂ m₃, f (m₁ ⊗ₜ (m₂ ⊗ₜ m₃)) = g (m₁ ⊗ₜ (m₂ ⊗ₜ m₃))) :
    f = g := by
  rw [← cancel_epi (α_ _ _ _).hom]
  exact tensor_ext₃' h

end MonoidalCategory

open Opposite

/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalPreadditive (ModuleCat.{u} R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerLeft]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerRight]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerLeft]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerRight]

set_option backward.isDefEq.respectTransparency false in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalLinear R (ModuleCat.{u} R) := by
  refine ⟨?_, ?_⟩
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerLeft]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [ModuleCat.hom_whiskerRight]
/-
**ModuleCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `ModuleCat`。
形式化陈述：ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Modul
e R Y] (f : X ->ₗ[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₗ[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom₂_compr₂ {M N P Q : ModuleCat.{u} R} (f : M →ₗ[R] N →ₗ[R] P) (g : P →ₗ[R] Q) :
    ofHom₂ (f.compr₂ g) = ofHom₂ f ≫ ofHom (Linear.rightComp R _ (ofHom g)) := rfl

end ModuleCat

