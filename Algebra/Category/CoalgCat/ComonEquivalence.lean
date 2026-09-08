/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.CoalgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.Tactic.SuppressCompilation

/-!
# The category equivalence between `R`-coalgebras and comonoid objects in `R-Mod`

Given a commutative ring `R`, this file defines the equivalence of categories between
`R`-coalgebras and comonoid objects in the category of `R`-modules.

We then use this to set up boilerplate for the `Coalgebra` instance on a tensor product of
coalgebras defined in `Mathlib/RingTheory/Coalgebra/TensorProduct.lean`.

## Implementation notes

We make the definition `CoalgCat.instMonoidalCategoryAux` in this file, which is the
monoidal structure on `CoalgCat` induced by the equivalence with `Comon(R-Mod)`. We
use this to show the comultiplication and counit on a tensor product of coalgebras satisfy
the coalgebra axioms, but our actual `MonoidalCategory` instance on `CoalgCat` is
constructed in `Mathlib/Algebra/Category/CoalgCat/Monoidal.lean` to have better
definitional equalities.

-/

@[expose] public section

suppress_compilation

universe v u

namespace CoalgCat

open CategoryTheory MonoidalCategory ComonObj

variable {R : Type u} [CommRing R]

@[simps counit comul]
/-
**CoalgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CoalgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (X : CoalgCat R) : ComonObj (ModuleCat.of R X) where
  counit := ModuleCat.ofHom Coalgebra.counit
  comul := ModuleCat.ofHom Coalgebra.comul
  counit_comul := ModuleCat.hom_ext <| by simpa using! Coalgebra.rTensor_counit_comp_comul
  comul_counit := ModuleCat.hom_ext <| by simpa using! Coalgebra.lTensor_counit_comp_comul
  comul_assoc := ModuleCat.hom_ext <| by simp_rw [ModuleCat.of_coe]; exact Coalgebra.coassoc.symm

/-- An `R`-coalgebra is a comonoid object in the category of `R`-modules. -/
@[simps X]
/-
**CoalgCat.toComonObj** 是 Mathlib 中的一个定义，位于命名空间 `CoalgCat`。
形式化陈述：toComonObj (X : CoalgCat R) : Comon (ModuleCat R)
参数：X : CoalgCat R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-coalgebra is a comonoid object in the category of `R`-modules.
-/
noncomputable def toComonObj (X : CoalgCat R) : Comon (ModuleCat R) := ⟨ModuleCat.of R X⟩

variable (R) in
/-- The natural functor from `R`-coalgebras to comonoid objects in the category of `R`-modules. -/
@[simps]
/-
**CoalgCat.toComon** 是 Mathlib 中的一个定义，位于命名空间 `CoalgCat`。
形式化陈述：toComon : CoalgCat R ⥤ Comon (ModuleCat R) where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural functor from `R`-coalgebras to comonoid objects in the category of `
R`-modules.
-/
def toComon : CoalgCat R ⥤ Comon (ModuleCat R) where
  obj X := toComonObj X
  map f :=
    { hom := ModuleCat.ofHom f.1
      isComonHom_hom :=
        { hom_counit := ModuleCat.hom_ext f.1.counit_comp
          hom_comul := ModuleCat.hom_ext f.1.map_comp_comul.symm } }

/-- A comonoid object in the category of `R`-modules has a natural comultiplication
and counit. -/
@[simps]
/-
**CoalgCat.ofComonObjCoalgebraStruct** 是 Mathlib 中的一个实例，位于命名空间 `CoalgCat`。
形式化陈述：ofComonObjCoalgebraStruct (X : ModuleCat R) [ComonObj X] : CoalgebraStruct
 R X where comul
参数：X : ModuleCat R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A comonoid object in the category of `R`-modules has a natural comultiplication
and counit.
-/
noncomputable instance ofComonObjCoalgebraStruct (X : ModuleCat R) [ComonObj X] :
    CoalgebraStruct R X where
  comul := Δ[X].hom
  counit := ε[X].hom

/-- A comonoid object in the category of `R`-modules has a natural `R`-coalgebra
structure. -/
/-
**CoalgCat.ofComonObj** 是 Mathlib 中的一个定义，位于命名空间 `CoalgCat`。
形式化陈述：ofComonObj (X : ModuleCat R) [ComonObj X] : CoalgCat R
参数：X : ModuleCat R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A comonoid object in the category of `R`-modules has a natural `R`-coalgebra
structure.
-/
noncomputable def ofComonObj (X : ModuleCat R) [ComonObj X] : CoalgCat R :=
  { ModuleCat.of R X with
    instCoalgebra :=
      { ofComonObjCoalgebraStruct X with
        coassoc := ModuleCat.hom_ext_iff.mp (comul_assoc X).symm
        rTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp (counit_comul X)
        lTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp (comul_counit X) } }

variable (R)

/-- The natural functor from comonoid objects in the category of `R`-modules to `R`-coalgebras. -/
/-
**CoalgCat.ofComon** 是 Mathlib 中的一个定义，位于命名空间 `CoalgCat`。
形式化陈述：ofComon : Comon (ModuleCat R) ⥤ CoalgCat R where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural functor from comonoid objects in the category of `R`-modules to `R`-
coalgebras.
-/
noncomputable def ofComon : Comon (ModuleCat R) ⥤ CoalgCat R where
  obj X := ofComonObj X.X
  map f :=
    { toCoalgHom' :=
      { f.hom.hom with
        counit_comp := ModuleCat.hom_ext_iff.mp (IsComonHom.hom_counit f.hom)
        map_comp_comul := ModuleCat.hom_ext_iff.mp ((IsComonHom.hom_comul f.hom).symm) } }

/-- The natural category equivalence between `R`-coalgebras and comonoid objects in the
category of `R`-modules. -/
@[simps]
/-
**CoalgCat.comonEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CoalgCat`。
形式化陈述：comonEquivalence : CoalgCat R ≌ Comon (ModuleCat R) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural category equivalence between `R`-coalgebras and comonoid objects in 
the
category of `R`-modules.
-/
def comonEquivalence : CoalgCat R ≌ Comon (ModuleCat R) where
  functor := toComon R
  inverse := ofComon R
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl

variable {R}

/-- The monoidal category structure on the category of `R`-coalgebras induced by the
equivalence with `Comon(R-Mod)`. This is just an auxiliary definition; the `MonoidalCategory`
instance we make in `Mathlib/Algebra/Category/CoalgCat/Monoidal.lean` has better
definitional equalities. -/
@[instance_reducible]
/-
**CoalgCat.instMonoidalCategoryAux** 是 Mathlib 中的一个定义，位于命名空间 `CoalgCat`。
形式化陈述：instMonoidalCategoryAux : MonoidalCategory (CoalgCat R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal category structure on the category of `R`-coalgebras induced by the
equivalence with `Comon(R-Mod)`. This is just an auxiliary definition; the `Mono
idalCategory`
instance we make in `Mathlib/Algebra/Category/CoalgCat/Monoidal.lean` has better
definitional equalities.
-/
noncomputable def instMonoidalCategoryAux : MonoidalCategory (CoalgCat R) :=
  Monoidal.transport (comonEquivalence R).symm

namespace MonoidalCategoryAux

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

attribute [local instance] instMonoidalCategoryAux

open MonoidalCategory ModuleCat.MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
/-
**CoalgCat.MonoidalCategoryAux.tensorObj_comul** 是 Mathlib 中的一个定理，位于命名空间 `CoalgC
at.MonoidalCategoryAux`。
形式化陈述：tensorObj_comul (K L : CoalgCat R) : Coalgebra.comul (R
参数：K L : CoalgCat R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoalgCat.ofComonObjCoalgebraStruct_comul`：∀ {R : Type u} [inst : CommRin
g R] (X : ModuleCat R) [inst_1 : CategoryTheory.ComonObj X],   CoalgebraStruct.c
omul = ModuleCat.Hom.hom Categ…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Comon.monoidal_tensorObj_comon_comul`：∀ (C : Type u₁) [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C]   [inst_2 : CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.BraidedCategory.unop_tensorμ`：∀ {C : Type u_2} [inst : Ca
tegoryTheory.Category.{v_2, u_2} C] [inst_1 : CategoryTheory.MonoidalCategory C]
   [inst_2 : CategoryTheory.Braid…
· 使用定理 `ModuleCat.MonoidalCategory.tensorμ_eq_tensorTensorTensorComm`：tensorμ_eq
_tensorTensorTensorComm {A B C D : ModuleCat R} : tensorμ A B C D = ofHom (Tenso
rProduct.tensorTensorTensorComm R A B C D).toLinea…
-/
theorem tensorObj_comul (K L : CoalgCat R) :
    Coalgebra.comul (R := R) (A := (K ⊗ L : CoalgCat R))
      = (TensorProduct.tensorTensorTensorComm R K K L L).toLinearMap
      ∘ₗ TensorProduct.map Coalgebra.comul Coalgebra.comul := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp only [Comon.monoidal_tensorObj_comon_comul,
    MonObj.tensorObj.mul_def, unop_comp, unop_tensorObj, unop_tensorHom,
    BraidedCategory.unop_tensorμ, tensorμ_eq_tensorTensorTensorComm, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom]
  rfl
/-
**CoalgCat.MonoidalCategoryAux.tensorHom_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `
CoalgCat.MonoidalCategoryAux`。
形式化陈述：tensorHom_toLinearMap (f : M ->ₗc[R] N) (g : P ->ₗc[R] Q) : (CoalgCat.ofHo
m f otimesₘ CoalgCat.ofHom g).1.toLinearMap = TensorProduct.map f.toLinearMap g.
toLinearMap
参数：f : M ->ₗc[R] N；g : P ->ₗc[R] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorHom_toLinearMap (f : M →ₗc[R] N) (g : P →ₗc[R] Q) :
    (CoalgCat.ofHom f ⊗ₘ CoalgCat.ofHom g).1.toLinearMap
      = TensorProduct.map f.toLinearMap g.toLinearMap := rfl
/-
**CoalgCat.MonoidalCategoryAux.associator_hom_toLinearMap** 是 Mathlib 中的一个定理，位于命
名空间 `CoalgCat.MonoidalCategoryAux`。
形式化陈述：associator_hom_toLinearMap : (α_ (CoalgCat.of R M) (CoalgCat.of R N) (Coal
gCat.of R P)).hom.1.toLinearMap = (TensorProduct.assoc R M N P).toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem associator_hom_toLinearMap :
    (α_ (CoalgCat.of R M) (CoalgCat.of R N) (CoalgCat.of R P)).hom.1.toLinearMap
      = (TensorProduct.assoc R M N P).toLinearMap :=
  TensorProduct.ext <| TensorProduct.ext <| by ext; rfl
/-
**CoalgCat.MonoidalCategoryAux.leftUnitor_hom_toLinearMap** 是 Mathlib 中的一个定理，位于命
名空间 `CoalgCat.MonoidalCategoryAux`。
形式化陈述：leftUnitor_hom_toLinearMap : (fun_ (CoalgCat.of R M)).hom.1.toLinearMap = 
(TensorProduct.lid R M).toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem leftUnitor_hom_toLinearMap :
    (λ_ (CoalgCat.of R M)).hom.1.toLinearMap = (TensorProduct.lid R M).toLinearMap :=
  TensorProduct.ext <| by ext; rfl
/-
**CoalgCat.MonoidalCategoryAux.rightUnitor_hom_toLinearMap** 是 Mathlib 中的一个定理，位于
命名空间 `CoalgCat.MonoidalCategoryAux`。
形式化陈述：rightUnitor_hom_toLinearMap : (ρ_ (CoalgCat.of R M)).hom.1.toLinearMap = (
TensorProduct.rid R M).toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
-/
theorem rightUnitor_hom_toLinearMap :
    (ρ_ (CoalgCat.of R M)).hom.1.toLinearMap = (TensorProduct.rid R M).toLinearMap :=
  TensorProduct.ext <| by ext; rfl

open TensorProduct

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
/-
**CoalgCat.MonoidalCategoryAux.comul_tensorObj** 是 Mathlib 中的一个定理，位于命名空间 `CoalgC
at.MonoidalCategoryAux`。
形式化陈述：comul_tensorObj : Coalgebra.comul (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoalgCat.ofComonObjCoalgebraStruct_comul`：∀ {R : Type u} [inst : CommRin
g R] (X : ModuleCat R) [inst_1 : CategoryTheory.ComonObj X],   CoalgebraStruct.c
omul = ModuleCat.Hom.hom Categ…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Comon.monoidal_tensorObj_comon_comul`：∀ (C : Type u₁) [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C]   [inst_2 : CategoryTheory.BraidedC…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Comon.ComonToMonOpOpObj_mon_mul`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]
   (A : CategoryTheory.Comon C), Cat…
· 使用定理 `CategoryTheory.BraidedCategory.unop_tensorμ`：∀ {C : Type u_2} [inst : Ca
tegoryTheory.Category.{v_2, u_2} C] [inst_1 : CategoryTheory.MonoidalCategory C]
   [inst_2 : CategoryTheory.Braid…
· 使用定理 `ModuleCat.MonoidalCategory.tensorμ_eq_tensorTensorTensorComm`：tensorμ_eq
_tensorTensorTensorComm {A B C D : ModuleCat R} : tensorμ A B C D = ofHom (Tenso
rProduct.tensorTensorTensorComm R A B C D).toLinea…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
-/
theorem comul_tensorObj :
    Coalgebra.comul (R := R) (A := (CoalgCat.of R M ⊗ CoalgCat.of R N : CoalgCat R))
      = Coalgebra.comul (A := M ⊗[R] N) := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
/-
**CoalgCat.MonoidalCategoryAux.comul_tensorObj_tensorObj_right** 是 Mathlib 中的一个定
理，位于命名空间 `CoalgCat.MonoidalCategoryAux`。
形式化陈述：comul_tensorObj_tensorObj_right : Coalgebra.comul (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoalgCat.ofComonObjCoalgebraStruct_comul`：∀ {R : Type u} [inst : CommRin
g R] (X : ModuleCat R) [inst_1 : CategoryTheory.ComonObj X],   CoalgebraStruct.c
omul = ModuleCat.Hom.hom Categ…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Comon.monoidal_tensorObj_comon_comul`：∀ (C : Type u₁) [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C]   [inst_2 : CategoryTheory.BraidedC…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Comon.ComonToMonOpOpObj_mon_mul`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]
   (A : CategoryTheory.Comon C), Cat…
· 使用定理 `CategoryTheory.BraidedCategory.unop_tensorμ`：∀ {C : Type u_2} [inst : Ca
tegoryTheory.Category.{v_2, u_2} C] [inst_1 : CategoryTheory.MonoidalCategory C]
   [inst_2 : CategoryTheory.Braid…
· 使用定理 `ModuleCat.MonoidalCategory.tensorμ_eq_tensorTensorTensorComm`：tensorμ_eq
_tensorTensorTensorComm {A B C D : ModuleCat R} : tensorμ A B C D = ofHom (Tenso
rProduct.tensorTensorTensorComm R A B C D).toLinea…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
-/
theorem comul_tensorObj_tensorObj_right :
    Coalgebra.comul (R := R) (A := (CoalgCat.of R M ⊗
      (CoalgCat.of R N ⊗ CoalgCat.of R P) : CoalgCat R))
      = Coalgebra.comul (A := M ⊗[R] (N ⊗[R] P)) := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp only [Comon.monoidal_tensorObj_comon_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
/-
**CoalgCat.MonoidalCategoryAux.comul_tensorObj_tensorObj_left** 是 Mathlib 中的一个定理
，位于命名空间 `CoalgCat.MonoidalCategoryAux`。
形式化陈述：comul_tensorObj_tensorObj_left : Coalgebra.comul (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoalgCat.ofComonObjCoalgebraStruct_comul`：∀ {R : Type u} [inst : CommRin
g R] (X : ModuleCat R) [inst_1 : CategoryTheory.ComonObj X],   CoalgebraStruct.c
omul = ModuleCat.Hom.hom Categ…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.BraidedCategory.unop_tensorμ`：∀ {C : Type u_2} [inst : Ca
tegoryTheory.Category.{v_2, u_2} C] [inst_1 : CategoryTheory.MonoidalCategory C]
   [inst_2 : CategoryTheory.Braid…
· 使用定理 `ModuleCat.MonoidalCategory.tensorμ_eq_tensorTensorTensorComm`：tensorμ_eq
_tensorTensorTensorComm {A B C D : ModuleCat R} : tensorμ A B C D = ofHom (Tenso
rProduct.tensorTensorTensorComm R A B C D).toLinea…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
-/
theorem comul_tensorObj_tensorObj_left :
    Coalgebra.comul (R := R)
      (A := ((CoalgCat.of R M ⊗ CoalgCat.of R N) ⊗ CoalgCat.of R P : CoalgCat R))
      = Coalgebra.comul (A := M ⊗[R] N ⊗[R] P) := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CoalgCat.MonoidalCategoryAux.counit_tensorObj** 是 Mathlib 中的一个定理，位于命名空间 `Coalg
Cat.MonoidalCategoryAux`。
形式化陈述：counit_tensorObj : Coalgebra.counit (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoalgCat.ofComonObjCoalgebraStruct_counit`：∀ {R : Type u} [inst : CommRi
ng R] (X : ModuleCat R) [inst_1 : CategoryTheory.ComonObj X],   CoalgebraStruct.
counit = ModuleCat.Hom.hom Cate…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Comon.MonOpOpToComonObj_comon_counit`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C]   (A : CategoryTheory.Mon Cᵒᵖ), Cat…
· 使用定理 `CategoryTheory.Comon.ComonToMonOpOpObj_mon_one`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]
   (A : CategoryTheory.Comon C), Cat…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
-/
theorem counit_tensorObj :
    Coalgebra.counit (R := R) (A := (CoalgCat.of R M ⊗ CoalgCat.of R N : CoalgCat R))
      = Coalgebra.counit (A := M ⊗[R] N) := by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CoalgCat.MonoidalCategoryAux.counit_tensorObj_tensorObj_right** 是 Mathlib 中的一个
定理，位于命名空间 `CoalgCat.MonoidalCategoryAux`。
形式化陈述：counit_tensorObj_tensorObj_right : Coalgebra.counit (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoalgCat.ofComonObjCoalgebraStruct_counit`：∀ {R : Type u} [inst : CommRi
ng R] (X : ModuleCat R) [inst_1 : CategoryTheory.ComonObj X],   CoalgebraStruct.
counit = ModuleCat.Hom.hom Cate…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Comon.MonOpOpToComonObj_comon_counit`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C]   (A : CategoryTheory.Mon Cᵒᵖ), Cat…
· 使用定理 `CategoryTheory.Comon.ComonToMonOpOpObj_mon_one`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]
   (A : CategoryTheory.Comon C), Cat…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
-/
theorem counit_tensorObj_tensorObj_right :
    Coalgebra.counit (R := R)
      (A := (CoalgCat.of R M ⊗ (CoalgCat.of R N ⊗ CoalgCat.of R P) : CoalgCat R))
      = Coalgebra.counit (A := M ⊗[R] (N ⊗[R] P)) := by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CoalgCat.MonoidalCategoryAux.counit_tensorObj_tensorObj_left** 是 Mathlib 中的一个定
理，位于命名空间 `CoalgCat.MonoidalCategoryAux`。
形式化陈述：counit_tensorObj_tensorObj_left : Coalgebra.counit (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoalgCat.ofComonObjCoalgebraStruct_counit`：∀ {R : Type u} [inst : CommRi
ng R] (X : ModuleCat R) [inst_1 : CategoryTheory.ComonObj X],   CoalgebraStruct.
counit = ModuleCat.Hom.hom Cate…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Comon.MonOpOpToComonObj_comon_counit`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C]   (A : CategoryTheory.Mon Cᵒᵖ), Cat…
· 使用定理 `CategoryTheory.Comon.ComonToMonOpOpObj_mon_one`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]
   (A : CategoryTheory.Comon C), Cat…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
-/
theorem counit_tensorObj_tensorObj_left :
    Coalgebra.counit (R := R)
      (A := ((CoalgCat.of R M ⊗ CoalgCat.of R N) ⊗ CoalgCat.of R P : CoalgCat R))
      = Coalgebra.counit (A := (M ⊗[R] N) ⊗[R] P) := by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

end CoalgCat.MonoidalCategoryAux

