/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module

public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# The category of commutative comonoids in a braided monoidal category.

We define the category of commutative comonoid objects in a braided monoidal category `C`.

## Main definitions

* `CommComon C` - The bundled structure of commutative comonoid objects

## Tags

comonoid, commutative, braided
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

variable (C) in
/-- A commutative comonoid object internal to a monoidal category. -/
/-
**CategoryTheory.CommComon** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] → [CategoryTheory.BraidedCategory C] → Ty
pe (max u₁ v₁)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative comonoid object internal to a monoidal category.
-/
structure CommComon where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [comon : ComonObj X]
  [comm : IsCommComonObj X]

attribute [instance] CommComon.comon CommComon.comm

namespace CommComon

/-- A commutative comonoid object is a comonoid object. -/
@[simps X]
/-
**CategoryTheory.CommComon.toComon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Com
mComon`。
形式化陈述：toComon (A : CommComon C) : Comon C
参数：A : CommComon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative comonoid object is a comonoid object.
-/
def toComon (A : CommComon C) : Comon C := ⟨A.X⟩

section

attribute [local instance] ComonObj.instTensorUnit in
/-- The trivial comonoid on the unit object is commutative. -/
/-
**CategoryTheory.CommComon.instCommComonObjUnit** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.CommComon`。
形式化陈述：instCommComonObjUnit : IsCommComonObj (𝟙_ C) where comul_comm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.braiding_tensorUnit_right`：braiding_tensorUnit_right (X :
 C) : (β_ X (𝟙_ C)).hom = (ρ_ X).hom ≫ (fun_ X).inv
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The trivial comonoid on the unit object is commutative.
-/
instance instCommComonObjUnit : IsCommComonObj (𝟙_ C) where
  comul_comm := by simp [← unitors_equal]

end

attribute [local instance] ComonObj.instTensorUnit in
variable (C) in
/-- The trivial commutative comonoid object. We later show this is initial in `CommComon C`. -/
@[simps!]
/-
**CategoryTheory.CommComon.trivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Com
mComon`。
形式化陈述：trivial : CommComon C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial commutative comonoid object. We later show this is initial in `CommC
omon C`.
-/
def trivial : CommComon C := mk (𝟙_ C)
/-
**CategoryTheory.CommComon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommComon`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CommComon C) :=
  ⟨trivial C⟩

variable {M : CommComon C}
/-
**CategoryTheory.CommComon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommComon`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (CommComon C) :=
  inferInstanceAs (Category (InducedCategory _ CommComon.toComon))

@[simp]
/-
**CategoryTheory.CommComon.id_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comm
Comon`。
形式化陈述：id_hom (A : CommComon C) : Comon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) =
 𝟙 A.X
参数：A : CommComon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_hom (A : CommComon C) : Comon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X :=
  rfl

@[simp]
/-
**CategoryTheory.CommComon.comp_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Co
mmComon`。
形式化陈述：comp_hom {R S T : CommComon C} (f : R ⟶ S) (g : S ⟶ T) : Comon.Hom.hom (f 
≫ g).hom = f.hom.hom ≫ g.hom.hom
参数：f : R ⟶ S；g : S ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom {R S T : CommComon C} (f : R ⟶ S) (g : S ⟶ T) :
    Comon.Hom.hom (f ≫ g).hom = f.hom.hom ≫ g.hom.hom :=
  rfl

@[ext]
/-
**CategoryTheory.CommComon.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Com
mComon`。
形式化陈述：hom_ext {A B : CommComon C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom) : f 
= g
参数：f g : A ⟶ B；h : f.hom.hom = g.hom.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.Comon.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cat
egory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {M N : Category
Theory.Comon C} {x…
-/
lemma hom_ext {A B : CommComon C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (Comon.Hom.ext h)

section

variable (C)

/-- The forgetful functor from commutative comonoid objects to comonoid objects. -/
@[simps!]
/-
**CategoryTheory.CommComon.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comm
Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from commutative comonoid objects to comonoid objects.
-/
def forget₂Comon : CommComon C ⥤ Comon C :=
  inducedFunctor _

end

end CommComon

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type*} [Category* C] [MonoidalCategory C] [SymmetricCategory C]
    (A B : C) [ComonObj A] [ComonObj B]
    [IsCommComonObj A] [IsCommComonObj B] : IsCommComonObj (A ⊗ B) where
  comul_comm := by
    rw [Comon.tensorObj_comul, Category.assoc, SymmetricCategory.tensorμ_braid_swap]
    simp

end CategoryTheory

