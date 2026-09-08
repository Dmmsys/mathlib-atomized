/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.HomCongr

/-!
# Reflective functors

Basic properties of reflective functors, especially those relating to their essential image.

Note properties of reflective functors relating to limits and colimits are included in
`Mathlib/CategoryTheory/Monad/Limits.lean`.
-/

@[expose] public section


universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Category Adjunction

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/--
A functor is *reflective*, or *a reflective inclusion*, if it is fully faithful and right adjoint.
-/
/-
**CategoryTheory.Reflective** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor D C → Type (max (max (max u₁ u₂) v₁) v₂)
参数：max (max (max u₁ u₂) v₁) v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is *reflective*, or *a reflective inclusion*, if it is fully faithful 
and right adjoint.
-/
class Reflective (R : D ⥤ C) extends R.Full, R.Faithful where
  /-- a choice of a left adjoint to `R` -/
  L : C ⥤ D
  /-- `R` is a right adjoint -/
  adj : L ⊣ R

variable (i : D ⥤ C)

/-- The reflector `C ⥤ D` when `R : D ⥤ C` is reflective. -/
/-
**CategoryTheory.reflector** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：reflector [Reflective i] : C ⥤ D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reflector `C ⥤ D` when `R : D ⥤ C` is reflective.
-/
def reflector [Reflective i] : C ⥤ D := Reflective.L (R := i)

/-- The adjunction `reflector i ⊣ i` when `i` is reflective. -/
/-
**CategoryTheory.reflectorAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：reflectorAdjunction [Reflective i] : reflector i ⊣ i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `reflector i ⊣ i` when `i` is reflective.
-/
def reflectorAdjunction [Reflective i] : reflector i ⊣ i := Reflective.adj
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Reflective i] : i.IsRightAdjoint := ⟨_, ⟨reflectorAdjunction i⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Reflective i] : (reflector i).IsLeftAdjoint := ⟨_, ⟨reflectorAdjunction i⟩⟩

/-- A reflective functor is fully faithful. -/
/-
**CategoryTheory.Functor.fullyFaithfulOfReflective** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (i : Cat
egoryTheory.Functor D C) → [CategoryTheory.Reflective i] → i.FullyFaithful
参数：i : CategoryTheory.Functor D C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A reflective functor is fully faithful.
-/
def Functor.fullyFaithfulOfReflective [Reflective i] : i.FullyFaithful :=
  (reflectorAdjunction i).fullyFaithfulROfIsIsoCounit

-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
/-- For a reflective functor `i` (with left adjoint `L`), with unit `η`, we have `η_iL = iL η`.
-/
/-
**CategoryTheory.unit_obj_eq_map_unit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：unit_obj_eq_map_unit [Reflective i] (X : C) : (reflectorAdjunction i).unit
.app (i.obj ((reflector i).obj X)) = i.map ((reflector i).map ((reflectorAdjunct
ion i).unit.app X))
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instIsRightAdjointOfReflective`：∀ {C : Type u₁} {D : Type
 u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   (i : CategoryTheor…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Reflective.toFull`：∀ {C : Type u₁} {D : Type u₂} {inst : 
CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {R : CategoryTheor…
· 使用定理 `CategoryTheory.Reflective.toFaithful`：∀ {C : Type u₁} {D : Type u₂} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u
₂} D}   {R : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For a reflective functor `i` (with left adjoint `L`), with unit `η`, we have `η_
iL = iL η`.
-/
theorem unit_obj_eq_map_unit [Reflective i] (X : C) :
    (reflectorAdjunction i).unit.app (i.obj ((reflector i).obj X)) =
      i.map ((reflector i).map ((reflectorAdjunction i).unit.app X)) := by
  rw [← cancel_mono (i.map ((reflectorAdjunction i).counit.app ((reflector i).obj X))),
    ← i.map_comp]
  simp

/--
When restricted to objects in `D` given by `i : D ⥤ C`, the unit is an isomorphism. In other words,
`η_iX` is an isomorphism for any `X` in `D`.
More generally this applies to objects essentially in the reflective subcategory, see
`Functor.essImage.unit_isIso`.
-/
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When restricted to objects in `D` given by `i : D ⥤ C`, the unit is an isomorphi
sm. In other words,
`η_iX` is an isomorphism for any `X` in `D`.
More generally this applies to objects essentially in the reflective subcategory
, see
`Functor.essImage.unit_isIso`.
-/
example [Reflective i] {B : D} : IsIso ((reflectorAdjunction i).unit.app (i.obj B)) :=
  inferInstance

variable {i}

/-- If `A` is essentially in the image of a reflective functor `i`, then `η_A` is an isomorphism.
This gives that the "witness" for `A` being in the essential image can instead be given as the
reflection of `A`, with the isomorphism as `η_A`.

(For any `B` in the reflective subcategory, we automatically have that `ε_B` is an iso.)
-/
/-
**CategoryTheory.Functor.essImage.unit_isIso** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor.essImage`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {i : CategoryTheory.Functor D C}
 [inst_2 : CategoryTheory.Reflective i] {A : C},   i.essImage A → CategoryTheory
.IsIso ((CategoryTheory.reflectorAdjunction i).unit.app A)
参数：(CategoryTheory.reflectorAdjunction i).unit.app A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.isIso_unit_app_iff_mem_essImage`：isIso_unit_ap
p_iff_mem_essImage [R.Faithful] [R.Full] {Y : C} : IsIso (h.unit.app Y) ↔ R.essI
mage Y
· 使用定理 `CategoryTheory.Reflective.toFaithful`：∀ {C : Type u₁} {D : Type u₂} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u
₂} D}   {R : CategoryTheor…
· 使用定理 `CategoryTheory.Reflective.toFull`：∀ {C : Type u₁} {D : Type u₂} {inst : 
CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {R : CategoryTheor…

--- 原说明 ---
If `A` is essentially in the image of a reflective functor `i`, then `η_A` is an
 isomorphism.
This gives that the "witness" for `A` being in the essential image can instead b
e given as the
reflection of `A`, with the isomorphism as `η_A`.

(For any `B` in the reflective subcategory, we automatically have that `ε_B` is 
an iso.)
-/
theorem Functor.essImage.unit_isIso [Reflective i] {A : C} (h : i.essImage A) :
    IsIso ((reflectorAdjunction i).unit.app A) := by
  rwa [isIso_unit_app_iff_mem_essImage]

/-- If `η_A` is a split monomorphism, then `A` is in the reflective subcategory. -/
/-
**CategoryTheory.mem_essImage_of_unit_isSplitMono** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：mem_essImage_of_unit_isSplitMono [Reflective i] {A : C} [IsSplitMono ((ref
lectorAdjunction i).unit.app A)] : i.essImage A
参数：(reflectorAdjunction i).unit.app A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.essImage.unit_isIso`：∀ {C : Type u₁} {D : Type u₂
} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {i : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.obj_mem_essImage`：obj_mem_essImage (F : D ⥤ C) (Y
 : D) : essImage F (F.obj Y)
· 使用定理 `CategoryTheory.epi_of_epi`：epi_of_epi (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ 
g)] : Epi g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.instIsSplitEpiMap`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   {X Y : C} (f : X ⟶…
· 使用定理 `CategoryTheory.retraction_isSplitEpi`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X)   [inst_1 : CategoryTheory.IsSpl
itMono f], CategoryTheory.…
· 使用定理 `CategoryTheory.isIso_of_epi_of_isSplitMono`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.Epi f]   [
CategoryTheory.IsSplitMono f], C…
· 使用定理 `CategoryTheory.Adjunction.mem_essImage_of_unit_isIso`：mem_essImage_of_un
it_isIso (A : C) [IsIso (h.unit.app A)] : R.essImage A

--- 原说明 ---
If `η_A` is a split monomorphism, then `A` is in the reflective subcategory.
-/
theorem mem_essImage_of_unit_isSplitMono [Reflective i] {A : C}
    [IsSplitMono ((reflectorAdjunction i).unit.app A)] : i.essImage A := by
  let η : 𝟭 C ⟶ reflector i ⋙ i := (reflectorAdjunction i).unit
  have : IsIso (η.app (i.obj ((reflector i).obj A))) :=
    Functor.essImage.unit_isIso ((i.obj_mem_essImage _))
  have : Epi (η.app A) := by
    refine @epi_of_epi _ _ _ _ _ (retraction (η.app A)) (η.app A) ?_
    rw [show retraction _ ≫ η.app A = _ from η.naturality (retraction (η.app A))]
    apply epi_comp (η.app (i.obj ((reflector i).obj A)))
  have := isIso_of_epi_of_isSplitMono (η.app A)
  exact (reflectorAdjunction i).mem_essImage_of_unit_isIso A

/-- Composition of reflective functors. -/
/-
**CategoryTheory.Reflective.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Refle
ctive`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     {E : Type u₃} →       [inst : Catego
ryTheory.Category.{v₁, u₁} C] →         [inst_1 : CategoryTheory.Category.{v₂, u
₂} D] →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             (F
 : CategoryTheory.Functor C D) →               (G : CategoryTheory.Functor D E) 
→                 [CategoryTheory.Reflective F] → [CategoryTheory.Reflective G] 
→ CategoryTheory.Reflective (F.comp G)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of reflective functors.
-/
instance Reflective.comp (F : C ⥤ D) (G : D ⥤ E) [Reflective F] [Reflective G] :
    Reflective (F ⋙ G) where
  L := reflector G ⋙ reflector F
  adj := (reflectorAdjunction G).comp (reflectorAdjunction F)

/-- (Implementation) Auxiliary definition for `unitCompPartialBijective`. -/
/-
**CategoryTheory.unitCompPartialBijectiveAux** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：unitCompPartialBijectiveAux [Reflective i] (A : C) (B : D) : (A ⟶ i.obj B)
 ≃ (i.obj ((reflector i).obj A) ⟶ i.obj B)
参数：A : C；B : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Reflective.toFull`：∀ {C : Type u₁} {D : Type u₂} {inst : 
CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {R : CategoryTheor…
· 使用定理 `CategoryTheory.Reflective.toFaithful`：∀ {C : Type u₁} {D : Type u₂} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u
₂} D}   {R : CategoryTheor…

--- 原说明 ---
(Implementation) Auxiliary definition for `unitCompPartialBijective`.
-/
def unitCompPartialBijectiveAux [Reflective i] (A : C) (B : D) :
    (A ⟶ i.obj B) ≃ (i.obj ((reflector i).obj A) ⟶ i.obj B) :=
  ((reflectorAdjunction i).homEquiv _ _).symm.trans
    (Functor.FullyFaithful.ofFullyFaithful i).homEquiv

/-- The description of the inverse of the bijection `unitCompPartialBijectiveAux`. -/
/-
**CategoryTheory.unitCompPartialBijectiveAux_symm_apply** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory`。
形式化陈述：unitCompPartialBijectiveAux_symm_apply [Reflective i] {A : C} {B : D} (f :
 i.obj ((reflector i).obj A) ⟶ i.obj B) : (unitCompPartialBijectiveAux _ _).symm
 f = (reflectorAdjunction i).unit.app A ≫ f
参数：f : i.obj ((reflector i).obj A) ⟶ i.obj B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Reflective.toFull`：∀ {C : Type u₁} {D : Type u₂} {inst : 
CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {R : CategoryTheor…
· 使用定理 `CategoryTheory.Reflective.toFaithful`：∀ {C : Type u₁} {D : Type u₂} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u
₂} D}   {R : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.homEquiv_symm_apply`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The description of the inverse of the bijection `unitCompPartialBijectiveAux`.
-/
theorem unitCompPartialBijectiveAux_symm_apply [Reflective i] {A : C} {B : D}
    (f : i.obj ((reflector i).obj A) ⟶ i.obj B) :
    (unitCompPartialBijectiveAux _ _).symm f = (reflectorAdjunction i).unit.app A ≫ f := by
  simp [unitCompPartialBijectiveAux, Adjunction.homEquiv_unit]

/-- If `i` has a reflector `L`, then the function `(i.obj (L.obj A) ⟶ B) → (A ⟶ B)` given by
precomposing with `η.app A` is a bijection provided `B` is in the essential image of `i`.
That is, the function `fun (f : i.obj (L.obj A) ⟶ B) ↦ η.app A ≫ f` is bijective,
as long as `B` is in the essential image of `i`.
This definition gives an equivalence: the key property that the inverse can be described
nicely is shown in `unitCompPartialBijective_symm_apply`.

This establishes there is a natural bijection `(A ⟶ B) ≃ (i.obj (L.obj A) ⟶ B)`. In other words,
from the point of view of objects in `D`, `A` and `i.obj (L.obj A)` look the same: specifically
that `η.app A` is an isomorphism.
-/
/-
**CategoryTheory.unitCompPartialBijective** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory`。
形式化陈述：unitCompPartialBijective [Reflective i] (A : C) {B : C} (hB : i.essImage B
) : (A ⟶ B) ≃ (i.obj ((reflector i).obj A) ⟶ B)
参数：A : C；hB : i.essImage B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i` has a reflector `L`, then the function `(i.obj (L.obj A) ⟶ B) → (A ⟶ B)` 
given by
precomposing with `η.app A` is a bijection provided `B` is in the essential imag
e of `i`.
That is, the function `fun (f : i.obj (L.obj A) ⟶ B) ↦ η.app A ≫ f` is bijective
,
as long as `B` is in the essential image of `i`.
This definition gives an equivalence: the key property that the inverse can be d
escribed
nicely is shown in `unitCompPartialBijective_symm_apply`.

This establishes there is a natural bijection `(A ⟶ B) ≃ (i.obj (L.obj A) ⟶ B)`.
 In other words,
from the point of view of objects in `D`, `A` and `i.obj (L.obj A)` look the sam
e: specifically
that `η.app A` is an isomorphism.
-/
def unitCompPartialBijective [Reflective i] (A : C) {B : C} (hB : i.essImage B) :
    (A ⟶ B) ≃ (i.obj ((reflector i).obj A) ⟶ B) :=
  calc
    (A ⟶ B) ≃ (A ⟶ i.obj (Functor.essImage.witness hB)) := Iso.homCongr (Iso.refl _) hB.getIso.symm
    _ ≃ (i.obj _ ⟶ i.obj (Functor.essImage.witness hB)) := unitCompPartialBijectiveAux _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B) :=
      Iso.homCongr (Iso.refl _) (Functor.essImage.getIso hB)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.unitCompPartialBijective_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory`。
形式化陈述：unitCompPartialBijective_symm_apply [Reflective i] (A : C) {B : C} (hB : i
.essImage B) (f) : (unitCompPartialBijective A hB).symm f = (reflectorAdjunction
 i).unit.app A ≫ f
参数：A : C；hB : i.essImage B；f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.unitCompPartialBijectiveAux_symm_apply`：unitCompPartialBi
jectiveAux_symm_apply [Reflective i] {A : C} {B : D} (f : i.obj ((reflector i).o
bj A) ⟶ i.obj B) : (unitCompPartialBijectiv…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unitCompPartialBijective_symm_apply [Reflective i] (A : C) {B : C} (hB : i.essImage B)
    (f) : (unitCompPartialBijective A hB).symm f = (reflectorAdjunction i).unit.app A ≫ f := by
  simp [unitCompPartialBijective, unitCompPartialBijectiveAux_symm_apply]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.unitCompPartialBijective_symm_natural** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory`。
形式化陈述：unitCompPartialBijective_symm_natural [Reflective i] (A : C) {B B' : C} (h
 : B ⟶ B') (hB : i.essImage B) (hB' : i.essImage B') (f : i.obj ((reflector i).o
bj A) ⟶ B) : (unitCompPartialBijective A hB').symm (f ≫ h) = (unitCompPartialBij
ective A hB).symm f ≫ h
参数：A : C；h : B ⟶ B'；hB : i.essImage B；hB' : i.essImage B'；f : i.obj ((reflector 
i).obj A) ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.unitCompPartialBijective_symm_apply`：unitCompPartialBijec
tive_symm_apply [Reflective i] (A : C) {B : C} (hB : i.essImage B) (f) : (unitCo
mpPartialBijective A hB).symm f = (refle…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unitCompPartialBijective_symm_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B')
    (hB : i.essImage B) (hB' : i.essImage B') (f : i.obj ((reflector i).obj A) ⟶ B) :
    (unitCompPartialBijective A hB').symm (f ≫ h) = (unitCompPartialBijective A hB).symm f ≫ h := by
  simp
/-
**CategoryTheory.unitCompPartialBijective_natural** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：unitCompPartialBijective_natural [Reflective i] (A : C) {B B' : C} (h : B 
⟶ B') (hB : i.essImage B) (hB' : i.essImage B') (f : A ⟶ B) : (unitCompPartialBi
jective A hB') (f ≫ h) = unitCompPartialBijective A hB f ≫ h
参数：A : C；h : B ⟶ B'；hB : i.essImage B；hB' : i.essImage B'；f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `CategoryTheory.unitCompPartialBijective_symm_natural`：unitCompPartialBij
ective_symm_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B') (hB : i.essIm
age B) (hB' : i.essImage B') (f : i.obj ((…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem unitCompPartialBijective_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B')
    (hB : i.essImage B) (hB' : i.essImage B') (f : A ⟶ B) :
    (unitCompPartialBijective A hB') (f ≫ h) = unitCompPartialBijective A hB f ≫ h := by
  rw [← Equiv.eq_symm_apply, unitCompPartialBijective_symm_natural A h hB, Equiv.symm_apply_apply]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Reflective i] (X : Functor.EssImageSubcategory i) :
    IsIso (NatTrans.app (reflectorAdjunction i).unit X.obj) :=
  Functor.essImage.unit_isIso X.property

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- These attributes are necessary to make automation work in `equivEssImageOfReflective`.
-- Making them global doesn't break anything elsewhere, but this is enough for now.
-- TODO: investigate further.
attribute [local simp 900] ObjectProperty.ι_map in
attribute [local ext] Functor.essImage_ext in
/-- If `i : D ⥤ C` is reflective, the inverse functor of `i ≌ F.essImage` can be explicitly
defined by the reflector. -/
@[simps]
/-
**CategoryTheory.equivEssImageOfReflective** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：equivEssImageOfReflective [Reflective i] : D ≌ i.EssImageSubcategory where
 functor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsIsoAppUnitReflectorAdjunctionObjEssImage`：∀ {C : Ty
pe u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   {i : CategoryTheor…

--- 原说明 ---
If `i : D ⥤ C` is reflective, the inverse functor of `i ≌ F.essImage` can be exp
licitly
defined by the reflector.
-/
def equivEssImageOfReflective [Reflective i] : D ≌ i.EssImageSubcategory where
  functor := i.toEssImage
  inverse := i.essImage.ι ⋙ reflector i
  unitIso := (asIso <| (reflectorAdjunction i).counit).symm
  counitIso := Functor.fullyFaithfulCancelRight i.essImage.ι <|
    NatIso.ofComponents (fun X ↦ (asIso ((reflectorAdjunction i).unit.app X.obj)).symm)

/--
A functor is *coreflective*, or *a coreflective inclusion*, if it is fully faithful and left
adjoint.
-/
/-
**CategoryTheory.Coreflective** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor C D → Type (max (max (max u₁ u₂) v₁) v₂)
参数：max (max (max u₁ u₂) v₁) v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is *coreflective*, or *a coreflective inclusion*, if it is fully faith
ful and left
adjoint.
-/
class Coreflective (L : C ⥤ D) extends L.Full, L.Faithful where
  /-- a choice of a right adjoint to `L` -/
  R : D ⥤ C
  /-- `L` is a left adjoint -/
  adj : L ⊣ R

variable (j : C ⥤ D)

/-- The coreflector `D ⥤ C` when `L : C ⥤ D` is coreflective. -/
/-
**CategoryTheory.coreflector** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：coreflector [Coreflective j] : D ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coreflector `D ⥤ C` when `L : C ⥤ D` is coreflective.
-/
def coreflector [Coreflective j] : D ⥤ C := Coreflective.R (L := j)

/-- The adjunction `j ⊣ coreflector j` when `j` is coreflective. -/
/-
**CategoryTheory.coreflectorAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：coreflectorAdjunction [Coreflective j] : j ⊣ coreflector j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `j ⊣ coreflector j` when `j` is coreflective.
-/
def coreflectorAdjunction [Coreflective j] : j ⊣ coreflector j := Coreflective.adj
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Coreflective j] : j.IsLeftAdjoint := ⟨_, ⟨coreflectorAdjunction j⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Coreflective j] : (coreflector j).IsRightAdjoint := ⟨_, ⟨coreflectorAdjunction j⟩⟩

/-- A coreflective functor is fully faithful. -/
/-
**CategoryTheory.Functor.fullyFaithfulOfCoreflective** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (j : Cat
egoryTheory.Functor C D) → [CategoryTheory.Coreflective j] → j.FullyFaithful
参数：j : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coreflective functor is fully faithful.
-/
def Functor.fullyFaithfulOfCoreflective [Coreflective j] : j.FullyFaithful :=
  (coreflectorAdjunction j).fullyFaithfulLOfIsIsoUnit
/-
**CategoryTheory.counit_obj_eq_map_counit** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory`。
形式化陈述：counit_obj_eq_map_counit [Coreflective j] (X : D) : (coreflectorAdjunction
 j).counit.app (j.obj ((coreflector j).obj X)) = j.map ((coreflector j).map ((co
reflectorAdjunction j).counit.app X))
参数：X : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_of_isLeftAdjoint`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instIsLeftAdjointOfCoreflective`：∀ {C : Type u₁} {D : Typ
e u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (j : CategoryTheor…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Coreflective.toFull`：∀ {C : Type u₁} {D : Type u₂} {inst 
: CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Coreflective.toFaithful`：∀ {C : Type u₁} {D : Type u₂} {i
nst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂,
 u₂} D}   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma counit_obj_eq_map_counit [Coreflective j] (X : D) :
    (coreflectorAdjunction j).counit.app (j.obj ((coreflector j).obj X)) =
      j.map ((coreflector j).map ((coreflectorAdjunction j).counit.app X)) := by
  rw [← cancel_epi (j.map ((coreflectorAdjunction j).unit.app ((coreflector j).obj X))),
    ← j.map_comp]
  simp
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Coreflective j] {B : C} : IsIso ((coreflectorAdjunction j).counit.app (j.obj B)) :=
  inferInstance

variable {j}
/-
**CategoryTheory.Functor.essImage.counit_isIso** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.essImage`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {j : CategoryTheory.Functor C D}
 [inst_2 : CategoryTheory.Coreflective j] {A : D},   j.essImage A → CategoryTheo
ry.IsIso ((CategoryTheory.coreflectorAdjunction j).counit.app A)
参数：(CategoryTheory.coreflectorAdjunction j).counit.app A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.isIso_counit_app_iff_mem_essImage`：isIso_couni
t_app_iff_mem_essImage [L.Faithful] [L.Full] {X : D} : IsIso (h.counit.app X) ↔ 
L.essImage X
· 使用定理 `CategoryTheory.Coreflective.toFaithful`：∀ {C : Type u₁} {D : Type u₂} {i
nst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂,
 u₂} D}   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Coreflective.toFull`：∀ {C : Type u₁} {D : Type u₂} {inst 
: CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {L : CategoryTheor…
-/
lemma Functor.essImage.counit_isIso [Coreflective j] {A : D} (h : j.essImage A) :
    IsIso ((coreflectorAdjunction j).counit.app A) := by
  rwa [isIso_counit_app_iff_mem_essImage]
/-
**CategoryTheory.mem_essImage_of_counit_isSplitEpi** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：mem_essImage_of_counit_isSplitEpi [Coreflective j] {A : D} [IsSplitEpi ((c
oreflectorAdjunction j).counit.app A)] : j.essImage A
参数：(coreflectorAdjunction j).counit.app A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.essImage.counit_isIso`：∀ {C : Type u₁} {D : Type 
u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {j : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.obj_mem_essImage`：obj_mem_essImage (F : D ⥤ C) (Y
 : D) : essImage F (F.obj Y)
· 使用定理 `CategoryTheory.mono_of_mono`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X)   [CategoryTheory.Mono (Catego
ryTheory.Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.instIsSplitMonoMap`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {X Y : C} (f : Y ⟶…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.isIso_of_mono_of_isSplitEpi`：isIso_of_mono_of_isSplitEpi 
{X Y : C} (f : X ⟶ Y) [Mono f] [IsSplitEpi f] : IsIso f
· 使用引理 `CategoryTheory.Adjunction.mem_essImage_of_counit_isIso`：mem_essImage_of_
counit_isIso (A : D) [IsIso (h.counit.app A)] : L.essImage A
-/
lemma mem_essImage_of_counit_isSplitEpi [Coreflective j] {A : D}
    [IsSplitEpi ((coreflectorAdjunction j).counit.app A)] : j.essImage A := by
  let ε : coreflector j ⋙ j ⟶ 𝟭 D := (coreflectorAdjunction j).counit
  have : IsIso (ε.app (j.obj ((coreflector j).obj A))) :=
    Functor.essImage.counit_isIso ((j.obj_mem_essImage _))
  have : Mono (ε.app A) := by
    refine @mono_of_mono _ _ _ _ _ (ε.app A) (section_ (ε.app A)) ?_
    rw [show ε.app A ≫ section_ _ = _ from (ε.naturality (section_ (ε.app A))).symm]
    apply mono_comp _ (ε.app (j.obj ((coreflector j).obj A)))
  have := isIso_of_mono_of_isSplitEpi (ε.app A)
  exact (coreflectorAdjunction j).mem_essImage_of_counit_isIso A
/-
**CategoryTheory.Coreflective.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cor
eflective`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     {E : Type u₃} →       [inst : Catego
ryTheory.Category.{v₁, u₁} C] →         [inst_1 : CategoryTheory.Category.{v₂, u
₂} D] →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             (F
 : CategoryTheory.Functor C D) →               (G : CategoryTheory.Functor D E) 
→                 [CategoryTheory.Coreflective F] →                   [CategoryT
heory.Coreflective G] → CategoryTheory.Coreflective (F.comp G)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Coreflective.comp (F : C ⥤ D) (G : D ⥤ E) [Coreflective F] [Coreflective G] :
    Coreflective (F ⋙ G) where
  R := coreflector G ⋙ coreflector F
  adj := (coreflectorAdjunction F).comp (coreflectorAdjunction G)

end CategoryTheory

