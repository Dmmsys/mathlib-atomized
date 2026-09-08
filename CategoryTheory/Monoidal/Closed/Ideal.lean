/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Subterminal

/-!
# Exponential ideals

An exponential ideal of a Cartesian closed category `C` is a subcategory `D ⊆ C` such that for any
`B : D` and `A : C`, the exponential `A ⟹ B` is in `D`: resembling ring-theoretic ideals. We
define the notion here for inclusion functors `i : D ⥤ C` rather than explicit subcategories to
preserve the principle of equivalence.

We additionally show that if `C` is Cartesian closed and `i : D ⥤ C` is a reflective functor, the
following are equivalent.
* The left adjoint to `i` preserves binary (equivalently, finite) products.
* `i` is an exponential ideal.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Category

open scoped CartesianClosed

section Ideal

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₁} D] {i : D ⥤ C}
variable (i) [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- The subcategory `D` of `C` expressed as an inclusion functor is an *exponential ideal* if
`B ∈ D` implies `A ⟹ B ∈ D` for all `A`.
-/
/-
**CategoryTheory.ExponentialIdeal** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₁, u₂} D] →         Category
Theory.Functor D C →           [inst_2 : CategoryTheory.CartesianMonoidalCategor
y C] → [CategoryTheory.MonoidalClosed C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subcategory `D` of `C` expressed as an inclusion functor is an *exponential 
ideal* if
`B ∈ D` implies `A ⟹ B ∈ D` for all `A`.
-/
class ExponentialIdeal : Prop where
  exp_closed : ∀ {B}, i.essImage B → ∀ A, i.essImage (A ⟹ B)
attribute [nolint docBlame] ExponentialIdeal.exp_closed

/-- To show `i` is an exponential ideal it suffices to show that `A ⟹ iB` is "in" `D` for any `A` in
`C` and `B` in `D`.
-/
/-
**CategoryTheory.ExponentialIdeal.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
ExponentialIdeal`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₁, u₂} D]   (i : CategoryTheory.Functor D C)
 [inst_2 : CategoryTheory.CartesianMonoidalCategory C]   [inst_3 : CategoryTheor
y.MonoidalClosed C],   (∀ (B : D) (A : C), i.essImage (A ⟹ i.obj B)) → CategoryT
heory.ExponentialIdeal i
参数：i : CategoryTheory.Functor D C；∀ (B : D) (A : C), i.essImage (A ⟹ i.obj B)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.essImage.ofIso`：∀ {C : Type u₁} {D : Type u₂} [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F : CategoryTheor…

--- 原说明 ---
To show `i` is an exponential ideal it suffices to show that `A ⟹ iB` is "in" `D
` for any `A` in
`C` and `B` in `D`.
-/
theorem ExponentialIdeal.mk' (h : ∀ (B : D) (A : C), i.essImage (A ⟹ i.obj B)) :
    ExponentialIdeal i :=
  ⟨fun hB A => by
    rcases hB with ⟨B', ⟨iB'⟩⟩
    exact Functor.essImage.ofIso ((ihom A).mapIso iB') (h B' A)⟩

/-- The entire category viewed as a subcategory is an exponential ideal. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entire category viewed as a subcategory is an exponential ideal.
-/
instance : ExponentialIdeal (𝟭 C) :=
  ExponentialIdeal.mk' _ fun _ _ => ⟨_, ⟨Iso.refl _⟩⟩

open MonoidalClosed

/-- The subcategory of subterminal objects is an exponential ideal. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subcategory of subterminal objects is an exponential ideal.
-/
instance : ExponentialIdeal (subterminalInclusion C) := by
  apply ExponentialIdeal.mk'
  intro B A
  refine ⟨⟨A ⟹ B.1, fun Z g h => ?_⟩, ⟨Iso.refl _⟩⟩
  exact uncurry_injective (B.2 (MonoidalClosed.uncurry g) (MonoidalClosed.uncurry h))

set_option backward.defeqAttrib.useBackward true in
/-- If `D` is a reflective subcategory, the property of being an exponential ideal is equivalent to
the presence of a natural isomorphism `i ⋙ exp A ⋙ leftAdjoint i ⋙ i ≅ i ⋙ exp A`, that is:
`(A ⟹ iB) ≅ i L (A ⟹ iB)`, naturally in `B`.
The converse is given in `ExponentialIdeal.mk_of_iso`.
-/
/-
**CategoryTheory.exponentialIdealReflective** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory`。
形式化陈述：exponentialIdealReflective (A : C) [Reflective i] [ExponentialIdeal i] : i
 ⋙ ihom A ⋙ reflector i ⋙ i ≅ i ⋙ ihom A
参数：A : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `D` is a reflective subcategory, the property of being an exponential ideal i
s equivalent to
the presence of a natural isomorphism `i ⋙ exp A ⋙ leftAdjoint i ⋙ i ≅ i ⋙ exp A
`, that is:
`(A ⟹ iB) ≅ i L (A ⟹ iB)`, naturally in `B`.
The converse is given in `ExponentialIdeal.mk_of_iso`.
-/
def exponentialIdealReflective (A : C) [Reflective i] [ExponentialIdeal i] :
    i ⋙ ihom A ⋙ reflector i ⋙ i ≅ i ⋙ ihom A := by
  symm
  apply NatIso.ofComponents _ _
  · intro X
    haveI := Functor.essImage.unit_isIso (ExponentialIdeal.exp_closed (i.obj_mem_essImage X) A)
    apply asIso ((reflectorAdjunction i).unit.app (A ⟹ i.obj X))
  · simp [asIso]

/-- Given a natural isomorphism `i ⋙ exp A ⋙ leftAdjoint i ⋙ i ≅ i ⋙ exp A`, we can show `i`
is an exponential ideal.
-/
/-
**CategoryTheory.ExponentialIdeal.mk_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ExponentialIdeal`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₁, u₂} D]   (i : CategoryTheory.Functor D C)
 [inst_2 : CategoryTheory.CartesianMonoidalCategory C]   [inst_3 : CategoryTheor
y.MonoidalClosed C] [inst_4 : CategoryTheory.Reflective i]   (h :     (A : C) → 
      i.comp ((CategoryTheory.ihom A).comp ((CategoryTheory.reflector i).comp i)
) ≅ i.comp (CategoryTheory.ihom A)),   CategoryTheory.ExponentialIdeal i
参数：i : CategoryTheory.Functor D C；h :     (A : C) →       i.comp ((CategoryTheor
y.ihom A).comp ((CategoryTheory.reflector i).comp i)) ≅ i.comp (CategoryTheory.i
hom A)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ExponentialIdeal.mk'`：∀ {C : Type u₁} {D : Type u₂} [inst
 : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₁, u₂
} D]   (i : CategoryTheor…

--- 原说明 ---
Given a natural isomorphism `i ⋙ exp A ⋙ leftAdjoint i ⋙ i ≅ i ⋙ exp A`, we can 
show `i`
is an exponential ideal.
-/
theorem ExponentialIdeal.mk_of_iso [Reflective i]
    (h : ∀ A : C, i ⋙ ihom A ⋙ reflector i ⋙ i ≅ i ⋙ ihom A) : ExponentialIdeal i := by
  apply ExponentialIdeal.mk'
  intro B A
  exact ⟨_, ⟨(h A).app B⟩⟩

end Ideal

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₁} D]
variable (i : D ⥤ C)

/- This cannot be a local instance since it has free variables,
it can instead be used as a have when needed.
We assume `HasFiniteProducts D` as a hypothesis below, to avoid making this a local instance.
-/
/-
**CategoryTheory.reflective_products** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：reflective_products [Limits.HasFiniteProducts C] [Reflective i] : Limits.H
asFiniteProducts D
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimitsOfShape_of_reflective`：hasLimitsOfShape_of_refle
ctive [HasLimitsOfShape J C] (R : D ⥤ C) [Reflective R] : HasLimitsOfShape J D
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
This cannot be a local instance since it has free variables,
it can instead be used as a have when needed.
We assume `HasFiniteProducts D` as a hypothesis below, to avoid making this a lo
cal instance.
-/
theorem reflective_products [Limits.HasFiniteProducts C] [Reflective i] :
    Limits.HasFiniteProducts D := ⟨fun _ => hasLimitsOfShape_of_reflective i⟩

open MonoidalClosed MonoidalCategory CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false in
open Limits in
/-- Given a reflective subcategory `D` of a category with chosen finite products `C`, `D` admits
finite chosen products. -/
-- Note: This is not an instance as one might already have a (different) `CartesianMonoidalCategory`
-- instance on `D` (as for example with sheaves).
-- See note [reducible non-instances]
/-
**CategoryTheory.CartesianMonoidalCategory.ofReflective** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₁, u₂} D] →         (i : Cat
egoryTheory.Functor D C) →           [CategoryTheory.CartesianMonoidalCategory C
] →             [CategoryTheory.Reflective i] → CategoryTheory.CartesianMonoidal
Category D
参数：i : CategoryTheory.Functor D C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev CartesianMonoidalCategory.ofReflective [CartesianMonoidalCategory C] [Reflective i] :
    CartesianMonoidalCategory D :=
  .ofChosenFiniteProducts
    ({ cone := Limits.asEmptyCone <| (reflector i).obj (𝟙_ C)
       isLimit := by
         apply isLimitOfReflects i
         apply isLimitChangeEmptyCone _ isTerminalTensorUnit
         letI : IsIso ((reflectorAdjunction i).unit.app (𝟙_ C)) := by
           have := reflective_products i
           refine Functor.essImage.unit_isIso ⟨terminal D, ⟨PreservesTerminal.iso i |>.trans ?_⟩⟩
           exact IsLimit.conePointUniqueUpToIso (limit.isLimit _) isTerminalTensorUnit
         exact asIso ((reflectorAdjunction i).unit.app (𝟙_ C)) })
  fun X Y ↦
    { cone := BinaryFan.mk
        ((reflector i).map (fst (i.obj X) (i.obj Y)) ≫ (reflectorAdjunction i).counit.app _)
        ((reflector i).map (snd (i.obj X) (i.obj Y)) ≫ (reflectorAdjunction i).counit.app _)
      isLimit := by
        apply isLimitOfReflects i
        apply IsLimit.equivOfNatIsoOfIso (pairComp X Y _) _ _ _ |>.invFun
          (tensorProductIsBinaryProduct (i.obj X) (i.obj Y))
        fapply BinaryFan.ext
        · change (reflector i ⋙ i).obj (i.obj X ⊗ i.obj Y) ≅ (𝟭 C).obj (i.obj X ⊗ i.obj Y)
          letI : IsIso ((reflectorAdjunction i).unit.app (i.obj X ⊗ i.obj Y)) := by
            apply Functor.essImage.unit_isIso
            have := reflective_products i
            use Limits.prod X Y
            constructor
            apply Limits.PreservesLimitPair.iso i _ _ |>.trans
            refine Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit (pair (i.obj X) (i.obj Y)))
              (tensorProductIsBinaryProduct _ _)
          exact asIso ((reflectorAdjunction i).unit.app (i.obj X ⊗ i.obj Y)) |>.symm
        · simp only [BinaryFan.fst, Cone.postcompose, pairComp]
          simp [← Functor.comp_map, ← NatTrans.naturality_assoc]
        · simp only [BinaryFan.snd, Cone.postcompose, pairComp]
          simp [← Functor.comp_map, ← NatTrans.naturality_assoc] }

variable [CartesianMonoidalCategory C] [Reflective i] [MonoidalClosed C]
  [CartesianMonoidalCategory D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If the reflector preserves binary products, the subcategory is an exponential ideal.
This is the converse of `preservesBinaryProductsOfExponentialIdeal`.
-/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the reflector preserves binary products, the subcategory is an exponential id
eal.
This is the converse of `preservesBinaryProductsOfExponentialIdeal`.
-/
instance (priority := 10) exponentialIdeal_of_preservesBinaryProducts
    [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) (reflector i)] :
    ExponentialIdeal i := by
  let ir := reflectorAdjunction i
  let L : C ⥤ D := reflector i
  let η : 𝟭 C ⟶ L ⋙ i := ir.unit
  let ε : i ⋙ L ⟶ 𝟭 D := ir.counit
  apply ExponentialIdeal.mk'
  intro B A
  let q : i.obj (L.obj (A ⟹ i.obj B)) ⟶ A ⟹ i.obj B := by
    apply MonoidalClosed.curry (ir.homEquiv _ _ _)
    apply _ ≫ (ir.homEquiv _ _).symm ((ihom.ev A).app (i.obj B))
    exact prodComparison L A _ ≫ (_ ◁ (ε.app _)) ≫ inv (prodComparison _ _ _)
  have : η.app (A ⟹ i.obj B) ≫ q = 𝟙 (A ⟹ i.obj B) := by
    dsimp
    rw [← curry_natural_left, curry_eq_iff, uncurry_id_eq_ev, ← ir.homEquiv_naturality_left,
      ir.homEquiv_apply_eq, Category.assoc, Category.assoc,
      prodComparison_natural_whiskerLeft_assoc, ← whiskerLeft_comp_assoc,
      ir.left_triangle_components, whiskerLeft_id, Category.id_comp]
    apply IsIso.hom_inv_id_assoc
  have : IsSplitMono (η.app (A ⟹ i.obj B)) := IsSplitMono.mk' ⟨_, this⟩
  apply mem_essImage_of_unit_isSplitMono

variable [ExponentialIdeal i]

set_option backward.defeqAttrib.useBackward true in
/-- If `i` witnesses that `D` is a reflective subcategory and an exponential ideal, then `D` is
itself Cartesian closed.

To allow for better control of definitional equality, this construction
takes in an explicit choice of lift of the essential image of `i` to `D`, in the form of a functor
`l : i.EssImageSubcategory ⥤ D` and natural isomorphism `φ : l ⋙ i ≅ i.essImage.ι`. When
`l ⋙ i` is defeq to `i.essImage.ι`, images of exponential objects in `D` under `i` will be defeq
to the respective exponential objects in `C`. -/
@[instance_reducible]
/-
**CategoryTheory.cartesianClosedOfReflective'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory`。
形式化陈述：cartesianClosedOfReflective' (l : i.EssImageSubcategory ⥤ D) (φ : l ⋙ i ≅ 
i.essImage.ι) : MonoidalClosed D where closed
参数：l : i.EssImageSubcategory ⥤ D；φ : l ⋙ i ≅ i.essImage.ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i` witnesses that `D` is a reflective subcategory and an exponential ideal, 
then `D` is
itself Cartesian closed.

To allow for better control of definitional equality, this construction
takes in an explicit choice of lift of the essential image of `i` to `D`, in the
 form of a functor
`l : i.EssImageSubcategory ⥤ D` and natural isomorphism `φ : l ⋙ i ≅ i.essImage.
ι`. When
`l ⋙ i` is defeq to `i.essImage.ι`, images of exponential objects in `D` under `
i` will be defeq
to the respective exponential objects in `C`.
-/
def cartesianClosedOfReflective' (l : i.EssImageSubcategory ⥤ D) (φ : l ⋙ i ≅ i.essImage.ι) :
    MonoidalClosed D where
  closed := fun B =>
    { rightAdj := i.essImage.lift (i ⋙ ihom (i.obj B))
        (fun X ↦ ExponentialIdeal.exp_closed (i.obj_mem_essImage X) _) ⋙ l
      adj := by
        apply (ihom.adjunction (i.obj B)).restrictFullyFaithful i.fullyFaithfulOfReflective
          i.fullyFaithfulOfReflective
        · symm
          refine NatIso.ofComponents (fun X => ?_) (fun f => ?_)
          · haveI :=
              Adjunction.rightAdjoint_preservesLimits.{0, 0} (reflectorAdjunction i)
            apply asIso (prodComparison i B X)
          · dsimp [asIso]
            rw [prodComparison_natural_whiskerLeft]
        · exact (i.essImage.liftCompιIso _ _).symm.trans <|
            (Functor.isoWhiskerLeft _ φ.symm).trans (Functor.associator _ _ _).symm }

set_option backward.defeqAttrib.useBackward true in
/-- If `i` witnesses that `D` is a reflective subcategory and an exponential ideal, then `D` is
itself Cartesian closed.

Unlike `cartesianClosedOfReflective'` this construction lifts exponential objects in `C` to
exponential objects in `D` by applying the reflector to them, even though they already lie in the
essential image of `i`; if you need better control over definitional equality, use
`cartesianClosedOfReflective'` instead. -/
@[instance_reducible]
/-
**CategoryTheory.cartesianClosedOfReflective** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：cartesianClosedOfReflective : MonoidalClosed D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i` witnesses that `D` is a reflective subcategory and an exponential ideal, 
then `D` is
itself Cartesian closed.

Unlike `cartesianClosedOfReflective'` this construction lifts exponential object
s in `C` to
exponential objects in `D` by applying the reflector to them, even though they a
lready lie in the
essential image of `i`; if you need better control over definitional equality, u
se
`cartesianClosedOfReflective'` instead.
-/
def cartesianClosedOfReflective : MonoidalClosed D :=
  cartesianClosedOfReflective' i (i.essImage.ι ⋙ reflector i)
    (NatIso.ofComponents (fun X ↦
      have := Functor.essImage.unit_isIso X.2
      (asIso ((reflectorAdjunction i).unit.app X.obj)).symm))

variable [BraidedCategory C]

/-- We construct a bijection between morphisms `L(A ⊗ B) ⟶ X` and morphisms `LA ⊗ LB ⟶ X`.
This bijection has two key properties:
* It is natural in `X`: See `bijection_natural`.
* When `X = LA ⨯ LB`, then the backwards direction sends the identity morphism to the product
  comparison morphism: See `bijection_symm_apply_id`.

Together these help show that `L` preserves binary products. This should be considered
*internal implementation* towards `preservesBinaryProductsOfExponentialIdeal`.
-/
/-
**CategoryTheory.bijection** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：bijection (A B : C) (X : D) : ((reflector i).obj (A otimes B) ⟶ X) ≃ ((ref
lector i).obj A otimes (reflector i).obj B ⟶ X)
参数：A B : C；X : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
We construct a bijection between morphisms `L(A ⊗ B) ⟶ X` and morphisms `LA ⊗ LB
 ⟶ X`.
This bijection has two key properties:
* It is natural in `X`: See `bijection_natural`.
* When `X = LA ⨯ LB`, then the backwards direction sends the identity morphism t
o the product
  comparison morphism: See `bijection_symm_apply_id`.

Together these help show that `L` preserves binary products. This should be cons
idered
*internal implementation* towards `preservesBinaryProductsOfExponentialIdeal`.
-/
noncomputable def bijection (A B : C) (X : D) :
    ((reflector i).obj (A ⊗ B) ⟶ X) ≃ ((reflector i).obj A ⊗ (reflector i).obj B ⟶ X) :=
  calc
    _ ≃ (A ⊗ B ⟶ i.obj X) := (reflectorAdjunction i).homEquiv _ _
    _ ≃ (B ⊗ A ⟶ i.obj X) := (β_ _ _).homCongr (Iso.refl _)
    _ ≃ (A ⟶ B ⟹ i.obj X) := (ihom.adjunction _).homEquiv _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B ⟹ i.obj X) :=
      (unitCompPartialBijective _ (ExponentialIdeal.exp_closed (i.obj_mem_essImage _) _))
    _ ≃ (B ⊗ i.obj ((reflector i).obj A) ⟶ i.obj X) := ((ihom.adjunction _).homEquiv _ _).symm
    _ ≃ (i.obj ((reflector i).obj A) ⊗ B ⟶ i.obj X) :=
      ((β_ _ _).homCongr (Iso.refl _))
    _ ≃ (B ⟶ i.obj ((reflector i).obj A) ⟹ i.obj X) := (ihom.adjunction _).homEquiv _ _
    _ ≃ (i.obj ((reflector i).obj B) ⟶ i.obj ((reflector i).obj A) ⟹ i.obj X) :=
      (unitCompPartialBijective _ (ExponentialIdeal.exp_closed (i.obj_mem_essImage _) _))
    _ ≃ (i.obj ((reflector i).obj A) ⊗ i.obj ((reflector i).obj B) ⟶ i.obj X) :=
      ((ihom.adjunction _).homEquiv _ _).symm
    _ ≃ (i.obj ((reflector i).obj A ⊗ (reflector i).obj B) ⟶ i.obj X) :=
      haveI : Limits.PreservesLimits i := (reflectorAdjunction i).rightAdjoint_preservesLimits
      haveI := Limits.preservesSmallestLimits_of_preservesLimits i
      Iso.homCongr (prodComparisonIso _ _ _).symm (Iso.refl (i.obj X))
    _ ≃ ((reflector i).obj A ⊗ (reflector i).obj B ⟶ X) :=
      i.fullyFaithfulOfReflective.homEquiv.symm

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.bijection_symm_apply_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：bijection_symm_apply_id (A B : C) : (bijection i A B _).symm (𝟙 _) = prodC
omparison _ _ _
参数：A B : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.unitCompPartialBijective_symm_apply`：unitCompPartialBijec
tive_symm_apply [Reflective i] (A : C) {B : C} (hB : i.essImage B) (f) : (unitCo
mpPartialBijective A hB).symm f = (refle…
· 使用定理 `CategoryTheory.MonoidalClosed.homEquiv_symm_apply_eq`：homEquiv_symm_appl
y_eq (f : Y ⟶ A ⟶[C] X) : ((ihom.adjunction A).homEquiv _ _).symm f = uncurry f
· 使用定理 `CategoryTheory.MonoidalClosed.homEquiv_apply_eq`：homEquiv_apply_eq (f : 
A otimes Y ⟶ X) : (ihom.adjunction A).homEquiv _ _ f = curry f
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_natural_left`：uncurry_natural_left
 (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) : uncurry (f ≫ g) = _ ◁ f ≫ uncurry g
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_left_assoc`：∀ {C : Ty
pe u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Monoida
lCategory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.SymmetricCategory.symmetry_assoc`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}  
 [self : CategoryTheory.SymmetricCate…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'_assoc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory
 C] {X₁ Y₁ X₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g :…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_symm_apply`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Adjunction.eq_unit_comp_map_iff`：eq_unit_comp_map_iff {A 
: C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) : dsimp% g = adj.unit.app A ≫ G
.map f ↔ F.map g ≫ adj.counit.app B …
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.instIsRightAdjointOfMonadicRightAdjoint`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   (R : CategoryTheor…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.prodComparisonIso_hom`：prodComp
arisonIso_hom : (prodComparisonIso F A B).hom = prodComparison F A B
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_fst`：tensorHom_fst {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ fst _ _ = fst _ _ 
≫ f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_fst`：prodCompari
son_fst : prodComparison F A B ≫ fst _ _ = F.map (fst A B)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
（共 32 条，此处仅展示前 30 条）
-/
theorem bijection_symm_apply_id (A B : C) :
    (bijection i A B _).symm (𝟙 _) = prodComparison _ _ _ := by
  simp only [bijection, Equiv.trans_def, curriedTensor_obj_obj, Equiv.symm_trans_apply,
    Equiv.symm_symm, Functor.FullyFaithful.homEquiv_apply, Functor.map_id, Iso.homCongr_symm,
    Iso.symm_symm_eq, Iso.refl_symm, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
    unitCompPartialBijective_symm_apply, Functor.id_obj, Functor.comp_obj, Iso.symm_inv]
  -- Porting note: added
  erw [homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq]
  rw [uncurry_natural_left, uncurry_curry, uncurry_natural_left, uncurry_curry,
    ← BraidedCategory.braiding_naturality_left_assoc, SymmetricCategory.symmetry_assoc,
    ← MonoidalCategory.whisker_exchange_assoc, ← tensorHom_def'_assoc,
    Adjunction.homEquiv_symm_apply, ← Adjunction.eq_unit_comp_map_iff, Iso.comp_inv_eq,
    Category.assoc, prodComparisonIso_hom i ((reflector i).obj A) ((reflector i).obj B)]
  apply hom_ext
  · rw [tensorHom_fst, Category.assoc, Category.assoc, prodComparison_fst, ← i.map_comp,
    prodComparison_fst]
    apply (reflectorAdjunction i).unit.naturality
  · rw [tensorHom_snd, Category.assoc, Category.assoc, prodComparison_snd, ← i.map_comp,
    prodComparison_snd]
    apply (reflectorAdjunction i).unit.naturality

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.bijection_natural** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：bijection_natural (A B : C) (X X' : D) (f : (reflector i).obj (A otimes B)
 ⟶ X) (g : X ⟶ X') : bijection i _ _ _ (f ≫ g) = bijection i _ _ _ f ≫ g
参数：A B : C；X X' : D；f : (reflector i).obj (A otimes B) ⟶ X；g : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.homEquiv_symm_apply_eq`：homEquiv_symm_appl
y_eq (f : Y ⟶ A ⟶[C] X) : ((ihom.adjunction A).homEquiv _ _).symm f = uncurry f
· 使用定理 `CategoryTheory.MonoidalClosed.homEquiv_apply_eq`：homEquiv_apply_eq (f : 
A otimes Y ⟶ X) : (ihom.adjunction A).homEquiv _ _ f = curry f
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Reflective.toFaithful`：∀ {C : Type u₁} {D : Type u₂} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u
₂} D}   {R : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalClosed.curry_natural_right`：curry_natural_right (
f : A otimes X ⟶ Y) (g : Y ⟶ Y') : curry (f ≫ g) = curry f ≫ (ihom _).map g
· 使用定理 `CategoryTheory.unitCompPartialBijective_natural`：unitCompPartialBijectiv
e_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B') (hB : i.essImage B) (hB
' : i.essImage B') (f : A ⟶ B) : (uni…
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_natural_right`：uncurry_natural_rig
ht (f : X ⟶ A ⟶[C] Y) (g : Y ⟶ Y') : uncurry (f ≫ (ihom _).map g) = uncurry f ≫ 
g
-/
theorem bijection_natural (A B : C) (X X' : D) (f : (reflector i).obj (A ⊗ B) ⟶ X) (g : X ⟶ X') :
    bijection i _ _ _ (f ≫ g) = bijection i _ _ _ f ≫ g := by
  dsimp [bijection]
  -- Porting note: added
  erw [homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq,
    homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq]
  apply i.map_injective
  rw [Functor.FullyFaithful.map_preimage, i.map_comp,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Category.comp_id, Functor.map_comp, Functor.FullyFaithful.map_preimage, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, curry_natural_right _ (i.map g),
    unitCompPartialBijective_natural, uncurry_natural_right, ← Category.assoc, curry_natural_right,
    unitCompPartialBijective_natural, uncurry_natural_right, Category.assoc]

/--
The bijection allows us to show that `prodComparison L A B` is an isomorphism, where the inverse
is the forward map of the identity morphism.
-/
/-
**CategoryTheory.prodComparison_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：prodComparison_iso (A B : C) : IsIso (prodComparison (reflector i) A B)
参数：A B : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `CategoryTheory.bijection_natural`：bijection_natural (A B : C) (X X' : D)
 (f : (reflector i).obj (A otimes B) ⟶ X) (g : X ⟶ X') : bijection i _ _ _ (f ≫ 
g) = bijection i _ _ _…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.bijection_symm_apply_id`：bijection_symm_apply_id (A B : C
) : (bijection i A B _).symm (𝟙 _) = prodComparison _ _ _
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
The bijection allows us to show that `prodComparison L A B` is an isomorphism, w
here the inverse
is the forward map of the identity morphism.
-/
theorem prodComparison_iso (A B : C) : IsIso
    (prodComparison (reflector i) A B) :=
  ⟨⟨bijection i _ _ _ (𝟙 _), by
      rw [← (bijection i _ _ _).injective.eq_iff, bijection_natural, ← bijection_symm_apply_id,
        Equiv.apply_symm_apply, Category.id_comp],
      by rw [← bijection_natural, Category.id_comp, ← bijection_symm_apply_id,
        Equiv.apply_symm_apply]⟩⟩

attribute [local instance] prodComparison_iso

open Limits

/--
If a reflective subcategory is an exponential ideal, then the reflector preserves binary products.
This is the converse of `exponentialIdeal_of_preserves_binary_products`.
-/
/-
**CategoryTheory.preservesBinaryProducts_of_exponentialIdeal** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory`。
形式化陈述：preservesBinaryProducts_of_exponentialIdeal : PreservesLimitsOfShape (Disc
rete WalkingPair) (reflector i) where preservesLimit {K}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.preservesLimit_pair_of_isIso_pr
odComparison`：preservesLimit_pair_of_isIso_prodComparison (A B : C) [IsIso (prod
Comparison F A B)] : PreservesLimit (pair A B) F
· 使用定理 `CategoryTheory.prodComparison_iso`：prodComparison_iso (A B : C) : IsIso 
(prodComparison (reflector i) A B)

--- 原说明 ---
If a reflective subcategory is an exponential ideal, then the reflector preserve
s binary products.
This is the converse of `exponentialIdeal_of_preserves_binary_products`.
-/
lemma preservesBinaryProducts_of_exponentialIdeal :
    PreservesLimitsOfShape (Discrete WalkingPair) (reflector i) where
  preservesLimit {K} :=
    letI := preservesLimit_pair_of_isIso_prodComparison
      (reflector i) (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
    Limits.preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm

/--
If a reflective subcategory is an exponential ideal, then the reflector preserves finite products.
-/
/-
**CategoryTheory.Limits.PreservesFiniteProducts.of_exponentialIdeal** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Limits.PreservesFiniteProducts`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₁, u₂} D]   (i : CategoryTheory.Functor D C)
 [inst_2 : CategoryTheory.CartesianMonoidalCategory C]   [inst_3 : CategoryTheor
y.Reflective i] [inst_4 : CategoryTheory.MonoidalClosed C]   [CategoryTheory.Car
tesianMonoidalCategory D] [CategoryTheory.ExponentialIdeal i] [CategoryTheory.Br
aidedCategory C],   CategoryTheory.Limits.PreservesFiniteProducts (CategoryTheor
y.reflector i)
参数：i : CategoryTheory.Functor D C；CategoryTheory.reflector i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.preservesBinaryProducts_of_exponentialIdeal`：preservesBin
aryProducts_of_exponentialIdeal : PreservesLimitsOfShape (Discrete WalkingPair) 
(reflector i) where preservesLimit {K}
· 使用引理 `CategoryTheory.leftAdjoint_preservesTerminal_of_reflective`：leftAdjoint_
preservesTerminal_of_reflective (R : D ⥤ C) [Reflective R] : PreservesLimitsOfSh
ape (Discrete.{v} PEmpty) (monadicLeftAdjoint R)…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteProducts.of_preserves_binary_and_te
rminal`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [
inst_1 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.F…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…

--- 原说明 ---
If a reflective subcategory is an exponential ideal, then the reflector preserve
s finite products.
-/
lemma Limits.PreservesFiniteProducts.of_exponentialIdeal : PreservesFiniteProducts (reflector i) :=
  have := preservesBinaryProducts_of_exponentialIdeal i
  have : PreservesLimitsOfShape _ (reflector i) := leftAdjoint_preservesTerminal_of_reflective.{0} i
  .of_preserves_binary_and_terminal _

end

end CategoryTheory

