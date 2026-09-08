/-
Copyright (c) 2024 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!

# The opposite category of an enriched category

When a monoidal category `V` is braided, we may define the opposite `V`-category of a
`V`-category. The symmetry map is required to define the composition morphism.

This file constructs the opposite `V`-category as an instance on the type `Cᵒᵖ` and constructs an
equivalence between
* `ForgetEnrichment V (Cᵒᵖ)`, the underlying category of the `V`-category `Cᵒᵖ`; and
* `(ForgetEnrichment V C)ᵒᵖ`, the opposite category of the underlying category of `C`.

We also show that if `C` is an enriched ordinary category (i.e. a category enriched in `V`
equipped with an identification `(X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))`) then `Cᵒᵖ` is again
an enriched ordinary category.

-/

@[expose] public section

universe v₁ u₁ v u

namespace CategoryTheory

open MonoidalCategory BraidedCategory

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V] [BraidedCategory V]

section

variable (C : Type u) [EnrichedCategory V C]

/-- For a `V`-category `C`, construct the opposite `V`-category structure on the type `Cᵒᵖ`
using the braiding in `V`. -/
/-
**CategoryTheory.EnrichedCategory.opposite** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.EnrichedCategory`。
形式化陈述：(V : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       [CategoryTheory.BraidedCategory V
] →         (C : Type u) → [CategoryTheory.EnrichedCategory V C] → CategoryTheor
y.EnrichedCategory V Cᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a `V`-category `C`, construct the opposite `V`-category structure on the typ
e `Cᵒᵖ`
using the braiding in `V`.
-/
instance EnrichedCategory.opposite : EnrichedCategory V Cᵒᵖ where
  Hom y x := EnrichedCategory.Hom x.unop y.unop
  id x := EnrichedCategory.id x.unop
  comp z y x := (β_ _ _).hom ≫ EnrichedCategory.comp (x.unop) (y.unop) (z.unop)
  id_comp _ _ := by
    simp only [braiding_naturality_left_assoc, braiding_tensorUnit_left,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.comp_id _ _
  comp_id _ _ := by
    simp only [braiding_naturality_right_assoc, braiding_tensorUnit_right,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.id_comp _ _
  assoc _ _ _ _ := by
    simp only [braiding_naturality_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← EnrichedCategory.assoc]
    simp only [braiding_tensor_left_hom, Category.assoc, Iso.inv_hom_id_assoc,
      braiding_naturality_right_assoc, braiding_tensor_right_hom]

end

/-- Unfold the definition of composition in the enriched opposite category. -/
@[reassoc]
/-
**CategoryTheory.eComp_op_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：eComp_op_eq {C : Type u} [EnrichedCategory V C] (x y z : Cᵒᵖ) : eComp V z 
y x = (β_ _ _).hom ≫ eComp V x.unop y.unop z.unop
参数：x y z : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unfold the definition of composition in the enriched opposite category.
-/
lemma eComp_op_eq {C : Type u} [EnrichedCategory V C] (x y z : Cᵒᵖ) :
    eComp V z y x = (β_ _ _).hom ≫ eComp V x.unop y.unop z.unop :=
  rfl

/-- When composing a tensor product of morphisms with the `V`-composition morphism in `Cᵒᵖ`,
this re-writes the `V`-composition to be in `C` and moves the braiding to the left. -/
@[reassoc]
/-
**CategoryTheory.tensorHom_eComp_op_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
`。
形式化陈述：tensorHom_eComp_op_eq {C : Type u} [EnrichedCategory V C] {x y z : Cᵒᵖ} {v
 w : V} (f : v ⟶ EnrichedCategory.Hom z y) (g : w ⟶ EnrichedCategory.Hom y x) : 
(f otimesₘ g) ≫ eComp V z y x = (β_ v w).hom ≫ (g otimesₘ f) ≫ eComp V x.unop y.
unop z.unop
参数：f : v ⟶ EnrichedCategory.Hom z y；g : w ⟶ EnrichedCategory.Hom y x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.eComp_op_eq`：eComp_op_eq {C : Type u} [EnrichedCategory V
 C] (x y z : Cᵒᵖ) : eComp V z y x = (β_ _ _).hom ≫ eComp V x.unop y.unop z.unop
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCate
gory C]   [inst_2 : CategoryTheory.BraidedCate…

--- 原说明 ---
When composing a tensor product of morphisms with the `V`-composition morphism i
n `Cᵒᵖ`,
this re-writes the `V`-composition to be in `C` and moves the braiding to the le
ft.
-/
lemma tensorHom_eComp_op_eq {C : Type u} [EnrichedCategory V C] {x y z : Cᵒᵖ} {v w : V}
    (f : v ⟶ EnrichedCategory.Hom z y) (g : w ⟶ EnrichedCategory.Hom y x) :
    (f ⊗ₘ g) ≫ eComp V z y x = (β_ v w).hom ≫ (g ⊗ₘ f) ≫ eComp V x.unop y.unop z.unop := by
  rw [eComp_op_eq]
  exact braiding_naturality_assoc f g _

-- This section establishes the equivalence on underlying categories
section

open ForgetEnrichment

variable (C : Type u) [EnrichedCategory V C]

/-- The functor going from the underlying category of the enriched category `Cᵒᵖ`
to the opposite of the underlying category of the enriched category `C`. -/
/-
**CategoryTheory.forgetEnrichmentOppositeEquivalence.functor** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.forgetEnrichmentOppositeEquivalence`。
形式化陈述：(V : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       [inst_2 : CategoryTheory.BraidedC
ategory V] →         (C : Type u) →           [inst_3 : CategoryTheory.EnrichedC
ategory V C] →             CategoryTheory.Functor (CategoryTheory.ForgetEnrichme
nt V Cᵒᵖ) (CategoryTheory.ForgetEnrichment V C)ᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor going from the underlying category of the enriched category `Cᵒᵖ`
to the opposite of the underlying category of the enriched category `C`.
-/
def forgetEnrichmentOppositeEquivalence.functor :
    ForgetEnrichment V Cᵒᵖ ⥤ (ForgetEnrichment V C)ᵒᵖ where
  obj x := x
  map {x y} f := f.op
  map_comp {x y z} f g := by
    have : (f ≫ g) = homTo V (f ≫ g) := rfl
    rw [this, ForgetEnrichment.homTo_comp, Category.assoc, tensorHom_eComp_op_eq,
      leftUnitor_inv_braiding_assoc, ← unitors_inv_equal, ← Category.assoc]
    congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The functor going from the opposite of the underlying category of the enriched category `C`
to the underlying category of the enriched category `Cᵒᵖ`. -/
/-
**CategoryTheory.forgetEnrichmentOppositeEquivalence.inverse** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.forgetEnrichmentOppositeEquivalence`。
形式化陈述：(V : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       [inst_2 : CategoryTheory.BraidedC
ategory V] →         (C : Type u) →           [inst_3 : CategoryTheory.EnrichedC
ategory V C] →             CategoryTheory.Functor (CategoryTheory.ForgetEnrichme
nt V C)ᵒᵖ (CategoryTheory.ForgetEnrichment V Cᵒᵖ)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor going from the opposite of the underlying category of the enriched c
ategory `C`
to the underlying category of the enriched category `Cᵒᵖ`.
-/
def forgetEnrichmentOppositeEquivalence.inverse :
    (ForgetEnrichment V C)ᵒᵖ ⥤ ForgetEnrichment V Cᵒᵖ where
  obj x := x
  map {x y} f := f.unop
  map_comp {x y z} f g := by
    have : g.unop ≫ f.unop = homTo V (g.unop ≫ f.unop) := rfl
    dsimp
    rw [this, ForgetEnrichment.homTo_comp, Category.assoc, unitors_inv_equal,
      ← leftUnitor_inv_braiding_assoc]
    have : (β_ _ _).hom ≫ (homTo V g.unop ⊗ₘ homTo V f.unop) ≫
      eComp V («to» V z.unop) («to» V y.unop) («to» V x.unop) =
      ((homTo V f.unop) ⊗ₘ (homTo V g.unop)) ≫ eComp V x y z := (tensorHom_eComp_op_eq V _ _).symm
    rw [this, ← Category.assoc]
    congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence between the underlying category of the enriched category `Cᵒᵖ` and
the opposite of the underlying category of the enriched category `C`. -/
@[simps]
/-
**CategoryTheory.forgetEnrichmentOppositeEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory`。
形式化陈述：forgetEnrichmentOppositeEquivalence : ForgetEnrichment V Cᵒᵖ ≌ (ForgetEnri
chment V C)ᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the underlying category of the enriched category `Cᵒᵖ` a
nd
the opposite of the underlying category of the enriched category `C`.
-/
def forgetEnrichmentOppositeEquivalence : ForgetEnrichment V Cᵒᵖ ≌ (ForgetEnrichment V C)ᵒᵖ where
  functor := forgetEnrichmentOppositeEquivalence.functor V C
  inverse := forgetEnrichmentOppositeEquivalence.inverse V C
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- If `D` is an enriched ordinary category then `Dᵒᵖ` is an enriched ordinary category. -/
/-
**CategoryTheory.EnrichedOrdinaryCategory.opposite** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.EnrichedOrdinaryCategory`。
形式化陈述：(V : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       [CategoryTheory.BraidedCategory V
] →         {D : Type u} →           [inst_3 : CategoryTheory.Category.{v, u} D]
 →             [CategoryTheory.EnrichedOrdinaryCategory V D] → CategoryTheory.En
richedOrdinaryCategory V Dᵒᵖ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `D` is an enriched ordinary category then `Dᵒᵖ` is an enriched ordinary categ
ory.
-/
instance EnrichedOrdinaryCategory.opposite {D : Type u} [Category.{v} D]
    [EnrichedOrdinaryCategory V D] : EnrichedOrdinaryCategory V Dᵒᵖ where
  homEquiv := Quiver.Hom.opEquiv.symm.trans homEquiv
  homEquiv_id x := homEquiv_id (x.unop)
  homEquiv_comp f g := by
    simp only [tensorHom_eComp_op_eq, leftUnitor_inv_braiding_assoc, ← unitors_inv_equal]
    exact homEquiv_comp g.unop f.unop

end

end CategoryTheory

