/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Equivalences of sheaf categories

Given a site `(C, J)` and a category `D` which is equivalent to `C`, with `C` and `D` possibly large
and possibly in different universes, we transport the Grothendieck topology `J` on `C` to `D` and
prove that the sheaf categories are equivalent.

We also prove that sheafification and the property `HasSheafCompose` transport nicely over this
equivalence, and apply it to essentially small sites. We also provide instances for existence of
sufficiently small limits in the sheaf category on the essentially small site.

## Main definitions

* `CategoryTheory.Equivalence.sheafCongr` is the equivalence of sheaf categories.

* `CategoryTheory.Equivalence.transportAndSheafify` is the functor which takes a presheaf on `C`,
  transports it over the equivalence to `D`, sheafifies there and then transports back to `C`.

* `CategoryTheory.Equivalence.transportSheafificationAdjunction`: `transportAndSheafify` is
  left adjoint to the functor taking a sheaf to its underlying presheaf.

* `CategoryTheory.smallSheafify` is the functor which takes a presheaf on an essentially small site
  `(C, J)`, transports to a small model, sheafifies there and then transports back to `C`.

* `CategoryTheory.smallSheafificationAdjunction`: `smallSheafify` is left adjoint to the functor
  taking a sheaf to its underlying presheaf.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w

namespace CategoryTheory

open CategoryTheory.Functor Limits GrothendieckTopology

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) (e : C ≌ D) (G : D ⥤ C)
variable (A : Type u₃) [Category.{v₃} A]

namespace Equivalence

/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [G.IsEquivalence] : IsCoverDense G J where
  is_cover U := by
    let e := (asEquivalence G).symm
    convert! J.top_mem U
    ext Y f
    simp only [Sieve.top_apply, iff_true]
    let g : e.inverse.obj _ ⟶ U := (e.unitInv.app Y) ≫ f
    have : (Sieve.coverByImage e.inverse U).arrows g := Presieve.in_coverByImage _ g
    replace := Sieve.downward_closed _ this (e.unit.app Y)
    simpa [g] using! this
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : e.functor.IsDenseSubsite J (e.inverse.inducedTopology J) := by
  have : J = e.functor.inducedTopology (e.inverse.inducedTopology J) := by
    ext
    simp [mem_inducedTopology_iff_of_isCoverDense, mem_inducedTopology_iff_of_isCoverDense,
      Sieve.functorPushforward_equivalence_eq_pullback]
  nth_rw 1 [this]
  infer_instance
/-
**CategoryTheory.Equivalence.eq_inducedTopology_of_isDenseSubsite** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Equivalence`。
形式化陈述：eq_inducedTopology_of_isDenseSubsite [e.inverse.IsDenseSubsite K J] : K = 
e.inverse.inducedTopology J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.ext`：ext {J₁ J₂ : GrothendieckTopolo
gy C} (h : (J₁ : forall X : C, Set (Sieve X)) = J₂) : J₁ = J₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense`：mem_indu
cedTopology_iff_of_isCoverDense [G.IsCoverDense K] {X : C} (S : Sieve X) : S in 
G.inducedTopology K X ↔ S.functorPushforward G in K …
· 使用定理 `CategoryTheory.Functor.locallyCoverDense_of_isCoverDense`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.instIsCoverDenseOfIsEquivalence`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.Grothendieck
Topology C) {D : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.Functor.functorPushforward_mem_iff`：functorPushforward_me
m_iff {X : C} {S : Sieve X} [G.IsDenseSubsite J K] : S.functorPushforward G in K
 _ ↔ S in J _
-/
lemma eq_inducedTopology_of_isDenseSubsite [e.inverse.IsDenseSubsite K J] :
    K = e.inverse.inducedTopology J := by
  ext
  rw [mem_inducedTopology_iff_of_isCoverDense]
  exact (e.inverse.functorPushforward_mem_iff K J).symm

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Equivalence.isDenseSubsite_functor_of_isCocontinuous** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Equivalence`。
形式化陈述：isDenseSubsite_functor_of_isCocontinuous [e.functor.IsCocontinuous J K] [e
.inverse.IsCocontinuous K J] : e.functor.IsDenseSubsite J K where functorPushfor
ward_mem_iff {X S}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.instIsCoverDenseOfIsEquivalence`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.Grothendieck
Topology C) {D : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaloisCoinsertion.u_l_eq`：∀ {α : Type u} {β : Type v} {u : α → β} {l : β
 → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsertion l 
u) (b : β), u …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `CategoryTheory.Functor.cover_lift`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (G : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Equivalence.fun_inv_map`：fun_inv_map (e : C ≌ D) (X Y : D
) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitI
nv.app Y
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Equivalence.counitInv_functor_comp`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   (e : C ≌ D) (X : C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
-/
lemma isDenseSubsite_functor_of_isCocontinuous
    [e.functor.IsCocontinuous J K] [e.inverse.IsCocontinuous K J] :
    e.functor.IsDenseSubsite J K where
  functorPushforward_mem_iff {X S} := by
    constructor
    · intro H
      refine J.superset_covering ?_ (e.functor.cover_lift J K H)
      rw [(Sieve.fullyFaithfulFunctorGaloisCoinsertion e.functor X).u_l_eq S]
    · intro H
      refine K.superset_covering ?_
        (e.inverse.cover_lift K J (J.pullback_stable (e.unitInv.app X) H))
      exact fun Y f (H : S _) ↦ ⟨_, _, e.counitInv.app Y, H, by simp⟩
/-
**CategoryTheory.Equivalence.isDenseSubsite_inverse_of_isCocontinuous** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Equivalence`。
形式化陈述：isDenseSubsite_inverse_of_isCocontinuous [e.functor.IsCocontinuous J K] [e
.inverse.IsCocontinuous K J] : e.inverse.IsDenseSubsite K J
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Equivalence.isDenseSubsite_functor_of_isCocontinuous`：isD
enseSubsite_functor_of_isCocontinuous [e.functor.IsCocontinuous J K] [e.inverse.
IsCocontinuous K J] : e.functor.IsDenseSubsite J K where …
-/
lemma isDenseSubsite_inverse_of_isCocontinuous
    [e.functor.IsCocontinuous J K] [e.inverse.IsCocontinuous K J] :
    e.inverse.IsDenseSubsite K J :=
  have : e.symm.functor.IsCocontinuous K J := inferInstanceAs (e.inverse.IsCocontinuous _ _)
  have : e.symm.inverse.IsCocontinuous J K := inferInstanceAs (e.functor.IsCocontinuous _ _)
  isDenseSubsite_functor_of_isCocontinuous _ _ e.symm

variable [e.inverse.IsDenseSubsite K J]
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : e.functor.IsDenseSubsite J K := by
  rw [e.eq_inducedTopology_of_isDenseSubsite J K]
  infer_instance

/-- The functor in the equivalence of sheaf categories. -/
@[simps!]
/-
**CategoryTheory.Equivalence.sheafCongr.functor** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Equivalence.sheafCongr`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (J : C
ategoryTheory.GrothendieckTopology C) →       {D : Type u₂} →         [inst_1 : 
CategoryTheory.Category.{v₂, u₂} D] →           (K : CategoryTheory.Grothendieck
Topology D) →             (e : C ≌ D) →               (A : Type u₃) →           
      [inst_2 : CategoryTheory.Category.{v₃, u₃} A] →                   [Categor
yTheory.Functor.IsDenseSubsite K J e.inverse] →                     CategoryTheo
ry.Functor (CategoryTheory.Sheaf J A) (CategoryTheory.Sheaf K A)
参数：J : CategoryTheory.GrothendieckTopology C；K : CategoryTheory.GrothendieckTopo
logy D；e : C ≌ D；A : Type u₃；CategoryTheory.Sheaf J A；CategoryTheory.Sheaf K A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor in the equivalence of sheaf categories.
-/
def sheafCongr.functor : Sheaf J A ⥤ Sheaf K A :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj e.inverse.op)
    (e.inverse.op_comp_isSheaf _ _)

/-- The inverse in the equivalence of sheaf categories. -/
@[simps!]
/-
**CategoryTheory.Equivalence.sheafCongr.inverse** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Equivalence.sheafCongr`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (J : C
ategoryTheory.GrothendieckTopology C) →       {D : Type u₂} →         [inst_1 : 
CategoryTheory.Category.{v₂, u₂} D] →           (K : CategoryTheory.Grothendieck
Topology D) →             (e : C ≌ D) →               (A : Type u₃) →           
      [inst_2 : CategoryTheory.Category.{v₃, u₃} A] →                   [Categor
yTheory.Functor.IsDenseSubsite K J e.inverse] →                     CategoryTheo
ry.Functor (CategoryTheory.Sheaf K A) (CategoryTheory.Sheaf J A)
参数：J : CategoryTheory.GrothendieckTopology C；K : CategoryTheory.GrothendieckTopo
logy D；e : C ≌ D；A : Type u₃；CategoryTheory.Sheaf K A；CategoryTheory.Sheaf J A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse in the equivalence of sheaf categories.
-/
def sheafCongr.inverse : Sheaf K A ⥤ Sheaf J A :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj e.functor.op)
    (e.functor.op_comp_isSheaf _ _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit iso in the equivalence of sheaf categories. -/
@[simps!]
/-
**CategoryTheory.Equivalence.sheafCongr.unitIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Equivalence.sheafCongr`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (J : C
ategoryTheory.GrothendieckTopology C) →       {D : Type u₂} →         [inst_1 : 
CategoryTheory.Category.{v₂, u₂} D] →           (K : CategoryTheory.Grothendieck
Topology D) →             (e : C ≌ D) →               (A : Type u₃) →           
      [inst_2 : CategoryTheory.Category.{v₃, u₃} A] →                   [inst_3 
: CategoryTheory.Functor.IsDenseSubsite K J e.inverse] →                     Cat
egoryTheory.Functor.id (CategoryTheory.Sheaf J A) ≅                       (Categ
oryTheory.Equivalence.sheafCongr.functor J K e A).comp                         (
CategoryTheory.Equivalence.sheafCongr.inverse J K e A)
参数：J : CategoryTheory.GrothendieckTopology C；K : CategoryTheory.GrothendieckTopo
logy D；e : C ≌ D；A : Type u₃；CategoryTheory.Sheaf J A；CategoryTheory.Equivalence
.sheafCongr.functor J K e A；CategoryTheory.Equivalence.sheafCongr.inverse J K e 
A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit iso in the equivalence of sheaf categories.
-/
def sheafCongr.unitIso : 𝟭 (Sheaf J A) ≅ functor J K e A ⋙ inverse J K e A :=
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _ (isoWhiskerRight e.op.unitIso F.obj))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The counit iso in the equivalence of sheaf categories. -/
@[simps!]
/-
**CategoryTheory.Equivalence.sheafCongr.counitIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Equivalence.sheafCongr`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (J : C
ategoryTheory.GrothendieckTopology C) →       {D : Type u₂} →         [inst_1 : 
CategoryTheory.Category.{v₂, u₂} D] →           (K : CategoryTheory.Grothendieck
Topology D) →             (e : C ≌ D) →               (A : Type u₃) →           
      [inst_2 : CategoryTheory.Category.{v₃, u₃} A] →                   [inst_3 
: CategoryTheory.Functor.IsDenseSubsite K J e.inverse] →                     (Ca
tegoryTheory.Equivalence.sheafCongr.inverse J K e A).comp                       
  (CategoryTheory.Equivalence.sheafCongr.functor J K e A) ≅                     
  CategoryTheory.Functor.id (CategoryTheory.Sheaf K A)
参数：J : CategoryTheory.GrothendieckTopology C；K : CategoryTheory.GrothendieckTopo
logy D；e : C ≌ D；A : Type u₃；CategoryTheory.Equivalence.sheafCongr.inverse J K e
 A；CategoryTheory.Equivalence.sheafCongr.functor J K e A；CategoryTheory.Sheaf K 
A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit iso in the equivalence of sheaf categories.
-/
def sheafCongr.counitIso : inverse J K e A ⋙ functor J K e A ≅ 𝟭 (Sheaf _ A) :=
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _ (isoWhiskerRight e.op.counitIso F.obj))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of sheaf categories. -/
@[simps]
/-
**CategoryTheory.Equivalence.sheafCongr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Equivalence`。
形式化陈述：sheafCongr : Sheaf J A ≌ Sheaf K A where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of sheaf categories.
-/
def sheafCongr : Sheaf J A ≌ Sheaf K A where
  functor := sheafCongr.functor J K e A
  inverse := sheafCongr.inverse J K e A
  unitIso := sheafCongr.unitIso J K e A
  counitIso := sheafCongr.counitIso J K e A
  functor_unitIso_comp X := by
    ext
    simp [← Functor.map_comp, ← op_comp]

variable [HasSheafify K A]

/-- Transport a presheaf to the equivalent category and sheafify there. -/
noncomputable
/-
**CategoryTheory.Equivalence.transportAndSheafify** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：transportAndSheafify : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
-/
def transportAndSheafify : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  e.op.congrLeft.functor ⋙ presheafToSheaf _ _ ⋙ (e.sheafCongr J K A).inverse

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An auxiliary definition for the sheafification adjunction. -/
noncomputable
/-
**CategoryTheory.Equivalence.transportIsoSheafToPresheaf** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Equivalence`。
形式化陈述：transportIsoSheafToPresheaf : (e.sheafCongr J K A).functor ⋙ sheafToPreshe
af K A ⋙ e.op.congrLeft.inverse ≅ sheafToPresheaf J A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def transportIsoSheafToPresheaf : (e.sheafCongr J K A).functor ⋙
    sheafToPresheaf K A ⋙ e.op.congrLeft.inverse ≅ sheafToPresheaf J A :=
  NatIso.ofComponents (fun F ↦ isoWhiskerRight e.op.unitIso.symm F.obj)

/-- Transporting and sheafifying is left adjoint to taking the underlying presheaf. -/
noncomputable
/-
**CategoryTheory.Equivalence.transportSheafificationAdjunction** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Equivalence`。
形式化陈述：transportSheafificationAdjunction : transportAndSheafify J K e A ⊣ sheafTo
Presheaf J A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
-/
def transportSheafificationAdjunction : transportAndSheafify J K e A ⊣ sheafToPresheaf J A :=
  ((e.op.congrLeft.toAdjunction.comp (sheafificationAdjunction _ _)).comp
    (e.sheafCongr J K A).symm.toAdjunction).ofNatIsoRight
    (transportIsoSheafToPresheaf _ _ _ _)
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteLimits <| transportAndSheafify J K e A where
  preservesFiniteLimits _ := comp_preservesLimitsOfShape _ _

include K e in
/-- Transport `HasSheafify` along an equivalence of sites. -/
/-
**CategoryTheory.Equivalence.hasSheafify** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Equivalence`。
形式化陈述：hasSheafify : HasSheafify J A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasSheafify.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) (A : Type u₂)   
[inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.instPreservesFiniteLimitsFunctorOppositeSheaf
TransportAndSheafify`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C
] (J : CategoryTheory.GrothendieckTopology C) {D : Type u₂}   [inst_1 : Category
Th…

--- 原说明 ---
Transport `HasSheafify` along an equivalence of sites.
-/
theorem hasSheafify : HasSheafify J A :=
  HasSheafify.mk' J A (transportSheafificationAdjunction J K e A)

variable {A : Type*} [Category* A] {B : Type*} [Category* B] (F : A ⥤ B)
  [K.HasSheafCompose F]

include K e in
/-
**CategoryTheory.Equivalence.hasSheafCompose** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Equivalence`。
形式化陈述：hasSheafCompose : J.HasSheafCompose F where isSheaf P hP
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.HasSheafCompose.isSheaf`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {A : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} A}   {B : Type u₃} {ins…
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf`：op_comp_isSheaf [Functor.IsConti
nuous F J K] (G : Sheaf K A) : Presheaf.IsSheaf J (F.op ⋙ G.obj)
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用定理 `CategoryTheory.Equivalence.instIsDenseSubsiteFunctor`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopolo
gy C) {D : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Presheaf.isSheaf_of_iso_iff`：isSheaf_of_iso_iff {P P' : C
ᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P'
-/
theorem hasSheafCompose : J.HasSheafCompose F where
  isSheaf P hP := by
    have hP' : Presheaf.IsSheaf K (e.inverse.op ⋙ P ⋙ F) := by
      change Presheaf.IsSheaf K ((_ ⋙ _) ⋙ _)
      apply HasSheafCompose.isSheaf
      exact e.inverse.op_comp_isSheaf K J ⟨P, hP⟩
    replace hP' : Presheaf.IsSheaf J (e.functor.op ⋙ e.inverse.op ⋙ P ⋙ F) :=
      e.functor.op_comp_isSheaf _ _ ⟨_, hP'⟩
    exact (Presheaf.isSheaf_of_iso_iff ((isoWhiskerRight e.op.unitIso.symm (P ⋙ F)))).mp hP'

end Equivalence

variable (B : Type u₄) [Category.{v₄} B] (F : A ⥤ B)

section
variable [EssentiallySmall.{w} C]
variable [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A]
variable [((equivSmallModel C).inverse.inducedTopology J).HasSheafCompose F]

/-- Transport to a small model and sheafify there. -/
noncomputable
/-
**CategoryTheory.smallSheafify** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：smallSheafify : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def smallSheafify : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A := (equivSmallModel C).transportAndSheafify J
  ((equivSmallModel C).inverse.inducedTopology J) A

/--
Transporting to a small model and sheafifying there is left adjoint to the underlying presheaf
functor
-/
noncomputable
/-
**CategoryTheory.smallSheafificationAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：smallSheafificationAdjunction : smallSheafify J A ⊣ sheafToPresheaf J A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def smallSheafificationAdjunction : smallSheafify J A ⊣ sheafToPresheaf J A :=
  (equivSmallModel C).transportSheafificationAdjunction J _ A
/-
**CategoryTheory.hasSheafifyEssentiallySmallSite** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory`。
形式化陈述：hasSheafifyEssentiallySmallSite : HasSheafify J A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.hasSheafify`：hasSheafify : HasSheafify J A
· 使用定理 `CategoryTheory.Functor.instIsDenseSubsiteInducedTopologyOfIsCoverDense`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   
[inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.locallyCoverDense_of_isCoverDense`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.instIsCoverDenseOfIsEquivalence`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.Grothendieck
Topology C) {D : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
-/
lemma hasSheafifyEssentiallySmallSite : HasSheafify J A :=
  (equivSmallModel C).hasSheafify J ((equivSmallModel C).inverse.inducedTopology J) A
/-
**CategoryTheory.hasSheafComposeEssentiallySmallSite** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory`。
形式化陈述：hasSheafComposeEssentiallySmallSite : HasSheafCompose J F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.hasSheafCompose`：hasSheafCompose : J.HasSheaf
Compose F where isSheaf P hP
· 使用定理 `CategoryTheory.Functor.instIsDenseSubsiteInducedTopologyOfIsCoverDense`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   
[inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.locallyCoverDense_of_isCoverDense`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.instIsCoverDenseOfIsEquivalence`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.Grothendieck
Topology C) {D : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
-/
instance hasSheafComposeEssentiallySmallSite : HasSheafCompose J F :=
  (equivSmallModel C).hasSheafCompose J ((equivSmallModel C).inverse.inducedTopology J) F

omit [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A] in
/-
**CategoryTheory.hasLimitsEssentiallySmallSite** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：hasLimitsEssentiallySmallSite [HasLimits <| Sheaf ((equivSmallModel C).inv
erse.inducedTopology J) A] : HasLimitsOfSize.{max v₃ w, max v₃ w} Sheaf J A
参数：(equivSmallModel C).inverse.inducedTopology J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.has_limits_of_equivalence`：has_limits_of_equiv
alence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfSize.{v, u} C] : HasLimitsOfSiz
e.{v, u} D
· 使用定理 `CategoryTheory.Functor.instIsDenseSubsiteInducedTopologyOfIsCoverDense`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   
[inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.locallyCoverDense_of_isCoverDense`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.instIsCoverDenseOfIsEquivalence`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.Grothendieck
Topology C) {D : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
lemma hasLimitsEssentiallySmallSite
    [HasLimits <| Sheaf ((equivSmallModel C).inverse.inducedTopology J) A] :
    HasLimitsOfSize.{max v₃ w, max v₃ w} <| Sheaf J A :=
  Adjunction.has_limits_of_equivalence ((equivSmallModel C).sheafCongr J
    ((equivSmallModel C).inverse.inducedTopology J) A).functor
/-
**CategoryTheory.hasColimitsEssentiallySmallSite** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory`。
形式化陈述：hasColimitsEssentiallySmallSite [HasColimits <| Sheaf ((equivSmallModel C)
.inverse.inducedTopology J) A] : HasColimitsOfSize.{max v₃ w, max v₃ w} Sheaf J 
A
参数：(equivSmallModel C).inverse.inducedTopology J。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.has_colimits_of_equivalence`：has_colimits_of_e
quivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfSize.{v, u} D] : HasColim
itsOfSize.{v, u} C
· 使用定理 `CategoryTheory.Functor.instIsDenseSubsiteInducedTopologyOfIsCoverDense`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   
[inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.locallyCoverDense_of_isCoverDense`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.instIsCoverDenseOfIsEquivalence`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.Grothendieck
Topology C) {D : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance hasColimitsEssentiallySmallSite
    [HasColimits <| Sheaf ((equivSmallModel C).inverse.inducedTopology J) A] :
    HasColimitsOfSize.{max v₃ w, max v₃ w} <| Sheaf J A :=
  Adjunction.has_colimits_of_equivalence ((equivSmallModel C).sheafCongr J
    ((equivSmallModel C).inverse.inducedTopology J) A).functor

end

namespace GrothendieckTopology

variable {A}
variable [G.IsCoverDense J] [G.Full]

section
variable [Functor.IsContinuous G K J] [(G.sheafPushforwardContinuous A K J).EssSurj]

open Localization

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.W_inverseImage_whiskeringLeft** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：W_inverseImage_whiskeringLeft : K.W.inverseImage ((whiskeringLeft Dᵒᵖ Cᵒᵖ 
A).obj G.op) = J.W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.W_eq_isLocal_range_sheafToPresheaf_o
bj`：W_eq_isLocal_range_sheafToPresheaf_obj : J.W = ObjectProperty.isLocal (· in 
Set.range (sheafToPresheaf J A).obj)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.isoClosure_isLocal`：isoClosure_isLocal : P
.isoClosure.isLocal = P.isLocal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用引理 `CategoryTheory.Functor.whiskerLeft_obj_map_bijective_of_isCoverDense`：wh
iskerLeft_obj_map_bijective_of_isCoverDense (G : C ⥤ D) [G.IsCoverDense K] [G.Is
LocallyFull K] {A : Type*} [Category* A] (P Q : Dᵒᵖ ⥤ A) (…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用引理 `CategoryTheory.MorphismProperty.inverseImage_iff`：inverseImage_iff (P : 
MorphismProperty D) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : P.inverseImage F f ↔ P (
F.map f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma W_inverseImage_whiskeringLeft :
    K.W.inverseImage ((whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj G.op) = J.W := by
  ext P Q f
  have h₁ : K.W (A := A) =
    ObjectProperty.isLocal (· ∈ Set.range (sheafToPresheaf J A ⋙
      ((whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj G.op)).obj) := by
    rw [W_eq_isLocal_range_sheafToPresheaf_obj, ← ObjectProperty.isoClosure_isLocal]
    conv_rhs => rw [← ObjectProperty.isoClosure_isLocal]
    apply congr_arg
    ext P
    constructor
    · rintro ⟨_, ⟨R, rfl⟩, ⟨e⟩⟩
      exact ⟨_, ⟨_, rfl⟩, ⟨e.trans ((sheafToPresheaf _ _).mapIso
        ((G.sheafPushforwardContinuous A K J).objObjPreimageIso R).symm)⟩⟩
    · rintro ⟨_, ⟨R, rfl⟩, ⟨e⟩⟩
      exact ⟨G.op ⋙ R.obj, ⟨(G.sheafPushforwardContinuous A K J).obj R, rfl⟩, ⟨e⟩⟩
  have h₂ : ∀ (R : Sheaf J A),
    Function.Bijective (fun (g : G.op ⋙ Q ⟶ G.op ⋙ R.obj) ↦ whiskerLeft G.op f ≫ g) ↔
      Function.Bijective (fun (g : Q ⟶ R.obj) ↦ f ≫ g) := fun R ↦ by
    rw [← Function.Bijective.of_comp_iff _
      (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense J G Q R.obj R.property)]
    exact Function.Bijective.of_comp_iff'
      (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense J G P R.obj R.property)
        (fun g ↦ f ≫ g)
  rw [h₁, J.W_eq_isLocal_range_sheafToPresheaf_obj, MorphismProperty.inverseImage_iff]
  constructor
  · rintro h _ ⟨R, rfl⟩
    exact (h₂ R).1 (h _ ⟨R, rfl⟩)
  · rintro h _ ⟨R, rfl⟩
    exact (h₂ R).2 (h _ ⟨R, rfl⟩)
/-
**CategoryTheory.GrothendieckTopology.W_whiskerLeft_iff** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：W_whiskerLeft_iff {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) : K.W (whiskerLeft G.op f) ↔
 J.W f
参数：f : P ⟶ Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.GrothendieckTopology.W_inverseImage_whiskeringLeft`：W_inv
erseImage_whiskeringLeft : K.W.inverseImage ((whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj G.op
) = J.W
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma W_whiskerLeft_iff {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    K.W (whiskerLeft G.op f) ↔ J.W f := by
  rw [← W_inverseImage_whiskeringLeft J K G]
  rfl

end

/-
**CategoryTheory.GrothendieckTopology.PreservesSheafification.transport** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology.PreservesSheafification`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryT
heory.GrothendieckTopology C) {D : Type u₂}   [inst_1 : CategoryTheory.Category.
{v₂, u₂} D] (K : CategoryTheory.GrothendieckTopology D)   (G : CategoryTheory.Fu
nctor D C) {A : Type u₃} [inst_2 : CategoryTheory.Category.{v₃, u₃} A] (B : Type
 u₄)   [inst_3 : CategoryTheory.Category.{v₄, u₄} B] (F : CategoryTheory.Functor
 A B) [G.IsCoverDense J] [G.Full]   [inst_6 : G.IsContinuous K J] [(G.sheafPushf
orwardContinuous B K J).EssSurj]   [(G.sheafPushforwardContinuous A K J).EssSurj
] [K.PreservesSheafification F], J.PreservesSheafification F
参数：J : CategoryTheory.GrothendieckTopology C；K : CategoryTheory.GrothendieckTopo
logy D；G : CategoryTheory.Functor D C；B : Type u₄；F : CategoryTheory.Functor A B
；G.sheafPushforwardContinuous B K J；G.sheafPushforwardContinuous A K J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.W_of_preservesSheafification`：W_of_p
reservesSheafification {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) (hf : J.W f) : J.W (whisk
erRight f F)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.GrothendieckTopology.W_whiskerLeft_iff`：W_whiskerLeft_iff
 {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) : K.W (whiskerLeft G.op f) ↔ J.W f
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `CategoryTheory.MorphismProperty.instHasOfPostcompPropertyIsomorphismsOfR
espectsIso`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : Catego
ryTheory.MorphismProperty C) [W.RespectsIso],   W.HasOfPostcompProperty …
· 使用定理 `CategoryTheory.ObjectProperty.instRespectsIsoIsLocal`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.ObjectProperty 
C),   P.isLocal.RespectsIso
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `CategoryTheory.MorphismProperty.of_precomp`：of_precomp [W.HasOfPrecompPr
operty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f) (hfg : W (f ≫ g)) : W
 g
· 使用定理 `CategoryTheory.MorphismProperty.instHasOfPrecompPropertyIsomorphismsOfRe
spectsIso`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : Categor
yTheory.MorphismProperty C) [W.RespectsIso],   W.HasOfPrecompProperty (…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Functor.whiskerRight_left`：whiskerRight_left (F : B ⥤ C) 
{G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) : whiskerRight (whiskerLeft F α) K = (Func
tor.associator _ _ _).hom ≫ wh…
-/
lemma PreservesSheafification.transport
    [Functor.IsContinuous G K J]
    [(G.sheafPushforwardContinuous B K J).EssSurj]
    [(G.sheafPushforwardContinuous A K J).EssSurj]
    [K.PreservesSheafification F] : J.PreservesSheafification F where
  le P Q f hf := by
    rw [← J.W_whiskerLeft_iff (G := G) (K := K)] at hf
    have := K.W_of_preservesSheafification F (whiskerLeft G.op f) hf
    rw [whiskerRight_left] at this
    have := K.W.of_postcomp (W' := MorphismProperty.isomorphisms _) _ _ (Iso.isIso_inv _) <|
      K.W.of_precomp (W' := MorphismProperty.isomorphisms _) _ _ (Iso.isIso_hom _) this
    rwa [K.W_whiskerLeft_iff (G := G) (J := J) (f := whiskerRight f F)] at this

variable [Functor.IsContinuous G K J] [(G.sheafPushforwardContinuous A K J).EssSurj]
variable [G.IsCocontinuous K J] {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
variable [K.WEqualsLocallyBijective A]
/-
**CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.transport** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryT
heory.GrothendieckTopology C) {D : Type u₂}   [inst_1 : CategoryTheory.Category.
{v₂, u₂} D] (K : CategoryTheory.GrothendieckTopology D)   (G : CategoryTheory.Fu
nctor D C) {A : Type u₃} [inst_2 : CategoryTheory.Category.{v₃, u₃} A] [G.IsCove
rDense J]   [G.Full] [inst_5 : G.IsContinuous K J] [(G.sheafPushforwardContinuou
s A K J).EssSurj] [G.IsCocontinuous K J]   {FA : A → A → Type u_1} {CA : A → Typ
e u_2} [inst_8 : (X Y : A) → FunLike (FA X Y) (CA X) (CA Y)]   [inst_9 : Categor
yTheory.ConcreteCategory A FA] [K.WEqualsLocallyBijective A],   CategoryTheory.C
overPreserving K J G → J.WEqualsLocallyBijective A
参数：J : CategoryTheory.GrothendieckTopology C；K : CategoryTheory.GrothendieckTopo
logy D；G : CategoryTheory.Functor D C；G.sheafPushforwardContinuous A K J；X Y : A
；FA X Y；CA X；CA Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.GrothendieckTopology.W_whiskerLeft_iff`：W_whiskerLeft_iff
 {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) : K.W (whiskerLeft G.op f) ↔ J.W f
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_whisker_iff`：isLocallyInjecti
ve_whisker_iff (hH : CoverPreserving J K H) [H.IsCocontinuous J K] [H.IsCoverDen
se K] : IsLocallyInjective J (whiskerLeft H.…
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_whisker_iff`：isLocallySurjec
tive_whisker_iff (hH : CoverPreserving J K H) [H.IsCocontinuous J K] [H.IsCoverD
ense K] : IsLocallySurjective J (whiskerLeft …
· 使用引理 `CategoryTheory.GrothendieckTopology.W_iff_isLocallyBijective`：W_iff_isLo
callyBijective : J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presheaf.IsLocallySur
jective J f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma WEqualsLocallyBijective.transport (hG : CoverPreserving K J G) :
    J.WEqualsLocallyBijective A where
  iff f := by
    rw [← W_whiskerLeft_iff J K G f, ← Presheaf.isLocallyInjective_whisker_iff K J G f hG,
      ← Presheaf.isLocallySurjective_whisker_iff K J G f hG, W_iff_isLocallyBijective]

variable [EssentiallySmall.{w} C]
  [∀ (X : Cᵒᵖ), HasLimitsOfShape (StructuredArrow X (equivSmallModel C).inverse.op) A]
/-
**CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology.WEqualsLocallyBi
jective`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryT
heory.GrothendieckTopology C) {A : Type u₃}   [inst_1 : CategoryTheory.Category.
{v₃, u₃} A] {FA : A → A → Type u_1} {CA : A → Type u_2}   [inst_2 : (X Y : A) → 
FunLike (FA X Y) (CA X) (CA Y)] [inst_3 : CategoryTheory.ConcreteCategory A FA] 
  [inst_4 : CategoryTheory.EssentiallySmall.{w, v₁, u₁} C]   [∀ (X : Cᵒᵖ),      
 CategoryTheory.Limits.HasLimitsOfShape         (CategoryTheory.StructuredArrow 
X (CategoryTheory.equivSmallModel C).inverse.op) A]   [((CategoryTheory.equivSma
llModel C).inverse.inducedTopology J).WEqualsLocallyBijective A],   J.WEqualsLoc
allyBijective A
参数：J : CategoryTheory.GrothendieckTopology C；X Y : A；FA X Y；CA X；CA Y；X : Cᵒᵖ；Ca
tegoryTheory.StructuredArrow X (CategoryTheory.equivSmallModel C).inverse.op；(Ca
tegoryTheory.equivSmallModel C).inverse.inducedTopology J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.transport`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.G
rothendieckTopology C) {D : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.instIsCoverDenseOfIsEquivalence`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.Grothendieck
Topology C) {D : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.instIsContinuousInducedTopology`：∀ {C : Type u₁} 
{D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsEquivalenceSheafSheafPushfor
wardContinuous`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.
{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.instIsDenseSubsiteInducedTopologyOfIsCoverDense`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   
[inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.locallyCoverDense_of_isCoverDense`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsCocontinuous`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.coverPreserving`：coverPreserving :
 CoverPreserving J K G
-/
lemma WEqualsLocallyBijective.ofEssentiallySmall
    [((equivSmallModel C).inverse.inducedTopology J).WEqualsLocallyBijective A] :
    J.WEqualsLocallyBijective A :=
  WEqualsLocallyBijective.transport J ((equivSmallModel C).inverse.inducedTopology J)
    (equivSmallModel C).inverse (IsDenseSubsite.coverPreserving _ _ _)

variable [∀ (X : Cᵒᵖ), HasLimitsOfShape (StructuredArrow X (equivSmallModel C).inverse.op) B]
variable [PreservesSheafification ((equivSmallModel C).inverse.inducedTopology J) F]
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesSheafification J F :=
  PreservesSheafification.transport (A := A) J
    ((equivSmallModel C).inverse.inducedTopology J) (equivSmallModel C).inverse B F

end GrothendieckTopology

end CategoryTheory

