/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveTopology
public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.CategoryTheory.Sites.LocallySurjective
/-!

# Locally surjective morphisms of coherent sheaves

This file characterises locally surjective morphisms of presheaves for the coherent, regular
and extensive topologies.

## Main results

* `regularTopology.isLocallySurjective_iff` A morphism of presheaves `f : F ⟶ G` is locally
  surjective for the regular topology iff for every object `X` of `C`, and every `y : G(X)`, there
  is an effective epimorphism `φ : X' ⟶ X` and an `x : F(X)` such that `f_{X'}(x) = G(φ)(y)`.

* `coherentTopology.isLocallySurjective_iff` a morphism of sheaves for the coherent topology on a
  preregular finitary extensive category is locally surjective if and only if it is
  locally surjective for the regular topology.

* `extensiveTopology.isLocallySurjective_iff` a morphism of sheaves for the extensive topology on a
  finitary extensive category is locally surjective iff it is objectwise surjective.
-/

public section

universe w

open CategoryTheory Sheaf Limits Opposite

namespace CategoryTheory

variable {C : Type*} (D : Type*) [Category* C] [Category* D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]

/-
**CategoryTheory.regularTopology.isLocallySurjective_iff** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.regularTopology`。
形式化陈述：∀ {C : Type u_1} (D : Type u_2) [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {FD : D → D → Type u_3} {C
D : D → Type w}   [inst_2 : (X Y : D) → FunLike (FD X Y) (CD X) (CD Y)] [inst_3 
: CategoryTheory.ConcreteCategory D FD]   [inst_4 : CategoryTheory.Preregular C]
 {F G : CategoryTheory.Functor Cᵒᵖ D} (f : F ⟶ G),   CategoryTheory.Presheaf.IsL
ocallySurjective (CategoryTheory.regularTopology C) f ↔     ∀ (X : C) (y : Categ
oryTheory.ToType (G.obj (Opposite.op X))),       ∃ X' φ,         ∃ (_ : Category
Theory.EffectiveEpi φ),           ∃ x,             (CategoryTheory.ConcreteCateg
ory.hom (f.app (Opposite.op X'))) x =               (CategoryTheory.ConcreteCate
gory.hom (G.map (Opposite.op φ))) y
参数：D : Type u_2；X Y : D；FD X Y；CD X；CD Y；f : F ⟶ G；CategoryTheory.regularTopolog
y C；X : C；y : CategoryTheory.ToType (G.obj (Opposite.op X))；_ : CategoryTheory.E
ffectiveEpi φ；CategoryTheory.ConcreteCategory.hom (f.app (Opposite.op X'))；Categ
oryTheory.ConcreteCategory.hom (G.map (Opposite.op φ))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.regularTopology.mem_sieves_iff_hasEffectiveEpi`：mem_sieve
s_iff_hasEffectiveEpi (S : Sieve X) : (S in (regularTopology C) X) ↔ exists (Y :
 C) (π : Y ⟶ X), EffectiveEpi π ∧ (S.arrows π)
-/
lemma regularTopology.isLocallySurjective_iff [Preregular C] {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G) :
    Presheaf.IsLocallySurjective (regularTopology C) f ↔
      ∀ (X : C) (y : ToType (G.obj ⟨X⟩)), (∃ (X' : C) (φ : X' ⟶ X) (_ : EffectiveEpi φ)
        (x : ToType (F.obj ⟨X'⟩)),
        f.app ⟨X'⟩ x = G.map ⟨φ⟩ y) := by
  constructor
  · intro ⟨h⟩ X y
    specialize h y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi] at h
    obtain ⟨X', π, h, h'⟩ := h
    exact ⟨X', π, h, h'⟩
  · intro h
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨X', π, h, h'⟩ := h _ y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi]
    exact ⟨X', π, h, h'⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.extensiveTopology.surjective_of_isLocallySurjective_sheaf_of_ty
pes** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.extensiveTopology`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.FinitaryPreExtensive C]   {F G : CategoryTheory.Functor Cᵒᵖ (Type 
w)} (f : F ⟶ G) [CategoryTheory.Limits.PreservesFiniteProducts F]   [CategoryThe
ory.Limits.PreservesFiniteProducts G],   CategoryTheory.Presheaf.IsLocallySurjec
tive (CategoryTheory.extensiveTopology C) f →     ∀ {X : C}, Function.Surjective
 ⇑(CategoryTheory.ConcreteCategory.hom (f.app (Opposite.op X)))
参数：Type w；f : F ⟶ G；CategoryTheory.extensiveTopology C；CategoryTheory.ConcreteCa
tegory.hom (f.app (Opposite.op X))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsLocallySurjective.imageSieve_mem`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {J : CategoryTheory.GrothendieckTop
ology C} {A : Type u'}   {inst_1 : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.extensiveTopology.mem_sieves_iff_contains_colimit_cofan`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Categor
yTheory.FinitaryPreExtensive C] {X : C}   (S : CategoryTheor…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Functor.initial_of_isLeftAdjoint`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.Initial.comp_preservesLimit`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeOppositeOfIsGroupoid`：∀ 
{C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 
: CategoryTheory.Category.{v₂, u₂} D]   {I : Type u_1} [in…
· 使用定理 `CategoryTheory.instIsGroupoidDiscrete`：∀ {I : Type u_1}, CategoryTheory.
IsGroupoid (CategoryTheory.Discrete I)
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Concrete.isLimit_ext`：isLimit_ext {D : Cone F} (hD
 : IsLimit D) (x y : ToType D.pt) : (forall j, D.π.app j x = D.π.app j y) -> x =
 y
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Types.instIsEquivalenceForgetTypeFun`：(CategoryTheory.for
get (Type u)).IsEquivalence
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.IsLimit.map_π`：map_π {F G : J ⥤ C} (c : Cone F) {d
 : Cone G} (hd : IsLimit d) (α : F ⟶ G) (j : J) : hd.map c α ≫ d.π.app j = c.π.a
pp j ≫ α.app j
-/
lemma extensiveTopology.surjective_of_isLocallySurjective_sheaf_of_types [FinitaryPreExtensive C]
    {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      (h : Presheaf.IsLocallySurjective (extensiveTopology C) f) {X : C} :
        Function.Surjective (f.app (op X)) := by
  intro x
  replace h := h.1 x
  rw [mem_sieves_iff_contains_colimit_cofan] at h
  obtain ⟨α, _, Y, π, h, h'⟩ := h
  let y : (a : α) → (F.obj ⟨Y a⟩) := fun a ↦ (h' a).choose
  let ht := (Types.productLimitCone (fun a ↦ F.obj ⟨Y a⟩)).isLimit
  let ht' := (Functor.Initial.isLimitWhiskerEquiv (Discrete.opposite α).inverse
    (Cocone.op (Cofan.mk X π))).symm h.some.op
  let i : ((a : α) → (F.obj ⟨Y a⟩)) ≅ (F.obj ⟨X⟩) :=
    ht.conePointsIsoOfNatIso (isLimitOfPreserves F ht')
      (Discrete.natIso (fun _ ↦ (Iso.refl (F.obj ⟨_⟩))))
  refine ⟨i.hom y, ?_⟩
  apply Concrete.isLimit_ext _ (isLimitOfPreserves G ht')
  intro ⟨a⟩
  simp only [Functor.comp_obj, Discrete.opposite_inverse_obj, Functor.op_obj, Discrete.functor_obj,
    Functor.mapCone_pt, Cone.whisker_pt, Cocone.op_pt, Cofan.mk_pt, Functor.const_obj_obj,
    Functor.mapCone_π_app, Cone.whisker_π, Cocone.op_π, Functor.whiskerLeft_app, NatTrans.op_app,
    Cofan.mk_ι_app]
  rw [← (h' a).choose_spec, ← NatTrans.naturality_apply (φ := f)]
  simp only [IsLimit.conePointsIsoOfNatIso_hom, ← comp_apply, i]
  erw [IsLimit.map_π]
  rfl
/-
**CategoryTheory.extensiveTopology.presheafIsLocallySurjective_iff** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.extensiveTopology`。
形式化陈述：∀ {C : Type u_1} (D : Type u_2) [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {FD : D → D → Type u_3} {C
D : D → Type w}   [inst_2 : (X Y : D) → FunLike (FD X Y) (CD X) (CD Y)] [inst_3 
: CategoryTheory.ConcreteCategory D FD]   [inst_4 : CategoryTheory.FinitaryPreEx
tensive C] {F G : CategoryTheory.Functor Cᵒᵖ D} (f : F ⟶ G)   [CategoryTheory.Li
mits.PreservesFiniteProducts F] [CategoryTheory.Limits.PreservesFiniteProducts G
]   [CategoryTheory.Limits.PreservesFiniteProducts (CategoryTheory.forget D)],  
 CategoryTheory.Presheaf.IsLocallySurjective (CategoryTheory.extensiveTopology C
) f ↔     ∀ (X : C), Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom (
f.app (Opposite.op X)))
参数：D : Type u_2；X Y : D；FD X Y；CD X；CD Y；f : F ⟶ G；CategoryTheory.forget D；Categ
oryTheory.extensiveTopology C；X : C；CategoryTheory.ConcreteCategory.hom (f.app (
Opposite.op X))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget`：isLocall
ySurjective_iff_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) : IsLocallySurjective
 J f ↔ IsLocallySurjective J (whiskerRight f (forget…
· 使用定理 `CategoryTheory.extensiveTopology.surjective_of_isLocallySurjective_sheaf
_of_types`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_
1 : CategoryTheory.FinitaryPreExtensive C]   {F G : CategoryTheory.Func…
· 使用定理 `CategoryTheory.Presheaf.isLocallySurjective_of_surjective`：isLocallySurj
ective_of_surjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) (H : forall U, Function.Surject
ive (f.app U)) : IsLocallySurjective J f where …
-/
lemma extensiveTopology.presheafIsLocallySurjective_iff [FinitaryPreExtensive C] {F G : Cᵒᵖ ⥤ D}
    (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      [PreservesFiniteProducts (forget D)] : Presheaf.IsLocallySurjective (extensiveTopology C) f ↔
        ∀ (X : C), Function.Surjective (f.app (op X)) := by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget (J := extensiveTopology C)]
    exact fun h _ ↦
      surjective_of_isLocallySurjective_sheaf_of_types (Functor.whiskerRight f (forget D)) h
  · exact fun a ↦
      Presheaf.isLocallySurjective_of_surjective _ _ (fun _ ↦ a _)
/-
**CategoryTheory.extensiveTopology.isLocallySurjective_iff** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.extensiveTopology`。
形式化陈述：∀ {C : Type u_1} (D : Type u_2) [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {FD : D → D → Type u_3} {C
D : D → Type w}   [inst_2 : (X Y : D) → FunLike (FD X Y) (CD X) (CD Y)] [inst_3 
: CategoryTheory.ConcreteCategory D FD]   [inst_4 : CategoryTheory.FinitaryExten
sive C] {F G : CategoryTheory.Sheaf (CategoryTheory.extensiveTopology C) D}   (f
 : F ⟶ G) [CategoryTheory.Limits.PreservesFiniteProducts (CategoryTheory.forget 
D)],   CategoryTheory.Sheaf.IsLocallySurjective f ↔     ∀ (X : C), Function.Surj
ective ⇑(CategoryTheory.ConcreteCategory.hom (f.hom.app (Opposite.op X)))
参数：D : Type u_2；X Y : D；FD X Y；CD X；CD Y；CategoryTheory.extensiveTopology C；f : 
F ⟶ G；CategoryTheory.forget D；X : C；CategoryTheory.ConcreteCategory.hom (f.hom.a
pp (Opposite.op X))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CategoryTheory.extensiveTopology.presheafIsLocallySurjective_iff`：∀ {C :
 Type u_1} (D : Type u_2) [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] {FD : D → D …
· 使用定理 `CategoryTheory.instPreservesFiniteProductsOppositeObjFunctorIsSheafExten
siveTopology`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D 
: Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma extensiveTopology.isLocallySurjective_iff [FinitaryExtensive C]
    {F G : Sheaf (extensiveTopology C) D} (f : F ⟶ G)
      [PreservesFiniteProducts (forget D)] : IsLocallySurjective f ↔
        ∀ (X : C), Function.Surjective (f.hom.app (op X)) :=
  extensiveTopology.presheafIsLocallySurjective_iff _ f.hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.regularTopology.isLocallySurjective_sheaf_of_types** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.regularTopology`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preregular C]   [inst_2 : CategoryTheory.FinitaryPreExtensive C] {
F G : CategoryTheory.Functor Cᵒᵖ (Type w)} (f : F ⟶ G)   [CategoryTheory.Limits.
PreservesFiniteProducts F] [CategoryTheory.Limits.PreservesFiniteProducts G],   
CategoryTheory.Presheaf.IsLocallySurjective (CategoryTheory.coherentTopology C) 
f →     CategoryTheory.Presheaf.IsLocallySurjective (CategoryTheory.regularTopol
ogy C) f
参数：Type w；f : F ⟶ G；CategoryTheory.coherentTopology C；CategoryTheory.regularTopo
logy C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.Presheaf.IsLocallySurjective.imageSieve_mem`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {J : CategoryTheory.GrothendieckTop
ology C} {A : Type u'}   {inst_1 : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryT
heory.Precoherent C] {X : C}   (S : CategoryTheory.Sieve X…
· 使用定理 `CategoryTheory.regularTopology.mem_sieves_iff_hasEffectiveEpi`：mem_sieve
s_iff_hasEffectiveEpi (S : Sieve X) : (S in (regularTopology C) X) ↔ exists (Y :
 C) (π : Y ⟶ X), EffectiveEpi π ∧ (S.arrows π)
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasFiniteCoproducts`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryPreExte
nsive C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.instHasProductOppositeOp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   [CategoryTheory
.Limits.HasCoproduct Z], CategoryThe…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instEffectiveEpiDescOfEffectiveEpiFamily`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {B : C} {α : Type u_2} (X : α → 
C)   (π : (a : α) → X a ⟶ B) [inst_1 : Catego…
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…
· 使用定理 `CategoryTheory.Limits.Concrete.isLimit_ext`：isLimit_ext {D : Cone F} (hD
 : IsLimit D) (x y : ToType D.pt) : (forall j, D.π.app j x = D.π.app j y) -> x =
 y
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Types.instIsEquivalenceForgetTypeFun`：(CategoryTheory.for
get (Type u)).IsEquivalence
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Functor.map_comp_apply`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.opCoproductIsoProduct_inv_comp_ι`：opCoproductIsoPr
oduct_inv_comp_ι [HasCoproduct Z] (b : α) : (opCoproductIsoProduct Z).inv ≫ (Sig
ma.ι Z b).op = Pi.π (op <| Z ·) b
· 使用定理 `CategoryTheory.Limits.piComparison_comp_π`：piComparison_comp_π [HasProdu
ct f] [HasProduct fun b => G.obj (f b)] (b : β) : piComparison G f ≫ Pi.π _ b = 
G.map (Pi.π f b)
· 使用定理 `CategoryTheory.Limits.Types.productIso_hom_comp_eval`：productIso_hom_com
p_eval {J : Type v} (F : J -> Type (max v u)) (j : J) : (productIso.{v, u} F).ho
m ≫ (↾fun f => f j) = Pi.π F j
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 34 条，此处仅展示前 30 条）
-/
lemma regularTopology.isLocallySurjective_sheaf_of_types [Preregular C] [FinitaryPreExtensive C]
    {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      (h : Presheaf.IsLocallySurjective (coherentTopology C) f) :
        Presheaf.IsLocallySurjective (regularTopology C) f where
  imageSieve_mem y := by
    replace h := h.1 y
    rw [coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily] at h
    obtain ⟨α, _, Z, π, h, h'⟩ := h
    rw [mem_sieves_iff_hasEffectiveEpi]
    let x : (a : α) → (F.obj ⟨Z a⟩) := fun a ↦ (h' a).choose
    let i' : ((a : α) → (F.obj ⟨Z a⟩)) ≅ (F.obj ⟨∐ Z⟩) := (Types.productIso _).symm ≪≫
      (PreservesProduct.iso F _).symm ≪≫ F.mapIso (opCoproductIsoProduct _).symm
    refine ⟨∐ Z, Sigma.desc π, inferInstance, i'.hom x, ?_⟩
    have := preservesLimitsOfShape_of_equiv (Discrete.opposite α).symm G
    apply Concrete.isLimit_ext _ (isLimitOfPreserves G (coproductIsCoproduct Z).op)
    intro ⟨⟨a⟩⟩
    simp only [Functor.comp_obj, Functor.op_obj, Discrete.functor_obj_eq_as, Functor.mapCone_pt,
      Cocone.op_pt, Cofan.mk_pt, Functor.const_obj_obj, Functor.mapCone_π_app, Cocone.op_π,
      NatTrans.op_app, Cofan.mk_ι_app, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_inv, comp_apply, ← f.naturality_apply (Sigma.ι Z a).op, i']
    have : f.app ⟨Z a⟩ (x a) = G.map (π a).op y := (h' a).choose_spec
    convert! this
    · rw [← Functor.map_comp_apply, opCoproductIsoProduct_inv_comp_ι, ← piComparison_comp_π]
      change ((PreservesProduct.iso F _).hom ≫ _) _ = _
      have := Types.productIso_hom_comp_eval (fun a ↦ F.obj (op (Z a))) a
      rw [← Iso.eq_inv_comp] at this
      simp only [types_comp_apply, Iso.inv_hom_id_apply]
      simp [← comp_apply]
    · simp only [← Functor.map_comp_apply, ← op_comp, Sigma.ι_desc]
/-
**CategoryTheory.coherentTopology.presheafIsLocallySurjective_iff** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.coherentTopology`。
形式化陈述：∀ {C : Type u_1} (D : Type u_2) [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {FD : D → D → Type u_3} {C
D : D → Type w}   [inst_2 : (X Y : D) → FunLike (FD X Y) (CD X) (CD Y)] [inst_3 
: CategoryTheory.ConcreteCategory D FD]   {F G : CategoryTheory.Functor Cᵒᵖ D} (
f : F ⟶ G) [inst_4 : CategoryTheory.Preregular C]   [inst_5 : CategoryTheory.Fin
itaryPreExtensive C] [CategoryTheory.Limits.PreservesFiniteProducts F]   [Catego
ryTheory.Limits.PreservesFiniteProducts G]   [CategoryTheory.Limits.PreservesFin
iteProducts (CategoryTheory.forget D)],   CategoryTheory.Presheaf.IsLocallySurje
ctive (CategoryTheory.coherentTopology C) f ↔     CategoryTheory.Presheaf.IsLoca
llySurjective (CategoryTheory.regularTopology C) f
参数：D : Type u_2；X Y : D；FD X Y；CD X；CD Y；f : F ⟶ G；CategoryTheory.forget D；Categ
oryTheory.coherentTopology C；CategoryTheory.regularTopology C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget`：isLocall
ySurjective_iff_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) : IsLocallySurjective
 J f ↔ IsLocallySurjective J (whiskerRight f (forget…
· 使用定理 `CategoryTheory.regularTopology.isLocallySurjective_sheaf_of_types`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheo
ry.Preregular C]   [inst_2 : CategoryTheory.FinitaryPre…
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_of_le`：isLocallySurjective_o
f_le {K : GrothendieckTopology C} (hJK : J <= K) {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) (h 
: IsLocallySurjective J f) : IsLocallyS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.extensive_regular_generate_coherent`：extensive_regular_ge
nerate_coherent [Preregular C] [FinitaryPreExtensive C] : ((extensiveCoverage C)
 ⊔ (regularCoverage C)).toGrothendieck =…
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma coherentTopology.presheafIsLocallySurjective_iff {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G)
    [Preregular C] [FinitaryPreExtensive C] [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      [PreservesFiniteProducts (forget D)] :
        Presheaf.IsLocallySurjective (coherentTopology C) f ↔
          Presheaf.IsLocallySurjective (regularTopology C) f := by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget,
      Presheaf.isLocallySurjective_iff_whisker_forget (J := regularTopology C)]
    exact regularTopology.isLocallySurjective_sheaf_of_types _
  · refine Presheaf.isLocallySurjective_of_le (J := regularTopology C) ?_ _
    rw [← extensive_regular_generate_coherent]
    exact (Coverage.gi _).gc.monotone_l le_sup_right
/-
**CategoryTheory.coherentTopology.isLocallySurjective_iff** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.coherentTopology`。
形式化陈述：∀ {C : Type u_1} (D : Type u_2) [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {FD : D → D → Type u_3} {C
D : D → Type w}   [inst_2 : (X Y : D) → FunLike (FD X Y) (CD X) (CD Y)] [inst_3 
: CategoryTheory.ConcreteCategory D FD]   [inst_4 : CategoryTheory.Preregular C]
 [inst_5 : CategoryTheory.FinitaryExtensive C]   {F G : CategoryTheory.Sheaf (Ca
tegoryTheory.coherentTopology C) D} (f : F ⟶ G)   [CategoryTheory.Limits.Preserv
esFiniteProducts (CategoryTheory.forget D)],   CategoryTheory.Sheaf.IsLocallySur
jective f ↔     CategoryTheory.Presheaf.IsLocallySurjective (CategoryTheory.regu
larTopology C) f.hom
参数：D : Type u_2；X Y : D；FD X Y；CD X；CD Y；CategoryTheory.coherentTopology C；f : F
 ⟶ G；CategoryTheory.forget D；CategoryTheory.regularTopology C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CategoryTheory.coherentTopology.presheafIsLocallySurjective_iff`：∀ {C : 
Type u_1} (D : Type u_2) [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} D] {FD : D → D …
· 使用定理 `CategoryTheory.Presheaf.instPreservesFiniteProductsOppositeObjFunctorIsS
heafCoherentTopology`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1
} C] {A : Type u₃}   [inst_1 : CategoryTheory.Category.{v₃, u₃} A] [inst_2 : Cat
eg…
-/
lemma coherentTopology.isLocallySurjective_iff [Preregular C] [FinitaryExtensive C]
    {F G : Sheaf (coherentTopology C) D} (f : F ⟶ G) [PreservesFiniteProducts (forget D)] :
      IsLocallySurjective f ↔ Presheaf.IsLocallySurjective (regularTopology C) f.hom :=
  presheafIsLocallySurjective_iff _ f.hom

end CategoryTheory

