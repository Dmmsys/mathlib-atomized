/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Complexes in functor categories

We can view a complex valued in a functor category `T ⥤ V` as
a functor from `T` to complexes valued in `V`.

When `V` is abelian, a morphism of short complexes or homological
complexes in the category `T ⥤ V` is a quasi-isomorphism iff
it is so after evaluation at any `t : T`.

## Future work
In fact there is an equivalence of categories
`HomologicalComplex (T ⥤ V) c ≌ T ⥤ HomologicalComplex V c`.

-/

@[expose] public section


universe v u

open CategoryTheory Limits

variable {T : Type*} [Category* T] {V : Type*} [Category* V]

namespace HomologicalComplex

variable [HasZeroMorphisms V] {ι : Type*} {c : ComplexShape ι}

/-- A complex of functors gives a functor to complexes. -/
@[simps]
/-
**HomologicalComplex.asFunctor** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：asFunctor (C : HomologicalComplex (T ⥤ V) c) : T ⥤ HomologicalComplex V c 
where obj t
参数：C : HomologicalComplex (T ⥤ V) c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complex of functors gives a functor to complexes.
-/
def asFunctor (C : HomologicalComplex (T ⥤ V) c) :
    T ⥤ HomologicalComplex V c where
  obj t :=
    { X := fun i => (C.X i).obj t
      d := fun i j => (C.d i j).app t
      d_comp_d' := fun i j k _ _ => by
        have := C.d_comp_d i j k
        rw [NatTrans.ext_iff, funext_iff] at this
        exact this t
      shape := fun i j h => by
        have := C.shape _ _ h
        rw [NatTrans.ext_iff, funext_iff] at this
        exact this t }
  map h :=
    { f := fun i => (C.X i).map h
      comm' := fun _ _ _ => NatTrans.naturality _ _ }
  map_id t := by
    ext i
    dsimp
    rw [(C.X i).map_id]
  map_comp h₁ h₂ := by
    ext i
    dsimp
    rw [Functor.map_comp]

-- TODO in fact, this is an equivalence of categories.
/-- The functorial version of `HomologicalComplex.asFunctor`. -/
@[simps]
/-
**HomologicalComplex.complexOfFunctorsToFunctorToComplex** 是 Mathlib 中的一个定义，位于命名
空间 `HomologicalComplex`。
形式化陈述：complexOfFunctorsToFunctorToComplex : HomologicalComplex (T ⥤ V) c ⥤ T ⥤ H
omologicalComplex V c where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial version of `HomologicalComplex.asFunctor`.
-/
def complexOfFunctorsToFunctorToComplex :
    HomologicalComplex (T ⥤ V) c ⥤ T ⥤ HomologicalComplex V c where
  obj C := C.asFunctor
  map f :=
    { app := fun t =>
        { f := fun i => (f.f i).app t
          comm' := fun i j _ => NatTrans.congr_app (f.comm i j) t }
      naturality := fun t t' g => by
        ext i
        exact (f.f i).naturality g }

end HomologicalComplex

namespace CategoryTheory.ShortComplex

variable [Abelian V] {S₁ S₂ : ShortComplex (T ⥤ V)} (f : S₁ ⟶ S₂)

/-
**CategoryTheory.ShortComplex.quasiIso_iff_evaluation** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ShortComplex`。
形式化陈述：quasiIso_iff_evaluation : QuasiIso f ↔ forall (j : T), QuasiIso (((evaluat
ion T V).obj j).mapShortComplex.map f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_evaluation_obj`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteLimitsFunctorObjEvaluationOfHas
FiniteLimits`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {K 
: Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} K] [CategoryThe…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteColimitsFunctorObjEvaluationOfH
asFiniteColimits`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C]
 {K : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} K] [CategoryThe…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff`：quasiIso_iff (φ : S₁ ⟶ S₂) : Q
uasiIso φ ↔ IsIso (homologyMap φ)
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
-/
lemma quasiIso_iff_evaluation :
    QuasiIso f ↔ ∀ (j : T),
      QuasiIso (((evaluation T V).obj j).mapShortComplex.map f) :=
  ⟨fun _ ↦ inferInstance, fun hf ↦ by
    rw [quasiIso_iff, NatTrans.isIso_iff_isIso_app]
    exact fun j ↦ ((MorphismProperty.isomorphisms V).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
      ((homologyFunctorIso ((evaluation T V).obj j)))).app (Arrow.mk f))).1
        ((quasiIso_iff _).1 (hf j))⟩

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable [Abelian V] {ι : Type*} {c : ComplexShape ι} {K₁ K₂ : HomologicalComplex (T ⥤ V) c}
  (f : K₁ ⟶ K₂)

/-
**HomologicalComplex.quasiIsoAt_iff_evaluation** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex`。
形式化陈述：quasiIsoAt_iff_evaluation (i : ι) : QuasiIsoAt f i ↔ forall (t : T), Quasi
IsoAt ((((evaluation T V).obj t).mapHomologicalComplex c).map f) i
参数：i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_evaluation_obj`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteLimitsFunctorObjEvaluationOfHas
FiniteLimits`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {K 
: Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} K] [CategoryThe…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteColimitsFunctorObjEvaluationOfH
asFiniteColimits`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C]
 {K : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} K] [CategoryThe…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma quasiIsoAt_iff_evaluation (i : ι) :
    QuasiIsoAt f i ↔ ∀ (t : T),
      QuasiIsoAt ((((evaluation T V).obj t).mapHomologicalComplex c).map f) i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff_evaluation]
  rfl
/-
**HomologicalComplex.quasiIso_iff_evaluation** 是 Mathlib 中的一个引理，位于命名空间 `Homologi
calComplex`。
形式化陈述：quasiIso_iff_evaluation : QuasiIso f ↔ forall (t : T), QuasiIso ((((evalua
tion T V).obj t).mapHomologicalComplex c).map f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_evaluation_obj`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma quasiIso_iff_evaluation :
    QuasiIso f ↔ ∀ (t : T),
      QuasiIso ((((evaluation T V).obj t).mapHomologicalComplex c).map f) := by
  simp only [quasiIso_iff, quasiIsoAt_iff_evaluation]
  tauto

end HomologicalComplex

