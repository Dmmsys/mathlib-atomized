/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.EpiWithInjectiveKernel

/-!
# Basic definitions for factorization lemmas

We define the class of morphisms
`degreewiseEpiWithInjectiveKernel : MorphismProperty (CochainComplex C ℤ)`
in the category of cochain complexes in an abelian category `C`.

When restricted to the full subcategory of bounded below cochain complexes in an
abelian category `C` that has enough injectives, this is the class of
fibrations for a model category structure on the bounded below
category of cochain complexes in `C`. In this folder, we intend to prove two factorization
lemmas in the category of bounded below cochain complexes (TODO):
* CM5a: any morphism `K ⟶ L` can be factored as `K ⟶ K' ⟶ L` where `i : K ⟶ K'` is a
  trivial cofibration (a mono that is also a quasi-isomorphism) and `p : K' ⟶ L` is a fibration.
* CM5b: any morphism `K ⟶ L` can be factored as `K ⟶ L' ⟶ L` where `i : K ⟶ L'` is a
  cofibration (i.e. a mono) and `p : L' ⟶ L` is a trivial fibration (i.e. a quasi-isomorphism
  which is also a fibration)

The difficult part is CM5a (whose proof uses CM5b). These lemmas shall be essential
ingredients in the proof that the bounded below derived category of an abelian
category `C` with enough injectives identifies to the bounded below homotopy category
of complexes of injective objects in `C`. This will be used in the construction
of total derived functors (and a refactor of the sequence of derived functors).

-/

@[expose] public section


open CategoryTheory Abelian Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace CochainComplex

/-- A morphism of cochain complexes `φ` in an abelian category satisfies
`degreewiseEpiWithInjectiveKernel φ` if for any `i : ℤ`, the morphism
`φ.f i` is an epimorphism with an injective kernel. -/
/-
**CochainComplex.degreewiseEpiWithInjectiveKernel** 是 Mathlib 中的一个定义，位于命名空间 `Coc
hainComplex`。
形式化陈述：degreewiseEpiWithInjectiveKernel : MorphismProperty (CochainComplex C Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of cochain complexes `φ` in an abelian category satisfies
`degreewiseEpiWithInjectiveKernel φ` if for any `i : ℤ`, the morphism
`φ.f i` is an epimorphism with an injective kernel.
-/
def degreewiseEpiWithInjectiveKernel : MorphismProperty (CochainComplex C ℤ) :=
  fun _ _ φ => ∀ (i : ℤ), epiWithInjectiveKernel (φ.f i)
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (degreewiseEpiWithInjectiveKernel (C := C)).IsMultiplicative where
  id_mem _ _ := MorphismProperty.id_mem _ _
  comp_mem _ _ hf hg n := MorphismProperty.comp_mem _ _ _ (hf n) (hg n)
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (degreewiseEpiWithInjectiveKernel (C := C)).IsStableUnderRetracts where
  of_retract r h i :=
    MorphismProperty.of_retract (r.map (HomologicalComplex.eval _ _ i)) (h i)
/-
**CochainComplex.degreewiseEpiWithInjectiveKernel_iff_of_isZero** 是 Mathlib 中的一个
引理，位于命名空间 `CochainComplex`。
形式化陈述：degreewiseEpiWithInjectiveKernel_iff_of_isZero {K L : CochainComplex C Int
} (f : K ⟶ L) (hL : IsZero L) : degreewiseEpiWithInjectiveKernel f ↔ forall (n :
 Int), Injective (K.X n)
参数：f : K ⟶ L；hL : IsZero L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.epiWithInjectiveKernel_iff_of_isZero`：epiWithInje
ctiveKernel_iff_of_isZero {X Y : C} (f : X ⟶ Y) (hY : IsZero Y) : epiWithInjecti
veKernel f ↔ Injective X
· 使用引理 `CategoryTheory.Functor.map_isZero`：map_isZero (F : C ⥤ D) [PreservesZero
Morphisms F] {X : C} (hX : IsZero X) : IsZero (F.obj X)
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma degreewiseEpiWithInjectiveKernel_iff_of_isZero {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (hL : IsZero L) :
    degreewiseEpiWithInjectiveKernel f ↔ ∀ (n : ℤ), Injective (K.X n) :=
  forall_congr' (fun n ↦ by
    rw [epiWithInjectiveKernel_iff_of_isZero]
    exact (HomologicalComplex.eval _ _ n).map_isZero hL)
/-
**CochainComplex.degreewiseEpiWithInjectiveKernel.epi** 是 Mathlib 中的一个定理，位于命名空间 
`CochainComplex.degreewiseEpiWithInjectiveKernel`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C]   {K L : CochainComplex C ℤ} {f : K ⟶ L}, CochainComple
x.degreewiseEpiWithInjectiveKernel f → CategoryTheory.Epi f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.epi_of_epi_f`：epi_of_epi_f {K L : HomologicalComplex 
V c} (φ : K ⟶ L) (hφ : forall i, Epi (φ.f i)) : Epi φ where left_cancellation g 
h eq
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma degreewiseEpiWithInjectiveKernel.epi {K L : CochainComplex C ℤ} {f : K ⟶ L}
    (h : degreewiseEpiWithInjectiveKernel f) : Epi f :=
  HomologicalComplex.epi_of_epi_f f (fun n ↦ (h n).1)

end CochainComplex

