/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.ModelCategory.Lifting
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# The model category structure on bounded below complexes

Let `C` be an abelian category with enough injectives. In this file,
we define a model category structure on the category `CochainComplex.Plus C`
of bounded below cochain complexes in `C`.
The cofibrations are monomorphisms, the weak equivalences are
quasi-isomorphisms and the fibrations are those morphisms
that are degreewise epimorphisms with an injective kernel.
The `ModelCategory` instance is scoped in the namespace
`CochainComplex.Plus.modelCategoryQuillen`.

## References
* [Daniel G. Quillen, Homotopical algebra, §I.1, Example B][Quillen1967]

-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra Limits

namespace CochainComplex.Plus.modelCategoryQuillen

variable {C : Type*} [Category C] [Abelian C]

/-- The weak equivalences in the category `CochainComplex.Plus C` of bounded
below cochain complexes are quasi-isomorphisms. -/
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weak equivalences in the category `CochainComplex.Plus C` of bounded
below cochain complexes are quasi-isomorphisms.
-/
scoped instance : CategoryWithWeakEquivalences (CochainComplex.Plus C) where
  weakEquivalences := quasiIso C

/-- The cofibrations in the category `CochainComplex.Plus C` of bounded
below cochain complexes are monomorphisms. -/
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofibrations in the category `CochainComplex.Plus C` of bounded
below cochain complexes are monomorphisms.
-/
scoped instance : CategoryWithCofibrations (CochainComplex.Plus C) where
  cofibrations := .monomorphisms _

/-- The fibrations in the category `CochainComplex.Plus C` of bounded
below cochain complexes are the morphisms that are degreewise epi with
an injective kernel. -/
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fibrations in the category `CochainComplex.Plus C` of bounded
below cochain complexes are the morphisms that are degreewise epi with
an injective kernel.
-/
scoped instance : CategoryWithFibrations (CochainComplex.Plus C) where
  fibrations := degreewiseEpiWithInjectiveKernel.inverseImage (ι C)
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (weakEquivalences (Plus C)).HasTwoOutOfThreeProperty :=
  inferInstanceAs (quasiIso C).HasTwoOutOfThreeProperty
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (weakEquivalences (Plus C)).IsStableUnderRetracts :=
  inferInstanceAs (quasiIso C).IsStableUnderRetracts
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (cofibrations (Plus C)).IsStableUnderRetracts :=
  inferInstanceAs (MorphismProperty.monomorphisms _).IsStableUnderRetracts
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fibrations (Plus C)).IsStableUnderRetracts :=
  inferInstanceAs (degreewiseEpiWithInjectiveKernel.inverseImage (ι C)).IsStableUnderRetracts
/-
**CochainComplex.Plus.modelCategoryQuillen.cofibration_iff** 是 Mathlib 中的一个引理，位于
命名空间 `CochainComplex.Plus.modelCategoryQuillen`。
形式化陈述：cofibration_iff {X Y : Plus C} (f : X ⟶ Y) : Cofibration f ↔ Mono f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.cofibration_iff`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Catego
ryWithCofibrations C],  …
-/
lemma cofibration_iff {X Y : Plus C} (f : X ⟶ Y) :
    Cofibration f ↔ Mono f :=
  HomotopicalAlgebra.cofibration_iff _
/-
**CochainComplex.Plus.modelCategoryQuillen.fibration_iff** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex.Plus.modelCategoryQuillen`。
形式化陈述：fibration_iff {X Y : Plus C} (f : X ⟶ Y) : Fibration f ↔ degreewiseEpiWith
InjectiveKernel f.hom
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.fibration_iff`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Category
WithFibrations C],   H…
-/
lemma fibration_iff {X Y : Plus C} (f : X ⟶ Y) :
    Fibration f ↔ degreewiseEpiWithInjectiveKernel f.hom :=
  HomotopicalAlgebra.fibration_iff _
/-
**CochainComplex.Plus.modelCategoryQuillen.isFibrant_iff** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex.Plus.modelCategoryQuillen`。
形式化陈述：isFibrant_iff (X : Plus C) : IsFibrant X ↔ forall (n : Int), Injective (X.
obj.X n)
参数：X : Plus C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `CochainComplex.Plus.instHasFiniteLimits`：∀ (C : Type u_1) [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   [CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopicalAlgebra.isFibrant_iff`：isFibrant_iff (X : C) : IsFibrant X ↔ 
Fibration (terminal.from X)
· 使用引理 `CochainComplex.Plus.modelCategoryQuillen.fibration_iff`：fibration_iff {X
 Y : Plus C} (f : X ⟶ Y) : Fibration f ↔ degreewiseEpiWithInjectiveKernel f.hom
· 使用引理 `CochainComplex.degreewiseEpiWithInjectiveKernel_iff_of_isZero`：degreewis
eEpiWithInjectiveKernel_iff_of_isZero {K L : CochainComplex C Int} (f : K ⟶ L) (
hL : IsZero L) : degreewiseEpiWithInjectiveKernel f…
· 使用引理 `CategoryTheory.Functor.map_isZero`：map_isZero (F : C ⥤ D) [PreservesZero
Morphisms F] {X : C} (hX : IsZero X) : IsZero (F.obj X)
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.fullSubcategoryInclusion_additive`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   (Z : CategoryTheory.ObjectProperty …
· 使用定理 `CategoryTheory.Limits.IsZero.of_mono_zero`：of_mono_zero (X Y : C) [Mono 
(0 : X ⟶ Y)] : IsZero X
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.Limits.terminal.isSplitMono_from`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {Y : C} [inst_1 : CategoryTheory.Limits.Has
Terminal C]   (f : ⊤_ C ⟶ Y), Categor…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isFibrant_iff (X : Plus C) :
    IsFibrant X ↔ ∀ (n : ℤ), Injective (X.obj.X n) := by
  rw [HomotopicalAlgebra.isFibrant_iff, fibration_iff,
    degreewiseEpiWithInjectiveKernel_iff_of_isZero]
  exact Functor.map_isZero (Plus.ι C) (IsZero.of_mono_zero _ X)
/-
**CochainComplex.Plus.modelCategoryQuillen.weakEquivalence_iff** 是 Mathlib 中的一个引
理，位于命名空间 `CochainComplex.Plus.modelCategoryQuillen`。
形式化陈述：weakEquivalence_iff {X Y : Plus C} (f : X ⟶ Y) : WeakEquivalence f ↔ Quasi
Iso f.hom
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.weakEquivalence_iff`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C…
-/
lemma weakEquivalence_iff {X Y : Plus C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ QuasiIso f.hom :=
  HomotopicalAlgebra.weakEquivalence_iff _
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B : CochainComplex.Plus C} (i : A ⟶ B) [Cofibration i] :
    Mono i := by
  rwa [← cofibration_iff]

set_option backward.defeqAttrib.useBackward true in
open HomComplex in
/-- Let `sq` be a commutative square in the category of bounded below cochain complexes
in an abelian category. We assume that the left morphism `i` is a monomorphism,
and `p` an epimorphism with a degreewise injective kernel. Then, there exists
a lifting for `sq` if `i` or `p` is a quasi-isomorphism. -/
/-
**CochainComplex.Plus.modelCategoryQuillen.lifting** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `sq` be a commutative square in the category of bounded below cochain comple
xes
in an abelian category. We assume that the left morphism `i` is a monomorphism,
and `p` an epimorphism with a degreewise injective kernel. Then, there exists
a lifting for `sq` if `i` or `p` is a quasi-isomorphism.
-/
private lemma lifting {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [Fibration p] (hip : WeakEquivalence i ∨ WeakEquivalence p) :
    HasLiftingProperty i p where
  sq_hasLift {t b} sq := by
    /- The proof is similar in both cases (whether `i` or `p` is a quasi-isomorphism).
    We first transform the variables so as to get a commutative square in `CochainComplex C ℤ`
    instead of the full subcategory `CochainComplex.Plus C`. -/
    obtain ⟨A, hA⟩ := A
    obtain ⟨B, hB⟩ := B
    obtain ⟨X, hX⟩ := X
    obtain ⟨Y, hY⟩ := Y
    have hi : Mono i.hom := inferInstance
    have hp : degreewiseEpiWithInjectiveKernel p.hom :=
      (fibration_iff p).1 inferInstance
    obtain ⟨i, rfl⟩ := ObjectProperty.homMk_surjective i
    obtain ⟨p, rfl⟩ := ObjectProperty.homMk_surjective p
    obtain ⟨t, rfl⟩ := ObjectProperty.homMk_surjective t
    obtain ⟨b, rfl⟩ := ObjectProperty.homMk_surjective b
    dsimp at i p t b hp hi
    have hip : QuasiIso i ∨ QuasiIso p := by
      simpa only [weakEquivalence_iff] using! hip
    replace sq : CommSq t i p b := sq.map (ObjectProperty.ι _)
    suffices sq.HasLift from ⟨⟨{ l := ObjectProperty.homMk sq.lift }⟩⟩
    have sq' (n : ℤ) : CommSq (t.f n) (i.f n) (p.f n) (b.f n) :=
      (sq.map (HomologicalComplex.eval _ _ n))
    /- The commutative square in `C` obtained by evaluating in a degree `n`
    admits a lifting because `i.f n` is a monomorphism and `p.f n` is
    an epimorphism with injective kernel. -/
    have (n : ℤ) : (sq' n).HasLift := by
      have := (hp n).hasLiftingProperty (i.f n)
      infer_instance
    /- In order to obtain a lifting in the original square, the obstruction
    lies in a cocycle `β : Cocycle (cokernel i) (kernel p) 1`. Thanks to the
    lemma `CochainComplex.Lifting.hasLift`, it suffices to show that `β`
    is a coboundary. -/
    let β : Cocycle (cokernel i) (kernel p) 1 :=
      Lifting.cocycle₁ sq (fun n ↦ { l := (sq' n).lift })
        (cokernelIsCokernel i) (kernelIsKernel p) (hπ := by simp) (hι := by simp)
    have (n : ℤ) : Injective ((kernel p).X n) :=
      Injective.of_iso
        (asIso (kernelComparison p (HomologicalComplex.eval _ _ n))).symm (hp n).2
    have : (kernel p).IsKInjective := by
      obtain ⟨d, hd⟩ := hX
      have : (kernel p).IsStrictlyGE d := by
        rw [isStrictlyGE_iff]
        intro i hi
        rw [IsZero.iff_id_eq_zero, ← cancel_mono ((kernel.ι p).f i)]
        apply (X.isZero_of_isStrictlyGE d i).eq_of_tgt
      exact isKInjective_of_injective _ d
    /- The cocycle `β` is a coboundary when `i` or `p` is a quasi-isomorphism. -/
    obtain ⟨α, hα⟩ : ∃ (α : Cochain (cokernel i) (kernel p) 0), δ 0 1 α = β.1 := by
      cases hip
      · refine IsKInjective.eq_δ_of_cocycle β ?_ 0 (by simp)
        have : (ShortComplex.mk _ _ (cokernel.condition i)).ShortExact :=
          { exact := ShortComplex.exact_cokernel i }
        exact this.acyclic_X₃ (by dsimp; infer_instance)
      · refine IsKInjective.eq_δ_of_cocycle' β ?_ 0 (by simp)
        have := hp.epi
        have : (ShortComplex.mk _ _ (kernel.condition p)).ShortExact :=
          { exact := ShortComplex.exact_kernel p }
        exact this.acyclic_X₁ (by dsimp; infer_instance)
    exact Lifting.hasLift sq _ (cokernelIsCokernel _) (kernelIsKernel _) α hα
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [WeakEquivalence i] [Fibration p] :
    HasLiftingProperty i p :=
  lifting _ _ (Or.inl inferInstance)
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [Fibration p] [WeakEquivalence p] :
    HasLiftingProperty i p :=
  lifting _ _ (Or.inr inferInstance)

variable [EnoughInjectives C]
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (trivialCofibrations (Plus C)).HasFactorization (fibrations (Plus C)) where
  nonempty_mapFactorizationData := by
    intro ⟨K, n, hn⟩ ⟨L, m, hm⟩ ⟨f⟩
    obtain ⟨d, _, _⟩ : ∃ (d : ℤ), K.IsStrictlyGE (d + 1) ∧ L.IsStrictlyGE d :=
      ⟨min (n - 1) m, K.isStrictlyGE_of_ge _ n (by grind),
        L.isStrictlyGE_of_ge _ m (by simp)⟩
    obtain ⟨K', _, i, p, _, _, hp, fac⟩ := cm5a f d
    exact ⟨{
      Z := ⟨K', d, inferInstance⟩
      i := ObjectProperty.homMk i
      p := ObjectProperty.homMk p
      hi :=
        ⟨by rwa [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, Plus.mono_iff],
          by assumption⟩
      hp := hp }⟩
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (cofibrations (Plus C)).HasFactorization (trivialFibrations (Plus C)) where
  nonempty_mapFactorizationData := by
    intro ⟨K, n, hn⟩ ⟨L, m, hm⟩ ⟨f⟩
    obtain ⟨d, _, _⟩ : ∃ (d : ℤ), K.IsStrictlyGE (d + 1) ∧ L.IsStrictlyGE d :=
      ⟨min (n - 1) m, K.isStrictlyGE_of_ge _ n (by grind),
        L.isStrictlyGE_of_ge _ m (by simp)⟩
    obtain ⟨K', _, i, p, _, hp, _, fac⟩ := cm5b f d
    exact ⟨{
      Z := ⟨K', d, inferInstance⟩
      i := ObjectProperty.homMk i
      p := ObjectProperty.homMk p
      hi := by rwa [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, Plus.mono_iff]
      hp := ⟨hp, by assumption⟩ }⟩

/-- The Quillen model category structure on the category `CochainComplex.Plus C`
of bounded below cochain complexes in an abelian category `C` with enough injectives. -/
/-
**CochainComplex.Plus.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `CochainCo
mplex.Plus.modelCategoryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Quillen model category structure on the category `CochainComplex.Plus C`
of bounded below cochain complexes in an abelian category `C` with enough inject
ives.
-/
scoped instance : ModelCategory (CochainComplex.Plus C) where

end CochainComplex.Plus.modelCategoryQuillen

