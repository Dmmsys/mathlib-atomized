/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Anodyne extensions

Anodyne extensions form a property of morphisms in the category of simplicial
sets. It contains horn inclusions and it is closed under coproducts, pushouts,
transfinite compositions and retracts. Equivalently, using the small
object argument, anodyne extensions can be defined (and are defined here)
as the class of morphisms that satisfy the left lifting property with respect
to the class of fibrations (for the Quillen model category structure:
fibrations are morphisms that have the right lifting property with respect
to horn inclusions). When the Quillen model category structure is fully
upstreamed (TODO @joelriou), it can be shown that a morphism `f` is an
anodyne extension iff `f` is a cofibration that is also a weak equivalence.

We also introduce the class of strong anodyne extensions that could be defined
as a closure similarly as anodyne extensions, but without taking the closure
under retracts. Sean Moss has given a combinatorial description of these
strong anodyne extensions: the inclusion `A.ι : A ⟶ X` of a subcomplex `A`
of a simplicial set `X` is a strong anodyne extension iff there exists
a regular pairing for `A`. In this file, we define strong anodyne extensions
in terms of such regular pairings, and using the main result of the file
`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/RelativeCellComplex.lean`
we show that a strong anodyne extension is an anodyne extension.

## TODO
* introduce inner variants of these definitions
* show that strong anodyne extensions are indeed stable under coproducts,
  transfinite compositions and pushouts (the proof should reduce to the
  construction of pairings)
* study the interaction between anodyne extension and binary products:
  the critical case consists in showing that inclusions
  `Λ[m, i] ⊗ Δ[n] ∪ Δ[m] ⊗ ∂Δ[n] ⟶ Δ[m] ⊗ Δ[n]` are strong anodyne extensions (@joelriou)
* show that anodyne extensions are stable under the subdivision functor (@joelriou)

## References
* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*, IV.2][gabriel-zisman-1967]
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial

namespace SSet

open MorphismProperty

open modelCategoryQuillen in
/-- In the category of simplicial sets, an anodyne extension is a morphism
that has the left lifting property with respect to fibrations, where
a fibration is a morphism that has the right lifting property with respect
to horn inclusions. We do not introduce a typeclass for anodyne extensions
because when the Quillen model structure is fully upstreamed (TODO @joelriou),
the assumption `anodyneExtensions f` can be spelled as
`[Cofibration f] [WeakEquivalence f]`. -/
/-
**SSet.anodyneExtensions** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：anodyneExtensions : MorphismProperty SSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the category of simplicial sets, an anodyne extension is a morphism
that has the left lifting property with respect to fibrations, where
a fibration is a morphism that has the right lifting property with respect
to horn inclusions. We do not introduce a typeclass for anodyne extensions
because when the Quillen model structure is fully upstreamed (TODO @joelriou),
the assumption `anodyneExtensions f` can be spelled as
`[Cofibration f] [WeakEquivalence f]`.
-/
def anodyneExtensions : MorphismProperty SSet.{u} := (fibrations _).llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
  IsStableUnderCoproducts
/-
**SSet.anodyneExtensions.of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `SSet.anodyneExtensi
ons`。
形式化陈述：∀ {X Y : _root_.SSet} (f : X ⟶ Y) [CategoryTheory.IsIso f], SSet.anodyneEx
tensions f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_isIso`：of_isIso (P : MorphismProperty
 C) [P.ContainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y) [IsIso f] : P f
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `SSet.instIsMultiplicativeAnodyneExtensions`：SSet.anodyneExtensions.IsMul
tiplicative
· 使用定理 `SSet.instRespectsIsoAnodyneExtensions`：SSet.anodyneExtensions.RespectsIs
o
-/
lemma anodyneExtensions.of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    anodyneExtensions f :=
  MorphismProperty.of_isIso anodyneExtensions f
/-
**SSet.anodyneExtensions_eq_llp_rlp** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：anodyneExtensions_eq_llp_rlp : anodyneExtensions.{u} = modelCategoryQuille
n.J.rlp.llp
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma anodyneExtensions_eq_llp_rlp :
    anodyneExtensions.{u} = modelCategoryQuillen.J.rlp.llp :=
  rfl
/-
**SSet.anodyneExtensions.horn_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma anodyneExtensions.horn_ι {n : ℕ} [NeZero n] (i : Fin (n + 1)) :
    anodyneExtensions.{u} Λ[n, i].ι := by
  rw [anodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (modelCategoryQuillen.horn_ι_mem_J n i)

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : MorphismProperty.IsSmall.{u}
    (MorphismProperty.ofHoms.{u} (fun (i : Fin (n + 2)) ↦ Λ[n + 1, i].ι)) :=
  isSmall_ofHoms ..
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsSmall.{u} modelCategoryQuillen.J.{u} :=
  isSmall_iSup ..
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCardinalForSmallObjectArgument modelCategoryQuillen.J.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [modelCategoryQuillen.J, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSmallObjectArgument.{u} modelCategoryQuillen.J.{u} :=
  ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩
/-
**SSet.anodyneExtensions_eq_retracts_transfiniteCompositions** 是 Mathlib 中的一个引理，
位于命名空间 `SSet`。
形式化陈述：anodyneExtensions_eq_retracts_transfiniteCompositions : anodyneExtensions 
= (transfiniteCompositions.{u} (coproducts.{u} modelCategoryQuillen.J.{u}).pusho
uts).retracts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.anodyneExtensions_eq_llp_rlp`：anodyneExtensions_eq_llp_rlp : anodyn
eExtensions.{u} = modelCategoryQuillen.J.rlp.llp
· 使用引理 `CategoryTheory.MorphismProperty.llp_rlp_of_hasSmallObjectArgument`：llp_r
lp_of_hasSmallObjectArgument : I.rlp.llp = (transfiniteCompositions.{w} (coprodu
cts.{w} I).pushouts).retracts
· 使用定理 `SSet.instHasSmallObjectArgumentJ`：SSet.modelCategoryQuillen.J.HasSmallOb
jectArgument
-/
lemma anodyneExtensions_eq_retracts_transfiniteCompositions :
    anodyneExtensions = (transfiniteCompositions.{u}
      (coproducts.{u} modelCategoryQuillen.J.{u}).pushouts).retracts := by
  rw [anodyneExtensions_eq_llp_rlp, llp_rlp_of_hasSmallObjectArgument]
/-
**SSet.anodyneExtensions_eq_retracts_transfiniteCompositionsOfShape** 是 Mathlib 
中的一个引理，位于命名空间 `SSet`。
形式化陈述：anodyneExtensions_eq_retracts_transfiniteCompositionsOfShape : anodyneExte
nsions = (transfiniteCompositionsOfShape (coproducts.{u} modelCategoryQuillen.J.
{u}).pushouts Nat).retracts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.anodyneExtensions_eq_llp_rlp`：anodyneExtensions_eq_llp_rlp : anodyn
eExtensions.{u} = modelCategoryQuillen.J.rlp.llp
· 使用引理 `CategoryTheory.SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_a
leph0`：llp_rlp_of_isCardinalForSmallObjectArgument_aleph0 [I.IsCardinalForSmallO
bjectArgument Cardinal.aleph0.{w}] : I.rlp.llp = (transfiniteCompos…
· 使用定理 `SSet.instIsCardinalForSmallObjectArgumentJAleph0`：SSet.modelCategoryQuil
len.J.IsCardinalForSmallObjectArgument Cardinal.aleph0
-/
lemma anodyneExtensions_eq_retracts_transfiniteCompositionsOfShape :
    anodyneExtensions = (transfiniteCompositionsOfShape
      (coproducts.{u} modelCategoryQuillen.J.{u}).pushouts ℕ).retracts := by
  rw [anodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

/-- In the category of simplicial sets, a strong anodyne extension is a morphism
which belongs to the closure of horn inclusions by pushouts, coproducts,
transfinite compositions (but not by retracts). We define this class here
by saying that `f : X ⟶ Y` is a strong anodyne extension if `f` is a monomorphism
and there exists a regular pairing (in the sense of Moss) for the subcomplex
`Subcomplex.range f` of `Y`. -/
/-
**SSet.strongAnodyneExtensions** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：strongAnodyneExtensions : MorphismProperty SSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the category of simplicial sets, a strong anodyne extension is a morphism
which belongs to the closure of horn inclusions by pushouts, coproducts,
transfinite compositions (but not by retracts). We define this class here
by saying that `f : X ⟶ Y` is a strong anodyne extension if `f` is a monomorphis
m
and there exists a regular pairing (in the sense of Moss) for the subcomplex
`Subcomplex.range f` of `Y`.
-/
def strongAnodyneExtensions : MorphismProperty SSet.{u} :=
  fun _ _ f ↦ Mono f ∧ ∃ (P : (Subcomplex.range f).Pairing), P.IsRegular
/-
**SSet.strongAnodyneExtensions.mono** 是 Mathlib 中的一个定理，位于命名空间 `SSet.strongAnodyn
eExtensions`。
形式化陈述：∀ {X Y : _root_.SSet} {f : X ⟶ Y}, SSet.strongAnodyneExtensions f → Catego
ryTheory.Mono f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma strongAnodyneExtensions.mono {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : strongAnodyneExtensions f) : Mono f := hf.1
/-
**SSet.Subcomplex.Pairing.strongAnodyneExtensions** 是 Mathlib 中的一个定理，位于命名空间 `SSe
t.Subcomplex.Pairing`。
形式化陈述：∀ {X : _root_.SSet} {A : X.Subcomplex} (P : A.Pairing) [P.IsRegular], SSet
.strongAnodyneExtensions A.ι
参数：P : A.Pairing。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.instMonoι`：∀ {X : _root_.SSet} (A : X.Subcomplex), Categ
oryTheory.Mono A.ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Subfunctor.range_ι`：range_ι (G : Subfunctor F) : range G.
ι = G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Subcomplex.Pairing.strongAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] :
    strongAnodyneExtensions A.ι :=
  ⟨inferInstance, by
    generalize h : Subcomplex.range A.ι = B
    obtain rfl : B = A := by simpa using h.symm
    exact ⟨P, inferInstance⟩⟩
/-
**SSet.strongAnodyneExtensions_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma strongAnodyneExtensions_ι_iff {X : SSet.{u}} (A : X.Subcomplex) :
    strongAnodyneExtensions A.ι ↔ ∃ (P : A.Pairing), P.IsRegular :=
  ⟨fun hA ↦ by
    obtain ⟨_, P, _, rfl⟩ :
        ∃ (B : X.Subcomplex) (P : B.Pairing), P.IsRegular ∧ B = A := by
      obtain ⟨_, P, _⟩ := hA
      exact ⟨_, P, inferInstance, by simp⟩
    exact ⟨P, inferInstance⟩,
  fun ⟨P, _⟩ ↦ P.strongAnodyneExtensions⟩
/-
**SSet.Subcomplex.Pairing.anodyneExtensions** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Subc
omplex.Pairing`。
形式化陈述：∀ {X : _root_.SSet} {A : X.Subcomplex} (P : A.Pairing) [P.IsRegular], SSet
.anodyneExtensions A.ι
参数：P : A.Pairing。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le`：trans
finiteCompositionsOfShape_le [W.IsStableUnderTransfiniteCompositionOfShape J] : 
W.transfiniteCompositionsOfShape J <= W
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.isSt
ableUnderTransfiniteCompositionOfShape`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {W : CategoryTheory.MorphismProperty C}   [self : W.IsStableUnd
erTransfiniteComposi…
· 使用定理 `SSet.instIsStableUnderTransfiniteCompositionAnodyneExtensions`：SSet.anod
yneExtensions.IsStableUnderTransfiniteComposition
· 使用定理 `SSet.Subcomplex.Pairing.IsRegular.toIsProper`：∀ {X : _root_.SSet} {A : X
.Subcomplex} {P : A.Pairing} [self : P.IsRegular], P.IsProper
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SSet.instIsStableUnderCobaseChangeAnodyneExtensions`：SSet.anodyneExtensi
ons.IsStableUnderCobaseChange
· 使用定理 `SSet.instIsStableUnderCoproductsAnodyneExtensions`：CategoryTheory.Morphi
smProperty.IsStableUnderCoproducts.{u_1, u_2, u_2 + 1} SSet.anodyneExtensions
· 使用定理 `SSet.anodyneExtensions.horn_ι`：∀ {n : ℕ} [NeZero n] (i : Fin (n + 1)), S
Set.anodyneExtensions (SSet.horn n i).ι
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用引理 `HomotopicalAlgebra.AttachCells.pushouts_coproducts`：pushouts_coproducts 
: (coproducts.{w} (ofHoms g)).pushouts f
-/
lemma Subcomplex.Pairing.anodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] :
    anodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      exact .horn_ι c.index⟩
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : strongAnodyneExtensions.{u}.RespectsIso where
  precomp e _ f hf := by
    obtain ⟨_, P, hP⟩ := hf
    refine ⟨inferInstance, P.ofIso (Iso.refl _) ?_, inferInstance⟩
    simp [Subcomplex.range_comp, Subcomplex.range_eq_top e,
      Subcomplex.image_top]
  postcomp e _ f hf := by
    obtain ⟨_, P, hP⟩ := hf
    refine ⟨inferInstance, P.ofIso (asIso e).symm ?_, inferInstance⟩
    simp [Subcomplex.preimage_inv, Subcomplex.range_comp]
/-
**SSet.strongAnodyneExtensions_le_anodyneExtensions** 是 Mathlib 中的一个引理，位于命名空间 `S
Set`。
形式化陈述：strongAnodyneExtensions_le_anodyneExtensions : strongAnodyneExtensions.{u}
 <= anodyneExtensions
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Subfunctor.toRange_ι`：toRange_ι : toRange p ≫ (range p).ι
 = p
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `SSet.instIsMultiplicativeAnodyneExtensions`：SSet.anodyneExtensions.IsMul
tiplicative
· 使用定理 `SSet.anodyneExtensions.of_isIso`：∀ {X Y : _root_.SSet} (f : X ⟶ Y) [Cate
goryTheory.IsIso f], SSet.anodyneExtensions f
· 使用定理 `SSet.Subcomplex.instIsIsoToRangeOfMono`：∀ {X Y : _root_.SSet} (f : X ⟶ Y
) [CategoryTheory.Mono f], CategoryTheory.IsIso (SSet.Subcomplex.toRange f)
· 使用定理 `SSet.Subcomplex.Pairing.anodyneExtensions`：∀ {X : _root_.SSet} {A : X.Su
bcomplex} (P : A.Pairing) [P.IsRegular], SSet.anodyneExtensions A.ι
-/
lemma strongAnodyneExtensions_le_anodyneExtensions :
    strongAnodyneExtensions.{u} ≤ anodyneExtensions := by
  rintro X Y f ⟨_, P, _⟩
  rw [← Subfunctor.toRange_ι f]
  exact comp_mem _ _ _ (.of_isIso _) P.anodyneExtensions

end SSet

