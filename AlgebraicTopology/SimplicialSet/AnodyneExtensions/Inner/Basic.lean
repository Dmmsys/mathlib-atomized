/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Inner anodyne extensions

Much of this file is mirrored from
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic`.

*Inner* anodyne extensions form a property of morphisms in the category of simplicial
sets. It contains *inner* horn inclusions and it is closed under coproducts, pushouts,
transfinite compositions and retracts. Equivalently, using the small
object argument, inner anodyne extensions can be defined (and are defined here)
as the class of morphisms that satisfy the left lifting property with respect
to the class of inner fibrations.

-/

public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial

namespace SSet

open MorphismProperty

/-- In the category of simplicial sets, an *inner* anodyne extension is a morphism
that has the left lifting property with respect to *inner* fibrations, where
an inner fibration is a morphism that has the right lifting property with respect
to inner horn inclusions. -/
@[expose, kerodon 01BR]
/-
**SSet.innerAnodyneExtensions** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：innerAnodyneExtensions : MorphismProperty SSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the category of simplicial sets, an *inner* anodyne extension is a morphism
that has the left lifting property with respect to *inner* fibrations, where
an inner fibration is a morphism that has the right lifting property with respec
t
to inner horn inclusions.
-/
def innerAnodyneExtensions : MorphismProperty SSet.{u} := innerFibrations.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
  IsStableUnderCoproducts
/-
**SSet.innerAnodyneExtensions.of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `SSet.innerAnod
yneExtensions`。
形式化陈述：∀ {X Y : _root_.SSet} (f : X ⟶ Y) [CategoryTheory.IsIso f], SSet.innerAnod
yneExtensions f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_isIso`：of_isIso (P : MorphismProperty
 C) [P.ContainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y) [IsIso f] : P f
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `SSet.instIsMultiplicativeInnerAnodyneExtensions`：SSet.innerAnodyneExtens
ions.IsMultiplicative
· 使用定理 `SSet.instRespectsIsoInnerAnodyneExtensions`：SSet.innerAnodyneExtensions.
RespectsIso
-/
lemma innerAnodyneExtensions.of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    innerAnodyneExtensions f :=
  MorphismProperty.of_isIso innerAnodyneExtensions f
/-
**SSet.innerAnodyneExtensions_eq_llp_rlp** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：innerAnodyneExtensions_eq_llp_rlp : innerAnodyneExtensions.{u} = innerHorn
Inclusions.rlp.llp
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma innerAnodyneExtensions_eq_llp_rlp :
    innerAnodyneExtensions.{u} = innerHornInclusions.rlp.llp :=
  rfl
/-
**SSet.innerAnodyneExtensions.horn_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma innerAnodyneExtensions.horn_ι {n : ℕ} {i : Fin (n + 1)}
    (h0 : 0 < i) (hn : i < Fin.last n) :
    innerAnodyneExtensions.{u} Λ[n, i].ι := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (horn_ι_mem_innerHornInclusions h0 hn)
/-
**SSet.innerAnodyneExtensions_le** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：innerAnodyneExtensions_le : innerAnodyneExtensions <= anodyneExtensions.{u
}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.anodyneExtensions_eq_llp_rlp`：anodyneExtensions_eq_llp_rlp : anodyn
eExtensions.{u} = modelCategoryQuillen.J.rlp.llp
· 使用引理 `SSet.innerAnodyneExtensions_eq_llp_rlp`：innerAnodyneExtensions_eq_llp_rl
p : innerAnodyneExtensions.{u} = innerHornInclusions.rlp.llp
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_iff_le_rlp`：le_llp_iff_le_rlp (T'
 : MorphismProperty C) : T <= T'.llp ↔ T' <= T.rlp
· 使用引理 `CategoryTheory.MorphismProperty.rlp_llp_rlp`：rlp_llp_rlp : T.rlp.llp.rlp
 = T.rlp
· 使用引理 `CategoryTheory.MorphismProperty.antitone_rlp`：antitone_rlp : Antitone (r
lp : MorphismProperty C -> _)
· 使用引理 `SSet.innerHornInclusions_le_J`：innerHornInclusions_le_J : innerHornInclu
sions.{u} <= modelCategoryQuillen.J
-/
lemma innerAnodyneExtensions_le : innerAnodyneExtensions ≤ anodyneExtensions.{u} := by
  rw [anodyneExtensions_eq_llp_rlp, innerAnodyneExtensions_eq_llp_rlp, le_llp_iff_le_rlp,
    rlp_llp_rlp]
  exact antitone_rlp innerHornInclusions_le_J

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsSmall.{u} innerHornInclusions.{u} := by
  rw [innerHornInclusions_eq_iSup]
  have (n : ℕ) : MorphismProperty.IsSmall.{u}
    (MorphismProperty.ofHoms.{u}
      fun p : {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)} ↦ Λ[n + 2, p].ι) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCardinalForSmallObjectArgument innerHornInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [innerHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSmallObjectArgument.{u} innerHornInclusions.{u} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩
/-
**SSet.innerAnodyneExtensions_eq_retracts_transfiniteCompositions** 是 Mathlib 中的
一个引理，位于命名空间 `SSet`。
形式化陈述：innerAnodyneExtensions_eq_retracts_transfiniteCompositions : innerAnodyneE
xtensions = (transfiniteCompositions.{u} (coproducts.{u} innerHornInclusions.{u}
).pushouts).retracts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.innerAnodyneExtensions_eq_llp_rlp`：innerAnodyneExtensions_eq_llp_rl
p : innerAnodyneExtensions.{u} = innerHornInclusions.rlp.llp
· 使用引理 `CategoryTheory.MorphismProperty.llp_rlp_of_hasSmallObjectArgument`：llp_r
lp_of_hasSmallObjectArgument : I.rlp.llp = (transfiniteCompositions.{w} (coprodu
cts.{w} I).pushouts).retracts
· 使用定理 `SSet.instHasSmallObjectArgumentInnerHornInclusions`：SSet.innerHornInclus
ions.HasSmallObjectArgument
-/
lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositions :
    innerAnodyneExtensions = (transfiniteCompositions.{u}
      (coproducts.{u} innerHornInclusions.{u}).pushouts).retracts := by
  rw [innerAnodyneExtensions_eq_llp_rlp, llp_rlp_of_hasSmallObjectArgument]
/-
**SSet.innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape** 是 Mat
hlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape : innerA
nodyneExtensions = (transfiniteCompositionsOfShape (coproducts.{u} innerHornIncl
usions.{u}).pushouts Nat).retracts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.innerAnodyneExtensions_eq_llp_rlp`：innerAnodyneExtensions_eq_llp_rl
p : innerAnodyneExtensions.{u} = innerHornInclusions.rlp.llp
· 使用引理 `CategoryTheory.SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_a
leph0`：llp_rlp_of_isCardinalForSmallObjectArgument_aleph0 [I.IsCardinalForSmallO
bjectArgument Cardinal.aleph0.{w}] : I.rlp.llp = (transfiniteCompos…
· 使用定理 `SSet.instIsCardinalForSmallObjectArgumentInnerHornInclusionsAleph0`：SSet
.innerHornInclusions.IsCardinalForSmallObjectArgument Cardinal.aleph0
-/
lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape :
    innerAnodyneExtensions = (transfiniteCompositionsOfShape
      (coproducts.{u} innerHornInclusions.{u}).pushouts ℕ).retracts := by
  rw [innerAnodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

/-- In the category of simplicial sets, a strong *inner* anodyne extension is a morphism
which belongs to the closure of *inner* horn inclusions by pushouts, coproducts,
transfinite compositions (but not by retracts). We define this class here
by saying that `f : X ⟶ Y` is a strong inner anodyne extension if `f` is a monomorphism
and there exists a regular, *inner* pairing (in the sense of Moss) for the subcomplex
`Subcomplex.range f` of `Y`. -/
/-
**SSet.strongInnerAnodyneExtensions** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：strongInnerAnodyneExtensions : MorphismProperty SSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the category of simplicial sets, a strong *inner* anodyne extension is a morp
hism
which belongs to the closure of *inner* horn inclusions by pushouts, coproducts,
transfinite compositions (but not by retracts). We define this class here
by saying that `f : X ⟶ Y` is a strong inner anodyne extension if `f` is a monom
orphism
and there exists a regular, *inner* pairing (in the sense of Moss) for the subco
mplex
`Subcomplex.range f` of `Y`.
-/
def strongInnerAnodyneExtensions : MorphismProperty SSet.{u} :=
  fun _ _ f ↦ Mono f ∧ ∃ (P : (Subcomplex.range f).Pairing) (_ : P.IsRegular), P.IsInner
/-
**SSet.strongInnerAnodyneExtensions.mono** 是 Mathlib 中的一个定理，位于命名空间 `SSet.strongI
nnerAnodyneExtensions`。
形式化陈述：∀ {X Y : _root_.SSet} {f : X ⟶ Y}, SSet.strongInnerAnodyneExtensions f → C
ategoryTheory.Mono f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma strongInnerAnodyneExtensions.mono {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : strongInnerAnodyneExtensions f) : Mono f := hf.1
/-
**SSet.strongInnerAnodyneExtensions_le_strongAnodyneExtensions** 是 Mathlib 中的一个引
理，位于命名空间 `SSet`。
形式化陈述：strongInnerAnodyneExtensions_le_strongAnodyneExtensions : strongInnerAnody
neExtensions.{u} <= strongAnodyneExtensions
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma strongInnerAnodyneExtensions_le_strongAnodyneExtensions :
    strongInnerAnodyneExtensions.{u} ≤ strongAnodyneExtensions :=
  fun _ _ _ ⟨_, P, _, _⟩ ↦ ⟨inferInstance, P, inferInstance⟩
/-
**SSet.Subcomplex.Pairing.strongInnerAnodyneExtensions** 是 Mathlib 中的一个定理，位于命名空间
 `SSet.Subcomplex.Pairing`。
形式化陈述：∀ {X : _root_.SSet} {A : X.Subcomplex} (P : A.Pairing) [h₁ : P.IsRegular] 
[h₂ : P.IsInner],   SSet.strongInnerAnodyneExtensions A.ι
参数：P : A.Pairing。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.Pairing.IsRegular.toIsProper`：∀ {X : _root_.SSet} {A : X
.Subcomplex} {P : A.Pairing} [self : P.IsRegular], P.IsProper
· 使用定理 `SSet.Subcomplex.instMonoι`：∀ {X : _root_.SSet} (A : X.Subcomplex), Categ
oryTheory.Mono A.ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Subfunctor.range_ι`：range_ι (G : Subfunctor F) : range G.
ι = G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SSet.Subcomplex.Pairing.instIsRegularOfIso`：∀ {X : _root_.SSet} {A : X.S
ubcomplex} (P : A.Pairing) {Y : _root_.SSet} {B : Y.Subcomplex} (e : Y ≅ X)   (h
A : A.preimage e.hom = B) [P.IsR…
· 使用定理 `SSet.Subcomplex.Pairing.instIsInnerOfIso`：∀ {X : _root_.SSet} {A : X.Sub
complex} (P : A.Pairing) {Y : _root_.SSet} {B : Y.Subcomplex} (e : Y ≅ X)   (hA 
: A.preimage e.hom = B) [inst …
-/
lemma Subcomplex.Pairing.strongInnerAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [h₁ : P.IsRegular] [h₂ : P.IsInner] :
    strongInnerAnodyneExtensions A.ι :=
  ⟨inferInstance, Pairing.ofIso P (Iso.refl _)
    (by simp only [Iso.refl_hom, preimage_id, Subfunctor.range_ι]), inferInstance, inferInstance⟩
/-
**SSet.strongInnerAnodyneExtensions_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma strongInnerAnodyneExtensions_ι_iff {X : SSet.{u}} (A : X.Subcomplex) :
    strongInnerAnodyneExtensions A.ι ↔ ∃ (P : A.Pairing) (_ : P.IsRegular), P.IsInner :=
  ⟨fun hA ↦ by
    obtain ⟨_, P, _, ⟨_, rfl⟩⟩ :
        ∃ (B : X.Subcomplex) (P : B.Pairing) (h : P.IsRegular), P.IsInner ∧ B = A := by
      obtain ⟨_, P₁, _, P₂⟩ := hA
      exact ⟨_, P₁, inferInstance, ⟨P₂, by simp⟩⟩
    exact ⟨P, ⟨inferInstance, inferInstance⟩⟩,
  fun ⟨P, ⟨_, _⟩⟩ ↦ P.strongInnerAnodyneExtensions⟩
/-
**SSet.Subcomplex.Pairing.innerAnodyneExtensions** 是 Mathlib 中的一个定理，位于命名空间 `SSet
.Subcomplex.Pairing`。
形式化陈述：∀ {X : _root_.SSet} {A : X.Subcomplex} (P : A.Pairing) [inst : P.IsRegular
] [P.IsInner], SSet.innerAnodyneExtensions A.ι
参数：P : A.Pairing。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.Pairing.IsRegular.toIsProper`：∀ {X : _root_.SSet} {A : X
.Subcomplex} {P : A.Pairing} [self : P.IsRegular], P.IsProper
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le`：trans
finiteCompositionsOfShape_le [W.IsStableUnderTransfiniteCompositionOfShape J] : 
W.transfiniteCompositionsOfShape J <= W
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.isSt
ableUnderTransfiniteCompositionOfShape`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {W : CategoryTheory.MorphismProperty C}   [self : W.IsStableUnd
erTransfiniteComposi…
· 使用定理 `SSet.instIsStableUnderTransfiniteCompositionInnerAnodyneExtensions`：SSet
.innerAnodyneExtensions.IsStableUnderTransfiniteComposition
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SSet.instIsStableUnderCobaseChangeInnerAnodyneExtensions`：SSet.innerAnod
yneExtensions.IsStableUnderCobaseChange
· 使用定理 `SSet.instIsStableUnderCoproductsInnerAnodyneExtensions`：CategoryTheory.M
orphismProperty.IsStableUnderCoproducts.{u_1, u_2, u_2 + 1} SSet.innerAnodyneExt
ensions
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `SSet.Subcomplex.Pairing.isUniquelyCodimOneFace`：isUniquelyCodimOneFace [
P.IsProper] (x : P.II) : S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.pos_iff_ne_zero`：∀ {n : ℕ} [inst : NeZero n] {a : Fin n}, 0 < a ↔ a 
≠ 0
· 使用定理 `SSet.Subcomplex.Pairing.IsInner.ne_zero`：∀ {X : _root_.SSet} {A : X.Subc
omplex} {P : A.Pairing} {inst : P.IsProper} [self : P.IsInner] (x : ↑P.II) {d : 
ℕ}   (hd : (↑x).dim = d), ⋯.i…
· 使用引理 `Fin.lt_last_iff_ne_last`：lt_last_iff_ne_last {a : Fin (n + 1)} : a < las
t n ↔ a != last n
· 使用定理 `SSet.Subcomplex.Pairing.IsInner.ne_last`：∀ {X : _root_.SSet} {A : X.Subc
omplex} {P : A.Pairing} {inst : P.IsProper} [self : P.IsInner] (x : ↑P.II) {d : 
ℕ}   (hd : (↑x).dim = d), ⋯.i…
· 使用定理 `SSet.innerAnodyneExtensions.horn_ι`：∀ {n : ℕ} {i : Fin (n + 1)}, 0 < i →
 i < Fin.last n → SSet.innerAnodyneExtensions (SSet.horn n i).ι
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用引理 `HomotopicalAlgebra.AttachCells.pushouts_coproducts`：pushouts_coproducts 
: (coproducts.{w} (ofHoms g)).pushouts f
-/
lemma Subcomplex.Pairing.innerAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] [P.IsInner] :
    innerAnodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      have h0 := Fin.pos_iff_ne_zero.mpr (IsInner.ne_zero c.s rfl)
      have hn := Fin.lt_last_iff_ne_last.mpr (IsInner.ne_last c.s rfl)
      have : NeZero c.dim := ⟨by grind⟩
      exact .horn_ι h0 hn⟩
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : strongInnerAnodyneExtensions.{u}.RespectsIso where
  precomp e _ f hf := by
    obtain ⟨_, P, hP, hP'⟩ := hf
    refine ⟨inferInstance, P.ofIso (Iso.refl _) ?_, inferInstance, inferInstance⟩
    simp [Subcomplex.range_comp, Subcomplex.range_eq_top e, Subcomplex.image_top]
  postcomp e _ f hf := by
    obtain ⟨_, P, hP, hP'⟩ := hf
    refine ⟨inferInstance, P.ofIso (asIso e).symm ?_, inferInstance, inferInstance⟩
    simp [Subcomplex.preimage_inv, Subcomplex.range_comp]
/-
**SSet.strongInnerAnodyneExtensions_le_innerAnodyneExtensions** 是 Mathlib 中的一个引理
，位于命名空间 `SSet`。
形式化陈述：strongInnerAnodyneExtensions_le_innerAnodyneExtensions : strongInnerAnodyn
eExtensions.{u} <= innerAnodyneExtensions
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
· 使用定理 `SSet.instIsMultiplicativeInnerAnodyneExtensions`：SSet.innerAnodyneExtens
ions.IsMultiplicative
· 使用定理 `SSet.innerAnodyneExtensions.of_isIso`：∀ {X Y : _root_.SSet} (f : X ⟶ Y) 
[CategoryTheory.IsIso f], SSet.innerAnodyneExtensions f
· 使用定理 `SSet.Subcomplex.instIsIsoToRangeOfMono`：∀ {X Y : _root_.SSet} (f : X ⟶ Y
) [CategoryTheory.Mono f], CategoryTheory.IsIso (SSet.Subcomplex.toRange f)
· 使用定理 `SSet.Subcomplex.Pairing.innerAnodyneExtensions`：∀ {X : _root_.SSet} {A :
 X.Subcomplex} (P : A.Pairing) [inst : P.IsRegular] [P.IsInner], SSet.innerAnody
neExtensions A.ι
-/
lemma strongInnerAnodyneExtensions_le_innerAnodyneExtensions :
    strongInnerAnodyneExtensions.{u} ≤ innerAnodyneExtensions := by
  rintro X Y f ⟨_, P, _, _⟩
  rw [← Subfunctor.toRange_ι f]
  exact comp_mem _ _ _ (.of_isIso _) P.innerAnodyneExtensions

end SSet

