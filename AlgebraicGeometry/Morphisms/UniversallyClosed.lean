/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.LocalAtTarget

/-!
# Universally closed morphism

A morphism of schemes `f : X ⟶ Y` is universally closed if `X ×[Y] Y' ⟶ Y'` is a closed map
for all base change `Y' ⟶ Y`.
This implies that `f` is topologically proper (`AlgebraicGeometry.Scheme.Hom.isProperMap`).

We show that being universally closed is local at the target, and is stable under compositions and
base changes.

-/

public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty

/-- A morphism of schemes `f : X ⟶ Y` is universally closed if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) a closed map.
-/
@[mk_iff]
/-
**AlgebraicGeometry.UniversallyClosed** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is universally closed if the base change `X ×[
Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) a closed map.
-/
class UniversallyClosed (f : X ⟶ Y) : Prop where
  universally_isClosedMap : universally (topologically @IsClosedMap) f

@[deprecated (since := "2026-01-20")]
alias UniversallyClosed.out := UniversallyClosed.universally_isClosedMap
/-
**AlgebraicGeometry.Scheme.Hom.isClosedMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Universa
llyClosed f], IsClosedMap ⇑f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.UniversallyClosed.universally_isClosedMap`：∀ {X Y : Al
gebraicGeometry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.UniversallyClosed 
f],   (AlgebraicGeometry.topologically @IsClosedM…
· 使用引理 `CategoryTheory.IsPullback.of_id_snd`：of_id_snd : IsPullback f (𝟙 _) (𝟙 _
) f
-/
lemma Scheme.Hom.isClosedMap {X Y : Scheme} (f : X ⟶ Y) [UniversallyClosed f] :
    IsClosedMap f := UniversallyClosed.universally_isClosedMap _ _ _ IsPullback.of_id_snd
/-
**AlgebraicGeometry.universallyClosed_eq** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：universallyClosed_eq : @UniversallyClosed = universally (topologically @Is
ClosedMap)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.universallyClosed_iff`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y),   AlgebraicGeometry.UniversallyClosed f ↔ (AlgebraicGeometry.to
pologically @IsClosedMap).uni…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem universallyClosed_eq : @UniversallyClosed = universally (topologically @IsClosedMap) := by
  ext X Y f; rw [universallyClosed_iff]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsClosedImmersion f] : UniversallyClosed f := by
  rw [universallyClosed_eq]
  intro X' Y' i₁ i₂ f' hf
  have hf' : IsClosedImmersion f' :=
    MorphismProperty.of_isPullback hf.flip inferInstance
  exact f'.isClosedEmbedding.isClosedMap
/-
**AlgebraicGeometry.universallyClosed_respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry`。
形式化陈述：universallyClosed_respectsIso : RespectsIso @UniversallyClosed
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.universallyClosed_eq`：universallyClosed_eq : @Universa
llyClosed = universally (topologically @IsClosedMap)
-/
theorem universallyClosed_respectsIso : RespectsIso @UniversallyClosed :=
  universallyClosed_eq.symm ▸ universally_respectsIso (topologically @IsClosedMap)
/-
**AlgebraicGeometry.universallyClosed_isStableUnderBaseChange** 是 Mathlib 中的一个实例
，位于命名空间 `AlgebraicGeometry`。
形式化陈述：universallyClosed_isStableUnderBaseChange : IsStableUnderBaseChange @Unive
rsallyClosed
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.universallyClosed_eq`：universallyClosed_eq : @Universa
llyClosed = universally (topologically @IsClosedMap)
-/
instance universallyClosed_isStableUnderBaseChange : IsStableUnderBaseChange @UniversallyClosed :=
  universallyClosed_eq.symm ▸ universally_isStableUnderBaseChange (topologically @IsClosedMap)
/-
**AlgebraicGeometry.isClosedMap_isStableUnderComposition** 是 Mathlib 中的一个实例，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：isClosedMap_isStableUnderComposition : IsStableUnderComposition (topologic
ally @IsClosedMap) where comp_mem f g hf hg
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X 
→ Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [in
st_2 :…
-/
instance isClosedMap_isStableUnderComposition :
    IsStableUnderComposition (topologically @IsClosedMap) where
  comp_mem f g hf hg := IsClosedMap.comp (f := f) (g := g) hg hf
/-
**AlgebraicGeometry.universallyClosed_isStableUnderComposition** 是 Mathlib 中的一个实
例，位于命名空间 `AlgebraicGeometry`。
形式化陈述：universallyClosed_isStableUnderComposition : IsStableUnderComposition @Uni
versallyClosed
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.universallyClosed_eq`：universallyClosed_eq : @Universa
llyClosed = universally (topologically @IsClosedMap)
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.universally`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.Ha
sPullbacks C]   (P : CategoryTheory.MorphismProperty C) [h…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
-/
instance universallyClosed_isStableUnderComposition :
    IsStableUnderComposition @UniversallyClosed := by
  rw [universallyClosed_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.UniversallyClosed.of_comp_surjective** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.UniversallyClosed`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicG
eometry.UniversallyClosed (CategoryTheory.CategoryStruct.comp f g)] [AlgebraicGe
ometry.Surjective f],   AlgebraicGeometry.UniversallyClosed g
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.UniversallyClosed.universally_isClosedMap`：∀ {X Y : Al
gebraicGeometry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.UniversallyClosed 
f],   (AlgebraicGeometry.topologically @IsClosedM…
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `IsClosedMap.of_comp_surjective`：∀ {X : Type u_1} {Y : Type u_2} {Z : Typ
e u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologic
alSpace Y] [inst_2 :…
· 使用定理 `AlgebraicGeometry.Surjective.surj`：∀ {X Y : AlgebraicGeometry.Scheme} {f
 : X ⟶ Y} [self : AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
· 使用定理 `CategoryTheory.MorphismProperty.pullback_fst`：pullback_fst {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong f] (H :
 P g) : P (pullback.fst f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme`：Category
Theory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Surjective
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
-/
lemma UniversallyClosed.of_comp_surjective {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyClosed (f ≫ g)] [Surjective f] : UniversallyClosed g := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have := UniversallyClosed.universally_isClosedMap _ _ _
    ((IsPullback.of_hasPullback i₁ f).paste_horiz H)
  exact IsClosedMap.of_comp_surjective (MorphismProperty.pullback_fst (P := @Surjective) _ _ ‹_›).1
    (Scheme.Hom.continuous _) this
/-
**AlgebraicGeometry.universallyClosedTypeComp** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry`。
形式化陈述：universallyClosedTypeComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [hf : U
niversallyClosed f] [hg : UniversallyClosed g] : UniversallyClosed (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
-/
instance universallyClosedTypeComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : UniversallyClosed f] [hg : UniversallyClosed g] : UniversallyClosed (f ≫ g) :=
  comp_mem _ _ _ hf hg
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @UniversallyClosed where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.universallyClosed_fst** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：universallyClosed_fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : Unive
rsallyClosed g] : UniversallyClosed (pullback.fst f g)
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.pullback_fst`：pullback_fst {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong f] (H :
 P g) : P (pullback.fst f g)
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
-/
instance universallyClosed_fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyClosed g] :
    UniversallyClosed (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g hg

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.universallyClosed_snd** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：universallyClosed_snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : Unive
rsallyClosed f] : UniversallyClosed (pullback.snd f g)
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
-/
instance universallyClosed_snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyClosed f] :
    UniversallyClosed (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf
/-
**AlgebraicGeometry.universallyClosed_isZariskiLocalAtTarget** 是 Mathlib 中的一个实例，
位于命名空间 `AlgebraicGeometry`。
形式化陈述：universallyClosed_isZariskiLocalAtTarget : IsZariskiLocalAtTarget @Univers
allyClosed
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.universallyClosed_eq`：universallyClosed_eq : @Universa
llyClosed = universally (topologically @IsClosedMap)
· 使用定理 `AlgebraicGeometry.universally_isZariskiLocalAtTarget`：universally_isZari
skiLocalAtTarget (P : MorphismProperty Scheme) (hP₂ : forall {X Y : Scheme.{u}} 
(f : X ⟶ Y) {ι : Type u} (U : ι -> Y.Opens…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.IsOpenCover.isClosedMap_iff_restrictPreimage`：isClosedM
ap_iff_restrictPreimage : IsClosedMap f ↔ forall i, IsClosedMap ((U i).1.restric
tPreimage f)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AlgebraicGeometry.morphismRestrict_base`：morphismRestrict_base {X Y : Sc
heme.{u}} (f : X ⟶ Y) (U : Y.Opens) : ⇑(f ∣_ U) = U.1.restrictPreimage f
-/
instance universallyClosed_isZariskiLocalAtTarget : IsZariskiLocalAtTarget @UniversallyClosed := by
  rw [universallyClosed_eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact hU.isClosedMap_iff_restrictPreimage.mpr H
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [UniversallyClosed f] : UniversallyClosed (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

open Scheme.Pullback _root_.PrimeSpectrum MvPolynomial in
/-- If `X` is universally closed over a field, then `X` is quasi-compact. -/
/-
**AlgebraicGeometry.compactSpace_of_universallyClosed** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry`。
形式化陈述：compactSpace_of_universallyClosed {K} [Field K] (f : X ⟶ Spec (.of K)) [Un
iversallyClosed f] : CompactSpace X
参数：f : X ⟶ Spec (.of K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isClosedMap`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f], IsClosedMap ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Cover.covers`：∀ {K : CategoryTheory.Precoverage
 AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeo
metry.Scheme.JointlySurject…
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.isBasis_iff_nbhd`：isBasis_iff_nbhd {B : Set (Open
s α)} : IsBasis B ↔ forall {U : Opens α} {x}, x in U -> exists U' in B, x in U' 
∧ U' <= U
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用引理 `MvPolynomial.aeval_ite_mem_eq_self`：aeval_ite_mem_eq_self (q : MvPolynom
ial σ R) {s : Set σ} (hs : (q.vars : Set σ) subseteq s) [forall i, Decidable (i 
in s)] : MvPolynomial.ae…
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `Set.iUnion₂_eq_univ_iff`：iUnion₂_eq_univ_iff {s : forall i, κ i -> Set α
} : ⋃ (i) (j), s i j = univ ↔ forall a, exists i j, a in s i j
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
If `X` is universally closed over a field, then `X` is quasi-compact.
-/
lemma compactSpace_of_universallyClosed
    {K} [Field K] (f : X ⟶ Spec (.of K)) [UniversallyClosed f] : CompactSpace X := by
  classical
  let 𝒰 : X.OpenCover := X.affineCover
  let U (i : 𝒰.I₀) : X.Opens := (𝒰.f i).opensRange
  let T : Scheme := Spec (.of <| MvPolynomial 𝒰.I₀ K)
  let q : T ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom MvPolynomial.C)
  let Ti (i : 𝒰.I₀) : T.Opens := basicOpen (MvPolynomial.X i)
  let fT : pullback f q ⟶ T := pullback.snd f q
  let p : pullback f q ⟶ X := pullback.fst f q
  let Z : Set (pullback f q :) := (⨆ i, fT ⁻¹ᵁ (Ti i) ⊓ p ⁻¹ᵁ (U i) : (pullback f q).Opens)ᶜ
  have hZ : IsClosed Z := by
    simp only [Z, isClosed_compl_iff, Opens.coe_iSup, Opens.coe_inf, Opens.map_coe]
    exact isOpen_iUnion fun i ↦ (fT.continuous.1 _ (Ti i).2).inter (p.continuous.1 _ (U i).2)
  let Zc : T.Opens := ⟨(fT '' Z)ᶜ, (fT.isClosedMap _ hZ).isOpen_compl⟩
  let ψ : MvPolynomial 𝒰.I₀ K →ₐ[K] K := MvPolynomial.aeval (fun _ ↦ 1)
  let t : T := Spec.map (CommRingCat.ofHom ψ.toRingHom) default
  have ht (i : 𝒰.I₀) : t ∈ Ti i := show ψ (.X i) ≠ 0 by simp [ψ]
  have htZc : t ∈ Zc := by
    intro ⟨z, hz, hzt⟩
    suffices ∃ i, fT z ∈ Ti i ∧ p z ∈ U i from hz (by simpa)
    exact ⟨𝒰.idx (p z), hzt ▸ ht _, by simpa [U] using 𝒰.covers (p z)⟩
  obtain ⟨U', ⟨g, rfl⟩, htU', hU'le⟩ := Opens.isBasis_iff_nbhd.mp isBasis_basic_opens htZc
  let σ : Finset 𝒰.I₀ := MvPolynomial.vars g
  let φ : MvPolynomial 𝒰.I₀ K →+* MvPolynomial 𝒰.I₀ K :=
    (MvPolynomial.aeval fun i : 𝒰.I₀ ↦ if i ∈ σ then MvPolynomial.X i else 0).toRingHom
  let t' : T := Spec.map (CommRingCat.ofHom φ) t
  have ht'g : t' ∈ PrimeSpectrum.basicOpen g :=
    show φ g ∉ t.asIdeal from (show φ g = g from aeval_ite_mem_eq_self g subset_rfl).symm ▸ htU'
  have h : t' ∉ fT '' Z := hU'le ht'g
  suffices ⋃ i ∈ σ, (U i).1 = Set.univ from
    ⟨this ▸ Finset.isCompact_biUnion _ fun i _ ↦ isCompact_range (𝒰.f i).continuous⟩
  rw [Set.iUnion₂_eq_univ_iff]
  contrapose! h
  obtain ⟨x, hx⟩ := h
  obtain ⟨z, rfl, hzr⟩ := exists_preimage_pullback x t' (Subsingleton.elim (f x) (q t'))
  suffices ∀ i, t ∈ (Ti i).comap ⟨_, continuous_comap φ⟩ → p z ∉ U i from
    ⟨z, by simpa [Z, p, fT, hzr], hzr⟩
  intro i hi₁ hi₂
  rw [comap_basicOpen, show φ (.X i) = 0 by simpa [φ] using (hx i · hi₂), basicOpen_zero] at hi₁
  cases hi₁

set_option backward.isDefEq.respectTransparency false in
@[stacks 04XU]
/-
**AlgebraicGeometry.Scheme.Hom.isProperMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Universa
llyClosed f], IsProperMap ⇑f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isProperMap_iff_isClosedMap_and_compact_fibers`：isProperMap_iff_isClosed
Map_and_compact_fibers : IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ forall y
, IsCompact (f ⁻¹' {y})
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isClosedMap`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f], IsClosedMap ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.compactSpace_of_universallyClosed`：compactSpace_of_uni
versallyClosed {K} [Field K] (f : X ⟶ Spec (.of K)) [UniversallyClosed f] : Comp
actSpace X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.range_fromSpecResidueField`：range_fromSpecResid
ueField (x : X.carrier) : Set.range (X.fromSpecResidueField x) = {x}
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.range_fst`：range_fst : Set.range (pull
back.fst f g) = f ⁻¹' Set.range g
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
-/
lemma Scheme.Hom.isProperMap (f : X ⟶ Y) [UniversallyClosed f] : IsProperMap f := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨f.continuous, f.isClosedMap, fun y ↦ ?_⟩
  have := compactSpace_of_universallyClosed (pullback.snd f (Y.fromSpecResidueField y))
  rw [← Scheme.range_fromSpecResidueField, ← Scheme.Pullback.range_fst]
  exact isCompact_range (Scheme.Hom.continuous _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [UniversallyClosed f] : QuasiCompact f where
  isCompact_preimage _ _ := f.isProperMap.isCompact_preimage

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.universallyClosed_eq_universallySpecializing** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：universallyClosed_eq_universallySpecializing : @UniversallyClosed = (topol
ogically @SpecializingMap).universally ⊓ @QuasiCompact
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.universally_eq_iff`：universally_eq_iff {
P : MorphismProperty C} : P.universally = P ↔ P.IsStableUnderBaseChange
· 使用定理 `CategoryTheory.MorphismProperty.universally_inf`：universally_inf (P Q : 
MorphismProperty C) : (P ⊓ Q).universally = P.universally ⊓ Q.universally
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.MorphismProperty.universally_mono`：universally_mono : Mon
otone (universally : MorphismProperty C -> MorphismProperty C)
· 使用引理 `IsClosedMap.specializingMap`：IsClosedMap.specializingMap (hf : IsClosedM
ap f) : SpecializingMap f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isClosedMap`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f], IsClosedMap ⇑f
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfUniversallyClosed`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f], Algebraic
Geometry.QuasiCompact f
· 使用定理 `AlgebraicGeometry.universallyClosed_eq`：universallyClosed_eq : @Universa
llyClosed = universally (topologically @IsClosedMap)
· 使用定理 `AlgebraicGeometry.isClosedMap_iff_specializingMap`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f], IsClosedMap ⇑f ↔ S
pecializingMap ⇑f
-/
lemma universallyClosed_eq_universallySpecializing :
    @UniversallyClosed = (topologically @SpecializingMap).universally ⊓ @QuasiCompact := by
  rw [← universally_eq_iff (P := @QuasiCompact).mpr inferInstance, ← universally_inf]
  apply le_antisymm
  · rw [← universally_eq_iff (P := @UniversallyClosed).mpr inferInstance]
    exact universally_mono fun X Y f H ↦ ⟨f.isClosedMap.specializingMap, inferInstance⟩
  · rw [universallyClosed_eq]
    exact universally_mono fun X Y f ⟨h₁, h₂⟩ ↦ (isClosedMap_iff_specializingMap _).mpr h₁
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) Surjective.of_universallyClosed_of_isDominant
    [UniversallyClosed f] [IsDominant f] : Surjective f := by
  rw [surjective_iff, ← Set.range_eq_univ, ← f.denseRange.closure_range,
    f.isClosedMap.isClosed_range.closure_eq]

end AlgebraicGeometry

