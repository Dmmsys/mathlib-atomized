/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.Topology.LocalAtTarget

/-!
# Universally injective morphism

A morphism of schemes `f : X ⟶ Y` is universally injective if `X ×[Y] Y' ⟶ Y'` is injective
for all base changes `Y' ⟶ Y`. This is equivalent to the diagonal morphism being surjective
(`AlgebraicGeometry.UniversallyInjective.iff_diagonal`).

We show that being universally injective is local at the target, and is stable under
compositions and base changes.

We also prove that universally injective is equivalent to being injective with
purely inseparable residue field extensions (also known as a radical morphism), see
`AlgebraicGeometry.tfae_universallyInjective` and Stacks tag 01S4.

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty Function

/--
A morphism of schemes `f : X ⟶ Y` is universally injective if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is injective (on points).
-/
@[mk_iff]
/-
**AlgebraicGeometry.UniversallyInjective** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicG
eometry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is universally injective if the base change `X
 ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is injective (on points).
-/
class UniversallyInjective (f : X ⟶ Y) : Prop where
  universally_injective : universally (topologically (Injective ·)) f
/-
**AlgebraicGeometry.Scheme.Hom.injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Universa
llyInjective f], Function.Injective ⇑f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.UniversallyInjective.universally_injective`：∀ {X Y : A
lgebraicGeometry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.UniversallyInject
ive f],   (AlgebraicGeometry.topologically fun {α …
· 使用引理 `CategoryTheory.IsPullback.of_id_snd`：of_id_snd : IsPullback f (𝟙 _) (𝟙 _
) f
-/
theorem Scheme.Hom.injective (f : X ⟶ Y) [UniversallyInjective f] :
    Function.Injective f :=
  UniversallyInjective.universally_injective _ _ _ .of_id_snd
/-
**AlgebraicGeometry.universallyInjective_eq** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：universallyInjective_eq : @UniversallyInjective = universally (topological
ly (Injective ·))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.universallyInjective_iff`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y),   AlgebraicGeometry.UniversallyInjective f ↔     (AlgebraicG
eometry.topologically fun {α β} …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem universallyInjective_eq :
    @UniversallyInjective = universally (topologically (Injective ·)) := by
  ext X Y f; rw [universallyInjective_iff]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.universallyInjective_eq_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：universallyInjective_eq_diagonal : @UniversallyInjective = diagonal @Surje
ctive
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.UniversallyInjective.universally_injective`：∀ {X Y : A
lgebraicGeometry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.UniversallyInject
ive f],   (AlgebraicGeometry.topologically fun {α …
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.universally_eq_iff`：universally_eq_iff {
P : MorphismProperty C} : P.universally = P ↔ P.IsStableUnderBaseChange
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.diagonal`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limi
ts.HasPullbacks C]   {P : CategoryTheory.MorphismPrope…
· 使用定理 `AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme`：Category
Theory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Surjective
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeSurjective`：CategoryTheory.Morphi
smProperty.RespectsIso @AlgebraicGeometry.Surjective
· 使用定理 `AlgebraicGeometry.universallyInjective_eq`：universallyInjective_eq : @Un
iversallyInjective = universally (topologically (Injective ·))
· 使用定理 `CategoryTheory.MorphismProperty.universally_mono`：universally_mono : Mon
otone (universally : MorphismProperty C -> MorphismProperty C)
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`：exists_preim
age_pullback (x : X) (y : Y) (h : f x = g y) : exists z : ↑(pullback f g), pullb
ack.fst f g z = x ∧ pullback.snd f g z = y
· 使用定理 `AlgebraicGeometry.Surjective.surj`：∀ {X Y : AlgebraicGeometry.Scheme} {f
 : X ⟶ Y} [self : AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
-/
theorem universallyInjective_eq_diagonal :
    @UniversallyInjective = diagonal @Surjective := by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨fun x ↦ ⟨pullback.fst f f x, hf.1 _ _ _ (IsPullback.of_hasPullback f f) ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
    rfl
  · rw [← universally_eq_iff.mpr (inferInstance : IsStableUnderBaseChange (diagonal @Surjective)),
      universallyInjective_eq]
    apply universally_mono
    intro X Y f hf x₁ x₂ e
    obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
    obtain ⟨t, rfl⟩ := hf.1 t
    rw [← ht₁, ← ht₂, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.diagonal_fst,
      pullback.diagonal_snd]
/-
**AlgebraicGeometry.UniversallyInjective.iff_diagonal** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.UniversallyInjective`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.Univer
sallyInjective f ↔ AlgebraicGeometry.Surjective (CategoryTheory.Limits.pullback.
diagonal f)
参数：f : X ⟶ Y；CategoryTheory.Limits.pullback.diagonal f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.universallyInjective_eq_diagonal`：universallyInjective
_eq_diagonal : @UniversallyInjective = diagonal @Surjective
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem UniversallyInjective.iff_diagonal :
    UniversallyInjective f ↔ Surjective (pullback.diagonal f) := by
  rw [universallyInjective_eq_diagonal]; rfl
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [Mono f] : UniversallyInjective f :=
  have := (pullback.isIso_diagonal_iff f).mpr inferInstance
  (UniversallyInjective.iff_diagonal f).mpr inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.UniversallyInjective.respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.UniversallyInjective`。
形式化陈述：CategoryTheory.MorphismProperty.RespectsIso @AlgebraicGeometry.Universally
Injective
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.diagonal`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasPullba
cks C]   {P : CategoryTheory.MorphismPrope…
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeSurjective`：CategoryTheory.Morphi
smProperty.RespectsIso @AlgebraicGeometry.Surjective
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.universallyInjective_eq_diagonal`：universallyInjective
_eq_diagonal : @UniversallyInjective = diagonal @Surjective
-/
theorem UniversallyInjective.respectsIso : RespectsIso @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.UniversallyInjective.isStableUnderBaseChange** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicGeometry.UniversallyInjective`。
形式化陈述：CategoryTheory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry
.UniversallyInjective
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.diagonal`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limi
ts.HasPullbacks C]   {P : CategoryTheory.MorphismPrope…
· 使用定理 `AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme`：Category
Theory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Surjective
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeSurjective`：CategoryTheory.Morphi
smProperty.RespectsIso @AlgebraicGeometry.Surjective
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.universallyInjective_eq_diagonal`：universallyInjective
_eq_diagonal : @UniversallyInjective = diagonal @Surjective
-/
instance UniversallyInjective.isStableUnderBaseChange :
    IsStableUnderBaseChange @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance
/-
**AlgebraicGeometry.universallyInjective_isStableUnderComposition** 是 Mathlib 中的
一个实例，位于命名空间 `AlgebraicGeometry`。
形式化陈述：universallyInjective_isStableUnderComposition : IsStableUnderComposition @
UniversallyInjective
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.universally`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.Ha
sPullbacks C]   (P : CategoryTheory.MorphismProperty C) [h…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.universallyInjective_eq`：universallyInjective_eq : @Un
iversallyInjective = universally (topologically (Injective ·))
-/
instance universallyInjective_isStableUnderComposition :
    IsStableUnderComposition @UniversallyInjective :=
  universallyInjective_eq ▸ inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @UniversallyInjective where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.universallyInjective_isZariskiLocalAtTarget** 是 Mathlib 中的一个
实例，位于命名空间 `AlgebraicGeometry`。
形式化陈述：universallyInjective_isZariskiLocalAtTarget : IsZariskiLocalAtTarget @Univ
ersallyInjective
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.instIsZariskiLocalAtTargetDiagonalScheme`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme) [AlgebraicGeometry.IsZarisk
iLocalAtTarget P],   AlgebraicGeometry.IsZariski…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.universallyInjective_eq_diagonal`：universallyInjective
_eq_diagonal : @UniversallyInjective = diagonal @Surjective
-/
instance universallyInjective_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[stacks 01S4]
/-
**AlgebraicGeometry.tfae_universallyInjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：tfae_universallyInjective : List.TFAE [ UniversallyInjective f, forall (K 
: Type u) [Field K], Function.Injective (fun g : Spec (.of K) ⟶ X => g ≫ f), Fun
ction.Injective f ∧ forall x, (f.residueFieldMap x).hom.IsPurelyInseparable, Sur
jective (pullback.diagonal f) ]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.UniversallyInjective.iff_diagonal`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.UniversallyInjective f ↔ Algebr
aicGeometry.Surjective (CategoryTheory.Li…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AlgebraicGeometry.Scheme.SpecToEquivOfField_eq_iff`：SpecToEquivOfField_e
q_iff {K : Type*} [Field K] {X : Scheme} {f₁ f₂ : Σ x : X.carrier, X.residueFiel
d x ⟶ .of K} : f₁ = f₂ ↔ exists e : f₁.1…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `IsPurelyInseparable.injective_comp_algebraMap`：injective_comp_algebraMap
 [CommRing L] [IsReduced L] : Function.Injective fun f : E ->+* L => f.comp (alg
ebraMap F E)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `CommRingCat.hom_ext_iff`：∀ {R S : CommRingCat} {f g : R ⟶ S}, f = g ↔ Co
mmRingCat.Hom.hom f = CommRingCat.Hom.hom g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.residueFieldMap_congr'_assoc`：∀ {X Y : Alge
braicGeometry.Scheme} {f : X ⟶ Y} {x₁ x₂ : ↥X} (e : x₁ = x₂) {Z : CommRingCat} (
h : X.residueField x₂ ⟶ Z),   CategoryTheory.Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_comp`：descR
esidueField_stalkClosedPointTo_comp {K : Type u} [Field K] (g : Spec (.of K) ⟶ X
) : dsimp% descResidueField (stalkClosedPointTo (g ≫ f)…
· 使用定理 `AlgebraicGeometry.surjective_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f 
: X ⟶ Y), AlgebraicGeometry.Surjective f ↔ Function.Surjective ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
（共 60 条，此处仅展示前 30 条）
-/
theorem tfae_universallyInjective :
    List.TFAE [
      UniversallyInjective f,
      ∀ (K : Type u) [Field K], Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f),
      Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable,
      Surjective (pullback.diagonal f) ] := by
  tfae_have 1 ↔ 4 := UniversallyInjective.iff_diagonal f
  tfae_have 3 → 2 := by
    intro ⟨h_inj, hf⟩ K _ g₁ g₂ hg
    obtain ⟨e, h⟩ := Scheme.SpecToEquivOfField_eq_iff.mp congr((Y.SpecToEquivOfField K) $(hg))
    apply (X.SpecToEquivOfField K).injective
    dsimp at e h
    simp only [Scheme.descResidueField_stalkClosedPointTo_comp] at e h
    rw [← f.residueFieldMap_congr'_assoc (h_inj e), CommRingCat.hom_ext_iff] at h
    rw [Scheme.SpecToEquivOfField_eq_iff]
    let x := g₁ (IsLocalRing.closedPoint K)
    have hfx := hf x
    algebraize [(f.residueFieldMap (g₁ (IsLocalRing.closedPoint K))).hom]
    refine ⟨h_inj e, CommRingCat.hom_ext ?_⟩
    exact IsPurelyInseparable.injective_comp_algebraMap
      (Y.residueField (f x)) (X.residueField x) _ h
  tfae_have 2 → 4 := fun h ↦ by
    rw [surjective_iff]
    intro z
    let φ := (pullback f f).fromSpecResidueField z
    have hφ₁ : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f :=
      h ((pullback f f).residueField z) (by simp [pullback.condition])
    have hφ₂ : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f := by cat_disch
    refine ⟨(φ ≫ pullback.fst f f) (IsLocalRing.closedPoint _), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hφ₂, Scheme.fromSpecResidueField_apply]
  tfae_have 4 → 3 := fun hf ↦ by
    have := tfae_1_iff_4.mpr hf
    refine ⟨f.injective, ?_⟩
    rw [surjective_iff] at hf
    intro x
    algebraize [(f.residueFieldMap x).hom]
    rw [RingHom.IsPurelyInseparable, isPurelyInseparable_iff_subsingleton_emb, subsingleton_iff]
    intro σ₁ σ₂
    apply AlgHom.coe_ringHom_injective
    let g₁ := (X.SpecToEquivOfField _).symm ⟨_, CommRingCat.ofHom σ₁.toRingHom⟩
    let g₂ := (X.SpecToEquivOfField _).symm ⟨_, CommRingCat.ofHom σ₂.toRingHom⟩
    suffices X.SpecToEquivOfField _ g₁ = X.SpecToEquivOfField _ g₂ by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact congr($(this).2.hom)
    let q := pullback.lift (f := f) (g := f) g₁ g₂ <| by
      simp only [g₁, g₂, Scheme.SpecToEquivOfField_symm_apply, AlgHom.toRingHom_eq_coe,
        Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField x, ← Spec.map_comp_assoc]
      congr 2
      ext a
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      exact (AlgHom.commutes σ₁ a).trans (AlgHom.commutes σ₂ a).symm
    have q_fst : q ≫ pullback.fst f f = g₁ := pullback.lift_fst _ _ _
    have q_snd : q ≫ pullback.snd f f = g₂ := pullback.lift_snd _ _ _
    rw [Scheme.SpecToEquivOfField_eq_iff, ← q_fst, ← q_snd]
    obtain ⟨u, hu⟩ := hf (q (IsLocalRing.closedPoint _))
    have hux : u = x := by
      have := congr(pullback.fst f f $(hu))
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply] at this
      simpa [Scheme.SpecToEquivOfField_symm_apply, q_fst, g₁] using this
    refine ⟨by simp [g₁, g₂, q_fst, q_snd], ?_⟩
    dsimp
    simp only [Scheme.descResidueField_stalkClosedPointTo_comp, ← Category.assoc]
    congr 1
    rw [← cancel_mono (Scheme.residueFieldCongr (hux ▸ hu).symm).hom]
    have : Mono (Scheme.Hom.residueFieldMap (pullback.diagonal f) x) :=
      ConcreteCategory.mono_of_injective _ (RingHom.injective _)
    simp [← cancel_mono ((pullback.diagonal f).residueFieldMap x), ← Scheme.residueFieldMap_comp,
      (pullback.fst f f).residueFieldMap_congr', (pullback.snd f f).residueFieldMap_congr'_assoc,
      Scheme.Hom.residueFieldMap_congr (pullback.diagonal_snd f),
      Scheme.Hom.residueFieldMap_congr (pullback.diagonal_fst f)]
  tfae_finish

end AlgebraicGeometry

