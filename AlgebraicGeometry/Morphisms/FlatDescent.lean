/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Properties of morphisms satisfying fpqc descent

In this file we show some global properties satisfy fpqc descent.

- universally closed
  (`AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`)
- universally open
  (`AlgebraicGeometry.descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact`)
- universally injective
  (`AlgebraicGeometry.descendsAlong_universallyInjective_surjective_inf_flat_inf_quasicompact`)
- being an isomorphism
  (`AlgebraicGeometry.descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`)
- being an open immersion
  (`AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact`)
-/

public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- Surjective satisfies fpqc descent. -/
/-
**AlgebraicGeometry.Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasic
ompact** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Flat`。
形式化陈述：CategoryTheory.MorphismProperty.DescendsAlong (@AlgebraicGeometry.Surjecti
ve)   (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓ @AlgebraicGeome
try.QuasiCompact)
参数：@AlgebraicGeometry.Surjective；@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeome
try.Flat ⊓ @AlgebraicGeometry.QuasiCompact。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.DescendsAlong.of_le`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] {P Q W : CategoryTheory.MorphismProp
erty C}   [P.DescendsAlong Q], W ≤ Q → P.…
· 使用定理 `CategoryTheory.MorphismProperty.instDescendsAlongOfIsStableUnderBaseChan
geOfHasOfPrecompPropertyOfRespectsRight`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {P Q : CategoryTheory.MorphismProperty C}   [Q.IsStableU
nderBaseChange] [P.Ha…
· 使用定理 `AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme`：Category
Theory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Surjective
· 使用定理 `AlgebraicGeometry.instHasOfPrecompPropertySchemeSurjective`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme),   CategoryTheory.MorphismP
roperty.HasOfPrecompProperty (@AlgebraicGeometry…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsOfIsStableUnderComposition`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Mor
phismProperty C)   [W.IsStableUnderComposition], W.Respects …
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.instIsMultiplicativeSchemeSurjective`：CategoryTheory.M
orphismProperty.IsMultiplicative @AlgebraicGeometry.Surjective
· 使用定理 `le_of_inf_eq'`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b
 = b → b ≤ a

--- 原说明 ---
Surjective satisfies fpqc descent.
-/
instance Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @Surjective (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  .of_le (Q := @Surjective) (le_of_inf_eq' (by grind))

set_option backward.isDefEq.respectTransparency.types false in
/-- Universally closed satisfies fpqc descent. -/
@[stacks 02KS]
/-
**AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quas
icompact** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
形式化陈述：descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact : Des
cendsAlong @UniversallyClosed (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact`
：∀ (P P' : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P'.IsStabl
eUnderBaseChange]   [P'.IsStableUnderComposition] [P.IsStable…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.inf`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismProp
erty C}   [P.IsStableUnderBaseChange] [Q.IsStable…
· 使用定理 `AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme`：Category
Theory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Surjective
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.inf`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismPro
perty C}   [P.IsStableUnderComposition] [Q.IsStabl…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.instIsMultiplicativeSchemeSurjective`：CategoryTheory.M
orphismProperty.IsMultiplicative @AlgebraicGeometry.Surjective
· 使用定理 `AlgebraicGeometry.Flat.instIsStableUnderCompositionScheme`：CategoryTheor
y.MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Flat
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.IsLocalIso.le_of_isZariskiLocalAtSource`：le_of_isZaris
kiLocalAtSource (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities] [IsZari
skiLocalAtSource P] : @IsLocalIso <= P
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `AlgebraicGeometry.Flat.instIsMultiplicativeScheme`：CategoryTheory.Morphi
smProperty.IsMultiplicative @AlgebraicGeometry.Flat
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `CategoryTheory.MorphismProperty.universally_mk'`：universally_mk' (P : Mo
rphismProperty C) [P.RespectsIso] {X Y : C} (g : X ⟶ Y) (H : forall {T : C} (f :
 T ⟶ Y) [HasPullback f g], P (pullbac…
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeTopologicallyIsClosedMap`：(Algebr
aicGeometry.topologically fun {α β} [TopologicalSpace α] [TopologicalSpace β] =>
 IsClosedMap).RespectsIso
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback`：∀ {P X Y Z : A
lgebraicGeometry.Scheme} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z},   
CategoryTheory.IsPullback fst snd f g → ∀ (s :…
· 使用引理 `CategoryTheory.Limits.isPullback_map_snd_snd`：isPullback_map_snd_snd {X 
Y Z S : C} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) : IsPullback (pullback.map _ _ _ 
_ (pullback.snd f g) (pullback.snd…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isClosedMap`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f], IsClosedMap ⇑f
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `Topology.IsCoinducing.isClosed_preimage`：∀ {X : Type u_1} {Y : Type u_2}
 {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolo
gy.IsCoinducing f → ∀ {s : Se…
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Universally closed satisfies fpqc descent.
-/
instance descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallyClosed (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  refine fun {R} S Y φ g ⟨_, _⟩ hfst ↦ ⟨universally_mk' _ _ fun {T} f _ s hs ↦ ?_⟩
  let p := pullback.fst (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g)
  let r : pullback (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g) ⟶ pullback f g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) (Spec.map φ) (pullback.condition ..)
      (pullback.condition ..)
  have : IsClosed ((pullback.snd (Spec.map φ) f).base ⁻¹' ((pullback.fst f g).base '' s)) := by
    rw [← Scheme.image_preimage_eq_of_isPullback (isPullback_map_snd_snd ..)]
    exact p.isClosedMap _ (hs.preimage r.continuous)
  rwa [(Flat.isQuotientMap_of_surjective _).isClosed_preimage] at this

set_option backward.isDefEq.respectTransparency.types false in
/-- Universally open satisfies fpqc descent. -/
@[stacks 02KT]
/-
**AlgebraicGeometry.descendsAlong_universallyOpen_surjective_inf_flat_inf_quasic
ompact** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
形式化陈述：descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact : Desce
ndsAlong @UniversallyOpen (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact`
：∀ (P P' : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P'.IsStabl
eUnderBaseChange]   [P'.IsStableUnderComposition] [P.IsStable…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.inf`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismProp
erty C}   [P.IsStableUnderBaseChange] [Q.IsStable…
· 使用定理 `AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme`：Category
Theory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Surjective
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.inf`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismPro
perty C}   [P.IsStableUnderComposition] [Q.IsStabl…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.instIsMultiplicativeSchemeSurjective`：CategoryTheory.M
orphismProperty.IsMultiplicative @AlgebraicGeometry.Surjective
· 使用定理 `AlgebraicGeometry.Flat.instIsStableUnderCompositionScheme`：CategoryTheor
y.MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Flat
· 使用定理 `AlgebraicGeometry.UniversallyOpen.instIsStableUnderBaseChangeScheme`：Cat
egoryTheory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Universa
llyOpen
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.IsLocalIso.le_of_isZariskiLocalAtSource`：le_of_isZaris
kiLocalAtSource (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities] [IsZari
skiLocalAtSource P] : @IsLocalIso <= P
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `AlgebraicGeometry.Flat.instIsMultiplicativeScheme`：CategoryTheory.Morphi
smProperty.IsMultiplicative @AlgebraicGeometry.Flat
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
· 使用定理 `AlgebraicGeometry.UniversallyOpen.instIsZariskiLocalAtTarget`：AlgebraicG
eometry.IsZariskiLocalAtTarget @AlgebraicGeometry.UniversallyOpen
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `CategoryTheory.MorphismProperty.universally_mk'`：universally_mk' (P : Mo
rphismProperty C) [P.RespectsIso] {X Y : C} (g : X ⟶ Y) (H : forall {T : C} (f :
 T ⟶ Y) [HasPullback f g], P (pullbac…
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeTopologicallyIsOpenMap`：(Algebrai
cGeometry.topologically fun {α β} [TopologicalSpace α] [TopologicalSpace β] => I
sOpenMap).RespectsIso
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback`：∀ {P X Y Z : A
lgebraicGeometry.Scheme} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z},   
CategoryTheory.IsPullback fst snd f g → ∀ (s :…
· 使用引理 `CategoryTheory.Limits.isPullback_map_snd_snd`：isPullback_map_snd_snd {X 
Y Z S : C} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) : IsPullback (pullback.map _ _ _ 
_ (pullback.snd f g) (pullback.snd…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenMap`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyOpen f], IsOpenMap ⇑f
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Universally open satisfies fpqc descent.
-/
instance descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallyOpen
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  refine fun {R} S Y φ g ⟨_, _⟩ hfst ↦ ⟨universally_mk' _ _ fun {T} f _ s hs ↦ ?_⟩
  let p := pullback.fst (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g)
  let r : pullback (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g) ⟶ pullback f g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) (Spec.map φ) (pullback.condition ..)
      (pullback.condition ..)
  have : IsOpen ((pullback.snd (Spec.map φ) f).base ⁻¹' ((pullback.fst f g).base '' s)) := by
    rw [← Scheme.image_preimage_eq_of_isPullback (isPullback_map_snd_snd ..)]
    exact p.isOpenMap _ (hs.preimage r.continuous)
  rwa [(Flat.isQuotientMap_of_surjective _).isOpen_preimage] at this

set_option backward.isDefEq.respectTransparency.types false in
/-- Universally injective satisfies fpqc descent. -/
@[stacks 02KW]
/-
**AlgebraicGeometry.descendsAlong_universallyInjective_surjective_inf_flat_inf_q
uasicompact** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
形式化陈述：descendsAlong_universallyInjective_surjective_inf_flat_inf_quasicompact : 
DescendsAlong @UniversallyInjective (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.universallyInjective_eq_diagonal`：universallyInjective
_eq_diagonal : @UniversallyInjective = diagonal @Surjective
· 使用定理 `CategoryTheory.MorphismProperty.instDescendsAlongDiagonalOfRespectsIsoOf
IsStableUnderBaseChange`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, 
u_1} C] [inst_1 : CategoryTheory.Limits.HasPullbacks C]   (P Q : CategoryTheory.
Morph…
· 使用定理 `AlgebraicGeometry.Flat.surjective_descendsAlong_surjective_inf_flat_inf_
quasicompact`：CategoryTheory.MorphismProperty.DescendsAlong (@AlgebraicGeometry.
Surjective)   (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓ @…
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeSurjective`：CategoryTheory.Morphi
smProperty.RespectsIso @AlgebraicGeometry.Surjective
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.inf`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismProp
erty C}   [P.IsStableUnderBaseChange] [Q.IsStable…
· 使用定理 `AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme`：Category
Theory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Surjective

--- 原说明 ---
Universally injective satisfies fpqc descent.
-/
instance descendsAlong_universallyInjective_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallyInjective (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [universallyInjective_eq_diagonal]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- Being an isomorphism satisfies fpqc descent. -/
@[stacks 02L4]
/-
**AlgebraicGeometry.descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicomp
act** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
形式化陈述：descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact : (isomorp
hisms Scheme.{u}).DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact`
：∀ (P P' : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P'.IsStabl
eUnderBaseChange]   [P'.IsStableUnderComposition] [P.IsStable…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.inf`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismProp
erty C}   [P.IsStableUnderBaseChange] [Q.IsStable…
· 使用定理 `AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme`：Category
Theory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Surjective
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.inf`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismPro
perty C}   [P.IsStableUnderComposition] [Q.IsStabl…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.instIsMultiplicativeSchemeSurjective`：CategoryTheory.M
orphismProperty.IsMultiplicative @AlgebraicGeometry.Surjective
· 使用定理 `AlgebraicGeometry.Flat.instIsStableUnderCompositionScheme`：CategoryTheor
y.MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Flat
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.isomorphisms`：∀ 
(C : Type u) [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheory.Morphi
smProperty.isomorphisms C).IsStableUnderBaseChange
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.IsLocalIso.le_of_isZariskiLocalAtSource`：le_of_isZaris
kiLocalAtSource (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities] [IsZari
skiLocalAtSource P] : @IsLocalIso <= P
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `AlgebraicGeometry.Flat.instIsMultiplicativeScheme`：CategoryTheory.Morphi
smProperty.IsMultiplicative @AlgebraicGeometry.Flat
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
· 使用定理 `AlgebraicGeometry.Scheme.instIsLocalAtTargetIsomorphismsZariskiPrecovera
ge`：(CategoryTheory.MorphismProperty.isomorphisms AlgebraicGeometry.Scheme).IsLo
calAtTarget   AlgebraicGeometry.Scheme.zariskiPrecoverage
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `CategoryTheory.MorphismProperty.of_pullback_fst_of_descendsAlong`：of_pul
lback_fst_of_descendsAlong [P.DescendsAlong Q] [HasPullback f g] (hf : Q f) (hfs
t : P (pullback.fst f g)) : P g
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffineHom f], AlgebraicGeometry.Qua
siCompact f
· 使用定理 `AlgebraicGeometry.isAffineHom_of_isAffine`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y],
   AlgebraicGeometry.IsAffineHo…
· 使用定理 `AlgebraicGeometry.instUniversallyInjectiveOfMonoScheme`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.Mono f], AlgebraicGeometry.Univer
sallyInjective f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `AlgebraicGeometry.Flat.surjective_descendsAlong_surjective_inf_flat_inf_
quasicompact`：CategoryTheory.MorphismProperty.DescendsAlong (@AlgebraicGeometry.
Surjective)   (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓ @…
· 使用定理 `AlgebraicGeometry.instSurjectiveOfIsIsoScheme`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.Surjective f
· 使用定理 `AlgebraicGeometry.UniversallyOpen.instOfIsOpenImmersion`：∀ {X Y : Algebr
aicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f],   Algebra
icGeometry.UniversallyOpen f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenMap`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyOpen f], IsOpenMap ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.injective`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyInjective f], Function.Injective ⇑f
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
Being an isomorphism satisfies fpqc descent.
-/
instance descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact :
    (isomorphisms Scheme.{u}).DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g h (hfst : IsIso _)
  have : IsAffine Y :=
    have : UniversallyInjective g :=
      of_pullback_fst_of_descendsAlong (P := @UniversallyInjective) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have : Surjective g :=
      of_pullback_fst_of_descendsAlong (P := @Surjective) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have hopen' : UniversallyOpen g :=
      of_pullback_fst_of_descendsAlong (P := @UniversallyOpen) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have : IsHomeomorph g.base := ⟨g.continuous, g.isOpenMap, g.injective, g.surjective⟩
    have : IsAffineHom g :=
      isAffineHom_of_isInducing g this.isInducing this.isClosedEmbedding.isClosed_range
    isAffine_of_isAffineHom g
  wlog hY : ∃ T, Y = Spec T generalizing Y
  · rw [← (isomorphisms Scheme).cancel_left_of_respectsIso Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
      pullback.map _ _ _ _ (𝟙 _) (Y.isoSpec.inv) (𝟙 _) (by simp) (by simp) ≫
        pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    change isomorphisms Scheme _
    rwa [heq, (isomorphisms Scheme).cancel_left_of_respectsIso]
  obtain ⟨T, rfl⟩ := hY
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  refine of_pullback_fst_Spec_of_codescendsAlong (P := isomorphisms Scheme.{u})
      (Q' := RingHom.FaithfullyFlat) (Q := fun f ↦ Function.Bijective f) (P' := @Surjective ⊓ @Flat)
      RingHom.FaithfullyFlat.codescendsAlong_bijective ?_ ?_ h hfst
  · intro _ _ f hf
    rwa [← flat_and_surjective_SpecMap_iff, and_comm]
  · simp_rw [← isIso_SpecMap_iff, implies_true]

set_option backward.isDefEq.respectTransparency.types false in
/-- Being an open immersion satisfies fpqc descent. -/
@[stacks 02L3]
/-
**AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasic
ompact'** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
形式化陈述：descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact' : IsOp
enImmersion.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.DescendsAlong.mk'`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {P Q : CategoryTheory.MorphismProperty
 C}   [P.RespectsIso],   (∀ {X Y Z : C}…
· 使用引理 `CategoryTheory.MorphismProperty.of_pullback_fst_of_descendsAlong`：of_pul
lback_fst_of_descendsAlong [P.DescendsAlong Q] [HasPullback f g] (hf : Q f) (hfs
t : P (pullback.fst f g)) : P g
· 使用定理 `AlgebraicGeometry.UniversallyOpen.instOfIsOpenImmersion`：∀ {X Y : Algebr
aicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f],   Algebra
icGeometry.UniversallyOpen f
· 使用定理 `IsOpenMap.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → IsOpen (S
et.range f)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenMap`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyOpen f], IsOpenMap ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Opens.range_ι`：range_ι : Set.range U.ι = U
· 使用定理 `AlgebraicGeometry.Scheme.Hom.injective`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyInjective f], Function.Injective ⇑f
· 使用定理 `AlgebraicGeometry.instUniversallyInjectiveOfMonoScheme`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.Mono f], AlgebraicGeometry.Univer
sallyInjective f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.lift_fac`：lift_fac (H' : Set.range g s
ubseteq Set.range f) : lift f g H' ≫ f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective`：isIso_iff_is
OpenImmersion_and_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso f ↔ IsOpenIm
mersion f ∧ Surjective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullbackLeftPullbackSndIso_hom_fst`：pullbackLeftPu
llbackSndIso_hom_fst : (pullbackLeftPullbackSndIso f g g').hom ≫ pullback.fst _ 
_ = pullback.fst _ _ ≫ pullback.fst _ _
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.of_comp`：of_comp {X Y Z : Scheme.{u}} 
(f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g] [IsOpenImmersion (f ≫ g)] : IsOpenIm
mersion f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Surjective.instFstScheme`：∀ {X Y Z : AlgebraicGeometry
.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.Surjective g],   AlgebraicGe
ometry.Surjective (CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.inf`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismProp
erty C}   [P.IsStableUnderBaseChange] [Q.IsStable…
· 使用定理 `AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme`：Category
Theory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Surjective

--- 原说明 ---
Being an open immersion satisfies fpqc descent.
-/
instance descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact' :
    IsOpenImmersion.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply DescendsAlong.mk'
  intro X Y Z f g _ hf hg
  have : UniversallyOpen g :=
    MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @UniversallyOpen) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f)
      hf inferInstance
  let U : Z.Opens := ⟨Set.range g.base, g.isOpenMap.isOpen_range⟩
  let f' := pullback.snd f U.ι
  let g' : Y ⟶ U := IsOpenImmersion.lift U.ι g (by simp [U])
  have : Surjective g' := ⟨fun ⟨x, ⟨y, hy⟩⟩ ↦
    ⟨y, by apply U.ι.injective; simp [← Scheme.Hom.comp_apply, g', hy]⟩⟩
  have : IsIso (pullback.fst f' g') := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨?_, inferInstance⟩
    have : IsOpenImmersion (pullback.fst f (g' ≫ U.ι)) := by
      rwa [AlgebraicGeometry.IsOpenImmersion.lift_fac]
    have : IsOpenImmersion (pullback.fst f' g' ≫ pullback.fst f U.ι) := by
      rw [← pullbackLeftPullbackSndIso_hom_fst]
      infer_instance
    exact .of_comp _ (pullback.fst _ _)
  have : IsIso g' := by
    apply MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := isomorphisms Scheme) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f') ?_ this
    exact MorphismProperty.pullback_snd _ _ hf
  rw [← IsOpenImmersion.lift_fac U.ι g (by simp [U])]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.HasRingHomProperty.descendsAlong_flat** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} [P.IsStab
leUnderBaseChange]   {Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommR
ing S] → (R →+* S) → Prop}   [AlgebraicGeometry.HasRingHomProperty P fun {R S} [
CommRing R] [CommRing S] => Q],   (RingHom.CodescendsAlong (fun {R S} [CommRing 
R] [CommRing S] => Q) fun {R S} [CommRing R] [CommRing S] =>       RingHom.Faith
fullyFlat) →     P.DescendsAlong (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeom
etry.Flat ⊓ @AlgebraicGeometry.QuasiCompact)
参数：R →+* S；RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => Q) fu
n {R S} [CommRing R] [CommRing S] =>       RingHom.FaithfullyFlat；@AlgebraicGeom
etry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓ @AlgebraicGeometry.QuasiCompact。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.descendsAlong`：∀ (P P' : CategoryTh
eory.MorphismProperty AlgebraicGeometry.Scheme)   (Q Q' : {R S : Type u} → [inst
 : CommRing R] → [inst_1 : CommRing S] →…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.inf`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismProp
erty C}   [P.IsStableUnderBaseChange] [Q.IsStable…
· 使用定理 `AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme`：Category
Theory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Surjective
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.inf`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismPro
perty C}   [P.IsStableUnderComposition] [Q.IsStabl…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.instIsMultiplicativeSchemeSurjective`：CategoryTheory.M
orphismProperty.IsMultiplicative @AlgebraicGeometry.Surjective
· 使用定理 `AlgebraicGeometry.Flat.instIsStableUnderCompositionScheme`：CategoryTheor
y.MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Flat
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `AlgebraicGeometry.IsLocalIso.le_of_isZariskiLocalAtSource`：le_of_isZaris
kiLocalAtSource (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities] [IsZari
skiLocalAtSource P] : @IsLocalIso <= P
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `AlgebraicGeometry.Flat.instIsMultiplicativeScheme`：CategoryTheory.Morphi
smProperty.IsMultiplicative @AlgebraicGeometry.Flat
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
· 使用引理 `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`：iff_flat_and_comap
_surjective : f.FaithfullyFlat ↔ f.Flat ∧ Function.Surjective (PrimeSpectrum.com
ap f)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.Scheme.Hom.surjective`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
-/
lemma HasRingHomProperty.descendsAlong_flat {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P Q] (h : RingHom.CodescendsAlong Q RingHom.FaithfullyFlat) :
    P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine HasRingHomProperty.descendsAlong _ _ _ _ ?_ ?_ h
  · rw [inf_comm]
    gcongr
    exact IsLocalIso.le_of_isZariskiLocalAtSource @Flat
  · intro R S f ⟨hf₁, hf₂⟩
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨?_, (Spec.map f).surjective⟩
    rwa [HasRingHomProperty.Spec_iff (P := @Flat)] at hf₂

set_option backward.isDefEq.respectTransparency.types false in
/-- fpqc descent implies fppf descent -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
fpqc descent implies fppf descent
-/
instance (P : MorphismProperty Scheme) [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsZariskiLocalAtTarget P] :
    P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  apply IsZariskiLocalAtTarget.descendsAlong
  rintro R X Y f g ⟨⟨h₁, h₂⟩, h₃⟩ H
  obtain ⟨V : X.Opens, hV, e⟩ := f.isOpenMap.exists_opens_image_eq_of_prespectralSpace
    f.continuous (by simp) isOpen_univ isCompact_univ
  refine MorphismProperty.of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (.paste_vert (.of_hasPullback V.ι _) (.of_hasPullback f g)) ⟨⟨?_, inferInstance⟩,
      (quasiCompact_iff_compactSpace _).mpr (isCompact_iff_compactSpace.mp hV)⟩ ?_
  · exact ⟨fun x ↦ have ⟨y, hyV, e⟩ := e.ge (Set.mem_univ x); ⟨⟨y, hyV⟩, e⟩⟩
  · exact IsZariskiLocalAtTarget.of_isPullback (.flip <| .of_hasPullback _ _) H

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Scheme} (f : X ⟶ Y) [Surjective f] [Flat f] [QuasiCompact f] :
    (Over.pullback f).Faithful :=
  MorphismProperty.faithful_overPullback_of_isomorphisms_descendAlong
    (P := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Scheme} (f : X ⟶ Y) [Surjective f] [Flat f] [LocallyOfFinitePresentation f] :
    (Over.pullback f).Faithful :=
  MorphismProperty.faithful_overPullback_of_isomorphisms_descendAlong
    (P := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

end AlgebraicGeometry

