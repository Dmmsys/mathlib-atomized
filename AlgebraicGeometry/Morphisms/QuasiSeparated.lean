/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Topology.Sheaves.CommRingCat

/-!
# Quasi-separated morphisms

A morphism of schemes `f : X ⟶ Y` is quasi-separated if the diagonal morphism `X ⟶ X ×[Y] X` is
quasi-compact.

A scheme is quasi-separated if the intersections of any two affine open sets is quasi-compact.
(`AlgebraicGeometry.quasiSeparatedSpace_iff_affine`)

We show that a morphism is quasi-separated if the preimage of every affine open is quasi-separated.

We also show that this property is local at the target,
and is stable under compositions and base-changes.

## Main result
- `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs` (**Qcqs lemma**):
  If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is `QuasiSeparated` if diagonal map is quasi-compact. -/
@[mk_iff]
/-
**AlgebraicGeometry.QuasiSeparated** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeometry`。
形式化陈述：QuasiSeparated (f : X ⟶ Y) : Prop where /-- A morphism is `QuasiSeparated`
 if diagonal map is quasi-compact. -/ quasiCompact_diagonal : QuasiCompact (pull
back.diagonal f)
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism is `QuasiSeparated` if diagonal map is quasi-compact.
-/
class QuasiSeparated (f : X ⟶ Y) : Prop where
  /-- A morphism is `QuasiSeparated` if diagonal map is quasi-compact. -/
  quasiCompact_diagonal : QuasiCompact (pullback.diagonal f) := by infer_instance

attribute [instance] QuasiSeparated.quasiCompact_diagonal
/-
**AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：quasiSeparatedSpace_iff_forall_affineOpens {X : Scheme} : QuasiSeparatedSp
ace X ↔ forall U V : X.affineOpens, IsCompact (U inter V : Set X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `quasiSeparatedSpace_iff`：∀ (α : Type u_3) [inst : TopologicalSpace α],  
 QuasiSeparatedSpace α ↔ ∀ (U V : Set α), IsOpen U → IsCompact U → IsOpen V → Is
Compact V → I…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompact`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsCompact ↑U
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.compact_open_induction_on`：compact_open_induction_on {
P : X.Opens -> Prop} (S : X.Opens) (hS : IsCompact (S : Set X)) (h₁ : P ⊥) (h₂ :
 forall (S : X.Opens) (_ : IsComp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
-/
theorem quasiSeparatedSpace_iff_forall_affineOpens {X : Scheme} :
    QuasiSeparatedSpace X ↔ ∀ U V : X.affineOpens, IsCompact (U ∩ V : Set X) := by
  rw [quasiSeparatedSpace_iff]
  constructor
  · intro H U V; exact H U V U.1.2 U.2.isCompact V.1.2 V.2.isCompact
  · intro H
    suffices
      ∀ (U : X.Opens) (_ : IsCompact U.1) (V : X.Opens) (_ : IsCompact V.1),
        IsCompact (U ⊓ V).1
      by intro U V hU hU' hV hV'; exact this ⟨U, hU⟩ hU' ⟨V, hV⟩ hV'
    intro U hU V hV
    refine compact_open_induction_on V hV ?_ ?_
    · simp
    · intro S _ V hV
      change IsCompact (U.1 ∩ (S.1 ∪ V.1))
      rw [Set.inter_union_distrib_left]
      apply hV.union
      clear hV
      refine compact_open_induction_on U hU ?_ ?_
      · simp
      · intro S _ W hW
        change IsCompact ((S.1 ∪ W.1) ∩ V.1)
        rw [Set.union_inter_distrib_right]
        apply hW.union
        apply H
/-
**AlgebraicGeometry.quasiCompact_affineProperty_iff_quasiSeparatedSpace** 是 Math
lib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：quasiCompact_affineProperty_iff_quasiSeparatedSpace [IsAffine Y] (f : X ⟶ 
Y) : AffineTargetMorphismProperty.diagonal (fun X _ _ _ => CompactSpace X) f ↔ Q
uasiSeparatedSpace X
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens`：quasiSepar
atedSpace_iff_forall_affineOpens {X : Scheme} : QuasiSeparatedSpace X ↔ forall U
 V : X.affineOpens, IsCompact (U inter V : Set X)
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `Homeomorph.compactSpace`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] (h : X ≃ₜ Y),   Comp
actSpace Y
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用引理 `AlgebraicGeometry.Scheme.Opens.range_ι`：range_ι : Set.range U.ι = U
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_left`：range_
pullback_to_base_of_left : Set.range (pullback.fst f g ≫ f) = Set.range f inter 
Set.range g
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem quasiCompact_affineProperty_iff_quasiSeparatedSpace [IsAffine Y] (f : X ⟶ Y) :
    AffineTargetMorphismProperty.diagonal (fun X _ _ _ ↦ CompactSpace X) f ↔
      QuasiSeparatedSpace X := by
  delta AffineTargetMorphismProperty.diagonal
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  constructor
  · intro H U V
    let g : pullback U.1.ι V.1.ι ⟶ X := pullback.fst _ _ ≫ U.1.ι
    have e := g.isOpenEmbedding.isEmbedding.toHomeomorph
    rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      at e
    rw [isCompact_iff_compactSpace]
    exact @Homeomorph.compactSpace _ _ _ _ (H _ _) e
  · introv H h₁ h₂
    let g : pullback f₁ f₂ ⟶ X := pullback.fst _ _ ≫ f₁
    have e := g.isOpenEmbedding.isEmbedding.toHomeomorph
    rw [IsOpenImmersion.range_pullback_to_base_of_left] at e
    simp_rw [isCompact_iff_compactSpace] at H
    exact @Homeomorph.compactSpace _ _ _ _
        (H ⟨_, isAffineOpen_opensRange f₁⟩ ⟨_, isAffineOpen_opensRange f₂⟩) e.symm
/-
**AlgebraicGeometry.quasiSeparated_eq_diagonal_is_quasiCompact** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：quasiSeparated_eq_diagonal_is_quasiCompact : @QuasiSeparated = MorphismPro
perty.diagonal @QuasiCompact
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.quasiSeparated_iff`：∀ {X Y : AlgebraicGeometry.Scheme}
 (f : X ⟶ Y),   AlgebraicGeometry.QuasiSeparated f ↔     autoParam (AlgebraicGeo
metry.QuasiCompact (Catego…
-/
theorem quasiSeparated_eq_diagonal_is_quasiCompact :
    @QuasiSeparated = MorphismProperty.diagonal @QuasiCompact := by ext; exact quasiSeparated_iff _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasAffineProperty @QuasiSeparated (fun X _ _ _ ↦ QuasiSeparatedSpace X) where
  __ := HasAffineProperty.copy
    quasiSeparated_eq_diagonal_is_quasiCompact.symm
    (by ext; exact quasiCompact_affineProperty_iff_quasiSeparatedSpace _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) (f : X ⟶ Y) [Mono f] :
    QuasiSeparated f where

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.quasiSeparated_isStableUnderComposition** 是 Mathlib 中的一个实例，位
于命名空间 `AlgebraicGeometry`。
形式化陈述：quasiSeparated_isStableUnderComposition : MorphismProperty.IsStableUnderCo
mposition @QuasiSeparated
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCa
rrierCommRingCat`：AlgebraicGeometry.HasAffineProperty @AlgebraicGeometry.QuasiCo
mpact fun X x x_1 x_2 => CompactSpace ↥X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.quasiSeparated_eq_diagonal_is_quasiCompact`：quasiSepar
ated_eq_diagonal_is_quasiCompact : @QuasiSeparated = MorphismProperty.diagonal @
QuasiCompact
-/
instance quasiSeparated_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @QuasiSeparated :=
  quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸ inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @QuasiSeparated where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange** 是 Mathlib 中的一个实例，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：quasiSeparated_isStableUnderBaseChange : MorphismProperty.IsStableUnderBas
eChange @QuasiSeparated
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.diagonal`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limi
ts.HasPullbacks C]   {P : CategoryTheory.MorphismPrope…
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCa
rrierCommRingCat`：AlgebraicGeometry.HasAffineProperty @AlgebraicGeometry.QuasiCo
mpact fun X x x_1 x_2 => CompactSpace ↥X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.quasiSeparated_eq_diagonal_is_quasiCompact`：quasiSepar
ated_eq_diagonal_is_quasiCompact : @QuasiSeparated = MorphismProperty.diagonal @
QuasiCompact
-/
instance quasiSeparated_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @QuasiSeparated :=
  quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸ inferInstance
/-
**AlgebraicGeometry.quasiSeparated_comp** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：quasiSeparated_comp (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSepar
ated g] : QuasiSeparated (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
-/
instance quasiSeparated_comp (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f]
    [QuasiSeparated g] : QuasiSeparated (f ≫ g) :=
  MorphismProperty.comp_mem _ f g inferInstance inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：quasiSeparatedSpace_iff_quasiSeparated (X : Scheme) : QuasiSeparatedSpace 
X ↔ QuasiSeparated (terminal.from X)
参数：X : Scheme。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpace
CarrierCarrierCommRingCat`：AlgebraicGeometry.HasAffineProperty @AlgebraicGeometr
y.QuasiSeparated fun X x x_1 x_2 => QuasiSeparatedSpace ↥X
· 使用定理 `AlgebraicGeometry.instIsAffineTerminalScheme`：AlgebraicGeometry.IsAffine
 (⊤_ AlgebraicGeometry.Scheme)
-/
theorem quasiSeparatedSpace_iff_quasiSeparated (X : Scheme) :
    QuasiSeparatedSpace X ↔ QuasiSeparated (terminal.from X) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [QuasiSeparated g] :
    QuasiSeparated (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [QuasiSeparated f] :
    QuasiSeparated (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [QuasiSeparated f] : QuasiSeparated (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [QuasiSeparated f] :
    QuasiSeparated (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance
/-
**AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry`。
形式化陈述：quasiSeparatedSpace_of_quasiSeparated (f : X ⟶ Y) [hY : QuasiSeparatedSpac
e Y] [QuasiSeparated f] : QuasiSeparatedSpace X
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated`：quasiSeparated
Space_iff_quasiSeparated (X : Scheme) : QuasiSeparatedSpace X ↔ QuasiSeparated (
terminal.from X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
-/
theorem quasiSeparatedSpace_of_quasiSeparated (f : X ⟶ Y)
    [hY : QuasiSeparatedSpace Y] [QuasiSeparated f] : QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_quasiSeparated] at hY ⊢
  rw [← terminalIsTerminal.hom_ext (f ≫ terminal.from Y) (terminal.from X)]
  infer_instance
/-
**AlgebraicGeometry.Scheme.Hom.isQuasiSeparated_preimage** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiSep
arated f] {U : Y.Opens},   IsQuasiSeparated ↑U → IsQuasiSeparated ↑((Topological
Space.Opens.map f.base).obj U)
参数：f : X ⟶ Y；(TopologicalSpace.Opens.map f.base).obj U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isQuasiSeparated_iff_quasiSeparatedSpace`：isQuasiSeparated_iff_quasiSepa
ratedSpace (s : Set α) (hs : IsOpen s) : IsQuasiSeparated s ↔ QuasiSeparatedSpac
e s
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated`：quasiSeparatedS
pace_of_quasiSeparated (f : X ⟶ Y) [hY : QuasiSeparatedSpace Y] [QuasiSeparated 
f] : QuasiSeparatedSpace X
· 使用定理 `AlgebraicGeometry.instQuasiSeparatedMorphismRestrict`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) (V : Y.Opens) [AlgebraicGeometry.QuasiSeparated f],
   AlgebraicGeometry.QuasiSeparated (f ∣_ …
-/
lemma Scheme.Hom.isQuasiSeparated_preimage [QuasiSeparated f] {U : Opens Y}
    (hU : IsQuasiSeparated (U : Set Y)) : IsQuasiSeparated (f ⁻¹ᵁ U : Set X) := by
  have : QuasiSeparatedSpace U := (isQuasiSeparated_iff_quasiSeparatedSpace _ U.2).mp hU
  exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ U).2).mpr
    (quasiSeparatedSpace_of_quasiSeparated (f ∣_ U))
/-
**AlgebraicGeometry.quasiSeparatedSpace_of_isAffine** 是 Mathlib 中的一个实例，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：quasiSeparatedSpace_of_isAffine (X : Scheme) [IsAffine X] : QuasiSeparated
Space X
参数：X : Scheme。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `quasiSeparatedSpace_congr`：quasiSeparatedSpace_congr (e : α ≃ₜ β) : Quas
iSeparatedSpace α ↔ QuasiSeparatedSpace β where mp _
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `PrimeSpectrum.instQuasiSeparatedSpace`：∀ {R : Type u} [inst : CommSemiri
ng R], QuasiSeparatedSpace (PrimeSpectrum R)
-/
instance quasiSeparatedSpace_of_isAffine (X : Scheme) [IsAffine X] : QuasiSeparatedSpace X :=
  (quasiSeparatedSpace_congr X.isoSpec.hom.homeomorph).2 PrimeSpectrum.instQuasiSeparatedSpace
/-
**AlgebraicGeometry.IsAffineOpen.isQuasiSeparated** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens}, AlgebraicGeometry.IsAffine
Open U → IsQuasiSeparated ↑U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isQuasiSeparated_iff_quasiSeparatedSpace`：isQuasiSeparated_iff_quasiSepa
ratedSpace (s : Set α) (hs : IsOpen s) : IsQuasiSeparated s ↔ QuasiSeparatedSpac
e s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
-/
theorem IsAffineOpen.isQuasiSeparated {U : X.Opens} (hU : IsAffineOpen U) :
    IsQuasiSeparated (U : Set X) := by
  rw [isQuasiSeparated_iff_quasiSeparatedSpace]
  exacts [@AlgebraicGeometry.quasiSeparatedSpace_of_isAffine _ hU, U.isOpen]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [QuasiSeparatedSpace X] : QuasiSeparated X.toSpecΓ :=
  HasAffineProperty.iff_of_isAffine.mpr ‹_›

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {I : Type u_1} (U : I → X.Opens),   Topol
ogicalSpace.IsOpenCover U →     (∀ (i : I), AlgebraicGeometry.IsAffineOpen (U i)
) →       (∀ (i j : I), IsCompact (↑(U i) ∩ ↑(U j))) → QuasiSeparatedSpace ↥X
参数：U : I → X.Opens；∀ (i : I), AlgebraicGeometry.IsAffineOpen (U i)；∀ (i j : I), 
IsCompact (↑(U i) ∩ ↑(U j))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCa
rrierCommRingCat`：AlgebraicGeometry.HasAffineProperty @AlgebraicGeometry.QuasiCo
mpact fun X x x_1 x_2 => CompactSpace ↥X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.quasiCompact_affineProperty_iff_quasiSeparatedSpace`：q
uasiCompact_affineProperty_iff_quasiSeparatedSpace [IsAffine Y] (f : X ⟶ Y) : Af
fineTargetMorphismProperty.diagonal (fun X _ _ _ => Compact…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.diagonal_of_openCover_sou
rce`：∀ {Q : AlgebraicGeometry.AffineTargetMorphismProperty} [Q.IsLocal] {X Y : A
lgebraicGeometry.Scheme} (f : X ⟶ Y)   (𝒰 : X.OpenCover) [inst : …
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `isCompact_univ_iff`：isCompact_univ_iff : IsCompact (univ : Set X) ↔ Comp
actSpace X
· 使用定理 `Topology.IsEmbedding.isCompact_iff`：Topology.IsEmbedding.isCompact_iff {
f : X -> Y} (hf : IsEmbedding f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_left`：range_
pullback_to_base_of_left : Set.range (pullback.fst f g ≫ f) = Set.range f inter 
Set.range g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.Opens.range_ι`：range_ι : Set.range U.ι = U
-/
theorem Scheme.quasiSeparatedSpace_of_isOpenCover
    {I : Type*} (U : I → X.Opens) (hU : IsOpenCover U)
    (hU₁ : ∀ i, IsAffineOpen (U i)) (hU₂ : ∀ i j, IsCompact (X := X) (U i ∩ U j)) :
    QuasiSeparatedSpace X := by
  let := HasAffineProperty.isLocal_affineProperty @QuasiCompact
  rw [← quasiCompact_affineProperty_iff_quasiSeparatedSpace X.toSpecΓ]
  have : ∀ i, IsAffine ((X.openCoverOfIsOpenCover U hU).X i) := hU₁
  refine AffineTargetMorphismProperty.diagonal_of_openCover_source _
    (Scheme.openCoverOfIsOpenCover _ _ hU) fun i j ↦ ?_
  rw [← isCompact_univ_iff, (pullback.fst ((X.openCoverOfIsOpenCover U hU).f i)
    ((X.openCoverOfIsOpenCover U hU).f j) ≫
    (X.openCoverOfIsOpenCover U hU).f i).isOpenEmbedding.isCompact_iff, Set.image_univ,
    IsOpenImmersion.range_pullback_to_base_of_left]
  simpa using hU₂ i j

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.quasiSeparatedSpace_iff_quasiCompact_prod_lift** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：quasiSeparatedSpace_iff_quasiCompact_prod_lift : QuasiSeparatedSpace X ↔ Q
uasiCompact (prod.lift (𝟙 X) (𝟙 X))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCa
rrierCommRingCat`：AlgebraicGeometry.HasAffineProperty @AlgebraicGeometry.QuasiCo
mpact fun X x x_1 x_2 => CompactSpace ↥X
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpace
CarrierCarrierCommRingCat`：AlgebraicGeometry.HasAffineProperty @AlgebraicGeometr
y.QuasiSeparated fun X x x_1 x_2 => QuasiSeparatedSpace ↥X
· 使用定理 `AlgebraicGeometry.instIsAffineTerminalScheme`：AlgebraicGeometry.IsAffine
 (⊤_ AlgebraicGeometry.Scheme)
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.quasiSeparated_iff`：∀ {X Y : AlgebraicGeometry.Scheme}
 (f : X ⟶ Y),   AlgebraicGeometry.QuasiSeparated f ↔     autoParam (AlgebraicGeo
metry.QuasiCompact (Catego…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `prodIsoPullback_hom_fst`：prodIsoPullback_hom_fst [HasTerminal C] [HasPul
lbacks C] (X Y : C) [HasBinaryProduct X Y] : (prodIsoPullback X Y).hom ≫ pullbac
k.fst _ _ = p…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用引理 `prodIsoPullback_hom_snd`：prodIsoPullback_hom_snd [HasTerminal C] [HasPul
lbacks C] (X Y : C) [HasBinaryProduct X Y] : (prodIsoPullback X Y).hom ≫ pullbac
k.snd _ _ = p…
-/
lemma quasiSeparatedSpace_iff_quasiCompact_prod_lift :
    QuasiSeparatedSpace X ↔ QuasiCompact (prod.lift (𝟙 X) (𝟙 X)) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso @QuasiCompact _ (prodIsoPullback X X).hom,
    ← HasAffineProperty.iff_of_isAffine (f := terminal.from X) (P := @QuasiSeparated),
    quasiSeparated_iff]
  congr!
  ext : 1 <;> simp
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [QuasiSeparatedSpace X] : QuasiCompact (prod.lift (𝟙 X) (𝟙 X)) := by
  rwa [← quasiSeparatedSpace_iff_quasiCompact_prod_lift]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [QuasiSeparatedSpace Y] (f g : X ⟶ Y) : QuasiCompact (equalizer.ι f g) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_equalizer_prod f g).flip inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace X] [QuasiSeparatedSpace Y] (f g : X ⟶ Y) :
    CompactSpace (equalizer f g).carrier := by
  constructor
  simpa using QuasiCompact.isCompact_preimage (f := equalizer.ι f g) _ isOpen_univ isCompact_univ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.QuasiSeparated.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.QuasiSeparated`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicG
eometry.QuasiSeparated (CategoryTheory.CategoryStruct.comp f g)], AlgebraicGeome
try.QuasiSeparated f
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderCompositionPrecoverageOfIsStab
leUnderComposition`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme) [P.IsStableUnderComposition],   (AlgebraicGeometry.Scheme.precoverage P).Is
…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
· 使用定理 `AlgebraicGeometry.HasAffineProperty.of_openCover`：∀ {P : CategoryTheory.
MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTargetMo
rphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpace
CarrierCarrierCommRingCat`：AlgebraicGeometry.HasAffineProperty @AlgebraicGeometr
y.QuasiSeparated fun X x x_1 x_2 => QuasiSeparatedSpace ↥X
· 使用定理 `AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated`：quasiSeparatedS
pace_of_quasiSeparated (f : X ⟶ Y) [hY : QuasiSeparatedSpace Y] [QuasiSeparated 
f] : QuasiSeparatedSpace X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.HasAffineProperty.of_isPullback`：∀ {P : CategoryTheory
.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTargetM
orphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `AlgebraicGeometry.instQuasiSeparatedOfMonoScheme`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) [CategoryTheory.Mono f], AlgebraicGeometry.QuasiSeparat
ed f
· 使用定理 `AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion`：∀ {X Y S X' Y' S'
 : AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S
') (i₁ : X ⟶ X')   (i₂ : Y ⟶ Y') (i₃ : S ⟶ …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem QuasiSeparated.of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated (f ≫ g)] :
    QuasiSeparated f := by
  let 𝒰 := (Z.affineCover.pullback₁ g).bind fun x => Scheme.affineCover _
  have (i : _) : IsAffine (𝒰.X i) := by dsimp [𝒰]; infer_instance
  apply HasAffineProperty.of_openCover
    ((Z.affineCover.pullback₁ g).bind fun x => Scheme.affineCover _)
  rintro ⟨i, j⟩; dsimp at i j
  refine @quasiSeparatedSpace_of_quasiSeparated _ _ ?_
    (HasAffineProperty.of_isPullback (.of_hasPullback _ (Z.affineCover.f i)) ‹_›) ?_
  · exact pullback.map _ _ _ _ (𝟙 _) _ _ (by simp) (Category.comp_id _) ≫
      (pullbackRightPullbackFstIso g (Z.affineCover.f i) f).hom
  · exact inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) QuasiSeparated.of_quasiSeparatedSpace
    (f : X ⟶ Y) [QuasiSeparatedSpace X] : QuasiSeparated f :=
  have : QuasiSeparated (f ≫ Y.toSpecΓ) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).mpr ‹_›
  .of_comp f Y.toSpecΓ
/-
**AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：quasiSeparated_iff_quasiSeparatedSpace (f : X ⟶ Y) [QuasiSeparatedSpace Y]
 : QuasiSeparated f ↔ QuasiSeparatedSpace X
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated`：quasiSeparatedS
pace_of_quasiSeparated (f : X ⟶ Y) [hY : QuasiSeparatedSpace Y] [QuasiSeparated 
f] : QuasiSeparatedSpace X
· 使用定理 `AlgebraicGeometry.QuasiSeparated.of_quasiSeparatedSpace`：∀ {X Y : Algebr
aicGeometry.Scheme} (f : X ⟶ Y) [QuasiSeparatedSpace ↥X], AlgebraicGeometry.Quas
iSeparated f
-/
theorem quasiSeparated_iff_quasiSeparatedSpace (f : X ⟶ Y) [QuasiSeparatedSpace Y] :
    QuasiSeparated f ↔ QuasiSeparatedSpace X :=
  ⟨fun _ ↦ quasiSeparatedSpace_of_quasiSeparated f, fun _ ↦ inferInstance⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @QuasiSeparated ⊤ where
  of_postcomp f g _ _ := .of_comp f g
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @QuasiCompact @QuasiSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    (by rw [quasiSeparated_eq_diagonal_is_quasiCompact])
/-
**AlgebraicGeometry.QuasiCompact.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.QuasiCompact`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicG
eometry.QuasiCompact (CategoryTheory.CategoryStruct.comp f g)] [AlgebraicGeometr
y.QuasiSeparated g],   AlgebraicGeometry.QuasiCompact f
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `AlgebraicGeometry.instHasOfPostcompPropertySchemeQuasiCompactQuasiSepara
ted`：CategoryTheory.MorphismProperty.HasOfPostcompProperty @AlgebraicGeometry.Qu
asiCompact @AlgebraicGeometry.QuasiSeparated
-/
lemma QuasiCompact.of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact (f ≫ g)] [QuasiSeparated g] :
    QuasiCompact f :=
  MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) quasiCompact_of_compactSpace {X Y : Scheme} (f : X ⟶ Y)
    [CompactSpace X] [QuasiSeparatedSpace Y] : QuasiCompact f :=
  have : QuasiCompact (f ≫ Y.toSpecΓ) := HasAffineProperty.iff_of_isAffine.mpr ‹_›
  .of_comp f Y.toSpecΓ
/-
**AlgebraicGeometry.quasiCompact_iff_compactSpace** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry`。
形式化陈述：quasiCompact_iff_compactSpace (f : X ⟶ Y) [QuasiSeparatedSpace Y] [Compact
Space Y] : QuasiCompact f ↔ CompactSpace X
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`：∀ {X Y : Al
gebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f] [CompactS
pace ↥Y], CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.quasiCompact_of_compactSpace`：∀ {X Y : AlgebraicGeomet
ry.Scheme} (f : X ⟶ Y) [CompactSpace ↥X] [QuasiSeparatedSpace ↥Y],   AlgebraicGe
ometry.QuasiCompact f
-/
theorem quasiCompact_iff_compactSpace (f : X ⟶ Y) [QuasiSeparatedSpace Y] [CompactSpace Y] :
    QuasiCompact f ↔ CompactSpace X :=
  ⟨fun _ ↦ QuasiCompact.compactSpace_of_compactSpace f, fun _ ↦ inferInstance⟩
/-
**AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry`。
形式化陈述：exists_eq_pow_mul_of_isAffineOpen (X : Scheme) (U : X.Opens) (hU : IsAffin
eOpen U) (f : Γ(X, U)) (x : Γ(X, X.basicOpen f)) : exists (n : Nat) (y : Γ(X, U)
), y |_ X.basicOpen f = (f |_ X.basicOpen f) ^ n * x
参数：X : Scheme；U : X.Opens；hU : IsAffineOpen U；f : Γ(X, U)；x : Γ(X, X.basicOpen f
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.IsLocalizationMap.surj`：∀ {M : Type u_1} [inst : CommMonoid M]
 {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.IsLoc
alizationMap f → ∀ (z …
· 使用定理 `IsLocalization'.toIsLocalizationMap`：∀ {R : Type u_1} {inst : CommSemiri
ng R} {M : Submonoid R} {S : Type u_2} {inst_1 : CommSemiring S}   {inst_2 : Alg
ebra R S} [self : IsLocal…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_eq_pow_mul_of_isAffineOpen (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (f : Γ(X, U)) (x : Γ(X, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(X, U)), y |_ X.basicOpen f = (f |_ X.basicOpen f) ^ n * x := by
  have := (hU.isLocalization_basicOpen f).1.2
  obtain ⟨⟨y, _, n, rfl⟩, d⟩ := this x
  use n, y
  simpa [mul_comm x] using! d.symm
/-
**AlgebraicGeometry.exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux
_aux** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux {X : TopC
at.{u}} (F : X.Presheaf CommRingCat) {U₁ U₂ U₃ U₄ U₅ U₆ U₇ : Opens X} {n₁ n₂ : N
at} {y₁ : F.obj (op U₁)} {y₂ : F.obj (op U₂)} {f : F.obj (op <| U₁ ⊔ U₂)} {x : F
.obj (op U₃)} (h₄₁ : U₄ <= U₁) (h₄₂ : U₄ <= U₂) (h₅₁ : U₅ <= U₁) (h₅₃ : U₅ <= U₃
) (h₆₂ : U₆ <= U₂) (h₆₃ : U₆ <= U₃) (h₇₄ : U₇ <= U₄) (h₇₅ : U₇ <= U₅) (h₇₆ : U₇ 
<= U₆) (e₁ : y₁ |_ U₅ = (f |_ U₁ |_ U₅) ^ n₁ * x |_ U₅) (e₂ : y₂ |_ U₆ = (f |_ U
₂ |_ U₆) ^ n₂ * x |_ U₆) :
参数：F : X.Presheaf CommRingCat；op U₁；op U₂；op <| U₁ ⊔ U₂；op U₃；h₄₁ : U₄ <= U₁；h₄₂
 : U₄ <= U₂；h₅₁ : U₅ <= U₁；h₅₃ : U₅ <= U₃；h₆₂ : U₆ <= U₂；h₆₃ : U₆ <= U₃；h₇₄ : U₇
 <= U₄；h₇₅ : U₇ <= U₅；h₇₆ : U₇ <= U₆；e₁ : y₁ |_ U₅ = (f |_ U₁ |_ U₅) ^ n₁ * x |_
 U₅；e₂ : y₂ |_ U₆ = (f |_ U₂ |_ U₆) ^ n₂ * x |_ U₆。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
-/
theorem exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux {X : TopCat.{u}}
    (F : X.Presheaf CommRingCat) {U₁ U₂ U₃ U₄ U₅ U₆ U₇ : Opens X} {n₁ n₂ : ℕ}
    {y₁ : F.obj (op U₁)} {y₂ : F.obj (op U₂)} {f : F.obj (op <| U₁ ⊔ U₂)}
    {x : F.obj (op U₃)} (h₄₁ : U₄ ≤ U₁) (h₄₂ : U₄ ≤ U₂) (h₅₁ : U₅ ≤ U₁) (h₅₃ : U₅ ≤ U₃)
    (h₆₂ : U₆ ≤ U₂) (h₆₃ : U₆ ≤ U₃) (h₇₄ : U₇ ≤ U₄) (h₇₅ : U₇ ≤ U₅) (h₇₆ : U₇ ≤ U₆)
    (e₁ : y₁ |_ U₅ = (f |_ U₁ |_ U₅) ^ n₁ * x |_ U₅)
    (e₂ : y₂ |_ U₆ = (f |_ U₂ |_ U₆) ^ n₂ * x |_ U₆) :
    (((f |_ U₁) ^ n₂ * y₁) |_ U₄) |_ U₇ = (((f |_ U₂) ^ n₁ * y₂) |_ U₄) |_ U₇ := by
  apply_fun (fun x : F.obj (op U₅) ↦ x |_ U₇) at e₁
  apply_fun (fun x : F.obj (op U₆) ↦ x |_ U₇) at e₂
  dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply] at e₁ e₂ ⊢
  simp only [map_mul, map_pow, ← op_comp, ← F.map_comp, homOfLE_comp, ← CommRingCat.comp_apply]
    at e₁ e₂ ⊢
  rw [e₁, e₂, mul_left_comm]
/-
**AlgebraicGeometry.exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux
** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux (X : Scheme) 
(S : X.affineOpens) (U₁ U₂ : X.Opens) {n₁ n₂ : Nat} {y₁ : Γ(X, U₁)} {y₂ : Γ(X, U
₂)} {f : Γ(X, U₁ ⊔ U₂)} {x : Γ(X, X.basicOpen f)} (h₁ : S.1 <= U₁) (h₂ : S.1 <= 
U₂) (e₁ : y₁ |_ X.basicOpen (f |_ U₁) = ((f |_ U₁ |_ X.basicOpen _) ^ n₁) * x |_
 X.basicOpen _) (e₂ : y₂ |_ X.basicOpen (f |_ U₂) = ((f |_ U₂ |_ X.basicOpen _) 
^ n₂) * x |_ X.basicOpen _) : exists n : Nat, forall m, n <= m -> ((f |_ U₁) ^ (
m + n₂) * y₁) |_ S.1 = ((f
参数：X : Scheme；S : X.affineOpens；U₁ U₂ : X.Opens；X, U₁；X, U₂；X, U₁ ⊔ U₂；X, X.basi
cOpen f；h₁ : S.1 <= U₁；h₂ : S.1 <= U₂；e₁ : y₁ |_ X.basicOpen (f |_ U₁) = ((f |_ 
U₁ |_ X.basicOpen _) ^ n₁) * x |_ X.basicOpen _；e₂ : y₂ |_ X.basicOpen (f |_ U₂)
 = ((f |_ U₂ |_ X.basicOpen _) ^ n₂) * x |_ X.basicOpen _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.exists_eq_pow_mul_of_is_compact_of_quasi_separated_spa
ce_aux_aux`：exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux {X 
: TopCat.{u}} (F : X.Presheaf CommRingCat) {U₁ U₂ U₃ U₄ U₅ U₆ U₇ : Opens…
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopCat.Presheaf.restrictOpen.congr_simp`：∀ {X : TopCat} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type u_
2}   [inst_1 : (X Y : C) → Fu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux (X : Scheme)
    (S : X.affineOpens) (U₁ U₂ : X.Opens) {n₁ n₂ : ℕ} {y₁ : Γ(X, U₁)}
    {y₂ : Γ(X, U₂)} {f : Γ(X, U₁ ⊔ U₂)}
    {x : Γ(X, X.basicOpen f)} (h₁ : S.1 ≤ U₁) (h₂ : S.1 ≤ U₂)
    (e₁ : y₁ |_ X.basicOpen (f |_ U₁) =
      ((f |_ U₁ |_ X.basicOpen _) ^ n₁) * x |_ X.basicOpen _)
    (e₂ : y₂ |_ X.basicOpen (f |_ U₂) =
      ((f |_ U₂ |_ X.basicOpen _) ^ n₂) * x |_ X.basicOpen _) :
    ∃ n : ℕ, ∀ m, n ≤ m →
      ((f |_ U₁) ^ (m + n₂) * y₁) |_ S.1 = ((f |_ U₂) ^ (m + n₁) * y₂) |_ S.1 := by
  obtain ⟨⟨_, n, rfl⟩, e⟩ :=
    (@IsLocalization.eq_iff_exists _ _ _ _ _ _
      (S.2.isLocalization_basicOpen (f |_ S.1))
        (((f |_ U₁) ^ n₂ * y₁) |_ S.1)
        (((f |_ U₂) ^ n₁ * y₂) |_ S.1)).mp <| by
    apply exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux (e₁ := e₁) (e₂ := e₂)
    · change X.basicOpen _ ≤ _
      simp only [TopCat.Presheaf.restrictOpenCommRingCat_apply, Scheme.basicOpen_res]
      exact inf_le_inf h₁ le_rfl
    · change X.basicOpen _ ≤ _
      simp only [TopCat.Presheaf.restrictOpenCommRingCat_apply, Scheme.basicOpen_res]
      exact inf_le_inf h₂ le_rfl
  use n
  intro m hm
  rw [← tsub_add_cancel_of_le hm]
  simp only [TopCat.Presheaf.restrictOpenCommRingCat_apply,
    pow_add, map_pow, map_mul, mul_assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp,
    ← CommRingCat.comp_apply] at e ⊢
  rw [e]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated** 是 Mathl
ib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated (X : Scheme.{u}) (U : X
.Opens) (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1) (f : Γ(X, U)) (x : Γ(X
, X.basicOpen f)) : exists (n : Nat) (y : Γ(X, U)), y |_ X.basicOpen f = (f |_ X
.basicOpen f) ^ n * x
参数：X : Scheme.{u}；U : X.Opens；hU : IsCompact U.1；hU' : IsQuasiSeparated U.1；f : 
Γ(X, U)；x : Γ(X, X.basicOpen f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.compact_open_induction_on`：compact_open_induction_on {
P : X.Opens -> Prop} (S : X.Opens) (hS : IsCompact (S : Set X)) (h₁ : P ⊥) (h₂ :
 forall (S : X.Opens) (_ : IsComp…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CommRingCat.subsingleton_of_isTerminal`：subsingleton_of_isTerminal {X : 
CommRingCat} (hX : IsTerminal X) : Subsingleton X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `IsQuasiSeparated.of_subset`：IsQuasiSeparated.of_subset {s t : Set α} (ht
 : IsQuasiSeparated t) (h : s subseteq t) : IsQuasiSeparated s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen`：exists_eq_pow_mul_o
f_isAffineOpen (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U) (f : Γ(X, U)) (x
 : Γ(X, X.basicOpen f)) : exists (n : Nat…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineO
pens`：isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens {U : Set X} : I
sCompact U ∧ IsOpen U ↔ exists s : Set X.affineOpens, s.Finite ∧ U…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompact`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsCompact ↑U
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
（共 56 条，此处仅展示前 30 条）
-/
theorem exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated (X : Scheme.{u}) (U : X.Opens)
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1) (f : Γ(X, U)) (x : Γ(X, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(X, U)), y |_ X.basicOpen f = (f |_ X.basicOpen f) ^ n * x := by
  dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply]
  revert hU' f x
  refine compact_open_induction_on U hU ?_ ?_
  · intro _ f x
    use 0, f
    refine @Subsingleton.elim _
      (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty ?_)) _ _
    rw [eq_bot_iff]
    exact X.basicOpen_le f
  · -- Given `f : 𝒪(S ∪ U), x : 𝒪(X_f)`, we need to show that `f ^ n * x` is the restriction of
    -- some `y : 𝒪(S ∪ U)` for some `n : ℕ`.
    intro S hS U hU hSU f x
    -- We know that such `y₁, n₁` exists on `S` by the induction hypothesis.
    obtain ⟨n₁, y₁, hy₁⟩ :=
      hU (hSU.of_subset Set.subset_union_left) (X.presheaf.map (homOfLE le_sup_left).op f)
        (X.presheaf.map (homOfLE _).op x)
    -- · rw [X.basicOpen_res]; exact inf_le_right
    -- We know that such `y₂, n₂` exists on `U` since `U` is affine.
    obtain ⟨n₂, y₂, hy₂⟩ :=
      exists_eq_pow_mul_of_isAffineOpen X _ U.2 (X.presheaf.map (homOfLE le_sup_right).op f)
        (X.presheaf.map (homOfLE _).op x)
    dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply] at hy₂
    -- swap; · rw [X.basicOpen_res]; exact inf_le_right
    -- Since `S ∪ U` is quasi-separated, `S ∩ U` can be covered by finite affine opens.
    obtain ⟨s, hs', hs⟩ :=
      isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
        ⟨hSU _ _ Set.subset_union_left S.2 hS Set.subset_union_right U.1.2
            U.2.isCompact,
          (S ⊓ U.1).2⟩
    have := hs'.to_subtype
    cases nonempty_fintype s
    replace hs : S ⊓ U.1 = iSup fun i : s => (i : X.Opens) := by ext1; simpa using hs
    have hs₁ (i : s) : i.1.1 ≤ S := by
      refine le_trans ?_ (inf_le_left (b := U.1))
      rw [hs]
      exact le_iSup (fun (i : s) => (i : X.Opens)) i
    have hs₂ (i : s) : i.1.1 ≤ U.1 := by
      refine le_trans ?_ (inf_le_right (a := S))
      rw [hs]
      exact le_iSup (fun (i : s) => (i : X.Opens)) i
    -- On each affine open in the intersection, we have `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`
    -- for some `n` since `f ^ n₂ * y₁ = f ^ (n₁ + n₂) * x = f ^ n₁ * y₂` on `X_f`.
    have := fun i ↦ exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux
      X i.1 S U (hs₁ i) (hs₂ i) hy₁ hy₂
    choose n hn using this
    -- We can thus choose a big enough `n` such that `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`
    -- on `S ∩ U`.
    have :
      X.presheaf.map (homOfLE <| inf_le_left).op
          (X.presheaf.map (homOfLE le_sup_left).op f ^ (Finset.univ.sup n + n₂) * y₁) =
        X.presheaf.map (homOfLE <| inf_le_right).op
          (X.presheaf.map (homOfLE le_sup_right).op f ^ (Finset.univ.sup n + n₁) * y₂) := by
      fapply X.sheaf.eq_of_locally_eq' fun i : s => i.1.1
      · refine fun i => homOfLE ?_; rw [hs]
        exact le_iSup (fun (i : s) => (i : X.Opens)) i
      · exact le_of_eq hs
      · intro i
        -- This unfolds `X.sheaf`
        change (X.presheaf.map _) _ = (X.presheaf.map _) _
        simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
        apply hn
        exact Finset.le_sup (Finset.mem_univ _)
    use Finset.univ.sup n + n₁ + n₂
    -- By the sheaf condition, since `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`, it can be glued into
    -- the desired section on `S ∪ U`.
    use (X.sheaf.objSupIsoProdEqLocus S U.1).inv ⟨⟨_ * _, _ * _⟩, this⟩
    refine (X.sheaf.objSupIsoProdEqLocus_inv_eq_iff _ _ _ (X.basicOpen_res _
      (homOfLE le_sup_left).op) (X.basicOpen_res _ (homOfLE le_sup_right).op)).mpr ⟨?_, ?_⟩
    · -- This unfolds `X.sheaf`
      change (X.presheaf.map _) _ = (X.presheaf.map _) _
      rw [add_assoc, add_comm n₁]
      simp only [pow_add, map_pow, map_mul, hy₁, ← CommRingCat.comp_apply, ← mul_assoc,
        ← Functor.map_comp, ← op_comp, homOfLE_comp]
    · -- This unfolds `X.sheaf`
      change (X.presheaf.map _) _ = (X.presheaf.map _) _
      simp only [pow_add, map_pow, map_mul, hy₂, ← CommRingCat.comp_apply, ← mul_assoc,
        ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.
This is known as the **Qcqs lemma** in [R. Vakil, *The rising sea*][RisingSea]. -/
/-
**AlgebraicGeometry.isLocalization_basicOpen_of_qcqs** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：isLocalization_basicOpen_of_qcqs {X : Scheme} {U : X.Opens} (hU : IsCompac
t U.1) (hU' : IsQuasiSeparated U.1) (f : Γ(X, U)) : IsLocalization.Away f (Γ(X, 
X.basicOpen f))
参数：hU : IsCompact U.1；hU' : IsQuasiSeparated U.1；f : Γ(X, U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`：isUnit_res_basicOpen
 {U : Opens X} (f : X.presheaf.obj (op U)) : IsUnit (X.presheaf.map (@homOfLE (O
pens X) _ _ _ (X.basicOpen_le f)).op f)
· 使用定理 `AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated`：ex
ists_eq_pow_mul_of_isCompact_of_isQuasiSeparated (X : Scheme.{u}) (U : X.Opens) 
(hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1) (f : Γ(X…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isC
ompact`：exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (X : Scheme
.{u}) {U : X.Opens} (hU : IsCompact U.1) (x f : Γ(X, U)) (H : x |_ (…

--- 原说明 ---
If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.
This is known as the **Qcqs lemma** in [R. Vakil, *The rising sea*][RisingSea].
-/
theorem isLocalization_basicOpen_of_qcqs {X : Scheme} {U : X.Opens} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1) (f : Γ(X, U)) :
    IsLocalization.Away f (Γ(X, X.basicOpen f)) := by
  constructor; constructor
  · rintro ⟨_, n, rfl⟩
    simp only [map_pow, RingHom.algebraMap_toAlgebra]
    exact IsUnit.pow _ (RingedSpace.isUnit_res_basicOpen _ f)
  · intro z
    obtain ⟨n, y, e⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X U hU hU' f z
    refine ⟨⟨y, _, n, rfl⟩, ?_⟩
    simpa only [map_pow, Subtype.coe_mk, RingHom.algebraMap_toAlgebra, mul_comm z] using! e.symm
  · intro x y
    rw [← sub_eq_zero, ← map_sub, RingHom.algebraMap_toAlgebra]
    simp_rw [← @sub_eq_zero _ _ (_ * x) (_ * y), ← mul_sub]
    generalize x - y = z
    intro H
    obtain ⟨n, e⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU _ _ H
    refine ⟨⟨_, n, rfl⟩, ?_⟩
    simpa [mul_comm z] using! e
/-
**AlgebraicGeometry.exists_of_res_eq_of_qcqs** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：exists_of_res_eq_of_qcqs {X : Scheme.{u}} {U : TopologicalSpace.Opens X} (
hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier) {f g s : Γ(X, U)} (
hfg : f |_ X.basicOpen s = g |_ X.basicOpen s) : exists n, s ^ n * f = s ^ n * g
参数：hU : IsCompact U.carrier；hU' : IsQuasiSeparated U.carrier；X, U；hfg : f |_ X.b
asicOpen s = g |_ X.basicOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.Away.exists_of_eq`：exists_of_eq {a b : R} (h : algebraMap
 R S a = algebraMap R S b) : exists (n : Nat), x ^ n * a = x ^ n * b
· 使用定理 `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`：isLocalization_basic
Open_of_qcqs {X : Scheme} {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSepar
ated U.1) (f : Γ(X, U)) : IsLocalization…
-/
lemma exists_of_res_eq_of_qcqs {X : Scheme.{u}} {U : TopologicalSpace.Opens X}
    (hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier)
    {f g s : Γ(X, U)} (hfg : f |_ X.basicOpen s = g |_ X.basicOpen s) :
    ∃ n, s ^ n * f = s ^ n * g := by
  obtain ⟨n, hc⟩ := (isLocalization_basicOpen_of_qcqs hU hU' s).exists_of_eq s hfg
  use n
/-
**AlgebraicGeometry.exists_of_res_eq_of_qcqs_of_top** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：exists_of_res_eq_of_qcqs_of_top {X : Scheme.{u}} [CompactSpace X] [QuasiSe
paratedSpace X] {f g s : Γ(X, ⊤)} (hfg : f |_ X.basicOpen s = g |_ X.basicOpen s
) : exists n, s ^ n * f = s ^ n * g
参数：X, ⊤；hfg : f |_ X.basicOpen s = g |_ X.basicOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.exists_of_res_eq_of_qcqs`：exists_of_res_eq_of_qcqs {X 
: Scheme.{u}} {U : TopologicalSpace.Opens X} (hU : IsCompact U.carrier) (hU' : I
sQuasiSeparated U.carrier) {f g …
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ
· 使用定理 `isQuasiSeparated_univ`：isQuasiSeparated_univ {α : Type*} [TopologicalSpa
ce α] [QuasiSeparatedSpace α] : IsQuasiSeparated (Set.univ : Set α)
-/
lemma exists_of_res_eq_of_qcqs_of_top {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {f g s : Γ(X, ⊤)} (hfg : f |_ X.basicOpen s = g |_ X.basicOpen s) :
    ∃ n, s ^ n * f = s ^ n * g :=
  exists_of_res_eq_of_qcqs (U := ⊤) CompactSpace.isCompact_univ isQuasiSeparated_univ hfg
/-
**AlgebraicGeometry.exists_of_res_zero_of_qcqs** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry`。
形式化陈述：exists_of_res_zero_of_qcqs {X : Scheme.{u}} {U : TopologicalSpace.Opens X}
 (hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier) {f s : Γ(X, U)} (
hf : f |_ X.basicOpen s = 0) : exists n, s ^ n * f = 0
参数：hU : IsCompact U.carrier；hU' : IsQuasiSeparated U.carrier；X, U；hf : f |_ X.ba
sicOpen s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.exists_of_res_eq_of_qcqs`：exists_of_res_eq_of_qcqs {X 
: Scheme.{u}} {U : TopologicalSpace.Opens X} (hU : IsCompact U.carrier) (hU' : I
sQuasiSeparated U.carrier) {f g …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.RingedSpace.res_zero`：res_zero {X : RingedSpace.{u}} {
U V : TopologicalSpace.Opens X} (hUV : U <= V) : (0 : X.presheaf.obj (op V)) |_ 
U = (0 : X.presheaf.obj (op …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma exists_of_res_zero_of_qcqs {X : Scheme.{u}} {U : TopologicalSpace.Opens X}
    (hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier)
    {f s : Γ(X, U)} (hf : f |_ X.basicOpen s = 0) :
    ∃ n, s ^ n * f = 0 := by
  suffices h : ∃ n, s ^ n * f = s ^ n * 0 by
    simpa using h
  apply exists_of_res_eq_of_qcqs hU hU'
  simpa
/-
**AlgebraicGeometry.exists_of_res_zero_of_qcqs_of_top** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry`。
形式化陈述：exists_of_res_zero_of_qcqs_of_top {X : Scheme} [CompactSpace X] [QuasiSepa
ratedSpace X] {f s : Γ(X, ⊤)} (hf : f |_ X.basicOpen s = 0) : exists n, s ^ n * 
f = 0
参数：X, ⊤；hf : f |_ X.basicOpen s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.exists_of_res_zero_of_qcqs`：exists_of_res_zero_of_qcqs
 {X : Scheme.{u}} {U : TopologicalSpace.Opens X} (hU : IsCompact U.carrier) (hU'
 : IsQuasiSeparated U.carrier) {f …
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ
· 使用定理 `isQuasiSeparated_univ`：isQuasiSeparated_univ {α : Type*} [TopologicalSpa
ce α] [QuasiSeparatedSpace α] : IsQuasiSeparated (Set.univ : Set α)
-/
lemma exists_of_res_zero_of_qcqs_of_top {X : Scheme} [CompactSpace X] [QuasiSeparatedSpace X]
    {f s : Γ(X, ⊤)} (hf : f |_ X.basicOpen s = 0) :
    ∃ n, s ^ n * f = 0 :=
  exists_of_res_zero_of_qcqs (U := ⊤) CompactSpace.isCompact_univ isQuasiSeparated_univ hf

set_option backward.isDefEq.respectTransparency false in
/-- If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.
This is known as the **Qcqs lemma** in [R. Vakil, *The rising sea*][RisingSea]. -/
/-
**AlgebraicGeometry.isIso_** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.
This is known as the **Qcqs lemma** in [R. Vakil, *The rising sea*][RisingSea].
-/
instance isIso_ΓSpec_adjunction_unit_app_basicOpen
    [CompactSpace X] [QuasiSeparatedSpace X] (f : Γ(X, ⊤)) :
    IsIso (X.toSpecΓ.app (PrimeSpectrum.basicOpen f)) := by
  refine @IsIso.of_isIso_comp_right _ _ _ _ _ _ (X.presheaf.map
    (eqToHom (Scheme.toSpecΓ_preimage_basicOpen _ _).symm).op) _ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  apply +allowSynthFailures IsLocalization.bijective
  · exact StructureSheaf.IsLocalization.to_basicOpen _ _
  · refine isLocalization_basicOpen_of_qcqs ?_ ?_ _
    · exact isCompact_univ
    · exact isQuasiSeparated_univ
  · simp [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, RingHom.algebraMap_toAlgebra,
      ← Functor.map_comp]

end AlgebraicGeometry

