/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
public import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
public import Mathlib.CategoryTheory.MorphismProperty.Descent

/-!
# Descent of morphism properties

Let `P` and `P'` be morphism properties. In this file we show some results to deduce
that `P` descends along `P'` from a codescent property of ring homomorphisms.

## Main results

- `HasRingHomProperty.descendsAlong`: if `P` is a local property induced by `Q`, `P'` implies
  `Q'` on global sections of affines and `Q` codescends along `Q'`, then `P` descends along `P'`.
- `HasAffineProperty.descendsAlong_of_affineAnd`: if `P` is given by `affineAnd Q`, `P'` implies
  `Q'` on global sections of affines and `Q` codescends along `Q'`, then `P` descends along `P'`
  (see TODOs).

## TODO

- Show that affine morphisms descend along faithfully-flat morphisms. This will make
  `HasAffineProperty.descendsAlong_of_affineAnd` useful.

-/

public section

universe u v

open TensorProduct CategoryTheory Limits

namespace AlgebraicGeometry

variable (P P' : MorphismProperty Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
/--
If `P` is local at the source, every quasi-compact scheme is dominated by an
affine scheme via `p : Y ⟶ X` such that `p` satisfies `P`.
-/
/-
**AlgebraicGeometry.Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) (X : Alge
braicGeometry.Scheme) [CompactSpace ↥X]   [AlgebraicGeometry.IsZariskiLocalAtSou
rce P] [P.ContainsIdentities],   ∃ Y p, AlgebraicGeometry.Surjective p ∧ P p ∧ A
lgebraicGeometry.IsAffine Y
参数：P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme；X : AlgebraicGeo
metry.Scheme。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicGeometry.Scheme.Cover.exists_eq`：∀ {K : CategoryTheory.Precover
age AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometr
y.Scheme.JointlySurjective K] …
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.Limits.Sigma.ι_desc`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {β : Type w} {f : β → C}   [inst_1 : CategoryTheory.Limits.
HasCoproduct f] {P : C} …
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`：iff_of_openCo
ver : P f ↔ forall i, P (𝒰.f i ≫ f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.sigmaOpenCover_f`：∀ {σ : Type v} (g : σ → AlgebraicGeo
metry.Scheme) [inst : Small.{u, v} σ] (b : σ),   (AlgebraicGeometry.sigmaOpenCov
er g).f b = CategoryTheo…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.of_isOpenImmersion`：of_isOpenIm
mersion [P.ContainsIdentities] [IsOpenImmersion f] : P f
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.instIsAffineSigmaObjScheme`：∀ {σ : Type v} (g : σ → Al
gebraicGeometry.Scheme) [inst : Finite σ] [∀ (i : σ), AlgebraicGeometry.IsAffine
 (g i)],   AlgebraicGeometry.IsAff…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AlgebraicGeometry.instIsAffineXSchemeFiniteSubcover`：∀ (X : AlgebraicGeo
metry.Scheme) [inst : CompactSpace ↥X] (𝒰 : X.OpenCover)   [∀ (i : 𝒰.I₀), Algebr
aicGeometry.IsAffine (𝒰.X i)] (i : 𝒰.fini…
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)

--- 原说明 ---
If `P` is local at the source, every quasi-compact scheme is dominated by an
affine scheme via `p : Y ⟶ X` such that `p` satisfies `P`.
-/
lemma Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource (X : Scheme.{u}) [CompactSpace X]
    [IsZariskiLocalAtSource P] [P.ContainsIdentities] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X), Surjective p ∧ P p ∧ IsAffine Y := by
  let 𝒰 := X.affineCover.finiteSubcover
  let p : ∐ (fun i : 𝒰.I₀ ↦ 𝒰.X i) ⟶ X := Sigma.desc (fun i ↦ 𝒰.f i)
  refine ⟨_, p, ⟨fun x ↦ ?_⟩, ?_, inferInstance⟩
  · obtain ⟨i, x, rfl⟩ := X.affineCover.finiteSubcover.exists_eq x
    use Sigma.ι X.affineCover.finiteSubcover.X i x
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (sigmaOpenCover _)]
    exact fun i ↦ by simpa [p] using IsZariskiLocalAtSource.of_isOpenImmersion _

set_option backward.isDefEq.respectTransparency false in
/-- If `P` is local at the target, to show `P` descends along `P'` we may assume
the base to be affine. -/
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：∀ (P P' : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [Algeb
raicGeometry.IsZariskiLocalAtTarget P]   [P'.IsStableUnderBaseChange],   (∀ {R :
 CommRingCat} {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ AlgebraicGeometry.Spec R
)       (g : Y ⟶ AlgebraicGeometry.Spec R), P' f → P (CategoryTheory.Limits.pull
back.fst f g) → P g) →     P.DescendsAlong P'
参数：P P' : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme；∀ {R : CommRi
ngCat} {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ AlgebraicGeometry.Spec R)      
 (g : Y ⟶ AlgebraicGeometry.Spec R), P' f → P (CategoryTheory.Limits.pullback.fs
t f g) → P g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.MorphismProperty.DescendsAlong.mk'`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {P Q : CategoryTheory.MorphismProperty
 C}   [P.RespectsIso],   (∀ {X Y Z : C}…
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover`：iff_of_openCo
ver (𝒰 : Y.OpenCover) : P f ↔ forall i, P (𝒰.pullbackHom f i)
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_fst`：pullbackR
ightPullbackFstIso_inv_snd_fst : (pullbackRightPullbackFstIso f g f').inv ≫ pull
back.snd _ _ ≫ pullback.fst _ _ = pullback.fst _ _ …
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_inv_fst_fst`：pullbackAssoc_inv_fst_f
st [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullbackLeftPullbackSndIso_hom_fst`：pullbackLeftPu
llbackSndIso_hom_fst : (pullbackLeftPullbackSndIso f g g').hom ≫ pullback.fst _ 
_ = pullback.fst _ _ ≫ pullback.fst _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_snd`：pullbackR
ightPullbackFstIso_inv_snd_snd : (pullbackRightPullbackFstIso f g f').inv ≫ pull
back.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_inv_snd`：pullbackAssoc_inv_snd [HasP
ullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullback.fst _
 _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackA…
· 使用定理 `CategoryTheory.Limits.pullbackLeftPullbackSndIso_hom_snd_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g : 
Y ⟶ Z) (g' : W ⟶ Y)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If `P` is local at the target, to show `P` descends along `P'` we may assume
the base to be affine.
-/
lemma IsZariskiLocalAtTarget.descendsAlong [IsZariskiLocalAtTarget P] [P'.IsStableUnderBaseChange]
    (H : ∀ {R : CommRingCat.{u}} {X Y : Scheme.{u}} (f : X ⟶ Spec R) (g : Y ⟶ Spec R),
      P' f → P (pullback.fst f g) → P g) :
    P.DescendsAlong P' := by
  apply MorphismProperty.DescendsAlong.mk'
  introv h hf
  wlog hZ : ∃ R, Z = Spec R generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) Z.affineCover]
    intro i
    let ι := Z.affineCover.f i
    let e : pullback (pullback.snd f ι) (pullback.snd g ι) ≅
        pullback (pullback.fst f g) (pullback.fst f ι) :=
      pullbackLeftPullbackSndIso f ι (pullback.snd g ι) ≪≫
        pullback.congrHom rfl pullback.condition.symm ≪≫
        (pullbackAssoc f g g ι).symm ≪≫ pullback.congrHom pullback.condition.symm rfl ≪≫
        (pullbackRightPullbackFstIso f ι (pullback.fst f g)).symm
    have heq : e.hom ≫ pullback.snd (pullback.fst f g) (pullback.fst f ι) =
        pullback.fst (pullback.snd f ι) (pullback.snd g ι) := by
      apply pullback.hom_ext <;> simp [e, pullback.condition]
    refine this (f := pullback.snd f ι) ?_ ?_ ⟨_, rfl⟩
    · exact P'.pullback_snd _ _ h
    · change P (pullback.fst (pullback.snd f ι) (pullback.snd g ι))
      rw [← heq, P.cancel_left_of_respectsIso]
      exact AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback (iY := pullback.fst f ι)
        (CategoryTheory.IsPullback.of_hasPullback _ _) hf
  obtain ⟨R, rfl⟩ := hZ
  exact H f g h hf

variable (Q Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

variable {Q Q'} in
/-
**AlgebraicGeometry.of_pullback_fst_Spec_of_codescendsAlong** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry`。
形式化陈述：of_pullback_fst_Spec_of_codescendsAlong [P.RespectsIso] (hQQ' : RingHom.Co
descendsAlong Q Q') (H₁ : forall {R S : CommRingCat.{u}} {f : R ⟶ S}, P' (Spec.m
ap f) -> Q' f.hom) (H₂ : forall {R S : CommRingCat.{u}} {f : R ⟶ S}, P (Spec.map
 f) ↔ Q f.hom) {R S T : CommRingCat.{u}} {f : Spec T ⟶ Spec R} {g : Spec S ⟶ Spe
c R} (h : P' f) (hf : P (pullback.fst f g)) : P g
参数：hQQ' : RingHom.CodescendsAlong Q Q'；H₁ : forall {R S : CommRingCat.{u}} {f : 
R ⟶ S}, P' (Spec.map f) -> Q' f.hom；H₂ : forall {R S : CommRingCat.{u}} {f : R ⟶
 S}, P (Spec.map f) ↔ Q f.hom；h : P' f；hf : P (pullback.fst f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.CodescendsAlong.algebraMap_tensorProduct`：∀ {P : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop}   (Q : {R S : 
Type u} → [inst : CommRing R] → [inst_…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.pullbackSpecIso_hom_fst`：pullbackSpecIso_hom_fst : (pu
llbackSpecIso R S T).hom ≫ Spec.map (ofHom includeLeftRingHom) = pullback.fst _ 
_
-/
lemma of_pullback_fst_Spec_of_codescendsAlong [P.RespectsIso]
    (hQQ' : RingHom.CodescendsAlong Q Q')
    (H₁ : ∀ {R S : CommRingCat.{u}} {f : R ⟶ S}, P' (Spec.map f) → Q' f.hom)
    (H₂ : ∀ {R S : CommRingCat.{u}} {f : R ⟶ S}, P (Spec.map f) ↔ Q f.hom)
    {R S T : CommRingCat.{u}}
    {f : Spec T ⟶ Spec R} {g : Spec S ⟶ Spec R} (h : P' f) (hf : P (pullback.fst f g)) :
    P g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom, ψ.hom]
  replace hf : P (pullback.fst (Spec.map <| CommRingCat.ofHom <| algebraMap R T)
    (Spec.map <| CommRingCat.ofHom <| algebraMap R S)) := hf
  rw [H₂]
  refine hQQ'.algebraMap_tensorProduct (R := R) (S := T) (T := S) _ (H₁ h) ?_
  rwa [← pullbackSpecIso_hom_fst R T S, P.cancel_left_of_respectsIso, H₂] at hf

/-- If `X` admits a morphism `p : T ⟶ X` from an affine scheme satisfying `P'`, to
show a property descends along a morphism `f : X ⟶ Z` satisfying `P'`, `X` may assumed to
be affine. -/
/-
**AlgebraicGeometry.IsStableUnderBaseChange.of_pullback_fst_of_isAffine** 是 Math
lib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsStableUnderBaseChange`。
形式化陈述：∀ (P P' : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P'.Re
spectsIso] [P'.IsStableUnderComposition]   [P.IsStableUnderBaseChange],   (∀ {R 
: CommRingCat} {S X : AlgebraicGeometry.Scheme} (f : AlgebraicGeometry.Spec R ⟶ 
S) (g : X ⟶ S),       P' f → P (CategoryTheory.Limits.pullback.fst f g) → P g) →
     ∀ {X Y Z T : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsAffine T] (p : 
T ⟶ X),       P' p → ∀ (f : X ⟶ Z) (g : Y ⟶ Z), P' f → P (CategoryTheory.Limits.
pullback.fst f g) → P g
参数：P P' : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme；∀ {R : CommRi
ngCat} {S X : AlgebraicGeometry.Scheme} (f : AlgebraicGeometry.Spec R ⟶ S) (g : 
X ⟶ S),       P' f → P (CategoryTheory.Limits.pullback.fst f g) → P g；p : T ⟶ X；
f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.pullback.fst f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst`：pullbackRight
PullbackFstIso_inv_fst : (pullbackRightPullbackFstIso f g f').inv ≫ pullback.fst
 f' (pullback.fst f g) = pullback.fst (f' ≫ f) …
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morphi
smProperty C}   [P.IsStableUnderBaseChange], P.RespectsIs…
· 使用定理 `CategoryTheory.MorphismProperty.pullback_fst`：pullback_fst {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong f] (H :
 P g) : P (pullback.fst f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongCompOfHa
sPullbacksAlong`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : C
ategoryTheory.MorphismProperty C) {X Y Z : C} (f : X ⟶ Y)   (g : Y ⟶ Z) [P.Is…
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksAlongOfHasPullbacks`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphi
smProperty C) [P.HasPullbacks]   {X Y : C} {f : X ⟶ Y}, P…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksOfHasPullbacks`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPro
perty C)   [CategoryTheory.Limits.HasPullbacks C], P…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme

--- 原说明 ---
If `X` admits a morphism `p : T ⟶ X` from an affine scheme satisfying `P'`, to
show a property descends along a morphism `f : X ⟶ Z` satisfying `P'`, `X` may a
ssumed to
be affine.
-/
lemma IsStableUnderBaseChange.of_pullback_fst_of_isAffine [P'.RespectsIso]
    [P'.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    (H : ∀ {R : CommRingCat.{u}} {S X : Scheme.{u}} (f : Spec R ⟶ S) (g : X ⟶ S),
      P' f → P (pullback.fst f g) → P g) {X Y Z T : Scheme.{u}} [IsAffine T] (p : T ⟶ X)
    (hp : P' p) (f : X ⟶ Z) (g : Y ⟶ Z) (h : P' f) (hf : P (pullback.fst f g)) : P g := by
  apply H ((T.isoSpec.inv ≫ p) ≫ f)
  · rw [Category.assoc, P'.cancel_left_of_respectsIso]
    exact P'.comp_mem _ _ hp h
  · rw [← pullbackRightPullbackFstIso_inv_fst f g (T.isoSpec.inv ≫ p),
        P.cancel_left_of_respectsIso]
    exact P.pullback_fst _ _ hf

open Opposite

variable [P'.IsStableUnderBaseChange] [P'.IsStableUnderComposition] [P.IsStableUnderBaseChange]
variable
  (H₁ : (@IsLocalIso ⊓ @Surjective : MorphismProperty Scheme) ≤ P')
  (H₂ : ∀ {R S : CommRingCat.{u}} {f : R ⟶ S}, P' (Spec.map f) → Q' f.hom)

set_option backward.isDefEq.respectTransparency.types false in
include H₁ in
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact** 是 Ma
thlib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：∀ (P P' : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P'.Is
StableUnderBaseChange]   [P'.IsStableUnderComposition] [P.IsStableUnderBaseChang
e],   @AlgebraicGeometry.IsLocalIso ⊓ @AlgebraicGeometry.Surjective ≤ P' →     ∀
 [AlgebraicGeometry.IsZariskiLocalAtTarget P],       (∀ {R S : CommRingCat} {Y :
 AlgebraicGeometry.Scheme} (φ : R ⟶ S) (g : Y ⟶ AlgebraicGeometry.Spec R),      
     P' (AlgebraicGeometry.Spec.map φ) →             P (CategoryTheory.Limits.pu
llback.fst (AlgebraicGeometry.Spec.map φ) g) → P g) →         P.DescendsAlong (P
' ⊓ @AlgebraicGeometry.QuasiCompact)
参数：P P' : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme；∀ {R S : Comm
RingCat} {Y : AlgebraicGeometry.Scheme} (φ : R ⟶ S) (g : Y ⟶ AlgebraicGeometry.S
pec R),           P' (AlgebraicGeometry.Spec.map φ) →             P (CategoryThe
ory.Limits.pullback.fst (AlgebraicGeometry.Spec.map φ) g) → P g；P' ⊓ @AlgebraicG
eometry.QuasiCompact。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong`：∀ (P P' : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme) [AlgebraicGeometry.IsZariski
LocalAtTarget P]   [P'.IsStableUnderBaseChan…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.inf`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismProp
erty C}   [P.IsStableUnderBaseChange] [Q.IsStable…
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.quasiCompact_iff_compactSpace`：quasiCompact_iff_compac
tSpace (f : X ⟶ Y) [QuasiSeparatedSpace Y] [CompactSpace Y] : QuasiCompact f ↔ C
ompactSpace X
· 使用定理 `AlgebraicGeometry.Scheme.compactSpace_of_isAffine`：∀ (X : AlgebraicGeome
try.Scheme) [AlgebraicGeometry.IsAffine X], CompactSpace ↥X
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AlgebraicGeometry.Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource`：
∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) (X : AlgebraicG
eometry.Scheme) [CompactSpace ↥X]   [AlgebraicGeometry.IsZar…
· 使用定理 `AlgebraicGeometry.IsLocalIso.instIsZariskiLocalAtSource`：AlgebraicGeomet
ry.IsZariskiLocalAtSource @AlgebraicGeometry.IsLocalIso
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `AlgebraicGeometry.IsLocalIso.instIsMultiplicativeScheme`：CategoryTheory.
MorphismProperty.IsMultiplicative @AlgebraicGeometry.IsLocalIso
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.inf`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] (P Q : CategoryTheory.MorphismProperty C) [P.R
espectsIso]   [Q.RespectsIso], (P ⊓ Q…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsOfRespectsLeftOfRespectsRigh
t`：∀ {C : Type u} [inst : CategoryTheory.CategoryStruct.{v, u} C] (P Q : Categor
yTheory.MorphismProperty C)   [P.RespectsLeft Q] [P.RespectsRig…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsLeft`：∀ {C : Type u} 
{inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPr
operty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morphi
smProperty C}   [P.IsStableUnderBaseChange], P.RespectsIs…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCa
rrierCommRingCat`：AlgebraicGeometry.HasAffineProperty @AlgebraicGeometry.QuasiCo
mpact fun X x x_1 x_2 => CompactSpace ↥X
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffineHom f], AlgebraicGeometry.Qua
siCompact f
· 使用定理 `AlgebraicGeometry.isAffineHom_of_isAffine`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y],
   AlgebraicGeometry.IsAffineHo…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst`：pullbackRight
PullbackFstIso_inv_fst : (pullbackRightPullbackFstIso f g f').inv ≫ pullback.fst
 f' (pullback.fst f g) = pullback.fst (f' ≫ f) …
（共 36 条，此处仅展示前 30 条）
-/
lemma IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact [IsZariskiLocalAtTarget P]
    (H : ∀ {R S : CommRingCat.{u}} {Y : Scheme.{u}} (φ : R ⟶ S) (g : Y ⟶ Spec R),
      P' (Spec.map φ) → P (pullback.fst (Spec.map φ) g) → P g) :
    P.DescendsAlong (P' ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong
  intro R X Y f g hf h
  wlog hX : ∃ T, X = Spec T generalizing X
  · have _ : CompactSpace X := by simpa [← quasiCompact_iff_compactSpace f] using hf.2
    obtain ⟨Y, p, hsurj, hP', hY⟩ := X.exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
    refine this (f := (Y.isoSpec.inv ≫ p) ≫ f) ?_ ?_ ⟨_, rfl⟩
    · rw [Category.assoc, (P' ⊓ @QuasiCompact).cancel_left_of_respectsIso]
      exact ⟨P'.comp_mem _ _ (H₁ _ ⟨hP', hsurj⟩) hf.1, inferInstance⟩
    · rw [← pullbackRightPullbackFstIso_inv_fst f g _, P.cancel_left_of_respectsIso]
      exact P.pullback_fst _ _ h
  obtain ⟨T, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  exact H φ g hf.1 h

include H₁ H₂ in
/--
Let `P` be the morphism property associated to the ring hom property `Q`. Suppose

- `P'` implies `Q'` on global sections for affine schemes,
- `P'` is satisfied for all surjective, local isomorphisms, and
- `Q` codescend along `Q'`.

Then `P` descends along quasi-compact morphisms satisfying `P'`.

Note: The second condition is in particular satisfied for faithfully flat morphisms.
-/
nonrec lemma HasRingHomProperty.descendsAlong [HasRingHomProperty P Q]
    (hQQ' : RingHom.CodescendsAlong Q Q') :
    P.DescendsAlong (P' ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ H₁
  introv h hf
  wlog hY : ∃ S, Y = Spec S generalizing Y
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) Y.affineCover]
    intro i
    have heq : pullback.fst (Spec.map φ) (Y.affineCover.f i ≫ g) =
        pullback.map _ _ _ _ (𝟙 _) (Y.affineCover.f i) (𝟙 _) (by simp) (by simp) ≫
          pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    exact this _ (heq ▸ AlgebraicGeometry.IsZariskiLocalAtSource.comp hf _) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hY
  apply of_pullback_fst_Spec_of_codescendsAlong _ _ hQQ' H₂ _ h hf
  simp [HasRingHomProperty.Spec_iff (P := P)]

include H₁ H₂ in
/--
Let `P` be a morphism property associated with `affineAnd Q`. Suppose

- `P'` implies `Q'` on global sections on affine schemes,
- `P'` is satisfied for surjective, local isomorphisms,
- affine morphisms descend along `P''`, and
- `Q` codescends along `Q'`,

Then `P` descends along quasi-compact morphisms satisfying `P'`.

Note: The second condition is in particular satisfied for faithfully flat morphisms.
-/
nonrec lemma HasAffineProperty.descendsAlong_of_affineAnd
    (hP : HasAffineProperty P (affineAnd Q)) [MorphismProperty.DescendsAlong @IsAffineHom P']
    (hQ : RingHom.RespectsIso Q) (hQQ' : RingHom.CodescendsAlong Q Q') :
    P.DescendsAlong (P' ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ H₁
  introv h hf
  have : IsAffine Y := by
    convert! isAffine_of_isAffineHom g
    exact MorphismProperty.of_pullback_fst_of_descendsAlong h <|
      AlgebraicGeometry.HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ hf
  wlog hY : ∃ S, Y = Spec S generalizing Y
  · rw [← P.cancel_left_of_respectsIso Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
        pullback.map _ _ _ _ (𝟙 _) (Y.isoSpec.inv) (𝟙 _) (by simp) (by simp) ≫
          pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    rwa [heq, P.cancel_left_of_respectsIso]
  obtain ⟨Y, rfl⟩ := hY
  apply of_pullback_fst_Spec_of_codescendsAlong _ _ hQQ' H₂ _ h hf
  simp [SpecMap_iff_of_affineAnd _ hQ]

end AlgebraicGeometry

