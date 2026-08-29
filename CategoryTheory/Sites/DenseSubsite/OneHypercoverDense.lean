/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Equivalence of categories of sheaves with a dense subsite that is 1-hypercover dense

Let `F : C₀ ⥤ C` be a functor equipped with Grothendieck topologies `J₀` and `J`.
Assume that `F` is a dense subsite. We introduce a typeclass
`IsOneHypercoverDense.{w} F J₀ J` which roughly says that objects in `C`
admits a `1`-hypercover consisting of objects in `C₀`.

Under the assumption that the coefficient category `A` has limits of size `w`, we
show that the restriction functor
`sheafPushforwardContinuous F A J₀ J : Sheaf J A ⥤ Sheaf J₀ A` is an equivalence
of categories (see `Functor.isEquivalence_of_isOneHypercoverDense`), which allows
to transport `HasWeakSheafify` and `HasSheafify` assumptions for the site `(C₀, J₀)`
to the site `(C, J)`, see `Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence`
and `Functor.IsDenseSubsite.hasSheafify_of_isEquivalence` in the file
`Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean`.

-/

@[expose] public section

universe w v₀ v v' u₀ u u'

namespace CategoryTheory

open Category Limits Opposite

variable {C₀ : Type u₀} {C : Type u} [Category.{v₀} C₀] [Category.{v} C]

namespace Functor

variable (F : C₀ ⥤ C) (J₀ : GrothendieckTopology C₀)
  (J : GrothendieckTopology C) {A : Type u'} [Category.{v'} A]

/--
Definition of `PreOneHypercoverDenseData` / `PreOneHypercoverDenseData` 的定义

English:
structure PreOneHypercoverDenseData
  parameters: (S : C)
  axioms and operations (8):
    - I₀ : Type w
    - X((i : I₀)) : C₀
    - f((i : I₀)) : F.obj (X i) ⟶ S
    - I₁((i₁ i₂ : I₀)) : Type w
    - Y(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : C₀
    - p₁(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
    - p₂(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
    - w(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : F.map (p₁ j) ≫ f i₁ = F.map (p₂ j) ≫ f i₂

中文:
结构 PreOneHypercoverDenseData
  参数: (S : C)
  公理与运算 (8 个):
    - I₀ : Type w
    - X((i : I₀)) : C₀
    - f((i : I₀)) : F.obj (X i) ⟶ S
    - I₁((i₁ i₂ : I₀)) : Type w
    - Y(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : C₀
    - p₁(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
    - p₂(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
    - w(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : F.map (p₁ j) ≫ f i₁ = F.map (p₂ j) ≫ f i₂
-/
structure PreOneHypercoverDenseData (S : C) where
  /-- the index type of the covering of `S` -/
  I₀ : Type w
  /-- the objects in the covering of `S` -/
  X (i : I₀) : C₀
  /-- the morphisms in the covering of `S` -/
  f (i : I₀) : F.obj (X i) ⟶ S
  /-- the index type of the coverings of the fibre products -/
  I₁ (i₁ i₂ : I₀) : Type w
  /-- the objects in the coverings of the fibre products -/
  Y ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : C₀
  /-- the first projection `Y j ⟶ X i₁` -/
  p₁ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
  /-- the second projection `Y j ⟶ X i₂` -/
  p₂ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
  w ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : F.map (p₁ j) ≫ f i₁ = F.map (p₂ j) ≫ f i₂

namespace PreOneHypercoverDenseData

attribute [reassoc] w

variable {F} {X : C} (data : PreOneHypercoverDenseData.{w} F X)

/-- The pre-`1`-hypercover induced by a `PreOneHypercoverDenseData` structure. -/
@[simps]
/--
Definition of `toPreOneHypercover` / `toPreOneHypercover` 的定义

English:
definition toPreOneHypercover
  signature: : PreOneHypercover X where
  body: data.I₀
  X i := F.obj (data.X i)
  f i := data.f i
  I₁ := data.I₁
  Y _ _ j := F.obj (data.Y j)
  p₁ _ _ j := F.map (data.p₁ j)
  p₂ _ _ j := F.map (data.p₂ j)
  w := data.w

中文:
定义 toPreOneHypercover
  签名: : PreOneHypercover X where
  定义体: data.I₀
  X i := F.obj (data.X i)
  f i := data.f i
  I₁ := data.I₁
  Y _ _ j := F.obj (data.Y j)
  p₁ _ _ j := F.map (data.p₁ j)
  p₂ _ _ j := F.map (data.p₂ j)
  w := data.w

Depends on / 依赖: data.I
-/
def toPreOneHypercover : PreOneHypercover X where
  I₀ := data.I₀
  X i := F.obj (data.X i)
  f i := data.f i
  I₁ := data.I₁
  Y _ _ j := F.obj (data.Y j)
  p₁ _ _ j := F.map (data.p₁ j)
  p₂ _ _ j := F.map (data.p₂ j)
  w := data.w

/--
Definition of `I₁'` / `I₁'` 的定义

English:
abbreviation I₁'
  signature: : Type w
  body: Sigma (fun (i : data.I₀ × data.I₀) => data.I₁ i.1 i.2)

中文:
缩写 I₁'
  签名: : Type w
  定义体: Sigma (fun (i : data.I₀ × data.I₀) => data.I₁ i.1 i.2)

Depends on / 依赖: data.I
-/
abbrev I₁' : Type w := Sigma (fun (i : data.I₀ × data.I₀) => data.I₁ i.1 i.2)

/-- The shape of the multiforks attached to `data : F.PreOneHypercoverDenseData X`. -/
@[simps]
/--
Definition of `multicospanShape` / `multicospanShape` 的定义

English:
definition multicospanShape
  signature: : MulticospanShape where
  body: data.I₀
  R := data.I₁'
  fst j := j.1.1
  snd j := j.1.2

中文:
定义 multicospanShape
  签名: : MulticospanShape where
  定义体: data.I₀
  R := data.I₁'
  fst j := j.1.1
  snd j := j.1.2

Depends on / 依赖: data.I
-/
def multicospanShape : MulticospanShape where
  L := data.I₀
  R := data.I₁'
  fst j := j.1.1
  snd j := j.1.2

/-- The diagram of the multiforks attached to `data : F.PreOneHypercoverDenseData X`. -/
@[simps]
/--
Definition of `multicospanIndex` / `multicospanIndex` 的定义

English:
definition multicospanIndex
  signature: (P : C₀ᵒᵖ ⥤ A)
  body: P.obj (Opposite.op (data.X i))
  right j := P.obj (Opposite.op (data.Y j.2))
  fst j := P.map ((data.p₁ j.2).op)
  snd j := P.map ((data.p₂ j.2).op)

中文:
定义 multicospanIndex
  签名: (P : C₀ᵒᵖ ⥤ A)
  定义体: P.obj (Opposite.op (data.X i))
  right j := P.obj (Opposite.op (data.Y j.2))
  fst j := P.map ((data.p₁ j.2).op)
  snd j := P.map ((data.p₂ j.2).op)

Depends on / 依赖: Opposite, Opposite.op, P.obj, data.X
-/
def multicospanIndex (P : C₀ᵒᵖ ⥤ A) : MulticospanIndex data.multicospanShape A where
  left i := P.obj (Opposite.op (data.X i))
  right j := P.obj (Opposite.op (data.Y j.2))
  fst j := P.map ((data.p₁ j.2).op)
  snd j := P.map ((data.p₂ j.2).op)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functoriality of the diagrams attached to `data : F.PreOneHypercoverDenseData X`
with respect to morphisms in `C₀ᵒᵖ ⥤ A`. -/
@[simps]
/--
Definition of `multicospanMap` / `multicospanMap` 的定义

English:
definition multicospanMap
  signature: {P Q : C₀ᵒᵖ ⥤ A} (f : P ⟶ Q)
  body: match x with
    | WalkingMulticospan.left i => f.app _
    | WalkingMulticospan.right j => f.app _
  naturality := by
    rintro (i₁ | j₁) (i₂ | j₂) (_ | _) <;>
    simp [MulticospanIndex.multicospan]

中文:
定义 multicospanMap
  签名: {P Q : C₀ᵒᵖ ⥤ A} (f : P ⟶ Q)
  定义体: match x with
    | WalkingMulticospan.left i => f.app _
    | WalkingMulticospan.right j => f.app _
  naturality := by
    rintro (i₁ | j₁) (i₂ | j₂) (_ | _) <;>
    simp [MulticospanIndex.multicospan]
-/
def multicospanMap {P Q : C₀ᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (data.multicospanIndex P).multicospan ⟶ (data.multicospanIndex Q).multicospan where
  app x := match x with
    | WalkingMulticospan.left i => f.app _
    | WalkingMulticospan.right j => f.app _
  naturality := by
    rintro (i₁ | j₁) (i₂ | j₂) (_ | _) <;>
    simp [MulticospanIndex.multicospan]

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism between the diagrams attached to `data : F.PreOneHypercoverDenseData X`
that are induced by isomorphisms in `C₀ᵒᵖ ⥤ A`. -/
@[simps]
/--
Definition of `multicospanMapIso` / `multicospanMapIso` 的定义

English:
definition multicospanMapIso
  signature: {P Q : C₀ᵒᵖ ⥤ A} (e : P ≅ Q)
  body: data.multicospanMap e.hom
  inv := data.multicospanMap e.inv

中文:
定义 multicospanMapIso
  签名: {P Q : C₀ᵒᵖ ⥤ A} (e : P ≅ Q)
  定义体: data.multicospanMap e.hom
  inv := data.multicospanMap e.inv

Depends on / 依赖: data.multicospanMap, e.hom, multicospanMap
-/
def multicospanMapIso {P Q : C₀ᵒᵖ ⥤ A} (e : P ≅ Q) :
    (data.multicospanIndex P).multicospan ≅ (data.multicospanIndex Q).multicospan where
  hom := data.multicospanMap e.hom
  inv := data.multicospanMap e.inv

/-- Given `data : F.PreOneHypercoverDenseData X`, an object `W₀ : C₀` and two
morphisms `p₁ : W₀ ⟶ data.X i₁` and `p₂ : W₀ ⟶ data.X i₂`, this is the sieve of `W₀`
consisting of morphisms `g : Z₀ ⟶ W₀` such that there exists a morphism `Z₀ ⟶ data.Y j`
such that `g ≫ p₁ = h ≫ data.p₁ j` and `g ≫ p₂ = h ≫ data.p₂ j`. -/
@[simps]
/--
Definition of `sieve₁₀` / `sieve₁₀` 的定义

English:
definition sieve₁₀
  signature: {i₁ i₂ : data.I₀} {W₀ : C₀} (p₁ : W₀ ⟶ data.X i₁) (p₂ : W₀ ⟶ data.X i₂)
  body: exists (j : data.I₁ i₁ i₂) (h : Z₀ ⟶ data.Y j),
    g ≫ p₁ = h ≫ data.p₁ j ∧ g ≫ p₂ = h ≫ data.p₂ j
  downward_closed := by
    rintro Z Z' g ⟨j, h, fac₁, fac₂⟩ φ
    exact ⟨j, φ ≫ h, by simpa using φ ≫= fac₁, by simpa using φ ≫= fac₂⟩

中文:
定义 sieve₁₀
  签名: {i₁ i₂ : data.I₀} {W₀ : C₀} (p₁ : W₀ ⟶ data.X i₁) (p₂ : W₀ ⟶ data.X i₂)
  定义体: exists (j : data.I₁ i₁ i₂) (h : Z₀ ⟶ data.Y j),
    g ≫ p₁ = h ≫ data.p₁ j ∧ g ≫ p₂ = h ≫ data.p₂ j
  downward_closed := by
    rintro Z Z' g ⟨j, h, fac₁, fac₂⟩ φ
    exact ⟨j, φ ≫ h, by simpa using φ ≫= fac₁, by simpa using φ ≫= fac₂⟩

Depends on / 依赖: data.I, data.Y
-/
def sieve₁₀ {i₁ i₂ : data.I₀} {W₀ : C₀} (p₁ : W₀ ⟶ data.X i₁) (p₂ : W₀ ⟶ data.X i₂) :
    Sieve W₀ where
  arrows Z₀ g := exists (j : data.I₁ i₁ i₂) (h : Z₀ ⟶ data.Y j),
    g ≫ p₁ = h ≫ data.p₁ j ∧ g ≫ p₂ = h ≫ data.p₂ j
  downward_closed := by
    rintro Z Z' g ⟨j, h, fac₁, fac₂⟩ φ
    exact ⟨j, φ ≫ h, by simpa using φ ≫= fac₁, by simpa using φ ≫= fac₂⟩

end PreOneHypercoverDenseData

/--
Definition of `OneHypercoverDenseData` / `OneHypercoverDenseData` 的定义

English:
structure OneHypercoverDenseData
  parameters: (S : C)
  extends: PreOneHypercoverDenseData.{w} F S
  axioms and operations (2):
    - mem₀ : toPreOneHypercoverDenseData.toPreOneHypercover.sieve₀ in J S
    - mem₁₀((i₁ i₂ : I₀) ⦃W₀) : C₀⦄ (p₁ : W₀ ⟶ X i₁) (p₂ : W₀ ⟶ X i₂) (w : F.map p₁ ≫ f i₁ = F.map p₂ ≫ f i₂) : toPreOneHypercoverDenseData.sieve₁₀ p₁ p₂ in J₀ W₀

中文:
结构 OneHypercoverDenseData
  参数: (S : C)
  继承: PreOneHypercoverDenseData.{w} F S
  公理与运算 (2 个):
    - mem₀ : toPreOneHypercoverDenseData.toPreOneHypercover.sieve₀ in J S
    - mem₁₀((i₁ i₂ : I₀) ⦃W₀) : C₀⦄ (p₁ : W₀ ⟶ X i₁) (p₂ : W₀ ⟶ X i₂) (w : F.map p₁ ≫ f i₁ = F.map p₂ ≫ f i₂) : toPreOneHypercoverDenseData.sieve₁₀ p₁ p₂ in J₀ W₀
-/
structure OneHypercoverDenseData (S : C) extends PreOneHypercoverDenseData.{w} F S where
  mem₀ : toPreOneHypercoverDenseData.toPreOneHypercover.sieve₀ in J S
  mem₁₀ (i₁ i₂ : I₀) ⦃W₀ : C₀⦄ (p₁ : W₀ ⟶ X i₁) (p₂ : W₀ ⟶ X i₂)
    (w : F.map p₁ ≫ f i₁ = F.map p₂ ≫ f i₂) :
    toPreOneHypercoverDenseData.sieve₁₀ p₁ p₂ in J₀ W₀

/--
Definition of `IsOneHypercoverDense` / `IsOneHypercoverDense` 的定义

English:
class IsOneHypercoverDense
  parameters: : Prop where
  axioms and operations (1):
    - nonempty_oneHypercoverDenseData((X : C)) : Nonempty (OneHypercoverDenseData.{w} F J₀ J X)

中文:
类 IsOneHypercoverDense
  参数: : 命题 where
  公理与运算 (1 个):
    - nonempty_oneHypercoverDenseData((X : C)) : Nonempty (OneHypercoverDenseData.{w} F J₀ J X)
-/
class IsOneHypercoverDense : Prop where
  nonempty_oneHypercoverDenseData (X : C) :
    Nonempty (OneHypercoverDenseData.{w} F J₀ J X)

section

variable [IsOneHypercoverDense.{w} F J₀ J]

/--
Definition of `oneHypercoverDenseData` / `oneHypercoverDenseData` 的定义

English:
definition oneHypercoverDenseData
  signature: (X : C)
  body: (IsOneHypercoverDense.nonempty_oneHypercoverDenseData X).some

中文:
定义 oneHypercoverDenseData
  签名: (X : C)
  定义体: (IsOneHypercoverDense.nonempty_oneHypercoverDenseData X).some

Depends on / 依赖: IsOneHypercoverDense, IsOneHypercoverDense.nonempty_oneHypercoverDenseData, nonempty_oneHypercoverDenseData
-/
noncomputable def oneHypercoverDenseData (X : C) : F.OneHypercoverDenseData J₀ J X :=
  (IsOneHypercoverDense.nonempty_oneHypercoverDenseData X).some

/--
lemma `isDenseSubsite_of_isOneHypercoverDense` / 引理 `isDenseSubsite_of_isOneHypercoverDense`

English:
lemma isDenseSubsite_of_isOneHypercoverDense
  statement: [F.IsLocallyFull J] [F.IsLocallyFaithful J]
  proof: ⟨fun X => by
    refine J.superset_covering ?_ (F.oneHypercoverDenseData J₀ J X).mem₀
    rintro Y _ ⟨_, a, _, h, rfl⟩
    cases h
    exact ⟨{ fac := rfl, ..}⟩⟩
  functorPushforward_mem_iff := h

中文:
引理 isDenseSubsite_of_isOneHypercoverDense
  结论: [F.IsLocallyFull J] [F.IsLocallyFaithful J]
  证明: ⟨fun X => by
    refine J.superset_covering ?_ (F.oneHypercoverDenseData J₀ J X).mem₀
    rintro Y _ ⟨_, a, _, h, rfl⟩
    cases h
    exact ⟨{ fac := rfl, ..}⟩⟩
  functorPushforward_mem_iff := h

Depends on / 依赖: F.oneHypercoverDenseData, J.superset_covering, functorPushforward_mem_iff, oneHypercoverDenseData, superset_covering
-/
lemma isDenseSubsite_of_isOneHypercoverDense [F.IsLocallyFull J] [F.IsLocallyFaithful J]
    (h : forall {X₀ : C₀} {S₀ : Sieve X₀},
      Sieve.functorPushforward F S₀ in J.sieves (F.obj X₀) ↔ S₀ in J₀.sieves X₀) :
    IsDenseSubsite J₀ J F where
  isCoverDense' := ⟨fun X => by
    refine J.superset_covering ?_ (F.oneHypercoverDenseData J₀ J X).mem₀
    rintro Y _ ⟨_, a, _, h, rfl⟩
    cases h
    exact ⟨{ fac := rfl, ..}⟩⟩
  functorPushforward_mem_iff := h

end

variable [IsDenseSubsite J₀ J F]

variable {F J₀ J} in
/--
lemma `IsOneHypercoverDense.of_hasPullbacks` / 引理 `IsOneHypercoverDense.of_hasPullbacks`

English:
lemma IsOneHypercoverDense.of_hasPullbacks
  statement: [HasPullbacks C] [F.Full] [F.Faithful]
  proof: by
    choose ι U f hf using hF
    exact ⟨{
      I₀ := ι S
      X := U S
      f := f S
      I₁ i j := ι (pullback (f _ i) (f _ j))
      Y i j := U (pullback (f _ i) (f _ j))
      p₁ i j k := F.preimage (f _ k ≫ pullback.fst _ _)
      p₂ i j k := F.preimage (f _ k ≫ pullback.snd _ _)
      w 

中文:
引理 IsOneHypercoverDense.of_hasPullbacks
  结论: [HasPullbacks C] [F.Full] [F.Faithful]
  证明: by
    choose ι U f hf using hF
    exact ⟨{
      I₀ := ι S
      X := U S
      f := f S
      I₁ i j := ι (pullback (f _ i) (f _ j))
      Y i j := U (pullback (f _ i) (f _ j))
      p₁ i j k := F.preimage (f _ k ≫ pullback.fst _ _)
      p₂ i j k := F.preimage (f _ k ≫ pullback.snd _ _)
      w 

Depends on / 依赖: F.preimage, IsCoverDense, IsCoverDense.functorPullback_pushforward_covering, IsDenseSubsite, IsDenseSubsite.isCoverDense, J.pullba, J.superset_covering, condition, functorPullback_pushforward_covering, functorPushforward_mem_iff, isCoverDense, preimage, pullba, pullback, pullback.condition, pullback.fst, pullback.snd, superset_covering
-/
lemma IsOneHypercoverDense.of_hasPullbacks [HasPullbacks C] [F.Full] [F.Faithful]
    (hF : forall (S : C), exists (ι : Type w) (U : ι -> C₀) (f : forall i, F.obj (U i) ⟶ S),
      Sieve.ofArrows _ f in J S) :
    IsOneHypercoverDense.{w} F J₀ J where
  nonempty_oneHypercoverDenseData S := by
    choose ι U f hf using hF
    exact ⟨{
      I₀ := ι S
      X := U S
      f := f S
      I₁ i j := ι (pullback (f _ i) (f _ j))
      Y i j := U (pullback (f _ i) (f _ j))
      p₁ i j k := F.preimage (f _ k ≫ pullback.fst _ _)
      p₂ i j k := F.preimage (f _ k ≫ pullback.snd _ _)
      w i j k := by simp [pullback.condition]
      mem₀ := hf S
      mem₁₀ i j W₀ p₁ p₂ hp := by
        have := IsDenseSubsite.isCoverDense J₀ J F
        rw [← functorPushforward_mem_iff J₀ J F]
        refine J.superset_covering ?_
          (IsCoverDense.functorPullback_pushforward_covering
            ⟨_, J.pullback_stable (pullback.lift _ _ hp) (hf (pullback (f _ i) (f _ j)))⟩)
        rintro T _ ⟨Z, q, r, ⟨_, s, _, ⟨k⟩, fac⟩, rfl⟩
        have fac₁ := fac =≫ pullback.fst _ _
        have fac₂ := fac =≫ pullback.snd _ _
        simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at fac₁ fac₂
        exact ⟨Z, q, r, ⟨k, F.preimage s, F.map_injective (by simp [fac₁]),
          F.map_injective (by simp [fac₂])⟩, rfl⟩ }⟩

namespace OneHypercoverDenseData

variable {F J₀ J}

section

variable {X : C} (data : OneHypercoverDenseData.{w} F J₀ J X)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `mem₁` / 引理 `mem₁`

English:
lemma mem₁
  statement: (i₁ i₂ : data.I₀) {W : C} (p₁ : W ⟶ F.obj (data.X i₁)) (p₂ : W ⟶ F.obj (data.X i₂))
  proof: by
  have := IsDenseSubsite.isCoverDense J₀ J F
  let S := Sieve.bind (Sieve.coverByImage F W).arrows
    (fun Y f hf => ((F.imageSieve (hf.some.map ≫ p₁) ⊓
        F.imageSieve (hf.some.map ≫ p₂)).functorPushforward F).pullback hf.some.lift)
  let T := Sieve.bind S.arrows (fun Z g hg => by
    letI

中文:
引理 mem₁
  结论: (i₁ i₂ : data.I₀) {W : C} (p₁ : W ⟶ F.obj (data.X i₁)) (p₂ : W ⟶ F.obj (data.X i₂))
  证明: by
  have := IsDenseSubsite.isCoverDense J₀ J F
  let S := Sieve.bind (Sieve.coverByImage F W).arrows
    (fun Y f hf => ((F.imageSieve (hf.some.map ≫ p₁) ⊓
        F.imageSieve (hf.some.map ≫ p₂)).functorPushforward F).pullback hf.some.lift)
  let T := Sieve.bind S.arrows (fun Z g hg => by
    letI

Depends on / 依赖: F.imageSieve, IsDenseSubsite, IsDenseSubsite.isCoverDense, J.bind_coveri, Presieve, Presieve.getFunctorPushforwardStructure, S.arrows, Sieve.bind, Sieve.coverByImage, Sieve.functorPushforward, Sieve.pullback, arrows, bindStruct, bind_coveri, coverByImage, data.sieve, functorPushforward, getFunctorPushforwardStructure, hf.some.lift, hf.some.map
-/
lemma mem₁ (i₁ i₂ : data.I₀) {W : C} (p₁ : W ⟶ F.obj (data.X i₁)) (p₂ : W ⟶ F.obj (data.X i₂))
    (w : p₁ ≫ data.f i₁ = p₂ ≫ data.f i₂) : data.toPreOneHypercover.sieve₁ p₁ p₂ in J W := by
  have := IsDenseSubsite.isCoverDense J₀ J F
  let S := Sieve.bind (Sieve.coverByImage F W).arrows
    (fun Y f hf => ((F.imageSieve (hf.some.map ≫ p₁) ⊓
        F.imageSieve (hf.some.map ≫ p₂)).functorPushforward F).pullback hf.some.lift)
  let T := Sieve.bind S.arrows (fun Z g hg => by
    letI str := Presieve.getFunctorPushforwardStructure hg.bindStruct.hg
    exact Sieve.pullback str.lift
      (Sieve.functorPushforward F (data.sieve₁₀ str.cover.1.choose str.cover.2.choose)))
  have hS : S in J W := by
    apply J.bind_covering
    · apply is_cover_of_isCoverDense
    · intro Y f hf
      apply J.pullback_stable
      rw [Functor.functorPushforward_mem_iff J₀]
      apply J₀.intersection_covering
      all_goals apply IsDenseSubsite.imageSieve_mem J₀ J
  have hT : T in J W := J.bind_covering hS (fun Z g hg => by
    apply J.pullback_stable
    rw [Functor.functorPushforward_mem_iff J₀]
    let str := Presieve.getFunctorPushforwardStructure hg.bindStruct.hg
    apply data.mem₁₀
    simp only [str.cover.1.choose_spec, str.cover.2.choose_spec, assoc, w])
  refine J.superset_covering ?_ hT
  rintro U f ⟨V, a, b, hb, h, _, rfl⟩
  let str := Presieve.getFunctorPushforwardStructure hb.bindStruct.hg
  obtain ⟨W₀, c : _ ⟶ _, d, ⟨j, e, h₁, h₂⟩, fac⟩ := h
  dsimp
  refine ⟨j, d ≫ F.map e, ?_, ?_⟩
  · rw [assoc, assoc, ← F.map_comp, ← h₁, F.map_comp, ← reassoc_of% fac,
      str.cover.1.choose_spec, ← reassoc_of% str.fac,
      Presieve.CoverByImageStructure.fac_assoc,
      Presieve.BindStruct.fac_assoc]
  · rw [assoc, assoc, ← F.map_comp, ← h₂, F.map_comp, ← reassoc_of% fac,
      str.cover.2.choose_spec, ← reassoc_of% str.fac,
      Presieve.CoverByImageStructure.fac_assoc,
      Presieve.BindStruct.fac_assoc]

/-- The `1`-hypercover associated to a `OneHypercoverDenseData` structure. -/
@[simps toPreOneHypercover]
/--
Definition of `toOneHypercover` / `toOneHypercover` 的定义

English:
definition toOneHypercover
  signature: {X : C} (data : F.OneHypercoverDenseData J₀ J X)
  body: data.toPreOneHypercover
  mem₀ := data.mem₀
  mem₁ := data.mem₁

中文:
定义 toOneHypercover
  签名: {X : C} (data : F.OneHypercoverDenseData J₀ J X)
  定义体: data.toPreOneHypercover
  mem₀ := data.mem₀
  mem₁ := data.mem₁

Depends on / 依赖: data.toPreOneHypercover, toPreOneHypercover
-/
def toOneHypercover {X : C} (data : F.OneHypercoverDenseData J₀ J X) :
    J.OneHypercover X where
  toPreOneHypercover := data.toPreOneHypercover
  mem₀ := data.mem₀
  mem₁ := data.mem₁

variable {X : C} (data : OneHypercoverDenseData.{w} F J₀ J X) {X₀ : C₀} (f : F.obj X₀ ⟶ X)

/--
Definition of `SieveStruct` / `SieveStruct` 的定义

English:
structure SieveStruct
  parameters: {Y₀ : C₀} (g : Y₀ ⟶ X₀)
  axioms and operations (3):
    - i₀ : data.I₀
    - q : F.obj Y₀ ⟶ F.obj (data.X i₀)
    - fac : q ≫ data.f i₀ = F.map g ≫ f  [default: by simp]

中文:
结构 SieveStruct
  参数: {Y₀ : C₀} (g : Y₀ ⟶ X₀)
  公理与运算 (3 个):
    - i₀ : data.I₀
    - q : F.obj Y₀ ⟶ F.obj (data.X i₀)
    - fac : q ≫ data.f i₀ = F.map g ≫ f  [默认: by simp]
-/
structure SieveStruct {Y₀ : C₀} (g : Y₀ ⟶ X₀) where
  /-- the index of the intermediate object -/
  i₀ : data.I₀
  /-- the morphism that is part of the factorization `fac`. -/
  q : F.obj Y₀ ⟶ F.obj (data.X i₀)
  fac : q ≫ data.f i₀ = F.map g ≫ f := by simp

attribute [reassoc (attr := simp)] SieveStruct.fac

/-- Given `data : OneHypercoverDenseData F J₀ J X` and a morphism `f : F.obj X₀ ⟶ X`,
this is the sieve of `X₀` consisting of morphisms `g : Y₀ ⟶ X₀` such that there
exists `i₀ : data.I₀`, `q : F.obj Y₀ ⟶ F.obj (data.X i₀)` such that
we have a factorization `q ≫ data.f i₀ = F.map g ≫ f`. -/
@[simps]
/--
Definition of `sieve` / `sieve` 的定义

English:
definition sieve
  signature: : Sieve X₀ where
  body: Nonempty (SieveStruct data f g)
  downward_closed := by
    rintro Y₀ Z₀ g ⟨h⟩ p
    exact ⟨{ i₀ := h.i₀, q := F.map p ≫ h.q, fac := by rw [assoc, h.fac, map_comp_assoc]}⟩

中文:
定义 sieve
  签名: : Sieve X₀ where
  定义体: Nonempty (SieveStruct data f g)
  downward_closed := by
    rintro Y₀ Z₀ g ⟨h⟩ p
    exact ⟨{ i₀ := h.i₀, q := F.map p ≫ h.q, fac := by rw [assoc, h.fac, map_comp_assoc]}⟩

Depends on / 依赖: Nonempty, SieveStruct
-/
def sieve : Sieve X₀ where
  arrows Y₀ g := Nonempty (SieveStruct data f g)
  downward_closed := by
    rintro Y₀ Z₀ g ⟨h⟩ p
    exact ⟨{ i₀ := h.i₀, q := F.map p ≫ h.q, fac := by rw [assoc, h.fac, map_comp_assoc]}⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `sieve_mem` / 引理 `sieve_mem`

English:
lemma sieve_mem
  statement: sieve data f in J₀ X₀
  proof: by
  have := IsDenseSubsite.isCoverDense J₀ J F
  have := IsDenseSubsite.isLocallyFull J₀ J F
  rw [← functorPushforward_mem_iff J₀ J F]
  let R : ⦃W : C⦄ -> ⦃p : W ⟶ F.obj X₀⦄ ->
    (Sieve.pullback f data.toOneHypercover.sieve₀).arrows p -> Sieve W := fun W p hp =>
      Sieve.bind (Sieve.coverByI

中文:
引理 sieve_mem
  结论: sieve data f in J₀ X₀
  证明: by
  have := IsDenseSubsite.isCoverDense J₀ J F
  have := IsDenseSubsite.isLocallyFull J₀ J F
  rw [← functorPushforward_mem_iff J₀ J F]
  let R : ⦃W : C⦄ -> ⦃p : W ⟶ F.obj X₀⦄ ->
    (Sieve.pullback f data.toOneHypercover.sieve₀).arrows p -> Sieve W := fun W p hp =>
      Sieve.bind (Sieve.coverByI

Depends on / 依赖: F.imageSieve, F.obj, IsDenseSubsite, IsDenseSubsite.isCoverDense, IsDenseSubsite.isLocallyFull, J.bind_covering, J.pullback_stable, J.superset_covering, Sieve.bind, Sieve.coverByImage, Sieve.functorPushforward, Sieve.pullback, arrows, bind_covering, coverByImage, data.toOneHypercover.mem, data.toOneHypercover.sieve, functorPushforward, functorPushforward_mem_iff, imageSieve
-/
lemma sieve_mem : sieve data f in J₀ X₀ := by
  have := IsDenseSubsite.isCoverDense J₀ J F
  have := IsDenseSubsite.isLocallyFull J₀ J F
  rw [← functorPushforward_mem_iff J₀ J F]
  let R : ⦃W : C⦄ -> ⦃p : W ⟶ F.obj X₀⦄ ->
    (Sieve.pullback f data.toOneHypercover.sieve₀).arrows p -> Sieve W := fun W p hp =>
      Sieve.bind (Sieve.coverByImage F W).arrows (fun U π hπ =>
        Sieve.pullback hπ.some.lift
          (Sieve.functorPushforward F (F.imageSieve (hπ.some.map ≫ p))))
  refine J.superset_covering ?_
    (J.bind_covering (J.pullback_stable f (data.toOneHypercover.mem₀)) (R := R)
    (fun W p hp => J.bind_covering (F.is_cover_of_isCoverDense J W) ?_))
  · rintro W' _ ⟨W, _, p, hp, ⟨Y₀, a, b, hb, ⟨U, c, d, ⟨x₁, w₁⟩, fac⟩, rfl⟩, rfl⟩
    have hp' := Sieve.ofArrows.fac hp
    dsimp at hp'
    refine ⟨U, x₁, d, ⟨Sieve.ofArrows.i hp,
      F.map c ≫ (Nonempty.some hb).map ≫ Sieve.ofArrows.h hp, ?_⟩, ?_⟩
    · rw [w₁, assoc, assoc, assoc, assoc, hp']
    · rw [w₁, assoc, ← reassoc_of% fac, hb.some.fac_assoc]
  · intro U π hπ
    apply J.pullback_stable
    apply functorPushforward_imageSieve_mem

end

section

namespace isSheaf_iff

variable {data : forall X, F.OneHypercoverDenseData J₀ J X} {G : Cᵒᵖ ⥤ A}
  (hG₀ : Presheaf.IsSheaf J₀ (F.op ⋙ G))
  (hG : forall (X : C), IsLimit ((data X).toOneHypercover.multifork G))
  {X : C} (S : J.Cover X)

section

variable {S} (s : Multifork (S.index G))

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def liftAux (i : (data X).I₀)
  body: hG₀.amalgamate ⟨_, cover_lift F J₀ _ (J.pullback_stable ((data X).f i) S.2)⟩
    (fun ⟨W₀, a, ha⟩ => s.ι ⟨_, F.map a ≫ (data X).f i, ha⟩) (by
      rintro ⟨W₀, a, ha⟩ ⟨Z₀, b, hb⟩ ⟨U₀, p₁, p₂, fac⟩
      exact s.condition
        { fst := ⟨_, _, ha⟩
          snd := ⟨_, _, hb⟩
          r := ⟨_, F.ma

中文:
定义 noncomputable
  签名: def liftAux (i : (data X).I₀)
  定义体: hG₀.amalgamate ⟨_, cover_lift F J₀ _ (J.pullback_stable ((data X).f i) S.2)⟩
    (fun ⟨W₀, a, ha⟩ => s.ι ⟨_, F.map a ≫ (data X).f i, ha⟩) (by
      rintro ⟨W₀, a, ha⟩ ⟨Z₀, b, hb⟩ ⟨U₀, p₁, p₂, fac⟩
      exact s.condition
        { fst := ⟨_, _, ha⟩
          snd := ⟨_, _, hb⟩
          r := ⟨_, F.ma
-/
private noncomputable def liftAux (i : (data X).I₀) : s.pt ⟶ G.obj (op (F.obj ((data X).X i))) :=
  hG₀.amalgamate ⟨_, cover_lift F J₀ _ (J.pullback_stable ((data X).f i) S.2)⟩
    (fun ⟨W₀, a, ha⟩ => s.ι ⟨_, F.map a ≫ (data X).f i, ha⟩) (by
      rintro ⟨W₀, a, ha⟩ ⟨Z₀, b, hb⟩ ⟨U₀, p₁, p₂, fac⟩
      exact s.condition
        { fst := ⟨_, _, ha⟩
          snd := ⟨_, _, hb⟩
          r := ⟨_, F.map p₁, F.map p₂, by
              simp only [← Functor.map_comp_assoc, fac]⟩ })

/--
lemma `liftAux_fac` / 引理 `liftAux_fac`

English:
lemma liftAux_fac
  statement: {i : (data X).I₀} {W₀ : C₀} (a : W₀ ⟶ (data X).X i)
  proof: hG₀.amalgamate_map _ _ _ ⟨W₀, a, ha⟩

中文:
引理 liftAux_fac
  结论: {i : (data X).I₀} {W₀ : C₀} (a : W₀ ⟶ (data X).X i)
  证明: hG₀.amalgamate_map _ _ _ ⟨W₀, a, ha⟩
-/
private lemma liftAux_fac {i : (data X).I₀} {W₀ : C₀} (a : W₀ ⟶ (data X).X i)
    (ha : S (F.map a ≫ (data X).f i)) :
    liftAux hG₀ s i ≫ G.map (F.map a).op = s.ι ⟨_, F.map a ≫ (data X).f i, ha⟩ :=
  hG₀.amalgamate_map _ _ _ ⟨W₀, a, ha⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def lift
  body: Multifork.IsLimit.lift (hG X) (fun i => liftAux hG₀ s i) (by
    rintro ⟨⟨i₁, i₂⟩, j⟩
    dsimp at i₁ i₂ j ⊢
    refine Presheaf.IsSheaf.hom_ext
      hG₀ ⟨_, cover_lift F J₀ _
        (J.pullback_stable (F.map ((data X).p₁ j) ≫ (data X).f i₁) S.2)⟩ _ _ ?_
    rintro ⟨W₀, a, ha⟩
    dsimp
    simp o

中文:
定义 noncomputable
  签名: def lift
  定义体: Multifork.IsLimit.lift (hG X) (fun i => liftAux hG₀ s i) (by
    rintro ⟨⟨i₁, i₂⟩, j⟩
    dsimp at i₁ i₂ j ⊢
    refine Presheaf.IsSheaf.hom_ext
      hG₀ ⟨_, cover_lift F J₀ _
        (J.pullback_stable (F.map ((data X).p₁ j) ≫ (data X).f i₁) S.2)⟩ _ _ ?_
    rintro ⟨W₀, a, ha⟩
    dsimp
    simp o
-/
private noncomputable def lift : s.pt ⟶ G.obj (op X) :=
  Multifork.IsLimit.lift (hG X) (fun i => liftAux hG₀ s i) (by
    rintro ⟨⟨i₁, i₂⟩, j⟩
    dsimp at i₁ i₂ j ⊢
    refine Presheaf.IsSheaf.hom_ext
      hG₀ ⟨_, cover_lift F J₀ _
        (J.pullback_stable (F.map ((data X).p₁ j) ≫ (data X).f i₁) S.2)⟩ _ _ ?_
    rintro ⟨W₀, a, ha⟩
    dsimp
    simp only [assoc, ← Functor.map_comp, ← op_comp]
    have ha₁ : S (F.map (a ≫ (data X).p₁ j) ≫ (data X).f i₁) := by simpa using ha
    have ha₂ : S (F.map (a ≫ (data X).p₂ j) ≫ (data X).f i₂) := by
      rwa [Functor.map_comp_assoc, ← (data X).w j]
    rw [liftAux_fac _ _ _ ha₁]; rw [liftAux_fac _ _ _ ha₂]
    congr 2
    rw [map_comp_assoc]; rw [map_comp_assoc]; rw [(data X).w j])

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `lift_map` / 引理 `lift_map`

English:
lemma lift_map
  given: (i : (data X).I₀)
  proof: Multifork.IsLimit.fac _ _ _ _

中文:
引理 lift_map
  条件: (i : (data X).I₀)
  证明: Multifork.IsLimit.fac _ _ _ _
-/
private lemma lift_map (i : (data X).I₀) :
    lift hG₀ hG s ≫ G.map ((data X).f i).op = liftAux hG₀ s i :=
  Multifork.IsLimit.fac _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `fac` / 引理 `fac`

English:
lemma fac
  given: (a : S.Arrow)
  proof: Multifork.IsLimit.hom_ext (hG _) (fun i =>
    Presheaf.IsSheaf.hom_ext hG₀
      ⟨_, cover_lift F J₀ _
        (J.pullback_stable ((data a.Y).f i ≫ a.f) (data X).mem₀)⟩ _ _ (by
        rintro ⟨X₀, b, ⟨_, c, _, h, fac₁⟩⟩
        obtain ⟨j⟩ := h
        refine Presheaf.IsSheaf.hom_ext hG₀
          ⟨

中文:
引理 fac
  条件: (a : S.Arrow)
  证明: Multifork.IsLimit.hom_ext (hG _) (fun i =>
    Presheaf.IsSheaf.hom_ext hG₀
      ⟨_, cover_lift F J₀ _
        (J.pullback_stable ((data a.Y).f i ≫ a.f) (data X).mem₀)⟩ _ _ (by
        rintro ⟨X₀, b, ⟨_, c, _, h, fac₁⟩⟩
        obtain ⟨j⟩ := h
        refine Presheaf.IsSheaf.hom_ext hG₀
          ⟨
-/
private lemma fac (a : S.Arrow) :
    lift hG₀ hG s ≫ G.map a.f.op = s.ι a :=
  Multifork.IsLimit.hom_ext (hG _) (fun i =>
    Presheaf.IsSheaf.hom_ext hG₀
      ⟨_, cover_lift F J₀ _
        (J.pullback_stable ((data a.Y).f i ≫ a.f) (data X).mem₀)⟩ _ _ (by
        rintro ⟨X₀, b, ⟨_, c, _, h, fac₁⟩⟩
        obtain ⟨j⟩ := h
        refine Presheaf.IsSheaf.hom_ext hG₀
          ⟨_, IsDenseSubsite.imageSieve_mem J₀ J F c⟩ _ _ ?_
        rintro ⟨Y₀, d, e, fac₂⟩
        dsimp at i j c fac₁ ⊢
        have he : S (F.map e ≫ (data X).f j) := by
          rw [fac₂]; rw [assoc]; rw [fac₁]
          simpa only [assoc] using S.1.downward_closed a.hf (F.map d ≫ F.map b ≫ (data a.Y).f i)
        simp only [assoc, ← Functor.map_comp, ← op_comp, ← fac₁]
        conv_lhs => simp only [op_comp, Functor.map_comp, assoc, lift_map_assoc]
        rw [← Functor.map_comp]; rw [← op_comp]; rw [← fac₂]; rw [liftAux_fac _ _ _ he]
        simpa using s.condition
          { fst := { hf := he, .. }
            snd := a
            r := ⟨_, 𝟙 _, F.map d ≫ F.map b ≫ (data a.Y).f i, by
              simp only [fac₁, fac₂, assoc, id_comp]⟩ }))

set_option backward.isDefEq.respectTransparency false in
variable {s} in
include hG hG₀ in
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {f₁ f₂ : s.pt ⟶ G.obj (op X)}
  proof: Multifork.IsLimit.hom_ext (hG X) (fun i => by
    refine Presheaf.IsSheaf.hom_ext hG₀
      ⟨_, cover_lift F J₀ _ (J.pullback_stable ((data X).f i) S.2)⟩ _ _ ?_
    rintro ⟨X₀, a, ha⟩
    dsimp
    simp only [assoc, ← Functor.map_comp]
    exact h ⟨_, _, ha⟩)

中文:
引理 hom_ext
  结论: {f₁ f₂ : s.pt ⟶ G.obj (op X)}
  证明: Multifork.IsLimit.hom_ext (hG X) (fun i => by
    refine Presheaf.IsSheaf.hom_ext hG₀
      ⟨_, cover_lift F J₀ _ (J.pullback_stable ((data X).f i) S.2)⟩ _ _ ?_
    rintro ⟨X₀, a, ha⟩
    dsimp
    simp only [assoc, ← Functor.map_comp]
    exact h ⟨_, _, ha⟩)
-/
private lemma hom_ext {f₁ f₂ : s.pt ⟶ G.obj (op X)}
    (h : forall (a : S.Arrow), f₁ ≫ G.map a.f.op = f₂ ≫ G.map a.f.op) : f₁ = f₂ :=
  Multifork.IsLimit.hom_ext (hG X) (fun i => by
    refine Presheaf.IsSheaf.hom_ext hG₀
      ⟨_, cover_lift F J₀ _ (J.pullback_stable ((data X).f i) S.2)⟩ _ _ ?_
    rintro ⟨X₀, a, ha⟩
    dsimp
    simp only [assoc, ← Functor.map_comp]
    exact h ⟨_, _, ha⟩)

end

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def isLimit
  body: Multifork.IsLimit.mk _
    (lift hG₀ hG) (fac hG₀ hG) (fun s _ hm =>
      hom_ext hG₀ hG (fun a => (hm a).trans (fac hG₀ hG s a).symm))

中文:
定义 noncomputable
  签名: def isLimit
  定义体: Multifork.IsLimit.mk _
    (lift hG₀ hG) (fac hG₀ hG) (fun s _ hm =>
      hom_ext hG₀ hG (fun a => (hm a).trans (fac hG₀ hG s a).symm))
-/
private noncomputable def isLimit : IsLimit (S.multifork G) :=
  Multifork.IsLimit.mk _
    (lift hG₀ hG) (fac hG₀ hG) (fun s _ hm =>
      hom_ext hG₀ hG (fun a => (hm a).trans (fac hG₀ hG s a).symm))

end isSheaf_iff

/--
lemma `isSheaf_iff` / 引理 `isSheaf_iff`

English:
lemma isSheaf_iff
  given: (data : forall X, F.OneHypercoverDenseData J₀ J X) (G : Cᵒᵖ ⥤ A)
  proof: by
  refine ⟨fun hG => ⟨op_comp_isSheaf F J₀ J ⟨_, hG⟩,
    fun X => ⟨(data X).toOneHypercover.isLimitMultifork ⟨G, hG⟩⟩⟩, fun ⟨hG₀, hG⟩ => ?_⟩
  rw [Presheaf.isSheaf_iff_multifork]
  replace hG := fun X => (hG X).some
  exact fun X S => ⟨isSheaf_iff.isLimit hG₀ hG S⟩

中文:
引理 isSheaf_iff
  条件: (data : 对任意 X, F.OneHypercoverDenseData J₀ J X) (G : Cᵒᵖ ⥤ A)
  证明: by
  refine ⟨fun hG => ⟨op_comp_isSheaf F J₀ J ⟨_, hG⟩,
    fun X => ⟨(data X).toOneHypercover.isLimitMultifork ⟨G, hG⟩⟩⟩, fun ⟨hG₀, hG⟩ => ?_⟩
  rw [Presheaf.isSheaf_iff_multifork]
  replace hG := fun X => (hG X).some
  exact fun X S => ⟨isSheaf_iff.isLimit hG₀ hG S⟩

Depends on / 依赖: Presheaf, Presheaf.isSheaf_iff_multifork, isLimit, isLimitMultifork, isSheaf_iff, isSheaf_iff.isLimit, isSheaf_iff_multifork, op_comp_isSheaf, replace, toOneHypercover, toOneHypercover.isLimitMultifork
-/
lemma isSheaf_iff (data : forall X, F.OneHypercoverDenseData J₀ J X) (G : Cᵒᵖ ⥤ A) :
    Presheaf.IsSheaf J G ↔
      Presheaf.IsSheaf J₀ (F.op ⋙ G) ∧
        forall (X : C), Nonempty (IsLimit ((data X).toOneHypercover.multifork G)) := by
  refine ⟨fun hG => ⟨op_comp_isSheaf F J₀ J ⟨_, hG⟩,
    fun X => ⟨(data X).toOneHypercover.isLimitMultifork ⟨G, hG⟩⟩⟩, fun ⟨hG₀, hG⟩ => ?_⟩
  rw [Presheaf.isSheaf_iff_multifork]
  replace hG := fun X => (hG X).some
  exact fun X S => ⟨isSheaf_iff.isLimit hG₀ hG S⟩

end

section

variable (data : forall X, OneHypercoverDenseData.{w} F J₀ J X)
  [HasLimitsOfSize.{w, w} A]

namespace essSurj

variable (G₀ : Sheaf J₀ A)

/--
Definition of `presheafObj` / `presheafObj` 的定义

English:
definition presheafObj
  signature: (X : C)
  body: multiequalizer ((data X).multicospanIndex G₀.obj)

中文:
定义 presheafObj
  签名: (X : C)
  定义体: multiequalizer ((data X).multicospanIndex G₀.obj)

Depends on / 依赖: multicospanIndex, multiequalizer
-/
noncomputable def presheafObj (X : C) : A :=
  multiequalizer ((data X).multicospanIndex G₀.obj)

/--
Definition of `presheafObjπ` / `presheafObjπ` 的定义

English:
definition presheafObjπ
  signature: (X : C) (i : (data X).I₀)
  body: Multiequalizer.ι ((data X).multicospanIndex G₀.obj) i

omit [IsDenseSubsite J₀ J F] in

中文:
定义 presheafObjπ
  签名: (X : C) (i : (data X).I₀)
  定义体: Multiequalizer.ι ((data X).multicospanIndex G₀.obj) i

omit [IsDenseSubsite J₀ J F] in

Depends on / 依赖: Multiequalizer, multicospanIndex
-/
noncomputable def presheafObjπ (X : C) (i : (data X).I₀) :
    presheafObj data G₀ X ⟶ G₀.obj.obj (op ((data X).X i)) :=
  Multiequalizer.ι ((data X).multicospanIndex G₀.obj) i

omit [IsDenseSubsite J₀ J F] in
variable {data G₀} in
@[ext]
/--
lemma `presheafObj_hom_ext` / 引理 `presheafObj_hom_ext`

English:
lemma presheafObj_hom_ext
  statement: {X : C} {Z : A} {f g : Z ⟶ presheafObj data G₀ X}
  proof: Multiequalizer.hom_ext _ _ _ h

omit [IsDenseSubsite J₀ J F] in
@[reassoc]

中文:
引理 presheafObj_hom_ext
  结论: {X : C} {Z : A} {f g : Z ⟶ presheafObj data G₀ X}
  证明: Multiequalizer.hom_ext _ _ _ h

omit [IsDenseSubsite J₀ J F] in
@[reassoc]

Depends on / 依赖: Multiequalizer, Multiequalizer.hom_ext, hom_ext
-/
lemma presheafObj_hom_ext {X : C} {Z : A} {f g : Z ⟶ presheafObj data G₀ X}
    (h : forall (i : (data X).I₀), f ≫ presheafObjπ data G₀ X i = g ≫ presheafObjπ data G₀ X i) :
    f = g :=
  Multiequalizer.hom_ext _ _ _ h

omit [IsDenseSubsite J₀ J F] in
@[reassoc]
/--
lemma `presheafObj_condition` / 引理 `presheafObj_condition`

English:
lemma presheafObj_condition
  given: (X : C) (i i' : (data X).I₀) (j : (data X).I₁ i i')
  proof: Multiequalizer.condition ((data X).multicospanIndex G₀.obj) ⟨⟨i, i'⟩, j⟩

中文:
引理 presheafObj_condition
  条件: (X : C) (i i' : (data X).I₀) (j : (data X).I₁ i i')
  证明: Multiequalizer.condition ((data X).multicospanIndex G₀.obj) ⟨⟨i, i'⟩, j⟩

Depends on / 依赖: Multiequalizer, Multiequalizer.condition, condition, multicospanIndex
-/
lemma presheafObj_condition (X : C) (i i' : (data X).I₀) (j : (data X).I₁ i i') :
    presheafObjπ data G₀ X i ≫ G₀.obj.map ((data X).p₁ j).op =
    presheafObjπ data G₀ X i' ≫ G₀.obj.map ((data X).p₂ j).op :=
  Multiequalizer.condition ((data X).multicospanIndex G₀.obj) ⟨⟨i, i'⟩, j⟩

/--
lemma `presheafObj_mapPreimage_condition` / 引理 `presheafObj_mapPreimage_condition`

English:
lemma presheafObj_mapPreimage_condition
  proof: by
  refine Presheaf.IsSheaf.hom_ext G₀.property ⟨_,
    J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F p₁)
      (IsDenseSubsite.imageSieve_mem J₀ J F p₂)⟩ _ _ ?_
  intro ⟨W₀, a, ⟨b₁, h₁⟩, ⟨b₂, h₂⟩⟩
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, (data X).mem₁₀ i₁ i₂ b₁ b₂ (by

中文:
引理 presheafObj_mapPreimage_condition
  证明: by
  refine Presheaf.IsSheaf.hom_ext G₀.property ⟨_,
    J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F p₁)
      (IsDenseSubsite.imageSieve_mem J₀ J F p₂)⟩ _ _ ?_
  intro ⟨W₀, a, ⟨b₁, h₁⟩, ⟨b₂, h₂⟩⟩
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, (data X).mem₁₀ i₁ i₂ b₁ b₂ (by

Depends on / 依赖: Functor, Functor.map_comp, IsDenseSubsit, IsDenseSubsite, IsDenseSubsite.imageSieve_mem, IsDenseSubsite.mapPreimage_map_of_fac, IsSheaf, Presheaf, Presheaf.IsSheaf.hom_ext, hom_ext, imageSieve_mem, intersection_covering, mapPreimage_map_of_fac, map_comp, op_comp, property
-/
lemma presheafObj_mapPreimage_condition
    (X : C) (i₁ i₂ : (data X).I₀) {Y₀ : C₀}
    (p₁ : F.obj Y₀ ⟶ F.obj ((data X).X i₁)) (p₂ : F.obj Y₀ ⟶ F.obj ((data X).X i₂))
    (fac : p₁ ≫ (data X).f i₁ = p₂ ≫ (data X).f i₂) :
    presheafObjπ data G₀ X i₁ ≫ IsDenseSubsite.mapPreimage J F G₀ p₁ =
      presheafObjπ data G₀ X i₂ ≫ IsDenseSubsite.mapPreimage J F G₀ p₂ := by
  refine Presheaf.IsSheaf.hom_ext G₀.property ⟨_,
    J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F p₁)
      (IsDenseSubsite.imageSieve_mem J₀ J F p₂)⟩ _ _ ?_
  intro ⟨W₀, a, ⟨b₁, h₁⟩, ⟨b₂, h₂⟩⟩
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, (data X).mem₁₀ i₁ i₂ b₁ b₂ (by simp only [h₁, h₂, assoc, fac])⟩ _ _ ?_
  intro ⟨U₀, c, ⟨j, t, fac₁, fac₂⟩⟩
  simp only [assoc, ← Functor.map_comp, ← op_comp,
    IsDenseSubsite.mapPreimage_map_of_fac J F G₀ p₁ (c ≫ a) (c ≫ b₁) (by simp [← h₁]),
    IsDenseSubsite.mapPreimage_map_of_fac J F G₀ p₂ (c ≫ a) (c ≫ b₂) (by simp [← h₂])]
  simpa [fac₁, fac₂] using presheafObj_condition_assoc _ _ _ _ _ _ _

/--
Definition of `presheafObjMultifork` / `presheafObjMultifork` 的定义

English:
abbreviation presheafObjMultifork
  signature: (X : C)
  body: Multifork.ofι _ (presheafObj data G₀ X) (presheafObjπ data G₀ X)
    (fun _ => presheafObj_condition _ _ _ _ _ _)

中文:
缩写 presheafObjMultifork
  签名: (X : C)
  定义体: Multifork.ofι _ (presheafObj data G₀ X) (presheafObjπ data G₀ X)
    (fun _ => presheafObj_condition _ _ _ _ _ _)

Depends on / 依赖: Multifork, Multifork.of, presheafObj, presheafObj_condition
-/
noncomputable abbrev presheafObjMultifork (X : C) :
    Multifork ((data X).multicospanIndex G₀.obj) :=
  Multifork.ofι _ (presheafObj data G₀ X) (presheafObjπ data G₀ X)
    (fun _ => presheafObj_condition _ _ _ _ _ _)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `presheafObjIsLimit` / `presheafObjIsLimit` 的定义

English:
definition presheafObjIsLimit
  signature: (X : C)
  body: IsLimit.ofIsoLimit (limit.isLimit _) (Multifork.ext (Iso.refl _))

中文:
定义 presheafObjIsLimit
  签名: (X : C)
  定义体: IsLimit.ofIsoLimit (limit.isLimit _) (Multifork.ext (Iso.refl _))

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, Iso.refl, Multifork, Multifork.ext, isLimit, limit.isLimit, ofIsoLimit
-/
noncomputable def presheafObjIsLimit (X : C) :
    IsLimit (presheafObjMultifork data G₀ X) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Multifork.ext (Iso.refl _))

namespace restriction

/--
Definition of `res` / `res` 的定义

English:
definition res
  signature: {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀}
  body: presheafObjπ data G₀ X h.i₀ ≫ IsDenseSubsite.mapPreimage J F G₀ h.q

中文:
定义 res
  签名: {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀}
  定义体: presheafObjπ data G₀ X h.i₀ ≫ IsDenseSubsite.mapPreimage J F G₀ h.q

Depends on / 依赖: IsDenseSubsite, IsDenseSubsite.mapPreimage, mapPreimage
-/
noncomputable def res {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀}
    (h : SieveStruct (data X) f g) :
    presheafObj data G₀ X ⟶ G₀.obj.obj (op Y₀) :=
  presheafObjπ data G₀ X h.i₀ ≫ IsDenseSubsite.mapPreimage J F G₀ h.q

/--
lemma `res_eq_res` / 引理 `res_eq_res`

English:
lemma res_eq_res
  statement: {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀}
  proof: by
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F h₁.q)
      (IsDenseSubsite.imageSieve_mem J₀ J F h₂.q)⟩ _ _ ?_
  rintro ⟨Z₀, a, ⟨b₁, w₁⟩, ⟨b₂, w₂⟩⟩
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, (data X).mem₁₀ h₁.i₀ h₂.i

中文:
引理 res_eq_res
  结论: {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀}
  证明: by
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F h₁.q)
      (IsDenseSubsite.imageSieve_mem J₀ J F h₂.q)⟩ _ _ ?_
  rintro ⟨Z₀, a, ⟨b₁, w₁⟩, ⟨b₂, w₂⟩⟩
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, (data X).mem₁₀ h₁.i₀ h₂.i

Depends on / 依赖: IsDenseSubsite, IsDenseSubsite.imageSieve_mem, IsDenseSubsite.mapPreimage_comp_map, IsSheaf, Presheaf, Presheaf.IsSheaf.hom_ext, hom_ext, imageSieve_mem, intersection_covering, mapPreimage_comp_map, presheafObj_mapPreimage_condition, property
-/
lemma res_eq_res {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀}
    (h₁ h₂ : SieveStruct (data X) f g) :
    res data G₀ h₁ = res data G₀ h₂ := by
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F h₁.q)
      (IsDenseSubsite.imageSieve_mem J₀ J F h₂.q)⟩ _ _ ?_
  rintro ⟨Z₀, a, ⟨b₁, w₁⟩, ⟨b₂, w₂⟩⟩
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, (data X).mem₁₀ h₁.i₀ h₂.i₀ b₁ b₂ (by rw [w₁, w₂, assoc, assoc, h₁.fac, h₂.fac])⟩ _ _ ?_
  rintro ⟨W₀, c, hc⟩
  dsimp [res]
  simp only [assoc, IsDenseSubsite.mapPreimage_comp_map]
  apply presheafObj_mapPreimage_condition
  simp

end restriction

/--
Definition of `restriction` / `restriction` 的定义

English:
definition restriction
  signature: {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X)
  body: G₀.2.amalgamate ⟨_, (data X).sieve_mem f⟩
    (fun ⟨Y₀, g, hg⟩ => restriction.res data G₀ hg.some) (by
      rintro ⟨Z₁, g₁, ⟨h₁⟩⟩ ⟨Z₂, g₂, ⟨h₂⟩⟩ ⟨T₀, p₁, p₂, w⟩
      dsimp at g₁ g₂ p₁ p₂ w ⊢
      rw [restriction.res_eq_res data G₀ _ h₁]; rw [restriction.res_eq_res data G₀ _ h₂]
      refine Presh

中文:
定义 restriction
  签名: {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X)
  定义体: G₀.2.amalgamate ⟨_, (data X).sieve_mem f⟩
    (fun ⟨Y₀, g, hg⟩ => restriction.res data G₀ hg.some) (by
      rintro ⟨Z₁, g₁, ⟨h₁⟩⟩ ⟨Z₂, g₂, ⟨h₂⟩⟩ ⟨T₀, p₁, p₂, w⟩
      dsimp at g₁ g₂ p₁ p₂ w ⊢
      rw [restriction.res_eq_res data G₀ _ h₁]; rw [restriction.res_eq_res data G₀ _ h₂]
      refine Presh

Depends on / 依赖: F.map, IsDenseSubsite, IsDenseSubsite.imageSieve_mem, IsSheaf, Presheaf, Presheaf.IsSheaf.hom_ext, amalgamate, hg.some, hom_ext, imageSieve_mem, intersection_covering, property, res_eq_res, restriction, restriction.res, restriction.res_eq_res, sieve_mem
-/
noncomputable def restriction {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) :
    presheafObj data G₀ X ⟶ G₀.obj.obj (op X₀) :=
  G₀.2.amalgamate ⟨_, (data X).sieve_mem f⟩
    (fun ⟨Y₀, g, hg⟩ => restriction.res data G₀ hg.some) (by
      rintro ⟨Z₁, g₁, ⟨h₁⟩⟩ ⟨Z₂, g₂, ⟨h₂⟩⟩ ⟨T₀, p₁, p₂, w⟩
      dsimp at g₁ g₂ p₁ p₂ w ⊢
      rw [restriction.res_eq_res data G₀ _ h₁]; rw [restriction.res_eq_res data G₀ _ h₂]
      refine Presheaf.IsSheaf.hom_ext G₀.property
        ⟨_, J₀.intersection_covering
          (IsDenseSubsite.imageSieve_mem J₀ J F (F.map p₁ ≫ h₁.q))
          (IsDenseSubsite.imageSieve_mem J₀ J F (F.map p₂ ≫ h₂.q))⟩ _ _ ?_
      rintro ⟨W₀, a, ⟨q₁, w₁⟩, ⟨q₂, w₂⟩⟩
      refine Presheaf.IsSheaf.hom_ext G₀.property
        ⟨_, (data X).mem₁₀ h₁.i₀ h₂.i₀ q₁ q₂ (by
        simp only [w₁, w₂, assoc, h₁.fac, h₂.fac, ← Functor.map_comp_assoc, w])⟩ _ _ ?_
      rintro ⟨U₀, b, hb⟩
      dsimp
      simp only [assoc, restriction.res, IsDenseSubsite.mapPreimage_comp_map]
      apply presheafObj_mapPreimage_condition
      simp only [assoc, h₁.fac, h₂.fac, ← Functor.map_comp_assoc, w])

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `restriction_map` / 引理 `restriction_map`

English:
lemma restriction_map
  statement: {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {Y₀ : C₀}
  proof: by
  have hg : (data X).sieve f g := ⟨i, p, fac⟩
  dsimp only [restriction]
  rw [G₀.2.amalgamate_map _ _ _ ⟨_]; rw [g]; rw [hg⟩]
  apply presheafObj_mapPreimage_condition
  rw [hg.some.fac]; rw [fac]

中文:
引理 restriction_map
  结论: {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {Y₀ : C₀}
  证明: by
  have hg : (data X).sieve f g := ⟨i, p, fac⟩
  dsimp only [restriction]
  rw [G₀.2.amalgamate_map _ _ _ ⟨_]; rw [g]; rw [hg⟩]
  apply presheafObj_mapPreimage_condition
  rw [hg.some.fac]; rw [fac]

Depends on / 依赖: amalgamate_map, hg.some.fac, presheafObj_mapPreimage_condition, restriction
-/
lemma restriction_map {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {Y₀ : C₀}
    (g : Y₀ ⟶ X₀) {i : (data X).I₀} (p : F.obj Y₀ ⟶ F.obj ((data X).X i))
    (fac : p ≫ (data X).f i = F.map g ≫ f) :
    restriction data G₀ f ≫ G₀.obj.map g.op =
      presheafObjπ data G₀ X i ≫ IsDenseSubsite.mapPreimage J F G₀ p := by
  have hg : (data X).sieve f g := ⟨i, p, fac⟩
  dsimp only [restriction]
  rw [G₀.2.amalgamate_map _ _ _ ⟨_]; rw [g]; rw [hg⟩]
  apply presheafObj_mapPreimage_condition
  rw [hg.some.fac]; rw [fac]

/--
lemma `restriction_eq_of_fac` / 引理 `restriction_eq_of_fac`

English:
lemma restriction_eq_of_fac
  statement: {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X)
  proof: by
  simpa using restriction_map data G₀ f (𝟙 _) p (by simpa using fac)

中文:
引理 restriction_eq_of_fac
  结论: {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X)
  证明: by
  simpa using restriction_map data G₀ f (𝟙 _) p (by simpa using fac)

Depends on / 依赖: restriction_map
-/
lemma restriction_eq_of_fac {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X)
    {i : (data X).I₀} (p : F.obj X₀ ⟶ F.obj ((data X).X i))
    (fac : p ≫ (data X).f i = f) :
    restriction data G₀ f =
      presheafObjπ data G₀ X i ≫ IsDenseSubsite.mapPreimage J F G₀ p := by
  simpa using restriction_map data G₀ f (𝟙 _) p (by simpa using fac)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `presheafMap` / `presheafMap` 的定义

English:
definition presheafMap
  signature: {X Y : C} (f : X ⟶ Y)
  body: Multiequalizer.lift _ _ (fun i₀ => restriction data G₀ ((data X).f i₀ ≫ f)) (by
    rintro ⟨⟨i₁, i₂⟩, j⟩
    obtain ⟨a, h₁, h₂⟩ : exists a, a = F.map ((data X).p₁ j) ≫ (data X).f i₁ ≫ f ∧
        a = F.map ((data X).p₂ j) ≫ (data X).f i₂ ≫ f := ⟨_, rfl, (data X).w_assoc j _⟩
    refine Presheaf.IsSh

中文:
定义 presheafMap
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: Multiequalizer.lift _ _ (fun i₀ => restriction data G₀ ((data X).f i₀ ≫ f)) (by
    rintro ⟨⟨i₁, i₂⟩, j⟩
    obtain ⟨a, h₁, h₂⟩ : exists a, a = F.map ((data X).p₁ j) ≫ (data X).f i₁ ≫ f ∧
        a = F.map ((data X).p₂ j) ≫ (data X).f i₂ ≫ f := ⟨_, rfl, (data X).w_assoc j _⟩
    refine Presheaf.IsSh

Depends on / 依赖: F.map, IsSheaf, J.pullback_stable, Multiequalizer, Multiequalizer.lift, Presheaf, Presheaf.IsSheaf.hom_ext, cover_lift, hom_ext, map_comp, op_comp, property, pullback_stable, restriction, restriction_map, w_assoc
-/
noncomputable def presheafMap {X Y : C} (f : X ⟶ Y) :
    presheafObj data G₀ Y ⟶ presheafObj data G₀ X :=
  Multiequalizer.lift _ _ (fun i₀ => restriction data G₀ ((data X).f i₀ ≫ f)) (by
    rintro ⟨⟨i₁, i₂⟩, j⟩
    obtain ⟨a, h₁, h₂⟩ : exists a, a = F.map ((data X).p₁ j) ≫ (data X).f i₁ ≫ f ∧
        a = F.map ((data X).p₂ j) ≫ (data X).f i₂ ≫ f := ⟨_, rfl, (data X).w_assoc j _⟩
    refine Presheaf.IsSheaf.hom_ext G₀.property
      ⟨_, cover_lift F J₀ _ (J.pullback_stable a (data Y).mem₀)⟩ _ _ ?_
    rintro ⟨W₀, b, ⟨_, p, _, ⟨i⟩, fac⟩⟩
    dsimp at fac ⊢
    simp only [assoc, ← map_comp, ← op_comp]
    rw [restriction_map (p := p)]; rw [restriction_map (p := p)]
    all_goals simp_all)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `presheafMap_π` / 引理 `presheafMap_π`

English:
lemma presheafMap_π
  given: {X Y : C} (f : X ⟶ Y) (i : (data X).I₀)
  proof: Multiequalizer.lift_ι _ _ _ _ _

中文:
引理 presheafMap_π
  条件: {X Y : C} (f : X ⟶ Y) (i : (data X).I₀)
  证明: Multiequalizer.lift_ι _ _ _ _ _

Depends on / 依赖: Multiequalizer, Multiequalizer.lift_
-/
lemma presheafMap_π {X Y : C} (f : X ⟶ Y) (i : (data X).I₀) :
    presheafMap data G₀ f ≫ presheafObjπ data G₀ X i =
      restriction data G₀ ((data X).f i ≫ f) :=
  Multiequalizer.lift_ι _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `presheafMap_restriction` / 引理 `presheafMap_restriction`

English:
lemma presheafMap_restriction
  given: {X Y : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) (g : X ⟶ Y)
  proof: by
  refine Presheaf.IsSheaf.hom_ext G₀.property ⟨_, GrothendieckTopology.bind_covering
    (hS := cover_lift F J₀ J (J.pullback_stable f (data X).mem₀)) (hR := fun Y₀ a ha =>
      cover_lift F J₀ J (J.pullback_stable
        (Sieve.ofArrows.h ha ≫ (data X).f (Sieve.ofArrows.i ha) ≫ g) (data Y).mem

中文:
引理 presheafMap_restriction
  条件: {X Y : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) (g : X ⟶ Y)
  证明: by
  refine Presheaf.IsSheaf.hom_ext G₀.property ⟨_, GrothendieckTopology.bind_covering
    (hS := cover_lift F J₀ J (J.pullback_stable f (data X).mem₀)) (hR := fun Y₀ a ha =>
      cover_lift F J₀ J (J.pullback_stable
        (Sieve.ofArrows.h ha ≫ (data X).f (Sieve.ofArrows.i ha) ≫ g) (data Y).mem

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.bind_covering, IsSheaf, J.pullback_stable, Presheaf, Presheaf.IsSheaf.hom_ext, Sieve.ofArrows.fac, Sieve.ofArrows.h, Sieve.ofArrows.i, bind_covering, cover_lift, hom_ext, ofArrows, property, pullback_stable
-/
lemma presheafMap_restriction {X Y : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) (g : X ⟶ Y) :
    presheafMap data G₀ g ≫ restriction data G₀ f = restriction data G₀ (f ≫ g) := by
  refine Presheaf.IsSheaf.hom_ext G₀.property ⟨_, GrothendieckTopology.bind_covering
    (hS := cover_lift F J₀ J (J.pullback_stable f (data X).mem₀)) (hR := fun Y₀ a ha =>
      cover_lift F J₀ J (J.pullback_stable
        (Sieve.ofArrows.h ha ≫ (data X).f (Sieve.ofArrows.i ha) ≫ g) (data Y).mem₀))⟩ _ _ ?_
  rintro ⟨U₀, _, Y₀, c, d, hd, hc, rfl⟩
  have hc' := Sieve.ofArrows.fac hc
  have hd' := Sieve.ofArrows.fac hd
  dsimp at hc hd hc' hd' ⊢
  /- #adaptation_note Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed the `fac`
  arguments below (i.e. `fac := by grind`). It is not yet clear whether this is due to defeq
  abuse in Mathlib or a problem in the new canonicalizer; a minimization would help. -/
  rw [assoc]; rw [← op_comp]; rw [restriction_map (i := Sieve.ofArrows.i hd)
    (p := F.map c ≫ Sieve.ofArrows.h hd) (fac := by simp; grind)]; rw [restriction_map (i := Sieve.ofArrows.i hc) (p := Sieve.ofArrows.h hc) (fac := by simp; grind)]; rw [presheafMap_π_assoc]
  dsimp
  have := J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F (Sieve.ofArrows.h hc))
    (J₀.pullback_stable c (IsDenseSubsite.imageSieve_mem J₀ J F (Sieve.ofArrows.h hd)))
  refine Presheaf.IsSheaf.hom_ext G₀.property ⟨_, this⟩ _ _ ?_
  rintro ⟨V₀, a, ⟨x₁, fac₁⟩, ⟨x₂, fac₂⟩⟩
  dsimp
  rw [assoc]; rw [assoc]; rw [IsDenseSubsite.mapPreimage_map_of_fac J F G₀ _ _ x₂ (by simpa using fac₂.symm)]; rw [IsDenseSubsite.mapPreimage_map_of_fac J F G₀ _ _ x₁ fac₁.symm]
  /- #adaptation_note Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), the last argument below was
  `by grind` (now `by simp_all`). It is not yet clear whether this is due to defeq abuse in
  Mathlib or a problem in the new canonicalizer; a minimization would help. -/
  rw [restriction_map data G₀ _ _ (F.map x₁) (by simp_all)]; rw [IsDenseSubsite.mapPreimage_map]

/--
lemma `presheafMap_id` / 引理 `presheafMap_id`

English:
lemma presheafMap_id
  given: (X : C)
  proof: by
  ext i
  rw [presheafMap_π]; rw [comp_id]; rw [id_comp]; rw [restriction_eq_of_fac data G₀ ((data X).f i) (𝟙 _) (by simp)]; rw [IsDenseSubsite.mapPreimage_id]; rw [comp_id]

@[reassoc]

中文:
引理 presheafMap_id
  条件: (X : C)
  证明: by
  ext i
  rw [presheafMap_π]; rw [comp_id]; rw [id_comp]; rw [restriction_eq_of_fac data G₀ ((data X).f i) (𝟙 _) (by simp)]; rw [IsDenseSubsite.mapPreimage_id]; rw [comp_id]

@[reassoc]

Depends on / 依赖: IsDenseSubsite, IsDenseSubsite.mapPreimage_id, comp_id, id_comp, mapPreimage_id, restriction_eq_of_fac
-/
lemma presheafMap_id (X : C) :
    presheafMap data G₀ (𝟙 X) = 𝟙 _ := by
  ext i
  rw [presheafMap_π]; rw [comp_id]; rw [id_comp]; rw [restriction_eq_of_fac data G₀ ((data X).f i) (𝟙 _) (by simp)]; rw [IsDenseSubsite.mapPreimage_id]; rw [comp_id]

@[reassoc]
/--
lemma `presheafMap_comp` / 引理 `presheafMap_comp`

English:
lemma presheafMap_comp
  given: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  ext i
  rw [assoc]; rw [presheafMap_π]; rw [presheafMap_π]; rw [presheafMap_restriction]; rw [assoc]

中文:
引理 presheafMap_comp
  条件: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  ext i
  rw [assoc]; rw [presheafMap_π]; rw [presheafMap_π]; rw [presheafMap_restriction]; rw [assoc]

Depends on / 依赖: presheafMap_restriction
-/
lemma presheafMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    presheafMap data G₀ (f ≫ g) = presheafMap data G₀ g ≫ presheafMap data G₀ f := by
  ext i
  rw [assoc]; rw [presheafMap_π]; rw [presheafMap_π]; rw [presheafMap_restriction]; rw [assoc]

/-- Let `F : C₀ ⥤ C` be a dense subsite and `data : ∀ X, F.OneHypercoverDenseData J₀ J X`
be a family. Let `G₀` be a sheaf on `C₀`. This is a presheaf on `C` which
extends `G₀` (see `OneHypercoverDenseData.essSurj.compPresheafIso`) and it is a sheaf
(see `OneHypercoverDenseData.essSurj.isSheaf`). -/
@[simps, implicit_reducible]
/--
Definition of `presheaf` / `presheaf` 的定义

English:
definition presheaf
  signature: : Cᵒᵖ ⥤ A where
  body: presheafObj data G₀ X.unop
  map f := presheafMap data G₀ f.unop
  map_id X := presheafMap_id data G₀ X.unop
  map_comp f g := presheafMap_comp data G₀ g.unop f.unop

中文:
定义 presheaf
  签名: : Cᵒᵖ ⥤ A where
  定义体: presheafObj data G₀ X.unop
  map f := presheafMap data G₀ f.unop
  map_id X := presheafMap_id data G₀ X.unop
  map_comp f g := presheafMap_comp data G₀ g.unop f.unop

Depends on / 依赖: X.unop, presheafObj
-/
noncomputable def presheaf : Cᵒᵖ ⥤ A where
  obj X := presheafObj data G₀ X.unop
  map f := presheafMap data G₀ f.unop
  map_id X := presheafMap_id data G₀ X.unop
  map_comp f g := presheafMap_comp data G₀ g.unop f.unop

namespace presheafObjObjIso

variable (X₀ : C₀)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: : (presheaf data G₀).obj (op (F.obj X₀)) ⟶ G₀.obj.obj (op X₀)
  body: G₀.2.amalgamate ⟨_, cover_lift F J₀ _ (data (F.obj X₀)).mem₀⟩ (fun ⟨W₀, a, ha⟩ =>
    presheafObjπ data G₀ _ (Sieve.ofArrows.i ha) ≫
      IsDenseSubsite.mapPreimage J F G₀ (Sieve.ofArrows.h ha)) (by
        rintro ⟨W₀, a, ha⟩ ⟨T₀, b, hb⟩ ⟨U₀, p₁, p₂, fac⟩
        have ha' := Sieve.ofArrows.fac ha
 

中文:
定义 hom
  签名: : (presheaf data G₀).obj (op (F.obj X₀)) ⟶ G₀.obj.obj (op X₀)
  定义体: G₀.2.amalgamate ⟨_, cover_lift F J₀ _ (data (F.obj X₀)).mem₀⟩ (fun ⟨W₀, a, ha⟩ =>
    presheafObjπ data G₀ _ (Sieve.ofArrows.i ha) ≫
      IsDenseSubsite.mapPreimage J F G₀ (Sieve.ofArrows.h ha)) (by
        rintro ⟨W₀, a, ha⟩ ⟨T₀, b, hb⟩ ⟨U₀, p₁, p₂, fac⟩
        have ha' := Sieve.ofArrows.fac ha
 

Depends on / 依赖: F.map, F.obj, IsDenseSubsite, IsDenseSubsite.mapPreimage, IsDenseSubsite.mapPreimage_comp_map, Sieve.ofArrows.fac, Sieve.ofArrows.h, Sieve.ofArrows.i, amalgamate, cover_lift, mapPreimage, mapPreimage_comp_map, ofArrows, restriction_eq_of_fac
-/
noncomputable def hom : (presheaf data G₀).obj (op (F.obj X₀)) ⟶ G₀.obj.obj (op X₀) :=
  G₀.2.amalgamate ⟨_, cover_lift F J₀ _ (data (F.obj X₀)).mem₀⟩ (fun ⟨W₀, a, ha⟩ =>
    presheafObjπ data G₀ _ (Sieve.ofArrows.i ha) ≫
      IsDenseSubsite.mapPreimage J F G₀ (Sieve.ofArrows.h ha)) (by
        rintro ⟨W₀, a, ha⟩ ⟨T₀, b, hb⟩ ⟨U₀, p₁, p₂, fac⟩
        have ha' := Sieve.ofArrows.fac ha
        have hb' := Sieve.ofArrows.fac hb
        dsimp at ha hb ha' hb' p₁ p₂ fac ⊢
        rw [assoc]; rw [assoc]; rw [IsDenseSubsite.mapPreimage_comp_map]; rw [IsDenseSubsite.mapPreimage_comp_map]; rw [← restriction_eq_of_fac data G₀ (F.map (p₁ ≫ a))
            (F.map p₁ ≫ Sieve.ofArrows.h ha) (by rw [assoc]; rw [ha']; rw [map_comp]),
          restriction_eq_of_fac data G₀ (F.map (p₁ ≫ a))
            (F.map p₂ ≫ Sieve.ofArrows.h hb) (by rw [assoc, hb', fac, map_comp])])

variable {X₀}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `hom_map` / 引理 `hom_map`

English:
lemma hom_map
  statement: {W₀ : C₀} (a : W₀ ⟶ X₀) {i : (data (F.obj X₀)).I₀}
  proof: by
  have ha : Sieve.functorPullback F (data (F.obj X₀)).toPreOneHypercover.sieve₀ a :=
    ⟨_, p, _, ⟨i⟩, fac⟩
  exact (G₀.2.amalgamate_map _ _ _ ⟨W₀, a, ha⟩).trans
    (presheafObj_mapPreimage_condition _ _ _ _ _ _ _
      ((Sieve.ofArrows.fac ha).trans fac.symm))

中文:
引理 hom_map
  结论: {W₀ : C₀} (a : W₀ ⟶ X₀) {i : (data (F.obj X₀)).I₀}
  证明: by
  have ha : Sieve.functorPullback F (data (F.obj X₀)).toPreOneHypercover.sieve₀ a :=
    ⟨_, p, _, ⟨i⟩, fac⟩
  exact (G₀.2.amalgamate_map _ _ _ ⟨W₀, a, ha⟩).trans
    (presheafObj_mapPreimage_condition _ _ _ _ _ _ _
      ((Sieve.ofArrows.fac ha).trans fac.symm))

Depends on / 依赖: F.obj, Sieve.functorPullback, Sieve.ofArrows.fac, amalgamate_map, fac.symm, functorPullback, ofArrows, presheafObj_mapPreimage_condition, toPreOneHypercover, toPreOneHypercover.sieve
-/
lemma hom_map {W₀ : C₀} (a : W₀ ⟶ X₀) {i : (data (F.obj X₀)).I₀}
    (p : F.obj W₀ ⟶ F.obj ((data (F.obj X₀)).X i))
    (fac : p ≫ (data (F.obj X₀)).f i = F.map a) :
    hom data G₀ X₀ ≫ G₀.obj.map a.op =
      presheafObjπ data G₀ _ i ≫ IsDenseSubsite.mapPreimage J F G₀ p := by
  have ha : Sieve.functorPullback F (data (F.obj X₀)).toPreOneHypercover.sieve₀ a :=
    ⟨_, p, _, ⟨i⟩, fac⟩
  exact (G₀.2.amalgamate_map _ _ _ ⟨W₀, a, ha⟩).trans
    (presheafObj_mapPreimage_condition _ _ _ _ _ _ _
      ((Sieve.ofArrows.fac ha).trans fac.symm))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `hom_mapPreimage` / 引理 `hom_mapPreimage`

English:
lemma hom_mapPreimage
  statement: {W₀ : C₀} (a : F.obj W₀ ⟶ F.obj X₀) {i : (data (F.obj X₀)).I₀}
  proof: by
  refine Presheaf.IsSheaf.hom_ext G₀.property
      ⟨_, IsDenseSubsite.imageSieve_mem J₀ J F a⟩ _ _ ?_
  rintro ⟨T₀, b, ⟨c, hc⟩⟩
  dsimp
  simp only [assoc, IsDenseSubsite.mapPreimage_comp_map, ← hc,
    IsDenseSubsite.mapPreimage_map]
  exact hom_map data G₀ c _ (by simp only [assoc, fac, hc])

中文:
引理 hom_mapPreimage
  结论: {W₀ : C₀} (a : F.obj W₀ ⟶ F.obj X₀) {i : (data (F.obj X₀)).I₀}
  证明: by
  refine Presheaf.IsSheaf.hom_ext G₀.property
      ⟨_, IsDenseSubsite.imageSieve_mem J₀ J F a⟩ _ _ ?_
  rintro ⟨T₀, b, ⟨c, hc⟩⟩
  dsimp
  simp only [assoc, IsDenseSubsite.mapPreimage_comp_map, ← hc,
    IsDenseSubsite.mapPreimage_map]
  exact hom_map data G₀ c _ (by simp only [assoc, fac, hc])

Depends on / 依赖: IsDenseSubsite, IsDenseSubsite.imageSieve_mem, IsDenseSubsite.mapPreimage_comp_map, IsDenseSubsite.mapPreimage_map, IsSheaf, Presheaf, Presheaf.IsSheaf.hom_ext, hom_ext, hom_map, imageSieve_mem, mapPreimage_comp_map, mapPreimage_map, property
-/
lemma hom_mapPreimage {W₀ : C₀} (a : F.obj W₀ ⟶ F.obj X₀) {i : (data (F.obj X₀)).I₀}
    (p : F.obj W₀ ⟶ F.obj ((data (F.obj X₀)).X i))
    (fac : p ≫ (data (F.obj X₀)).f i = a) :
    hom data G₀ X₀ ≫ IsDenseSubsite.mapPreimage J F G₀ a =
      presheafObjπ data G₀ _ i ≫ IsDenseSubsite.mapPreimage J F G₀ p := by
  refine Presheaf.IsSheaf.hom_ext G₀.property
      ⟨_, IsDenseSubsite.imageSieve_mem J₀ J F a⟩ _ _ ?_
  rintro ⟨T₀, b, ⟨c, hc⟩⟩
  dsimp
  simp only [assoc, IsDenseSubsite.mapPreimage_comp_map, ← hc,
    IsDenseSubsite.mapPreimage_map]
  exact hom_map data G₀ c _ (by simp only [assoc, fac, hc])

variable (X₀)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : G₀.obj.obj (op X₀) ⟶ (presheaf data G₀).obj (op (F.obj X₀))
  body: Multiequalizer.lift _ _
    (fun i => IsDenseSubsite.mapPreimage J F G₀ ((data (F.obj X₀)).f i)) (by
      intro ⟨⟨i, i'⟩, j⟩
      simp [IsDenseSubsite.mapPreimage_comp_map, (data (F.obj X₀)).w j])

@[reassoc (attr := simp)]

中文:
定义 inv
  签名: : G₀.obj.obj (op X₀) ⟶ (presheaf data G₀).obj (op (F.obj X₀))
  定义体: Multiequalizer.lift _ _
    (fun i => IsDenseSubsite.mapPreimage J F G₀ ((data (F.obj X₀)).f i)) (by
      intro ⟨⟨i, i'⟩, j⟩
      simp [IsDenseSubsite.mapPreimage_comp_map, (data (F.obj X₀)).w j])

@[reassoc (attr := simp)]

Depends on / 依赖: F.obj, IsDenseSubsite, IsDenseSubsite.mapPreimage, IsDenseSubsite.mapPreimage_comp_map, Multiequalizer, Multiequalizer.lift, mapPreimage, mapPreimage_comp_map
-/
noncomputable def inv : G₀.obj.obj (op X₀) ⟶ (presheaf data G₀).obj (op (F.obj X₀)) :=
  Multiequalizer.lift _ _
    (fun i => IsDenseSubsite.mapPreimage J F G₀ ((data (F.obj X₀)).f i)) (by
      intro ⟨⟨i, i'⟩, j⟩
      simp [IsDenseSubsite.mapPreimage_comp_map, (data (F.obj X₀)).w j])

@[reassoc (attr := simp)]
/--
lemma `inv_π` / 引理 `inv_π`

English:
lemma inv_π
  given: (i : (data (F.obj X₀)).I₀)
  proof: Multiequalizer.lift_ι _ _ _ _ _

中文:
引理 inv_π
  条件: (i : (data (F.obj X₀)).I₀)
  证明: Multiequalizer.lift_ι _ _ _ _ _

Depends on / 依赖: Multiequalizer, Multiequalizer.lift_
-/
lemma inv_π (i : (data (F.obj X₀)).I₀) :
    inv data G₀ X₀ ≫ presheafObjπ data G₀ (F.obj X₀) i =
      IsDenseSubsite.mapPreimage J F G₀ ((data (F.obj X₀)).f i) :=
  Multiequalizer.lift_ι _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inv_restriction` / 引理 `inv_restriction`

English:
lemma inv_restriction
  given: {Y₀ : C₀} (f : F.obj Y₀ ⟶ F.obj X₀)
  proof: by
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, IsDenseSubsite.imageSieve_mem J₀ J F f⟩ _ _ ?_
  rintro ⟨W₀, a, b, fac₁⟩
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, J₀.pullback_stable b (cover_lift F J₀ _ (data (F.obj X₀)).mem₀)⟩ _ _ ?_
  rintro ⟨T₀, c, _, d, _, ⟨i⟩, fac₂⟩
  dsimp

中文:
引理 inv_restriction
  条件: {Y₀ : C₀} (f : F.obj Y₀ ⟶ F.obj X₀)
  证明: by
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, IsDenseSubsite.imageSieve_mem J₀ J F f⟩ _ _ ?_
  rintro ⟨W₀, a, b, fac₁⟩
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, J₀.pullback_stable b (cover_lift F J₀ _ (data (F.obj X₀)).mem₀)⟩ _ _ ?_
  rintro ⟨T₀, c, _, d, _, ⟨i⟩, fac₂⟩
  dsimp

Depends on / 依赖: F.obj, Functor, Functor.map_comp, IsDenseSubsite, IsDenseSubsite.imageSieve_mem, IsDenseSubsite.mapPreimage_comp, IsSheaf, Presheaf, Presheaf.IsSheaf.hom_ext, cover_lift, hom_ext, imageSieve_mem, mapPreimage_comp, map_comp, map_comp_assoc, op_comp, property, pullback_stable, restriction_map
-/
lemma inv_restriction {Y₀ : C₀} (f : F.obj Y₀ ⟶ F.obj X₀) :
    inv data G₀ X₀ ≫ restriction data G₀ f =
      IsDenseSubsite.mapPreimage J F G₀ f := by
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, IsDenseSubsite.imageSieve_mem J₀ J F f⟩ _ _ ?_
  rintro ⟨W₀, a, b, fac₁⟩
  refine Presheaf.IsSheaf.hom_ext G₀.property
    ⟨_, J₀.pullback_stable b (cover_lift F J₀ _ (data (F.obj X₀)).mem₀)⟩ _ _ ?_
  rintro ⟨T₀, c, _, d, _, ⟨i⟩, fac₂⟩
  dsimp at i d fac₂ ⊢
  simp only [assoc, ← Functor.map_comp, ← op_comp]
  rw [restriction_map data G₀ f (c ≫ a) d
    (by rw [fac₂]; rw [map_comp]; rw [map_comp_assoc]; rw [fac₁]), inv_π_assoc,
    ← IsDenseSubsite.mapPreimage_comp, fac₂,
    IsDenseSubsite.mapPreimage_comp_map J F G₀, map_comp,
      map_comp_assoc, fac₁]

end presheafObjObjIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `presheafObjObjIso` / `presheafObjObjIso` 的定义

English:
definition presheafObjObjIso
  signature: (X₀ : C₀)
  body: presheafObjObjIso.hom data G₀ X₀
  inv := presheafObjObjIso.inv data G₀ X₀
  hom_inv_id := presheafObj_hom_ext fun i => by
    rw [assoc]; rw [presheafObjObjIso.inv_π]; rw [id_comp]; rw [presheafObjObjIso.hom_mapPreimage data G₀ _ (𝟙 _) (fac := by simp)]; rw [IsDenseSubsite.mapPreimage_id]; rw [comp

中文:
定义 presheafObjObjIso
  签名: (X₀ : C₀)
  定义体: presheafObjObjIso.hom data G₀ X₀
  inv := presheafObjObjIso.inv data G₀ X₀
  hom_inv_id := presheafObj_hom_ext fun i => by
    rw [assoc]; rw [presheafObjObjIso.inv_π]; rw [id_comp]; rw [presheafObjObjIso.hom_mapPreimage data G₀ _ (𝟙 _) (fac := by simp)]; rw [IsDenseSubsite.mapPreimage_id]; rw [comp

Depends on / 依赖: presheafObjObjIso, presheafObjObjIso.hom
-/
noncomputable def presheafObjObjIso (X₀ : C₀) :
    (presheaf data G₀).obj (op (F.obj X₀)) ≅ G₀.obj.obj (op X₀) where
  hom := presheafObjObjIso.hom data G₀ X₀
  inv := presheafObjObjIso.inv data G₀ X₀
  hom_inv_id := presheafObj_hom_ext fun i => by
    rw [assoc]; rw [presheafObjObjIso.inv_π]; rw [id_comp]; rw [presheafObjObjIso.hom_mapPreimage data G₀ _ (𝟙 _) (fac := by simp)]; rw [IsDenseSubsite.mapPreimage_id]; rw [comp_id]
  inv_hom_id := by
    refine Presheaf.IsSheaf.hom_ext G₀.property
      ⟨_, cover_lift F J₀ _ (data (F.obj X₀)).mem₀⟩ _ _ ?_
    rintro ⟨Y₀, a, X, b, c, ⟨i⟩, fac⟩
    dsimp at i b fac ⊢
    simp [presheafObjObjIso.hom_map data G₀ _ b fac, ← IsDenseSubsite.mapPreimage_comp, fac]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `presheafMap_presheafObjObjIso_hom` / 引理 `presheafMap_presheafObjObjIso_hom`

English:
lemma presheafMap_presheafObjObjIso_hom
  given: (X : C) (i : (data X).I₀)
  proof: by
  rw [← cancel_mono (presheafObjObjIso data G₀ ((data X).X i)).inv]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]
  apply presheafObj_hom_ext
  intro j
  rw [assoc]; rw [presheafMap_π]; rw [presheafObjObjIso]; rw [presheafObjObjIso.inv_π data G₀]
  apply restriction_eq_of_fac
  simp

中文:
引理 presheafMap_presheafObjObjIso_hom
  条件: (X : C) (i : (data X).I₀)
  证明: by
  rw [← cancel_mono (presheafObjObjIso data G₀ ((data X).X i)).inv]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]
  apply presheafObj_hom_ext
  intro j
  rw [assoc]; rw [presheafMap_π]; rw [presheafObjObjIso]; rw [presheafObjObjIso.inv_π data G₀]
  apply restriction_eq_of_fac
  simp

Depends on / 依赖: Iso.hom_inv_id, cancel_mono, comp_id, hom_inv_id, presheafObjObjIso, presheafObjObjIso.inv_, presheafObj_hom_ext, restriction_eq_of_fac
-/
lemma presheafMap_presheafObjObjIso_hom (X : C) (i : (data X).I₀) :
    presheafMap data G₀ ((data X).f i) ≫ (presheafObjObjIso data G₀ ((data X).X i)).hom =
      presheafObjπ data G₀ X i := by
  rw [← cancel_mono (presheafObjObjIso data G₀ ((data X).X i)).inv]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]
  apply presheafObj_hom_ext
  intro j
  rw [assoc]; rw [presheafMap_π]; rw [presheafObjObjIso]; rw [presheafObjObjIso.inv_π data G₀]
  apply restriction_eq_of_fac
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `presheafObjObjIso_inv_naturality` / 引理 `presheafObjObjIso_inv_naturality`

English:
lemma presheafObjObjIso_inv_naturality
  given: {X₀ Y₀ : C₀} (f : X₀ ⟶ Y₀)
  proof: by
  apply presheafObj_hom_ext
  intro j
  simp [presheafObjObjIso, IsDenseSubsite.mapPreimage_comp]

中文:
引理 presheafObjObjIso_inv_naturality
  条件: {X₀ Y₀ : C₀} (f : X₀ ⟶ Y₀)
  证明: by
  apply presheafObj_hom_ext
  intro j
  simp [presheafObjObjIso, IsDenseSubsite.mapPreimage_comp]

Depends on / 依赖: IsDenseSubsite, IsDenseSubsite.mapPreimage_comp, mapPreimage_comp, presheafObjObjIso, presheafObj_hom_ext
-/
lemma presheafObjObjIso_inv_naturality {X₀ Y₀ : C₀} (f : X₀ ⟶ Y₀) :
    G₀.obj.map f.op ≫ (presheafObjObjIso data G₀ X₀).inv =
      (presheafObjObjIso data G₀ Y₀).inv ≫ presheafMap data G₀ (F.map f) := by
  apply presheafObj_hom_ext
  intro j
  simp [presheafObjObjIso, IsDenseSubsite.mapPreimage_comp]


set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `compPresheafIso` / `compPresheafIso` 的定义

English:
definition compPresheafIso
  signature: : F.op ⋙ presheaf data G₀ ≅ G₀.obj
  body: (NatIso.ofComponents (fun _ => (presheafObjObjIso data G₀ _).symm)
    (fun f => presheafObjObjIso_inv_naturality data G₀ f.unop)).symm

中文:
定义 compPresheafIso
  签名: : F.op ⋙ presheaf data G₀ ≅ G₀.obj
  定义体: (NatIso.ofComponents (fun _ => (presheafObjObjIso data G₀ _).symm)
    (fun f => presheafObjObjIso_inv_naturality data G₀ f.unop)).symm

Depends on / 依赖: NatIso, NatIso.ofComponents, f.unop, ofComponents, presheafObjObjIso, presheafObjObjIso_inv_naturality
-/
noncomputable def compPresheafIso : F.op ⋙ presheaf data G₀ ≅ G₀.obj :=
  (NatIso.ofComponents (fun _ => (presheafObjObjIso data G₀ _).symm)
    (fun f => presheafObjObjIso_inv_naturality data G₀ f.unop)).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isSheaf` / 引理 `isSheaf`

English:
lemma isSheaf
  statement: Presheaf.IsSheaf J (presheaf data G₀)
  proof: by
  rw [isSheaf_iff data]
  constructor
  · exact (Presheaf.isSheaf_of_iso_iff (compPresheafIso data G₀)).2 G₀.property
  · intro X
    refine ⟨(IsLimit.postcomposeHomEquiv
      (WalkingMulticospan.functorExt
          (fun _ => presheafObjObjIso _ _ _) (fun _ => presheafObjObjIso _ _ _)
         

中文:
引理 isSheaf
  结论: Presheaf.IsSheaf J (presheaf data G₀)
  证明: by
  rw [isSheaf_iff data]
  constructor
  · exact (Presheaf.isSheaf_of_iso_iff (compPresheafIso data G₀)).2 G₀.property
  · intro X
    refine ⟨(IsLimit.postcomposeHomEquiv
      (WalkingMulticospan.functorExt
          (fun _ => presheafObjObjIso _ _ _) (fun _ => presheafObjObjIso _ _ _)
         

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, IsLimit.postcomposeHomEquiv, Iso.refl, Multifork, Multifork.ext, PreOneHypercover, Presheaf, Presheaf.isSheaf_of_iso_iff, WalkingMulticospan, WalkingMulticospan.functorExt, compPresheafIso, functorExt, hom.naturality, isSheaf_iff, isSheaf_of_iso_iff, naturality, ofIsoLimit, postcomposeHomEquiv, presheafObjIsLimit
-/
lemma isSheaf : Presheaf.IsSheaf J (presheaf data G₀) := by
  rw [isSheaf_iff data]
  constructor
  · exact (Presheaf.isSheaf_of_iso_iff (compPresheafIso data G₀)).2 G₀.property
  · intro X
    refine ⟨(IsLimit.postcomposeHomEquiv
      (WalkingMulticospan.functorExt
          (fun _ => presheafObjObjIso _ _ _) (fun _ => presheafObjObjIso _ _ _)
          (fun _ => (compPresheafIso _ _).hom.naturality _)
          (fun _ => (compPresheafIso _ _).hom.naturality _)) _).1
      (IsLimit.ofIsoLimit (presheafObjIsLimit data G₀ X)
        (Multifork.ext (Iso.refl _) (fun i => ?_)))⟩
    simp [Multifork.ι, PreOneHypercover.multifork, MulticospanIndex.multicospan]

/--
Definition of `sheaf` / `sheaf` 的定义

English:
definition sheaf
  signature: : Sheaf J A
  body: ⟨presheaf data G₀, isSheaf data G₀⟩

中文:
定义 sheaf
  签名: : Sheaf J A
  定义体: ⟨presheaf data G₀, isSheaf data G₀⟩

Depends on / 依赖: isSheaf, presheaf
-/
noncomputable def sheaf : Sheaf J A := ⟨presheaf data G₀, isSheaf data G₀⟩

/--
Definition of `sheafIso` / `sheafIso` 的定义

English:
definition sheafIso
  signature: : (sheafPushforwardContinuous F A J₀ J).obj (sheaf data G₀) ≅ G₀
  body: (fullyFaithfulSheafToPresheaf J₀ A).preimageIso (compPresheafIso data G₀)

中文:
定义 sheafIso
  签名: : (sheafPushforwardContinuous F A J₀ J).obj (sheaf data G₀) ≅ G₀
  定义体: (fullyFaithfulSheafToPresheaf J₀ A).preimageIso (compPresheafIso data G₀)

Depends on / 依赖: compPresheafIso, fullyFaithfulSheafToPresheaf, preimageIso
-/
noncomputable def sheafIso : (sheafPushforwardContinuous F A J₀ J).obj (sheaf data G₀) ≅ G₀ :=
  (fullyFaithfulSheafToPresheaf J₀ A).preimageIso (compPresheafIso data G₀)

end essSurj

variable (A)

include data in
/--
lemma `essSurj` / 引理 `essSurj`

English:
lemma essSurj
  statement: EssSurj (sheafPushforwardContinuous F A J₀ J) where
  proof: ⟨_, ⟨essSurj.sheafIso data G₀⟩⟩

include data in

中文:
引理 essSurj
  结论: EssSurj (sheafPushforwardContinuous F A J₀ J) where
  证明: ⟨_, ⟨essSurj.sheafIso data G₀⟩⟩

include data in

Depends on / 依赖: essSurj, essSurj.sheafIso, sheafIso
-/
lemma essSurj : EssSurj (sheafPushforwardContinuous F A J₀ J) where
  mem_essImage G₀ := ⟨_, ⟨essSurj.sheafIso data G₀⟩⟩

include data in
/--
lemma `isEquivalence` / 引理 `isEquivalence`

English:
lemma isEquivalence
  statement: IsEquivalence (sheafPushforwardContinuous F A J₀ J) where
  proof: essSurj A data

中文:
引理 isEquivalence
  结论: IsEquivalence (sheafPushforwardContinuous F A J₀ J) where
  证明: essSurj A data

Depends on / 依赖: essSurj
-/
lemma isEquivalence : IsEquivalence (sheafPushforwardContinuous F A J₀ J) where
  essSurj := essSurj A data

end

end OneHypercoverDenseData

variable (A)

/--
lemma `isEquivalence_of_isOneHypercoverDense` / 引理 `isEquivalence_of_isOneHypercoverDense`

English:
lemma isEquivalence_of_isOneHypercoverDense
  proof: OneHypercoverDenseData.isEquivalence.{w} A (oneHypercoverDenseData F J₀ J)

中文:
引理 isEquivalence_of_isOneHypercoverDense
  证明: OneHypercoverDenseData.isEquivalence.{w} A (oneHypercoverDenseData F J₀ J)

Depends on / 依赖: OneHypercoverDenseData, OneHypercoverDenseData.isEquivalence, isEquivalence, oneHypercoverDenseData
-/
lemma isEquivalence_of_isOneHypercoverDense
    [HasLimitsOfSize.{w, w} A] [IsOneHypercoverDense.{w} F J₀ J] :
    IsEquivalence (sheafPushforwardContinuous F A J₀ J) :=
  OneHypercoverDenseData.isEquivalence.{w} A (oneHypercoverDenseData F J₀ J)

end Functor

end CategoryTheory
