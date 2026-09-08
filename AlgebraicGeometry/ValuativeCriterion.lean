/-
Copyright (c) 2024 Andrew Yang, Qi Ge, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Qi Ge, Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.RingHom.Injective
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Valuative criterion

## Main results

- `AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion`:
  A morphism is universally closed if and only if
  it is quasi-compact and satisfies the existence part of the valuative criterion.
- `AlgebraicGeometry.IsSeparated.eq_valuativeCriterion`:
  A morphism is separated if and only if
  it is quasi-separated and satisfies the uniqueness part of the valuative criterion.
- `AlgebraicGeometry.IsProper.eq_valuativeCriterion`:
  A morphism is proper if and only if
  it is qcqs and of finite type and satisfies the valuative criterion.

## Future projects
Show that it suffices to check discrete valuation rings when the base is Noetherian.

-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/--
A valuative commutative square over a morphism `f : X ⟶ Y` is a square
```
Spec K ⟶ Y
  |       |
  ↓       ↓
Spec R ⟶ X
```
where `R` is a valuation ring, and `K` is its ring of fractions.

We are interested in finding lifts `Spec R ⟶ Y` of this diagram.
-/
/-
**AlgebraicGeometry.ValuativeCommSq** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Type (u + 1)
参数：X ⟶ Y；u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valuative commutative square over a morphism `f : X ⟶ Y` is a square
```
Spec K ⟶ Y
  |       |
  ↓       ↓
Spec R ⟶ X
```
where `R` is a valuation ring, and `K` is its ring of fractions.

We are interested in finding lifts `Spec R ⟶ Y` of this diagram.
-/
structure ValuativeCommSq {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The valuation ring of a valuative commutative square. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [valuationRing : ValuationRing R]
  /-- The field of fractions of a valuative commutative square. -/
  K : Type u
  [field : Field K]
  [algebra : Algebra R K]
  [isFractionRing : IsFractionRing R K]
  /-- The top map in a valuative commutative map. -/
  (i₁ : Spec (.of K) ⟶ X)
  /-- The bottom map in a valuative commutative map. -/
  (i₂ : Spec (.of R) ⟶ Y)
  (commSq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) f i₂)

namespace ValuativeCommSq

attribute [instance] commRing domain valuationRing field algebra isFractionRing

end ValuativeCommSq

/-- A morphism `f : X ⟶ Y` satisfies the existence part of the valuative criterion if
every valuative commutative square over `f` has (at least) a lift. -/
/-
**AlgebraicGeometry.ValuativeCriterion.Existence** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.ValuativeCriterion`。
形式化陈述：CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.commSq`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f),   CategoryTheory.
CommSq self.i₁ (AlgebraicGeome…

--- 原说明 ---
A morphism `f : X ⟶ Y` satisfies the existence part of the valuative criterion i
f
every valuative commutative square over `f` has (at least) a lift.
-/
def ValuativeCriterion.Existence : MorphismProperty Scheme :=
  fun _ _ f ↦ ∀ S : ValuativeCommSq f, S.commSq.HasLift

/-- A morphism `f : X ⟶ Y` satisfies the uniqueness part of the valuative criterion if
every valuative commutative square over `f` has at most one lift. -/
/-
**AlgebraicGeometry.ValuativeCriterion.Uniqueness** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.ValuativeCriterion`。
形式化陈述：CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.commSq`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f),   CategoryTheory.
CommSq self.i₁ (AlgebraicGeome…

--- 原说明 ---
A morphism `f : X ⟶ Y` satisfies the uniqueness part of the valuative criterion 
if
every valuative commutative square over `f` has at most one lift.
-/
def ValuativeCriterion.Uniqueness : MorphismProperty Scheme :=
  fun _ _ f ↦ ∀ S : ValuativeCommSq f, Subsingleton S.commSq.LiftStruct

/-- A morphism `f : X ⟶ Y` satisfies the valuative criterion if
every valuative commutative square over `f` has a unique lift. -/
/-
**AlgebraicGeometry.ValuativeCriterion** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：ValuativeCriterion : MorphismProperty Scheme
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.commSq`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f),   CategoryTheory.
CommSq self.i₁ (AlgebraicGeome…

--- 原说明 ---
A morphism `f : X ⟶ Y` satisfies the valuative criterion if
every valuative commutative square over `f` has a unique lift.
-/
def ValuativeCriterion : MorphismProperty Scheme :=
  fun _ _ f ↦ ∀ S : ValuativeCommSq f, Nonempty (Unique (S.commSq.LiftStruct))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
/-
**AlgebraicGeometry.ValuativeCriterion.iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.ValuativeCriterion`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y},   AlgebraicGeometry.Valuat
iveCriterion f ↔     AlgebraicGeometry.ValuativeCriterion.Existence f ∧ Algebrai
cGeometry.ValuativeCriterion.Uniqueness f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.commSq`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f),   CategoryTheory.
CommSq self.i₁ (AlgebraicGeome…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ValuativeCriterion.iff {f : X ⟶ Y} :
    ValuativeCriterion f ↔ Existence f ∧ Uniqueness f := by
  change (∀ _, _) ↔ (∀ _, _) ∧ (∀ _, _)
  simp_rw [← forall_and, unique_iff_subsingleton_and_nonempty, and_comm, CommSq.HasLift.iff]
/-
**AlgebraicGeometry.ValuativeCriterion.eq** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.ValuativeCriterion`。
形式化陈述：AlgebraicGeometry.ValuativeCriterion =   AlgebraicGeometry.ValuativeCriter
ion.Existence ⊓ AlgebraicGeometry.ValuativeCriterion.Uniqueness
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `AlgebraicGeometry.ValuativeCriterion.iff`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y},   AlgebraicGeometry.ValuativeCriterion f ↔     AlgebraicGeomet
ry.ValuativeCriterion.Existenc…
-/
lemma ValuativeCriterion.eq :
    ValuativeCriterion = Existence ⊓ Uniqueness := by
  ext X Y f
  exact iff
/-
**AlgebraicGeometry.ValuativeCriterion.existence** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.ValuativeCriterion`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y},   AlgebraicGeometry.Valuat
iveCriterion f → AlgebraicGeometry.ValuativeCriterion.Existence f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.ValuativeCriterion.iff`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y},   AlgebraicGeometry.ValuativeCriterion f ↔     AlgebraicGeomet
ry.ValuativeCriterion.Existenc…
-/
lemma ValuativeCriterion.existence {f : X ⟶ Y} (h : ValuativeCriterion f) :
    ValuativeCriterion.Existence f := (iff.mp h).1
/-
**AlgebraicGeometry.ValuativeCriterion.uniqueness** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.ValuativeCriterion`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y},   AlgebraicGeometry.Valuat
iveCriterion f → AlgebraicGeometry.ValuativeCriterion.Uniqueness f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.ValuativeCriterion.iff`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y},   AlgebraicGeometry.ValuativeCriterion f ↔     AlgebraicGeomet
ry.ValuativeCriterion.Existenc…
-/
lemma ValuativeCriterion.uniqueness {f : X ⟶ Y} (h : ValuativeCriterion f) :
    ValuativeCriterion.Uniqueness f := (iff.mp h).2

namespace ValuativeCriterion.Existence

open IsLocalRing

set_option backward.isDefEq.respectTransparency.types false in
@[stacks 01KE]
/-
**AlgebraicGeometry.ValuativeCriterion.Existence.specializingMap** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.ValuativeCriterion.Existence`。
形式化陈述：specializingMap (H : ValuativeCriterion.Existence f) : SpecializingMap f
参数：H : ValuativeCriterion.Existence f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用引理 `IsLocalRing.exists_factor_valuationRing`：IsLocalRing.exists_factor_valua
tionRing [IsLocalRing R] (f : R ->+* K) : exists (A : ValuationSubring K) (h : _
), IsLocalHom (f.codRestrict …
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.fromSpecResidueField.eq_1`：∀ (X : AlgebraicGeom
etry.Scheme) (x : ↥X),   X.fromSpecResidueField x =     CategoryTheory.CategoryS
truct.comp (AlgebraicGeometry.Spec.map (…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.SpecMap_stalkMap_fromSpecStalk`：SpecMap_stalkMa
p_fromSpecStalk {x} : Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ = X.fromSpecSt
alk x ≫ f
· 使用引理 `AlgebraicGeometry.Scheme.SpecMap_stalkSpecializes_fromSpecStalk`：SpecMap
_stalkSpecializes_fromSpecStalk {x y : X} (h : x ⤳ y) : Spec.map (X.presheaf.sta
lkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStal…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `ValuationSubring.instValuationRingSubtypeMem`：∀ {K : Type u} [inst : Fie
ld K] (A : ValuationSubring K), ValuationRing ↥A
· 使用定理 `ValuationSubring.instIsFractionRingSubtypeMem`：∀ {K : Type u} [inst : Fi
eld K] (A : ValuationSubring K), IsFractionRing (↥A) K
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.commSq`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f),   CategoryTheory.
CommSq self.i₁ (AlgebraicGeome…
· 使用定理 `CategoryTheory.CommSq.HasLift.exists_lift`：∀ {C : Type u_1} {inst : Cate
goryTheory.Category.{v_1, u_1} C} {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶
 Y}   {g : B ⟶ Y} {sq : Categor…
· 使用定理 `ValuationRing.isLocalRing`：∀ (A : Type u) [inst : CommRing A] [Nontrivia
l A] [PreValuationRing A], IsLocalRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `ValuationRing.of_field`：∀ (K : Type u) [inst : Field K], ValuationRing K
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
· 使用定理 `IsLocalRing.specializes_closedPoint`：specializes_closedPoint (x : PrimeS
pectrum R) : x ⤳ closedPoint R
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
（共 32 条，此处仅展示前 30 条）
-/
lemma specializingMap (H : ValuativeCriterion.Existence f) :
    SpecializingMap f := by
  intro x' y h
  let stalk_y_to_residue_x' : Y.presheaf.stalk y ⟶ X.residueField x' :=
    Y.presheaf.stalkSpecializes h ≫ f.stalkMap x' ≫ X.residue x'
  obtain ⟨A, hA, hA_local⟩ := exists_factor_valuationRing stalk_y_to_residue_x'.hom
  let stalk_y_to_A : Y.presheaf.stalk y ⟶ .of A :=
    CommRingCat.ofHom (stalk_y_to_residue_x'.hom.codRestrict _ hA)
  have w : X.fromSpecResidueField x' ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x'))) ≫
        Spec.map stalk_y_to_A ≫ Y.fromSpecStalk y := by
    rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  obtain ⟨l, hl₁, hl₂⟩ := (H { R := A, K := X.residueField x', commSq := ⟨w⟩, .. }).exists_lift
  dsimp only at hl₁ hl₂
  refine ⟨l (closedPoint A), ?_, ?_⟩
  · simp_rw [← Scheme.fromSpecResidueField_apply x' (closedPoint (X.residueField x')), ← hl₁]
    exact (specializes_closedPoint _).map l.continuous
  · rw [← Scheme.Hom.comp_apply, hl₂]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    have : Spec.map stalk_y_to_A (closedPoint A) = closedPoint (Y.presheaf.stalk y) :=
      comap_closedPoint (S := A) (stalk_y_to_residue_x'.hom.codRestrict A.toSubring hA)
    rw [this, Y.fromSpecStalk_closedPoint]
/-
**AlgebraicGeometry.ValuativeCriterion.Existence.** 是 Mathlib 中的一个实例，位于命名空间 `Alg
ebraicGeometry.ValuativeCriterion.Existence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S : CommRingCat} (e : R ≅ S) : IsLocalHom e.hom.hom :=
  isLocalHom_of_isIso _

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.ValuativeCriterion.Existence.of_specializingMap** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.ValuativeCriterion.Existence`。
形式化陈述：of_specializingMap (H : (topologically @SpecializingMap).universally f) : 
ValuativeCriterion.Existence f
参数：H : (topologically @SpecializingMap).universally f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.commSq`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f),   CategoryTheory.
CommSq self.i₁ (AlgebraicGeome…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuationRing.isLocalRing`：∀ (A : Type u) [inst : CommRing A] [Nontrivia
l A] [PreValuationRing A], IsLocalRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `ValuationRing.of_field`：∀ (K : Type u) [inst : Field K], ValuationRing K
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsLocalRing.specializes_closedPoint`：specializes_closedPoint (x : PrimeS
pectrum R) : x ⤳ closedPoint R
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
· 使用定理 `isLocalHom_of_isIso`：isLocalHom_of_isIso {R S : CommRingCat} (f : R ⟶ S)
 [IsIso f] : IsLocalHom f.hom
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `trivial`：True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.stalkClosedPointIso_inv`：stalkClosedPointIso_inv : (st
alkClosedPointIso R).inv = StructureSheaf.toStalk R _
· 使用定理 `TopCat.Presheaf.stalkCongr_hom`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   (
F : TopCat.Presheaf …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X 
: TopCat}   (F : TopCat.Presheaf …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.germ_stalkMap_assoc`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) (U : Y.Opens) (x : ↥X) (hx : f x ∈ U) {Z : CommRingCat}
   (h : X.presheaf.stalk x ⟶ Z),   Cat…
· 使用引理 `AlgebraicGeometry.Scheme.preimage_eq_top_of_closedPoint_mem`：preimage_eq
_top_of_closedPoint_mem {U : Opens X} (hU : f (closedPoint R) in U) : f ⁻¹ᵁ U = 
⊤
· 使用引理 `AlgebraicGeometry.Scheme.germ_stalkClosedPointTo`：germ_stalkClosedPointT
o (U : Opens X) (hU : f (closedPoint R) in U) : X.presheaf.germ U _ hU ≫ stalkCl
osedPointTo f = f.app U ≫ ((Spec R).pr…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_app_assoc`：∀ {X Y Z : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) {Z_1 : CommRingCat}   (h :     X
.presheaf.obj (Opposite.op ((Topo…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
（共 63 条，此处仅展示前 30 条）
-/
lemma of_specializingMap (H : (topologically @SpecializingMap).universally f) :
    ValuativeCriterion.Existence f := by
  rintro ⟨R, K, i₁, i₂, ⟨w⟩⟩
  have : IsDomain (CommRingCat.of R) := ‹_›
  have : ValuationRing (CommRingCat.of R) := ‹_›
  let : Field (CommRingCat.of K) := ‹_›
  replace H := H (pullback.snd i₂ f) i₂ (pullback.fst i₂ f) (.of_hasPullback i₂ f)
  let lft := pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R K))) i₁ w.symm
  obtain ⟨x, h₁, h₂⟩ := @H (lft (closedPoint _)) _ (specializes_closedPoint (R := R) _)
  let e : CommRingCat.of R ≅ (Spec <| .of R).presheaf.stalk (pullback.fst i₂ f x) :=
    (stalkClosedPointIso (.of R)).symm ≪≫
      (Spec <| .of R).presheaf.stalkCongr (.of_eq h₂.symm)
  let α := e.hom ≫ (pullback.fst i₂ f).stalkMap x
  have : IsLocalHom e.hom.hom := isLocalHom_of_isIso e.hom
  have : IsLocalHom α.hom := inferInstanceAs
    (IsLocalHom (((pullback.fst i₂ f).stalkMap x).hom.comp e.hom.hom))
  let β := (pullback i₂ f).presheaf.stalkSpecializes h₁ ≫ Scheme.stalkClosedPointTo lft
  have hαβ : α ≫ β = CommRingCat.ofHom (algebraMap R K) := by
    simp only [CommRingCat.coe_of, Iso.trans_hom, Iso.symm_hom, TopCat.Presheaf.stalkCongr_hom,
      Category.assoc, α, e, β, stalkClosedPointIso_inv, StructureSheaf.toStalk]
    change (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec <| .of R).presheaf.germ _ _ _ ≫ _ = _
    simp only [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap_assoc]
    -- `map_top` introduces defeq problems, according to `check_compositions`.
    -- This is probably the cause of the `erw` needed below.
    simp only [TopologicalSpace.Opens.map_top]
    rw [Scheme.germ_stalkClosedPointTo lft ⊤ trivial]
    erw [← Scheme.Hom.comp_app_assoc lft (pullback.fst i₂ f)]
    rw [pullback.lift_fst]
    simp
  have hbij := (bijective_rangeRestrict_comp_of_valuationRing (R := R) (K := K) α.hom β.hom
    (CommRingCat.hom_ext_iff.mp hαβ))
  let φ : (pullback i₂ f).presheaf.stalk x ⟶ CommRingCat.of R := CommRingCat.ofHom <|
    (RingEquiv.ofBijective _ hbij).symm.toRingHom.comp β.hom.rangeRestrict
  have hαφ : α ≫ φ = 𝟙 _ := by ext x; exact (RingEquiv.ofBijective _ hbij).symm_apply_apply x
  have hαφ' : (pullback.fst i₂ f).stalkMap x ≫ φ = e.inv := by
    rw [← cancel_epi e.hom, ← Category.assoc, hαφ, e.hom_inv_id]
  have hφβ : φ ≫ CommRingCat.ofHom (algebraMap R K) = β :=
    hαβ ▸ CommRingCat.hom_ext (RingHom.ext fun x ↦ congr_arg Subtype.val
      ((RingEquiv.ofBijective _ hbij).apply_symm_apply (β.hom.rangeRestrict x)))
  refine ⟨⟨⟨Spec.map ((pullback.snd i₂ f).stalkMap x ≫ φ) ≫ X.fromSpecStalk _, ?_, ?_⟩⟩⟩
  · simp only [← Spec.map_comp_assoc, Category.assoc, hφβ]
    simp only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, β]
    -- This next line only fires as `rw`, not `simp`:
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
    simp [lft]
  · simp only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← pullback.condition]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, ← Spec.map_comp_assoc, hαφ']
    simp only [Iso.trans_inv, TopCat.Presheaf.stalkCongr_inv, Iso.symm_inv, Spec.map_comp,
      Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, e]
    rw [← Spec_stalkClosedPointIso, ← Spec.map_comp_assoc,
      Iso.inv_hom_id, Spec.map_id, Category.id_comp]
/-
**AlgebraicGeometry.ValuativeCriterion.Existence.stableUnderBaseChange** 是 Mathl
ib 中的一个实例，位于命名空间 `AlgebraicGeometry.ValuativeCriterion.Existence`。
形式化陈述：stableUnderBaseChange : ValuativeCriterion.Existence.IsStableUnderBaseChan
ge
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.domain`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f), IsDomain self.R
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.valuationRing`：∀ {X Y : AlgebraicGeome
try.Scheme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f), ValuationR
ing self.R
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.isFractionRing`：∀ {X Y : AlgebraicGeom
etry.Scheme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f),   IsFract
ionRing self.R self.K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.commSq`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f),   CategoryTheory.
CommSq self.i₁ (AlgebraicGeome…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CommSq.HasLift.exists_lift`：∀ {C : Type u_1} {inst : Cate
goryTheory.Category.{v_1, u_1} C} {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶
 Y}   {g : B ⟶ Y} {sq : Categor…
· 使用引理 `CategoryTheory.IsPullback.hom_ext`：hom_ext (hP : IsPullback fst snd f g)
 {W : C} {k l : W ⟶ P} (h₀ : k ≫ fst = l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l
· 使用引理 `CategoryTheory.IsPullback.lift_fst`：lift_fst (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h
· 使用引理 `CategoryTheory.IsPullback.lift_snd`：lift_snd (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k
-/
instance stableUnderBaseChange : ValuativeCriterion.Existence.IsStableUnderBaseChange := by
  constructor
  intro Y' X X' Y Y'_to_Y f X'_to_X f' hP hf commSq
  let commSq' : ValuativeCommSq f :=
  { R := commSq.R
    K := commSq.K
    i₁ := commSq.i₁ ≫ X'_to_X
    i₂ := commSq.i₂ ≫ Y'_to_Y
    commSq := ⟨by simp only [Category.assoc, hP.w, reassoc_of% commSq.commSq.w]⟩ }
  obtain ⟨l₀, hl₁, hl₂⟩ := (hf commSq').exists_lift
  refine ⟨⟨⟨hP.lift l₀ commSq.i₂ (by simp_all only [commSq']), ?_, hP.lift_snd _ _ _⟩⟩⟩
  apply hP.hom_ext
  · simpa
  · simp only [Category.assoc]
    rw [hP.lift_snd]
    rw [commSq.commSq.w]

@[stacks 01KE]
/-
**AlgebraicGeometry.ValuativeCriterion.Existence.eq** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.ValuativeCriterion.Existence`。
形式化陈述：AlgebraicGeometry.ValuativeCriterion.Existence = (AlgebraicGeometry.topolo
gically @SpecializingMap).universally
参数：AlgebraicGeometry.topologically @SpecializingMap。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `CategoryTheory.MorphismProperty.universally_mono`：universally_mono : Mon
otone (universally : MorphismProperty C -> MorphismProperty C)
· 使用引理 `AlgebraicGeometry.ValuativeCriterion.Existence.specializingMap`：speciali
zingMap (H : ValuativeCriterion.Existence f) : SpecializingMap f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.universally_eq`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Mor
phismProperty C}   [hP : P.IsStableUnderBaseChange], P.unive…
· 使用引理 `AlgebraicGeometry.ValuativeCriterion.Existence.of_specializingMap`：of_sp
ecializingMap (H : (topologically @SpecializingMap).universally f) : ValuativeCr
iterion.Existence f
-/
protected lemma eq :
    ValuativeCriterion.Existence = (topologically @SpecializingMap).universally := by
  ext
  constructor
  · intro _
    apply MorphismProperty.universally_mono
    · apply specializingMap
    · rwa [MorphismProperty.IsStableUnderBaseChange.universally_eq]
  · apply of_specializingMap

end ValuativeCriterion.Existence

/-- The **valuative criterion** for universally closed morphisms. -/
@[stacks 01KF]
/-
**AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.UniversallyClosed`。
形式化陈述：@AlgebraicGeometry.UniversallyClosed = AlgebraicGeometry.ValuativeCriterio
n.Existence ⊓ @AlgebraicGeometry.QuasiCompact
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.universallyClosed_eq_universallySpecializing`：universa
llyClosed_eq_universallySpecializing : @UniversallyClosed = (topologically @Spec
ializingMap).universally ⊓ @QuasiCompact
· 使用定理 `AlgebraicGeometry.ValuativeCriterion.Existence.eq`：AlgebraicGeometry.Val
uativeCriterion.Existence = (AlgebraicGeometry.topologically @SpecializingMap).u
niversally

--- 原说明 ---
The **valuative criterion** for universally closed morphisms.
-/
lemma UniversallyClosed.eq_valuativeCriterion :
    @UniversallyClosed = ValuativeCriterion.Existence ⊓ @QuasiCompact := by
  rw [universallyClosed_eq_universallySpecializing, ValuativeCriterion.Existence.eq]

/-- The **valuative criterion** for universally closed morphisms. -/
@[stacks 01KF]
/-
**AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.UniversallyClosed`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCom
pact f],   AlgebraicGeometry.ValuativeCriterion.Existence f → AlgebraicGeometry.
UniversallyClosed f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion`：@AlgebraicGeo
metry.UniversallyClosed = AlgebraicGeometry.ValuativeCriterion.Existence ⊓ @Alge
braicGeometry.QuasiCompact

--- 原说明 ---
The **valuative criterion** for universally closed morphisms.
-/
lemma UniversallyClosed.of_valuativeCriterion [QuasiCompact f]
    (hf : ValuativeCriterion.Existence f) : UniversallyClosed f := by
  rw [eq_valuativeCriterion]
  exact ⟨hf, ‹_›⟩

section Uniqueness

/-- The **valuative criterion** for separated morphisms. -/
@[stacks 01L0]
/-
**AlgebraicGeometry.IsSeparated.of_valuativeCriterion** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.IsSeparated`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiSep
arated f],   AlgebraicGeometry.ValuativeCriterion.Uniqueness f → AlgebraicGeomet
ry.IsSeparated f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y
 ⟶ Z},   CategoryTh…
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.commSq`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f),   CategoryTheory.
CommSq self.i₁ (AlgebraicGeome…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst_assoc`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : Cate
goryTheory.Limits.HasPullback f f] {Z :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.domain`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f), IsDomain self.R
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.valuationRing`：∀ {X Y : AlgebraicGeome
try.Scheme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f), ValuationR
ing self.R
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.isFractionRing`：∀ {X Y : AlgebraicGeom
etry.Scheme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f),   IsFract
ionRing self.R self.K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用引理 `CategoryTheory.IsPullback.hom_ext`：hom_ext (hP : IsPullback fst snd f g)
 {W : C} {k l : W ⟶ P} (h₀ : k ≫ fst = l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion`：∀ {X Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f],   Algebrai
cGeometry.ValuativeCriterion.Existence f → Alge…
· 使用定理 `AlgebraicGeometry.QuasiSeparated.quasiCompact_diagonal`：∀ {X Y : Algebra
icGeometry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.QuasiSeparated f],   Al
gebraicGeometry.QuasiCompact (CategoryTheory…
· 使用引理 `AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion`：of_isPreimmersion
 {X Y : Scheme} (f : X ⟶ Y) [IsPreimmersion f] (hf : IsClosed (Set.range f)) : I
sClosedImmersion f
· 使用定理 `AlgebraicGeometry.IsImmersion.toIsPreimmersion`：∀ {X Y : AlgebraicGeomet
ry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsImmersion f],   AlgebraicGeom
etry.IsPreimmersion f
· 使用定理 `AlgebraicGeometry.IsImmersion.instDiagonalScheme`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.IsImmersion (CategoryTheory.Limits
.pullback.diagonal f)
· 使用定理 `IsClosedMap.isClosed_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → IsC
losed (Set.range…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isClosedMap`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f], IsClosedMap ⇑f

--- 原说明 ---
The **valuative criterion** for separated morphisms.
-/
lemma IsSeparated.of_valuativeCriterion [QuasiSeparated f]
    (hf : ValuativeCriterion.Uniqueness f) : IsSeparated f where
  isClosedImmersion_diagonal := by
    suffices h : ValuativeCriterion.Existence (pullback.diagonal f) by
      have := UniversallyClosed.of_valuativeCriterion (pullback.diagonal f) h
      exact .of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range
    intro S
    have hc : CommSq S.i₁ (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))
        f (S.i₂ ≫ pullback.fst f f ≫ f) := ⟨by simp [← S.commSq.w_assoc]⟩
    let S' : ValuativeCommSq f := ⟨S.R, S.K, S.i₁, S.i₂ ≫ pullback.fst f f ≫ f, hc⟩
    have : Subsingleton S'.commSq.LiftStruct := hf S'
    let S'l₁ : S'.commSq.LiftStruct := ⟨S.i₂ ≫ pullback.fst f f,
      by simp [S', ← S.commSq.w_assoc], by simp [S']⟩
    let S'l₂ : S'.commSq.LiftStruct := ⟨S.i₂ ≫ pullback.snd f f,
      by simp [S', ← S.commSq.w_assoc], by simp [S', pullback.condition]⟩
    have h₁₂ : S'l₁ = S'l₂ := Subsingleton.elim _ _
    constructor
    constructor
    refine ⟨S.i₂ ≫ pullback.fst _ _, ?_, ?_⟩
    · simp [← S.commSq.w_assoc]
    · simp only [Category.assoc]
      apply IsPullback.hom_ext (IsPullback.of_hasPullback _ _)
      · simp
      · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
        exact congrArg CommSq.LiftStruct.l h₁₂

set_option backward.isDefEq.respectTransparency false in
@[stacks 01KZ]
/-
**AlgebraicGeometry.IsSeparated.valuativeCriterion** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.IsSeparated`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsSepara
ted f],   AlgebraicGeometry.ValuativeCriterion.Uniqueness f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.commSq`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f),   CategoryTheory.
CommSq self.i₁ (AlgebraicGeome…
· 使用定理 `CategoryTheory.CommSq.LiftStruct.ext`：∀ {C : Type u_1} {inst : CategoryT
heory.Category.{v_1, u_1} C} {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y}  
 {g : B ⟶ Y} {sq : Categor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange`：CategoryThe
ory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.IsClosedImmersio
n
· 使用定理 `AlgebraicGeometry.IsSeparated.diagonal_isClosedImmersion`：∀ {X Y : Algeb
raicGeometry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsSeparated f],   Alg
ebraicGeometry.IsClosedImmersion (CategoryTheo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.hasAffineProperty`：AlgebraicGeometry
.HasAffineProperty @AlgebraicGeometry.IsClosedImmersion fun X x f [AlgebraicGeom
etry.IsAffine x] =>   AlgebraicGeometry.IsA…
· 使用引理 `CategoryTheory.IsPullback.hom_ext`：hom_ext (hP : IsPullback fst snd f g)
 {W : C} {k l : W ⟶ P} (h₀ : k ≫ fst = l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RingHom.toMorphismProperty_respectsIso_iff`：toMorphismProperty_respectsI
so_iff : RespectsIso P ↔ (toMorphismProperty P).RespectsIso
· 使用定理 `RingHom.injective_respectsIso`：RingHom.RespectsIso fun {R S} [CommRing R
] [CommRing S] f => Function.Injective ⇑f
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `AlgebraicGeometry.ValuativeCommSq.isFractionRing`：∀ {X Y : AlgebraicGeom
etry.Scheme} {f : X ⟶ Y} (self : AlgebraicGeometry.ValuativeCommSq f),   IsFract
ionRing self.R self.K
（共 42 条，此处仅展示前 30 条）
-/
lemma IsSeparated.valuativeCriterion [IsSeparated f] : ValuativeCriterion.Uniqueness f := by
  intro S
  constructor
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩
  ext : 1
  dsimp at *
  have h := hl₁'.trans hl₂'.symm
  let Z := pullback (pullback.diagonal f) (pullback.lift l₁ l₂ h)
  let g : Z ⟶ Spec (.of S.R) := pullback.snd _ _
  have : IsClosedImmersion g := MorphismProperty.pullback_snd _ _ inferInstance
  have hZ : IsAffine Z := by
    rw [@HasAffineProperty.iff_of_isAffine @IsClosedImmersion] at this
    exact this.left
  suffices IsIso g by
    rw [← cancel_epi g]
    conv_lhs => rw [← pullback.lift_fst l₁ l₂ h, ← pullback.condition_assoc]
    conv_rhs => rw [← pullback.lift_snd l₁ l₂ h, ← pullback.condition_assoc]
    simp
  suffices h : Function.Bijective (g.appTop) by
    refine (HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)).mpr ?_
    exact ⟨hZ, (ConcreteCategory.isIso_iff_bijective _).mpr h⟩
  constructor
  · let l : Spec (.of S.K) ⟶ Z :=
      pullback.lift S.i₁ (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) (by
        apply IsPullback.hom_ext (IsPullback.of_hasPullback _ _)
        · simpa using hl₁.symm
        · simpa using hl₂.symm)
    have hg : l ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) :=
      pullback.lift_snd _ _ _
    have : Function.Injective ((l ≫ g).appTop) := by
      rw [hg]
      let e := arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom <| algebraMap S.R S.K)
      let P : MorphismProperty CommRingCat :=
        RingHom.toMorphismProperty <| fun f ↦ Function.Injective f
      have : (RingHom.toMorphismProperty <| fun f ↦ Function.Injective f).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.injective_respectsIso
      change P _
      rw [← MorphismProperty.arrow_mk_iso_iff (P := P) e]
      exact FaithfulSMul.algebraMap_injective S.R S.K
    rw [Scheme.Hom.comp_appTop] at this
    exact Function.Injective.of_comp this
  · rw [@HasAffineProperty.iff_of_isAffine @IsClosedImmersion] at this
    exact this.right

/-- The **valuative criterion** for separated morphisms. -/
/-
**AlgebraicGeometry.IsSeparated.eq_valuativeCriterion** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.IsSeparated`。
形式化陈述：@AlgebraicGeometry.IsSeparated = AlgebraicGeometry.ValuativeCriterion.Uniq
ueness ⊓ @AlgebraicGeometry.QuasiSeparated
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.IsSeparated.valuativeCriterion`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsSeparated f],   AlgebraicGeometry.
ValuativeCriterion.Uniqueness f
· 使用定理 `AlgebraicGeometry.IsSeparated.instQuasiSeparated`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsSeparated f], AlgebraicGeometry.Qu
asiSeparated f
· 使用定理 `AlgebraicGeometry.IsSeparated.of_valuativeCriterion`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiSeparated f],   AlgebraicGeo
metry.ValuativeCriterion.Uniqueness f → A…

--- 原说明 ---
The **valuative criterion** for separated morphisms.
-/
lemma IsSeparated.eq_valuativeCriterion :
    @IsSeparated = ValuativeCriterion.Uniqueness ⊓ @QuasiSeparated := by
  ext X Y f
  exact ⟨fun _ ↦ ⟨IsSeparated.valuativeCriterion f, inferInstance⟩,
    fun ⟨H, _⟩ ↦ .of_valuativeCriterion f H⟩

end Uniqueness

set_option backward.isDefEq.respectTransparency.types false in
/-- The **valuative criterion** for proper morphisms. -/
@[stacks 0BX5]
/-
**AlgebraicGeometry.IsProper.eq_valuativeCriterion** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.IsProper`。
形式化陈述：@AlgebraicGeometry.IsProper =   AlgebraicGeometry.ValuativeCriterion ⊓ @Al
gebraicGeometry.QuasiCompact ⊓ @AlgebraicGeometry.QuasiSeparated ⊓     @Algebrai
cGeometry.LocallyOfFiniteType
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.isProper_eq`：isProper_eq : @IsProper = (@IsSeparated ⊓
 @UniversallyClosed : MorphismProperty Scheme) ⊓ @LocallyOfFiniteType
· 使用定理 `AlgebraicGeometry.IsSeparated.eq_valuativeCriterion`：@AlgebraicGeometry.
IsSeparated = AlgebraicGeometry.ValuativeCriterion.Uniqueness ⊓ @AlgebraicGeomet
ry.QuasiSeparated
· 使用定理 `AlgebraicGeometry.ValuativeCriterion.eq`：AlgebraicGeometry.ValuativeCrit
erion =   AlgebraicGeometry.ValuativeCriterion.Existence ⊓ AlgebraicGeometry.Val
uativeCriterion.Uniqueness
· 使用定理 `AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion`：@AlgebraicGeo
metry.UniversallyClosed = AlgebraicGeometry.ValuativeCriterion.Existence ⊓ @Alge
braicGeometry.QuasiCompact
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
The **valuative criterion** for proper morphisms.
-/
lemma IsProper.eq_valuativeCriterion :
    @IsProper = ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType := by
  rw [isProper_eq, IsSeparated.eq_valuativeCriterion, ValuativeCriterion.eq,
    UniversallyClosed.eq_valuativeCriterion]
  simp_rw [inf_assoc]
  ext X Y f
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ _
  tauto

/-- The **valuative criterion** for proper morphisms. -/
@[stacks 0BX5]
/-
**AlgebraicGeometry.IsProper.of_valuativeCriterion** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.IsProper`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCom
pact f] [AlgebraicGeometry.QuasiSeparated f]   [AlgebraicGeometry.LocallyOfFinit
eType f], AlgebraicGeometry.ValuativeCriterion f → AlgebraicGeometry.IsProper f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsProper.eq_valuativeCriterion`：@AlgebraicGeometry.IsP
roper =   AlgebraicGeometry.ValuativeCriterion ⊓ @AlgebraicGeometry.QuasiCompact
 ⊓ @AlgebraicGeometry.QuasiSeparated ⊓…

--- 原说明 ---
The **valuative criterion** for proper morphisms.
-/
lemma IsProper.of_valuativeCriterion [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    (H : ValuativeCriterion f) : IsProper f := by
  rw [eq_valuativeCriterion]
  exact ⟨⟨⟨‹_›, ‹_›⟩, ‹_›⟩, ‹_›⟩

end AlgebraicGeometry

