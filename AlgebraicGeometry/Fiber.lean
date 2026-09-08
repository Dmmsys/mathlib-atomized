/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Scheme-theoretic fiber

## Main result
- `AlgebraicGeometry.Scheme.Hom.fiber`: `f.fiber y` is the scheme-theoretic fiber of `f` at `y`.
- `AlgebraicGeometry.Scheme.Hom.fiberHomeo`: `f.fiber y` is homeomorphic to `f ⁻¹' {y}`.
- `AlgebraicGeometry.Scheme.Hom.finite_preimage`: Finite morphisms have finite fibers.
- `AlgebraicGeometry.Scheme.Hom.discrete_fiber`: Finite morphisms have discrete fibers.

-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- `f.fiber y` is the scheme-theoretic fiber of `f` at `y`. -/
/-
**AlgebraicGeometry.Scheme.Hom.fiber** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → ↥Y → AlgebraicGeometry.Scheme
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f.fiber y` is the scheme-theoretic fiber of `f` at `y`.
-/
def Scheme.Hom.fiber (f : X ⟶ Y) (y : Y) : Scheme := pullback f (Y.fromSpecResidueField y)

/-- `f.fiberι y : f.fiber y ⟶ X` is the embedding of the scheme-theoretic fiber into `X`. -/
/-
**AlgebraicGeometry.Scheme.Hom.fiber** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → ↥Y → AlgebraicGeometry.Scheme
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f.fiberι y : f.fiber y ⟶ X` is the embedding of the scheme-theoretic fiber into
 `X`.
-/
def Scheme.Hom.fiberι (f : X ⟶ Y) (y : Y) : f.fiber y ⟶ X := pullback.fst _ _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (y : Y) : (f.fiber y).CanonicallyOver X where hom := f.fiberι y

/-- The canonical map from the scheme-theoretic fiber to the residue field. -/
/-
**AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   (f : X ⟶ Y) → (y : ↥Y) → AlgebraicGeo
metry.Scheme.Hom.fiber f y ⟶ AlgebraicGeometry.Spec (Y.residueField y)
参数：f : X ⟶ Y；y : ↥Y；Y.residueField y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the scheme-theoretic fiber to the residue field.
-/
def Scheme.Hom.fiberToSpecResidueField (f : X ⟶ Y) (y : Y) :
    f.fiber y ⟶ Spec (Y.residueField y) :=
  pullback.snd _ _

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.fiber_fac** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (y : ↥Y),   CategoryTheory.
CategoryStruct.comp (AlgebraicGeometry.Scheme.Hom.fiberι f y) f =     CategoryTh
eory.CategoryStruct.comp (AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField f
 y)       (Y.fromSpecResidueField y)
参数：f : X ⟶ Y；y : ↥Y；AlgebraicGeometry.Scheme.Hom.fiberι f y；AlgebraicGeometry.Sc
heme.Hom.fiberToSpecResidueField f y；Y.fromSpecResidueField y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
-/
lemma Scheme.Hom.fiber_fac (f : X ⟶ Y) (y : Y) :
    f.fiberι y ≫ f = f.fiberToSpecResidueField y ≫ Y.fromSpecResidueField y :=
  pullback.condition

/-- The fiber of `f` at `y` is naturally a `κ(y)`-scheme. -/
/-
**AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   (f : X ⟶ Y) → (y : ↥Y) → (AlgebraicGe
ometry.Scheme.Hom.fiber f y).Over (AlgebraicGeometry.Spec (Y.residueField y))
参数：f : X ⟶ Y；y : ↥Y；AlgebraicGeometry.Scheme.Hom.fiber f y；AlgebraicGeometry.Spe
c (Y.residueField y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber of `f` at `y` is naturally a `κ(y)`-scheme.
-/
@[reducible] def Scheme.Hom.fiberOverSpecResidueField
    (f : X ⟶ Y) (y : Y) : (f.fiber y).Over (Spec (Y.residueField y)) where
  hom := f.fiberToSpecResidueField y
/-
**AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField_apply** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (y : ↥Y) (x : ↥(AlgebraicGe
ometry.Scheme.Hom.fiber f y)),   (AlgebraicGeometry.Scheme.Hom.fiberToSpecResidu
eField f y) x = IsLocalRing.closedPoint ↑(Y.residueField y)
参数：f : X ⟶ Y；y : ↥Y；x : ↥(AlgebraicGeometry.Scheme.Hom.fiber f y)；AlgebraicGeome
try.Scheme.Hom.fiberToSpecResidueField f y；Y.residueField y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
lemma Scheme.Hom.fiberToSpecResidueField_apply (f : X ⟶ Y) (y : Y) (x : f.fiber y) :
    f.fiberToSpecResidueField y x = IsLocalRing.closedPoint (Y.residueField y) :=
  Subsingleton.elim (α := PrimeSpectrum _) _ _

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isPullback_fiberToSpecResidueField_of_isPullback {P X Y Z : Scheme.{u}} {f
st : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (
y : Y) : IsPullback (pullback.map _ _ _ _ fst (Spec.map (g.residueFieldMap y)) g
 h.w.symm (by simp)) (snd.fiberToSpecResidueField y) (f.fiberToSpecResidueField 
(g y)) (Spec.map (g.residueFieldMap y))
参数：h : IsPullback fst snd f g；y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_right`：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 
C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ 
: X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ …
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueFiel
d`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (x : ↥X),   CategoryTheory.Cat
egoryStruct.comp (AlgebraicGeometry.Spec.map (AlgebraicGeometry…
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isPullback_fiberToSpecResidueField_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (y : Y) :
    IsPullback (pullback.map _ _ _ _ fst (Spec.map (g.residueFieldMap y)) g h.w.symm (by simp))
      (snd.fiberToSpecResidueField y)
      (f.fiberToSpecResidueField (g y))
      (Spec.map (g.residueFieldMap y)) := by
  refine .of_right (h₁₂ := pullback.fst _ _) ?_ ?_
      (IsPullback.of_hasPullback f (Z.fromSpecResidueField (g y)))
  · simpa using! (IsPullback.of_hasPullback _ _).paste_horiz h
  · simp [Scheme.Hom.fiberToSpecResidueField]

set_option backward.isDefEq.respectTransparency false in
/-- The morphism from the fiber of `Spec S ⟶ Spec R` at some prime `p` to `Spec κ(p)`
is isomorphic to the map induced by `κ(p) ⟶ κ(p) ⊗[R] S`. -/
/-
**AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Spec`。
形式化陈述：(R S : Type u) →   [inst : CommRing R] →     [inst_1 : CommRing S] →      
 [inst_2 : Algebra R S] →         (p : PrimeSpectrum R) →           CategoryTheo
ry.Arrow.mk               (AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField 
                (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S))
) p) ≅             CategoryTheory.Arrow.mk               (AlgebraicGeometry.Spec
.map (CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)))
)
参数：AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S))；CommRingCat.o
fHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism from the fiber of `Spec S ⟶ Spec R` at some prime `p` to `Spec κ(p)
`
is isomorphic to the map induced by `κ(p) ⟶ κ(p) ⊗[R] S`.
-/
noncomputable def Spec.fiberToSpecResidueFieldIso (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) :
    Arrow.mk ((Spec.map (CommRingCat.ofHom <| algebraMap R S)).fiberToSpecResidueField p) ≅
      Arrow.mk (Spec.map <| CommRingCat.ofHom <|
        algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) := by
  refine Arrow.isoMk' _ _
    (pullbackSymmetry _ _ ≪≫ ?_ ≪≫ pullbackSpecIso R p.asIdeal.ResidueField S) ?_ ?_
  · refine pullback.congrHom
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) p).symm rfl ≪≫ ?_
    refine asIso <| pullback.map _ _ _ _ (Spec.map <| (Scheme.Spec.residueFieldIso (.of R) _).inv)
      (𝟙 _) (𝟙 _) (by simp) (by simp)
  · exact Scheme.Spec.mapIso (Scheme.Spec.residueFieldIso (.of R) _).symm.op
  · cat_disch

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.range_fiber** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Hom.range_fiberι (f : X ⟶ Y) (y : Y) :
    Set.range (f.fiberι y) = f ⁻¹' {y} := by
  simp [fiber, fiberι, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (y : Y) : IsPreimmersion (f.fiberι y) :=
  MorphismProperty.pullback_fst _ _ inferInstance

/-- The scheme-theoretic fiber of `f` at `y` is homeomorphic to `f ⁻¹' {y}`. -/
/-
**AlgebraicGeometry.Scheme.Hom.fiberHomeo** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (f : X ⟶ Y) → (y : ↥Y) → ↥(AlgebraicGeo
metry.Scheme.Hom.fiber f y) ≃ₜ ↑(⇑f ⁻¹' {y})
参数：f : X ⟶ Y；y : ↥Y；AlgebraicGeometry.Scheme.Hom.fiber f y；⇑f ⁻¹' {y}。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.range_fiberι`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) (y : ↥Y),   Set.range ⇑(AlgebraicGeometry.Scheme.Hom.fiberι f 
y) = ⇑f ⁻¹' {y}

--- 原说明 ---
The scheme-theoretic fiber of `f` at `y` is homeomorphic to `f ⁻¹' {y}`.
-/
def Scheme.Hom.fiberHomeo (f : X ⟶ Y) (y : Y) : f.fiber y ≃ₜ f ⁻¹' {y} :=
  .trans (f.fiberι y).isEmbedding.toHomeomorph (.setCongr (f.range_fiberι y))

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.fiberHomeo_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (y : ↥Y) (x : ↥(AlgebraicGe
ometry.Scheme.Hom.fiber f y)),   ↑((AlgebraicGeometry.Scheme.Hom.fiberHomeo f y)
 x) = (AlgebraicGeometry.Scheme.Hom.fiberι f y) x
参数：f : X ⟶ Y；y : ↥Y；x : ↥(AlgebraicGeometry.Scheme.Hom.fiber f y)；(AlgebraicGeom
etry.Scheme.Hom.fiberHomeo f y) x；AlgebraicGeometry.Scheme.Hom.fiberι f y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Hom.fiberHomeo_apply (f : X ⟶ Y) (y : Y) (x : f.fiber y) :
    (f.fiberHomeo y x).1 = f.fiberι y x := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.fiber** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → ↥Y → AlgebraicGeometry.Scheme
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Hom.fiberι_fiberHomeo_symm (f : X ⟶ Y) (y : Y) (x : f ⁻¹' {y}) :
    f.fiberι y ((f.fiberHomeo y).symm x) = x :=
  congr($((f.fiberHomeo y).apply_symm_apply x).1)

/-- A point `x` as a point in the fiber of `f` at `f x`. -/
/-
**AlgebraicGeometry.Scheme.Hom.asFiber** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (f : X ⟶ Y) → (x : ↥X) → ↥(AlgebraicGeo
metry.Scheme.Hom.fiber f (f x))
参数：f : X ⟶ Y；x : ↥X；AlgebraicGeometry.Scheme.Hom.fiber f (f x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A point `x` as a point in the fiber of `f` at `f x`.
-/
def Scheme.Hom.asFiber (f : X ⟶ Y) (x : X) : f.fiber (f x) :=
    (f.fiberHomeo (f x)).symm ⟨x, rfl⟩

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.fiber** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → ↥Y → AlgebraicGeometry.Scheme
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Hom.fiberι_asFiber (f : X ⟶ Y) (x : X) : f.fiberι _ (f.asFiber x) = x :=
  f.fiberι_fiberHomeo_symm _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) [QuasiCompact f] (y : Y) : CompactSpace (f.fiber y) :=
  haveI : QuasiCompact (f.fiberToSpecResidueField y) :=
      MorphismProperty.pullback_snd _ _ inferInstance
  HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)
    (f := f.fiberToSpecResidueField y).mp inferInstance
/-
**AlgebraicGeometry.Scheme.Hom.isCompact_preimage_singleton** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCom
pact f] (y : ↥Y), IsCompact (⇑f ⁻¹' {y})
参数：f : X ⟶ Y；y : ↥Y；⇑f ⁻¹' {y}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `AlgebraicGeometry.instCompactSpaceCarrierCarrierCommRingCatFiberOfQuasiC
ompact`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiC
ompact f] (y : ↥Y),   CompactSpace ↥(AlgebraicGeometry.Scheme.Hom.fi…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.range_fiberι`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) (y : ↥Y),   Set.range ⇑(AlgebraicGeometry.Scheme.Hom.fiberι f 
y) = ⇑f ⁻¹' {y}
-/
lemma Scheme.Hom.isCompact_preimage_singleton (f : X ⟶ Y) [QuasiCompact f] (y : Y) :
    IsCompact (f ⁻¹' {y}) :=
  f.range_fiberι y ▸ isCompact_range (f.fiberι y).continuous

@[deprecated (since := "2026-02-05")]
alias QuasiCompact.isCompact_preimage_singleton := Scheme.Hom.isCompact_preimage_singleton

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) [IsAffineHom f] (y : Y) : IsAffine (f.fiber y) :=
  haveI : IsAffineHom (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  isAffine_of_isAffineHom (f.fiberToSpecResidueField y)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (y : Y) [LocallyOfFiniteType f] : JacobsonSpace (f.fiber y) :=
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  LocallyOfFiniteType.jacobsonSpace (f.fiberToSpecResidueField y)

/-- The `κ(x)`-point of `f ⁻¹' {f x}` corresponding to `x`. -/
/-
**AlgebraicGeometry.Scheme.Hom.asFiberHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   (f : X ⟶ Y) → (x : ↥X) → AlgebraicGeo
metry.Spec (X.residueField x) ⟶ AlgebraicGeometry.Scheme.Hom.fiber f (f x)
参数：f : X ⟶ Y；x : ↥X；X.residueField x；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `κ(x)`-point of `f ⁻¹' {f x}` corresponding to `x`.
-/
def Scheme.Hom.asFiberHom (f : X ⟶ Y) (x : X) : Spec (X.residueField x) ⟶ f.fiber (f x) :=
  pullback.lift (X.fromSpecResidueField x) (Spec.map (f.residueFieldMap _)) (by simp)

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.asFiberHom_fiber** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Hom.asFiberHom_fiberι (f : X ⟶ Y) (x : X) :
    f.asFiberHom x ≫ f.fiberι _ = X.fromSpecResidueField x := pullback.lift_fst ..

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.asFiberHom_fiberToSpecResidueField** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (x : ↥X),   CategoryTheory.
CategoryStruct.comp (AlgebraicGeometry.Scheme.Hom.asFiberHom f x)       (Algebra
icGeometry.Scheme.Hom.fiberToSpecResidueField f (f x)) =     AlgebraicGeometry.S
pec.map (AlgebraicGeometry.Scheme.Hom.residueFieldMap f x)
参数：f : X ⟶ Y；x : ↥X；AlgebraicGeometry.Scheme.Hom.asFiberHom f x；AlgebraicGeometr
y.Scheme.Hom.fiberToSpecResidueField f (f x)；AlgebraicGeometry.Scheme.Hom.residu
eFieldMap f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
lemma Scheme.Hom.asFiberHom_fiberToSpecResidueField (f : X ⟶ Y) (x : X) :
    f.asFiberHom x ≫ f.fiberToSpecResidueField _ = Spec.map (f.residueFieldMap _) :=
  pullback.lift_snd ..

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.asFiberHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (x : ↥X) (y : ↥(AlgebraicGe
ometry.Spec (X.residueField x))),   (AlgebraicGeometry.Scheme.Hom.asFiberHom f x
) y = AlgebraicGeometry.Scheme.Hom.asFiber f x
参数：f : X ⟶ Y；x : ↥X；y : ↥(AlgebraicGeometry.Spec (X.residueField x))；AlgebraicGe
ometry.Scheme.Hom.asFiberHom f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isEmbedding`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [self : AlgebraicGeometry.IsPreimmersion f], Topology.IsEmbeddi
ng ⇑f
· 使用定理 `AlgebraicGeometry.instIsPreimmersionFiberι`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) (y : ↥Y),   AlgebraicGeometry.IsPreimmersion (AlgebraicGeomet
ry.Scheme.Hom.fiberι f y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.asFiberHom_fiberι`：∀ {X Y : AlgebraicGeomet
ry.Scheme} (f : X ⟶ Y) (x : ↥X),   CategoryTheory.CategoryStruct.comp (Algebraic
Geometry.Scheme.Hom.asFiberHom f x) …
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
· 使用定理 `AlgebraicGeometry.Scheme.Hom.fiberι_asFiber`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) (x : ↥X),   (AlgebraicGeometry.Scheme.Hom.fiberι f (f x)) (A
lgebraicGeometry.Scheme.Hom.asFib…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.Hom.asFiberHom_apply (f : X ⟶ Y) (x : X) (y) :
    f.asFiberHom x y = f.asFiber x :=
  (f.fiberι _).isEmbedding.injective (by simp [← Scheme.Hom.comp_apply])

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.range_asFiberHom** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (x : ↥X),   Set.range ⇑(Alg
ebraicGeometry.Scheme.Hom.asFiberHom f x) = {AlgebraicGeometry.Scheme.Hom.asFibe
r f x}
参数：f : X ⟶ Y；x : ↥X；AlgebraicGeometry.Scheme.Hom.asFiberHom f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.instNonemptyCarrierCarrierCommRingCatSpecOfNontrivialC
arrier`：∀ {A : CommRingCat} [Nontrivial ↑A], Nonempty ↥(AlgebraicGeometry.Spec A
)
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.asFiberHom_apply`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) (x : ↥X) (y : ↥(AlgebraicGeometry.Spec (X.residueField x))
),   (AlgebraicGeometry.Scheme.Hom.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma Scheme.Hom.range_asFiberHom (f : X ⟶ Y) (x : X) :
    Set.range (f.asFiberHom x) = {f.asFiber x} := by aesop
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (x : X) : IsPreimmersion (f.asFiberHom x) :=
  have : IsPreimmersion (f.asFiberHom x ≫ f.fiberι _) := f.asFiberHom_fiberι x ▸ inferInstance
  .of_comp _ (f.fiberι _)

end AlgebraicGeometry

