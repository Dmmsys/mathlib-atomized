/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal

/-!
# Sheaf of continuous maps associated to topological space

Given a topological space `T`, we consider the presheaf on `Scheme` given by `U ↦ C(U, T)`
and show that it is a Zariski sheaf (TODO: show that it is a fpqc sheaf).
When `T` is discrete, this is the constant sheaf associated to `T` (TODO).

## Main declarations

- `AlgebraicGeometry.continuousMapPresheaf`: The sheaf `U ↦ C(U, T)` for a topological space `T`.
- `AlgebraicGeometry.continuousMapPresheafAb`: For a topological abelian group `A`, this is
  `continuousMapPresheaf A` viewed as a sheaf of abelian groups.

## TODOs

- Show that `continuousMapPresheaf` is a sheaf for the fpqc topology (@chrisflav).
-/

@[expose] public section

open CategoryTheory Limits

universe w' w v₂ u₂ v u

namespace AlgebraicGeometry

variable (S : Scheme.{u}) (T : Type v) [TopologicalSpace T]

/--
The yoneda embedding of `TopCat` precomposed with the forgetful functor from `Scheme`. This is the
presheaf `U ↦ C(U, T)`. For universe reasons, we implement it by hand.
-/
@[simps]
/-
**AlgebraicGeometry.continuousMapPresheaf** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：continuousMapPresheaf (T : Type v) [TopologicalSpace T] : Scheme.{u}ᵒᵖ ⥤ T
ype (max v u) where obj U
参数：T : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The yoneda embedding of `TopCat` precomposed with the forgetful functor from `Sc
heme`. This is the
presheaf `U ↦ C(U, T)`. For universe reasons, we implement it by hand.
-/
def continuousMapPresheaf (T : Type v) [TopologicalSpace T] : Scheme.{u}ᵒᵖ ⥤ Type (max v u) where
  obj U := C(U.unop, T)
  map {U V} f := ↾fun g ↦ ContinuousMap.comp g f.unop.base.hom

/-- `continuousMapPresheaf` is isomorphic to the composition of the forgetful
functor to `TopCat` and the yoneda embedding. -/
/-
**AlgebraicGeometry.continuousMapPresheafIsoUlift** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry`。
形式化陈述：continuousMapPresheafIsoUlift : continuousMapPresheaf T ≅ Scheme.forgetToT
op.op ⋙ TopCat.uliftFunctor.op ⋙ yoneda.obj (.of <| ULift T)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`continuousMapPresheaf` is isomorphic to the composition of the forgetful
functor to `TopCat` and the yoneda embedding.
-/
def continuousMapPresheafIsoUlift :
    continuousMapPresheaf T ≅
      Scheme.forgetToTop.op ⋙ TopCat.uliftFunctor.op ⋙ yoneda.obj (.of <| ULift T) :=
  NatIso.ofComponents fun U ↦ equivEquivIso <|
    (ContinuousMap.uliftEquiv U.1 T).symm.trans
    (TopCat.Hom.equivContinuousMap
      (TopCat.uliftFunctor.obj <| Scheme.forgetToTop.obj U.1)
      (TopCat.uliftFunctor.obj (TopCat.of T))).symm
/-
**AlgebraicGeometry.isSheaf_zariskiTopology_continuousMapPresheaf** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isSheaf_zariskiTopology_continuousMapPresheaf : Presheaf.IsSheaf Scheme.za
riskiTopology (continuousMapPresheaf T)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_of_iso_iff`：isSheaf_of_iso_iff {P P' : C
ᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P'
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf_of_isSheaf`：op_comp_isSheaf_of_is
Sheaf [IsContinuous F J K] (P : Dᵒᵖ ⥤ A) (h : Presheaf.IsSheaf K P) : Presheaf.I
sSheaf J (F.op ⋙ P)
· 使用定理 `AlgebraicGeometry.Scheme.instIsContinuousTopCatForgetToTopZariskiTopolog
yGrothendieckTopology`：AlgebraicGeometry.Scheme.forgetToTop.IsContinuous Algebra
icGeometry.Scheme.zariskiTopology TopCat.grothendieckTopology
· 使用定理 `TopCat.instIsContinuousUliftFunctorGrothendieckTopology`：TopCat.uliftFun
ctor.IsContinuous TopCat.grothendieckTopology TopCat.grothendieckTopology
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresenta
ble`：isSheaf_of_isRepresentable {J : GrothendieckTopology C} [Subcanonical J] (P
 : Cᵒᵖ ⥤ Type w) [P.IsRepresentable] : Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.Functor.instIsRepresentableObjOppositeTypeYoneda`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C}, (CategoryTheory.yo
neda.obj X).IsRepresentable
-/
lemma isSheaf_zariskiTopology_continuousMapPresheaf :
    Presheaf.IsSheaf Scheme.zariskiTopology (continuousMapPresheaf T) := by
  rw [Presheaf.isSheaf_of_iso_iff (continuousMapPresheafIsoUlift T)]
  apply Scheme.forgetToTop.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  apply TopCat.uliftFunctor.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isSheaf_fpqcTopology_continuousMapPresheaf : Presheaf.IsSheaf Scheme.fpqcT
opology (continuousMapPresheaf T)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用引理 `AlgebraicGeometry.Scheme.fpqcTopology_eq_propQCTopology`：fpqcTopology_eq
_propQCTopology : fpqcTopology = Scheme.propQCTopology @Flat
· 使用定理 `AlgebraicGeometry.isSheaf_type_propQCTopology_iff`：∀ {P : CategoryTheory
.MorphismProperty AlgebraicGeometry.Scheme} [P.IsStableUnderBaseChange] [P.IsMul
tiplicative]   (F : CategoryTheory.Func…
· 使用定理 `AlgebraicGeometry.Flat.instIsMultiplicativeScheme`：CategoryTheory.Morphi
smProperty.IsMultiplicative @AlgebraicGeometry.Flat
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.isSheaf_zariskiTopology_continuousMapPresheaf`：isSheaf
_zariskiTopology_continuousMapPresheaf : Presheaf.IsSheaf Scheme.zariskiTopology
 (continuousMapPresheaf T)
· 使用引理 `CategoryTheory.Presieve.isSheafFor_singleton`：isSheafFor_singleton {X Y 
: C} {f : X ⟶ Y} : Presieve.IsSheafFor P (.singleton f) ↔ forall (x : P.obj (op 
X)), (forall {Z : C} (p₁ p₂ : Z ⟶ …
· 使用引理 `AlgebraicGeometry.Flat.isQuotientMap_of_surjective`：isQuotientMap_of_sur
jective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f] 
: Topology.IsQuotientMap f
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffineHom f], AlgebraicGeometry.Qua
siCompact f
· 使用定理 `AlgebraicGeometry.isAffineHom_of_isAffine`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y],
   AlgebraicGeometry.IsAffineHo…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`：exists_preim
age_pullback (x : X) (y : Y) (h : f x = g y) : exists z : ↑(pullback f g), pullb
ack.fst f g z = x ∧ pullback.snd f g z = y
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `Topology.IsQuotientMap.lift_comp`：lift_comp : (hf.lift g h).comp f = g
· 使用定理 `ContinuousMap.cancel_right`：cancel_right {f₁ f₂ : C(β, γ)} {g : C(α, β)}
 (hg : Surjective g) : f₁.comp g = f₂.comp g ↔ f₁ = f₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.surjective`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
-/
lemma isSheaf_fpqcTopology_continuousMapPresheaf :
    Presheaf.IsSheaf Scheme.fpqcTopology (continuousMapPresheaf T) := by
  rw [isSheaf_iff_isSheaf_of_type, Scheme.fpqcTopology_eq_propQCTopology,
    isSheaf_type_propQCTopology_iff]
  refine ⟨?_, fun {R S} f hf₁ hf₂ ↦ ?_⟩
  · rw [← isSheaf_iff_isSheaf_of_type]
    exact isSheaf_zariskiTopology_continuousMapPresheaf _
  · rw [Presieve.isSheafFor_singleton]
    have : Topology.IsQuotientMap (Spec.map f) := Flat.isQuotientMap_of_surjective _
    intro (x : C(Spec S, T)) h
    refine ⟨?_, ?_, ?_⟩
    · refine Topology.IsQuotientMap.lift this x fun a b hfab ↦ ?_
      obtain ⟨c, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback a b hfab
      exact congr($(h (pullback.fst (Spec.map f) (Spec.map f))
        (pullback.snd _ _) pullback.condition).1 c)
    · apply Topology.IsQuotientMap.lift_comp
    · intro y hy
      rwa [← ContinuousMap.cancel_right (Spec.map f).surjective, Topology.IsQuotientMap.lift_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-- `continuousMapPresheaf` is `U ↦ C(ConnectedComponents U, T)` if `T` is totally
disconnected. -/
/-
**AlgebraicGeometry.continuousMapPresheafEquivOfTotallyDisconnectedSpace** 是 Mat
hlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：continuousMapPresheafEquivOfTotallyDisconnectedSpace [TotallyDisconnectedS
pace T] (U : Scheme.{u}) : (continuousMapPresheaf T).obj (.op U) ≃ C(ConnectedCo
mponents U, T) where toFun f
参数：U : Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`continuousMapPresheaf` is `U ↦ C(ConnectedComponents U, T)` if `T` is totally
disconnected.
-/
def continuousMapPresheafEquivOfTotallyDisconnectedSpace [TotallyDisconnectedSpace T]
    (U : Scheme.{u}) :
    (continuousMapPresheaf T).obj (.op U) ≃ C(ConnectedComponents U, T) where
  toFun f := ⟨f.continuous.connectedComponentsLift, f.continuous.connectedComponentsLift_continuous⟩
  invFun f := .comp f ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  right_inv f := by
    apply ContinuousMap.coe_injective
    dsimp
    exact (Continuous.connectedComponentsLift_unique _ _ (by simp)).symm

/-- `continuousMapPresheaf` as a presheaf of abelian groups associated to a topological abelian
group. -/
/-
**AlgebraicGeometry.continuousMapPresheafAb** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry`。
形式化陈述：continuousMapPresheafAb (A : Type v) [TopologicalSpace A] [AddCommGroup A]
 [IsTopologicalAddGroup A] : Scheme.{u}ᵒᵖ ⥤ Ab.{max v u} where obj U
参数：A : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`continuousMapPresheaf` as a presheaf of abelian groups associated to a topologi
cal abelian
group.
-/
def continuousMapPresheafAb (A : Type v) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] :
    Scheme.{u}ᵒᵖ ⥤ Ab.{max v u} where
  obj U := AddCommGrpCat.of C(U.unop, A)
  map {U V} f := AddCommGrpCat.ofHom (ContinuousMap.compAddMonoidHom' f.unop.base.hom)

variable (A : Type v) [TopologicalSpace A] [AddCommGroup A] [IsTopologicalAddGroup A]

/-- `continuousMapPresheafAb` viewed as a type valued sheaf is isomorphic to
`continuousMapPresheaf`. -/
/-
**AlgebraicGeometry.continuousMapPresheafAbForgetIso** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：continuousMapPresheafAbForgetIso : continuousMapPresheafAb A ⋙ CategoryThe
ory.forget Ab ≅ continuousMapPresheaf A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`continuousMapPresheafAb` viewed as a type valued sheaf is isomorphic to
`continuousMapPresheaf`.
-/
def continuousMapPresheafAbForgetIso :
    continuousMapPresheafAb A ⋙ CategoryTheory.forget Ab ≅ continuousMapPresheaf A :=
  Iso.refl _
/-
**AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheafAb** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isSheaf_fpqcTopology_continuousMapPresheafAb : Presheaf.IsSheaf Scheme.fpq
cTopology (continuousMapPresheafAb A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp`：isSheaf_of_isSheaf_comp
 (s : A ⥤ B) [ReflectsLimitsOfSize.{v₁, max v₁ u₁} s] (h : IsSheaf J (P ⋙ s)) : 
IsSheaf J P
· 使用定理 `CategoryTheory.reflectsLimitsOfCreatesLimits`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
· 使用引理 `AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf`：isSheaf_fp
qcTopology_continuousMapPresheaf : Presheaf.IsSheaf Scheme.fpqcTopology (continu
ousMapPresheaf T)
-/
lemma isSheaf_fpqcTopology_continuousMapPresheafAb :
    Presheaf.IsSheaf Scheme.fpqcTopology (continuousMapPresheafAb A) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget Ab)
  exact isSheaf_fpqcTopology_continuousMapPresheaf _

end AlgebraicGeometry

