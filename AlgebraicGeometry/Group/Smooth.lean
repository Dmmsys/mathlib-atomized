/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Smoothness of group schemes

## Main results
- `AlgebraicGeometry.smooth_of_grpObj`:
  If `G` is a group scheme over a field `k` that is geometrically reduced and locally
  of finite type, then `G` is smooth over `k`.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {G : Scheme} (f : G ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [GrpObj (Over.mk f)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open MonObj MonoidalCategory CartesianMonoidalCategory in
/--
If `G` is a group scheme over an algebraically closed field `k` that is reduced and locally
of finite type, then `G` is smooth over `k`.
-/
/-
**AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is a group scheme over an algebraically closed field `k` that is reduced 
and locally
of finite type, then `G` is smooth over `k`.
-/
private lemma smooth_of_grpObj_of_isAlgClosed [IsReduced G] [IsAlgClosed K] : Smooth f := by
  have := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty G := ⟨η[Over.mk f].1 (IsLocalRing.closedPoint _)⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints H f.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy : y ∈ f.smoothLocus, hyc⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.2.isLocallyClosed
  let x' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨x, hxc⟩).2
  let y' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨y, hyc⟩).2
  let α := (GrpObj.mulRight (A := Over.mk f) x').symm ≪≫
    (GrpObj.mulRight (A := Over.mk f) y')
  have hα : x' ≫ α.hom = y' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have hα' : α.hom.left x = y := by
    simpa [x', y', pointEquivClosedPoint] using congr(($hα).left (IsLocalRing.closedPoint K))
  rw! [← hα', ← α.hom.left.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    show α.hom.left ≫ f = f from α.hom.w] at hy
  exact hx hy
/-
**AlgebraicGeometry.smooth_of_grpObj** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：smooth_of_grpObj [GeometricallyReduced f] : Smooth f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_pullback_snd_of_descendsAlong`：of_pul
lback_snd_of_descendsAlong [P.DescendsAlong Q] [HasPullback f g] (hg : Q g) (hsn
d : P (pullback.snd f g)) : P f
· 使用定理 `AlgebraicGeometry.instDescendsAlongSchemeSmoothMinMorphismPropertySurjec
tiveFlatQuasiCompact`：CategoryTheory.MorphismProperty.DescendsAlong (@AlgebraicG
eometry.Smooth)   (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓ @Al
ge…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.instSurjectiveOfNonemptyOfSubsingletonCarrierCarrierCo
mmRingCat`：∀ {X Y : AlgebraicGeometry.Scheme} [Nonempty ↥X] [Subsingleton ↥Y] (f
 : X ⟶ Y), AlgebraicGeometry.Surjective f
· 使用定理 `AlgebraicGeometry.instNonemptyCarrierCarrierCommRingCatSpecOfNontrivialC
arrier`：∀ {A : CommRingCat} [Nontrivial ↑A], Nonempty ↥(AlgebraicGeometry.Spec A
)
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `AlgebraicGeometry.Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIn
tegral`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [Subsingleton ↥Y] [Algebr
aicGeometry.IsIntegral Y],   AlgebraicGeometry.Flat f
· 使用定理 `AlgebraicGeometry.instIsIntegralSpecOfIsDomainCarrier`：∀ {R : CommRingCa
t} [IsDomain ↑R], AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Spec R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffineHom f], AlgebraicGeometry.Qua
siCompact f
· 使用定理 `AlgebraicGeometry.isAffineHom_of_isAffine`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y],
   AlgebraicGeometry.IsAffineHo…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `_private.Mathlib.AlgebraicGeometry.Group.Smooth.0.AlgebraicGeometry.smoo
th_of_grpObj_of_isAlgClosed`：∀ {K : Type u} [inst : Field K] {G : AlgebraicGeome
try.Scheme} (f : G ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))   [AlgebraicGeom
etry.Loca…
· 使用定理 `AlgebraicGeometry.instLocallyOfFiniteTypeSndScheme`：∀ {X Y S : Algebraic
Geometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType 
f],   AlgebraicGeometry.LocallyOfFiniteT…
· 使用定理 `AlgebraicGeometry.instIsReducedPullbackSchemeOfGeometricallyReducedOfFla
tOfIsLocallyNoetherian`：∀ {X Y S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y 
⟶ S) [AlgebraicGeometry.GeometricallyReduced f]   [AlgebraicGeometry.Flat f] [Al
gebr…
· 使用定理 `AlgebraicGeometry.instIsReducedSpecOfIsReducedCarrier`：∀ {R : CommRingCa
t} [H : IsReduced ↑R], AlgebraicGeometry.IsReduced (AlgebraicGeometry.Spec R)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `AlgebraicGeometry.instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier`：
∀ {R : CommRingCat} [IsNoetherianRing ↑R], AlgebraicGeometry.IsLocallyNoetherian
 (AlgebraicGeometry.Spec R)
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
-/
lemma smooth_of_grpObj [GeometricallyReduced f] : Smooth f := by
  let Ω : Type u := AlgebraicClosure K
  let g : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom <| algebraMap K Ω)
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := g)
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · let : GrpObj (Over.mk (Limits.pullback.snd f g)) := Over.grpObjMkPullbackSnd
    exact smooth_of_grpObj_of_isAlgClosed _

end AlgebraicGeometry

