/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Abelian varieties

## Main results
- `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`:
  A proper geometrically integral group scheme over a field is commutative.

-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : Over (Spec (.of K))) [GrpObj G] : IsClosedImmersion η[G].left :=
  isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom η[G].left (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClo
sed** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed [IsAlgClos
ed K] (G : Over (Spec (.of K))) [IsProper G.hom] [IsIntegral (G otimes G).left] 
[GrpObj G] : IsCommMonObj G
参数：G : Over (Spec (.of K))；G otimes G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationRing.isLocalRing`：∀ (A : Type u) [inst : CommRing A] [Nontrivia
l A] [PreValuationRing A], IsLocalRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `ValuationRing.of_field`：∀ (K : Type u) [inst : Field K], ValuationRing K
· 使用定理 `isClosed_discrete`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Discret
eTopology α] (s : Set α), IsClosed s
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.discreteTopology`：∀ {X : AlgebraicGe
ometry.Scheme} [AlgebraicGeometry.IsLocallyArtinian X], DiscreteTopology ↥X
· 使用定理 `AlgebraicGeometry.IsArtinianScheme.toIsLocallyArtinian`：∀ {X : Algebraic
Geometry.Scheme} [self : AlgebraicGeometry.IsArtinianScheme X], AlgebraicGeometr
y.IsLocallyArtinian X
· 使用定理 `AlgebraicGeometry.instIsArtinianSchemeSpecOfIsArtinianRingCarrier`：∀ {R 
: CommRingCat} [IsArtinianRing ↑R], AlgebraicGeometry.IsArtinianScheme (Algebrai
cGeometry.Spec R)
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.IsProper.instCompScheme`：∀ {X Y Z : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsProper f]   [AlgebraicGeome
try.IsProper g], AlgebraicGeome…
· 使用定理 `AlgebraicGeometry.IsProper.instFstScheme`：∀ {X Y S : AlgebraicGeometry.S
cheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.IsProper g],   AlgebraicGeomet
ry.IsProper (CategoryTheory.Li…
· 使用定理 `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f] [JacobsonS
pace ↥Y],   JacobsonSpace ↥X
· 使用定理 `AlgebraicGeometry.IsProper.toLocallyOfFiniteType`：∀ {X Y : AlgebraicGeom
etry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsProper f],   AlgebraicGeome
try.LocallyOfFiniteType f
· 使用定理 `AlgebraicGeometry.instJacobsonSpaceCarrierCarrierCommRingCatSpecOfOfIsJa
cobsonRing`：∀ {R : Type u_1} [inst : CommRing R] [IsJacobsonRing R], JacobsonSpa
ce ↥(AlgebraicGeometry.Spec (CommRingCat.of R))
· 使用定理 `instIsJacobsonRingOfKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : CommRin
g R] [Ring.KrullDimLE 0 R], IsJacobsonRing R
· 使用定理 `IsArtinianRing.instKrullDimLEOfNatNat`：∀ (R : Type u_1) [inst : CommRing
 R] [IsArtinianRing R], Ring.KrullDimLE 0 R
· 使用定理 `Function.surjective_to_subsingleton`：surjective_to_subsingleton [na : No
nempty α] [Subsingleton β] (f : α -> β) : Surjective f
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `AlgebraicGeometry.Surjective.instFstScheme`：∀ {X Y Z : AlgebraicGeometry
.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.Surjective g],   AlgebraicGe
ometry.Surjective (CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Over.Hom.w`：∀ {T : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Over X} (φ : f ⟶ g),   CategoryTheo
ry.CategoryStru…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 142 条，此处仅展示前 30 条）
-/
theorem isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed [IsAlgClosed K]
    (G : Over (Spec (.of K))) [IsProper G.hom] [IsIntegral (G ⊗ G).left] [GrpObj G] :
    IsCommMonObj G := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : Nonempty G.left := ⟨η[G].left point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsProper ((GrpObj.commutator G).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsClosedImmersion ((lift η[G] η[G]).left ≫ (fst G G).left) := by
    simpa using inferInstanceAs (IsClosedImmersion η[G].left)
  have : IsClosedImmersion (lift η[G] η[G]).left := .of_comp _ (g := (fst G G).left)
  let γ : G ⊗ G ⟶ G ⊗ G := lift (fst _ _) (GrpObj.commutator _)
  have : IsProper (γ.left ≫ (fst G G).left) := by simpa [γ]
  have : IsProper γ.left := .of_comp _ (fst G G).left
  -- It suffices to check that `γ : (x, y) ↦ x * y * x⁻¹ * y⁻¹` is constantly `1`.
  rw [isCommMonObj_iff_commutator_eq_toUnit_η]
  ext1
  have H : γ.left '' ((fst G G).left ⁻¹' {η[G].left point}) ⊆ {(lift η[G] η[G]).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro H
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton];
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift η[G] η[G]).left.isClosedMap _ hpoint).preimage γ.left.continuous).isOpen_compl
      · exact (η[G].left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨c, hc⟩, e⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : c point = c₀ := congr(($e).1)
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (Over.homMk c hc ≫ snd G G)
    have : c ≫ pullback.fst G.hom G.hom = η[G].left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa) (by simp) (by simpa)
    have H₁ : c = fc.left ≫ (η[G] ▷ G).left := by dsimp; ext <;> simp [fc, S, this]
    have H₂ : fc ≫ η ▷ G ≫ γ = lift η η := by ext1 <;> simp [fc, γ, S]
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  -- Since the image of `y ↦ γ(e, y)` is finite, by Zariski Main, there exists an open
  -- `1 ∈ U ⊆ G` such that `γ ∣_ U` factors through a finite scheme over `U`.
  obtain ⟨U, hηU, H⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    γ.left (fst G G).left (η[G].left point) (by
      dsimp [-Scheme.Hom.comp_base, γ]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset H)
  have H (x : U) : ((pullback.fst G.hom G.hom) ⁻¹' {x.1} ∩ Set.range ⇑γ.left).Finite := by
    refine ((((γ.left.imageι ≫ (fst G G).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ γ.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G G).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact γ.left.isClosedMap.isClosed_range)]
  -- It suffices to check set-theoretic equality on closed points of `U ×[k] G`.
  refine ext_of_apply_eq G.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by simpa using (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    let xe : (G ⊗ G).left := (fst G G ≫ (ρ_ _).inv ≫ G ◁ η[G]).left y
    have : γ.left y = xe := by
      -- By the choice of `U`, the set `γ({y} ×[k] G)` is finite and hence, by irreducibility,
      -- a singleton.
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ γ.left.continuous
        γ.left.isClosedMap ((H ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, γ])) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert!
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨xe, subset_closure ?_, ?_⟩
        · simp [xe, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
        · simp only [xe, γ, ← Scheme.Hom.comp_apply, ← Over.comp_left]
          congr 6; ext <;> simp
    convert! congr((snd G G).left $this) using 1
    · simp [γ, ← Scheme.Hom.comp_apply]
    · simp [xe, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
  · simp

set_option backward.defeqAttrib.useBackward true in
/-- A proper geometrically integral group scheme over a field is commutative. -/
@[stacks 0BFD]
/-
**AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isCommMonObj_of_isProper_of_geometricallyIntegral (G : Over (Spec (.of K))
) [IsProper G.hom] [GeometricallyIntegral G.hom] [GrpObj G] : IsCommMonObj G
参数：G : Over (Spec (.of K))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.IsProper.instSndScheme`：∀ {X Y S : AlgebraicGeometry.S
cheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.IsProper f],   AlgebraicGeomet
ry.IsProper (CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.instIsIntegralPullbackSchemeOfGeometricallyIntegralOfF
latOfUniversallyOpenOfIsLocallyNoetherian_1`：∀ {X Y S : AlgebraicGeometry.Scheme
} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.GeometricallyIntegral g]   [Algebra
icGeometry.Flat g] [Algeb…
· 使用定理 `AlgebraicGeometry.instGeometricallyIntegralSndScheme`：∀ {X Y S : Algebra
icGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.GeometricallyInteg
ral f],   AlgebraicGeometry.GeometricallyI…
· 使用定理 `AlgebraicGeometry.Flat.instSndScheme`：∀ {X Y Z : AlgebraicGeometry.Schem
e} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.Flat f],   AlgebraicGeometry.Flat 
(CategoryTheory.Limits.pul…
· 使用定理 `AlgebraicGeometry.Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIn
tegral`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [Subsingleton ↥Y] [Algebr
aicGeometry.IsIntegral Y],   AlgebraicGeometry.Flat f
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `AlgebraicGeometry.instIsIntegralSpecOfIsDomainCarrier`：∀ {R : CommRingCa
t} [IsDomain ↑R], AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Spec R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `AlgebraicGeometry.instUniversallyOpenOfIsIntegralOfSubsingletonCarrierCa
rrierCommRingCat`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeome
try.IsIntegral Y] [Subsingleton ↥Y],   AlgebraicGeometry.UniversallyOpen f
· 使用定理 `AlgebraicGeometry.instIsIntegralPullbackSchemeOfGeometricallyIntegralOfF
latOfUniversallyOpenOfIsLocallyNoetherian`：∀ {X Y S : AlgebraicGeometry.Scheme} 
(f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.GeometricallyIntegral f]   [Algebraic
Geometry.Flat f] [Algeb…
· 使用定理 `AlgebraicGeometry.instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier`：
∀ {R : CommRingCat} [IsNoetherianRing ↑R], AlgebraicGeometry.IsLocallyNoetherian
 (AlgebraicGeometry.Spec R)
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFinite
Type`：∀ {X Y S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeo
metry.IsLocallyNoetherian Y]   [AlgebraicGeometry.LocallyOfFiniteT…
· 使用定理 `AlgebraicGeometry.IsProper.toLocallyOfFiniteType`：∀ {X Y : AlgebraicGeom
etry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsProper f],   AlgebraicGeome
try.LocallyOfFiniteType f
· 使用定理 `AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_is
AlgClosed`：isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed [IsAl
gClosed K] (G : Over (Spec (.of K))) [IsProper G.hom] [IsIntegral (G ot…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isCommMonObj_iff_commutator_eq_toUnit_η`：isCommMonObj_iff
_commutator_eq_toUnit_η : IsCommMonObj G ↔ GrpObj.commutator G = toUnit _ ≫ η
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `AlgebraicGeometry.instFaithfulOverSchemePullbackOfSurjectiveOfFlatOfQuas
iCompact`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Surj
ective f] [AlgebraicGeometry.Flat f]   [AlgebraicGeometry.QuasiCompact…
· 使用定理 `AlgebraicGeometry.instSurjectiveOfNonemptyOfSubsingletonCarrierCarrierCo
mmRingCat`：∀ {X Y : AlgebraicGeometry.Scheme} [Nonempty ↥X] [Subsingleton ↥Y] (f
 : X ⟶ Y), AlgebraicGeometry.Surjective f
· 使用定理 `AlgebraicGeometry.instNonemptyCarrierCarrierCommRingCatSpecOfNontrivialC
arrier`：∀ {A : CommRingCat} [Nontrivial ↑A], Nonempty ↥(AlgebraicGeometry.Spec A
)
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffineHom f], AlgebraicGeometry.Qua
siCompact f
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
A proper geometrically integral group scheme over a field is commutative.
-/
theorem isCommMonObj_of_isProper_of_geometricallyIntegral
    (G : Over (Spec (.of K))) [IsProper G.hom] [GeometricallyIntegral G.hom] [GrpObj G] :
    IsCommMonObj G := by
  let f := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let G' := (Over.pullback f).obj G
  have : IsProper G'.hom := by dsimp [G']; infer_instance
  have : IsIntegral (G' ⊗ G').left := by dsimp [G']; infer_instance
  let : GrpObj G' := Functor.grpObjObj
  have := isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed G'
  rw [isCommMonObj_iff_commutator_eq_toUnit_η] at this ⊢
  apply (Over.pullback f).map_injective
  rw [← cancel_epi (Functor.Monoidal.μIso (Over.pullback f) G G).hom]
  dsimp [GrpObj.commutator] at this ⊢
  simpa only [Functor.map_mul, one_eq_one, comp_one, Functor.map_one, Functor.map_inv',
    comp_mul, GrpObj.comp_inv, Functor.Monoidal.μ_fst, Functor.Monoidal.μ_snd]

end AlgebraicGeometry

