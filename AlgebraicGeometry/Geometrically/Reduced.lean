/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Geometrically Reduced Schemes

## Main results
- `AlgebraicGeometry.GeometricallyReduced`:
  We say that morphism `f : X ⟶ Y` is geometrically reduced if for all `Spec K ⟶ Y` with `K`
  a field, `X ×[Y] Spec K` is reduced.
  We also provide the fact that this is stable under base change (by `infer_instance`)
- `GeometricallyReduced.iff_geometricallyReduced_fiber`:
  A scheme is geometrically reduced over `S` iff the fibers of all
  `s : S` are geometrically reduced.
- `AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`:
  If `X` is geometrically reduced and flat over a reduced and locally noetherian scheme,
  then `X` is also reduced.
  In particular, the base change of a geometrically reduced and flat scheme to an
  reduced and locally noetherian scheme is reduced (by `infer_instance`).

## TODO
Get rid of the noetherian assumption.
-/

public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- We say that morphism `f : X ⟶ Y` is geometrically reduced if for all `Spec K ⟶ Y` with `K`
a field, `X ×[Y] Spec K` is reduced. -/
@[mk_iff]
/-
**AlgebraicGeometry.GeometricallyReduced** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicG
eometry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that morphism `f : X ⟶ Y` is geometrically reduced if for all `Spec K ⟶ Y
` with `K`
a field, `X ×[Y] Spec K` is reduced.
-/
class GeometricallyReduced (f : X ⟶ Y) : Prop where
  geometrically_isReduced : geometrically IsReduced f
/-
**AlgebraicGeometry.GeometricallyReduced.eq_geometrically** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.GeometricallyReduced`。
形式化陈述：@AlgebraicGeometry.GeometricallyReduced = AlgebraicGeometry.geometrically 
AlgebraicGeometry.IsReduced
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.geometricallyReduced_iff`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y),   AlgebraicGeometry.GeometricallyReduced f ↔ AlgebraicGeomet
ry.geometrically AlgebraicGeomet…
-/
lemma GeometricallyReduced.eq_geometrically :
    @GeometricallyReduced = geometrically IsReduced := by
  ext; exact geometricallyReduced_iff _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderBaseChange @GeometricallyReduced :=
  GeometricallyReduced.eq_geometrically ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyReduced g] : GeometricallyReduced (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyReduced f] : GeometricallyReduced (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : S.Opens) [GeometricallyReduced f] : GeometricallyReduced (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict ..).flip ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : S) [GeometricallyReduced f] :
    GeometricallyReduced (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : S) [GeometricallyReduced f] : IsReduced (f.fiber s) :=
  GeometricallyReduced.geometrically_isReduced _ _ _ (.of_hasPullback _ _)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_finite_irreducible
Components** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.GeometricallyReduced`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Geometri
callyReduced f] [AlgebraicGeometry.Flat f]   [AlgebraicGeometry.IsReduced Y] [Fi
nite ↑(irreducibleComponents ↥Y)], AlgebraicGeometry.IsReduced X
参数：f : X ⟶ Y；irreducibleComponents ↥Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents`：is
Field_stalk_of_closure_mem_irreducibleComponents (x : X) (hx : closure {x} in ir
reducibleComponents X) [IsReduced X] : IsField (X.presheaf…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIrreducible.closure_genericPoint`：IsIrreducible.closure_genericPoint [
QuasiSober α] {S : Set α} (hS : IsIrreducible S) (hS' : IsClosed S) : closure ({
hS.genericPoint} : Set α…
· 使用定理 `isClosed_of_mem_irreducibleComponents`：isClosed_of_mem_irreducibleCompon
ents (s) (H : s in irreducibleComponents X) : IsClosed s
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `AlgebraicGeometry.IsArtinianScheme.finite`：∀ {X : AlgebraicGeometry.Sche
me} [AlgebraicGeometry.IsArtinianScheme X], Finite ↥X
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
· 使用定理 `Set.Finite.isCompact`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Se
t X}, s.Finite → IsCompact s
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用引理 `AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isDominant`：isScheme
TheoreticallyDominant_iff_isDominant (f : X ⟶ Y) [QuasiCompact f] [IsReduced Y] 
: IsSchemeTheoreticallyDominant f ↔ IsDominant f
· 使用定理 `AlgebraicGeometry.isDominant_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f 
: X ⟶ Y), AlgebraicGeometry.IsDominant f ↔ DenseRange ⇑f
· 使用定理 `denseRange_iff_closure_range`：denseRange_iff_closure_range : DenseRange 
f ↔ closure (range f) = univ
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `irreducibleComponent_mem_irreducibleComponents`：irreducibleComponent_mem
_irreducibleComponents (x : X) : irreducibleComponent x in irreducibleComponents
 X
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 56 条，此处仅展示前 30 条）
-/
lemma GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents
    (f : X ⟶ Y) [GeometricallyReduced f] [Flat f]
    [IsReduced Y] [Finite (irreducibleComponents Y)] : IsReduced X := by
  let pt (Z : irreducibleComponents Y) := Y.presheaf.stalk Z.property.1.genericPoint
  have hpt (Z : _) : IsField (pt Z) :=
    isField_stalk_of_closure_mem_irreducibleComponents _ _ (by
      rw [Z.property.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.property)]
      exact Z.property)
  let (Z : _) := (hpt Z).toField
  let Z := ∐ fun Z ↦ Spec (pt Z)
  let g : Z ⟶ Y := Sigma.desc fun Z ↦ Y.fromSpecStalk _
  have : Finite Z := (sigmaMk _).finite_iff.mp inferInstance
  have : QuasiCompact g := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  have H : IsSchemeTheoreticallyDominant g := by
    rw [isSchemeTheoreticallyDominant_iff_isDominant, isDominant_iff, denseRange_iff_closure_range,
      Set.eq_univ_iff_forall]
    intro y
    let z : Z := Sigma.ι (fun Z ↦ Spec (pt Z)) ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩
      (IsLocalRing.closedPoint _)
    have hz : g z ⤳ y := by
      simp only [g, z, Z, ← Scheme.Hom.comp_apply, Sigma.ι_desc, pt,
        Scheme.fromSpecStalk_closedPoint]
      exact (IsIrreducible.isGenericPoint_genericPoint _
        isClosed_irreducibleComponent).specializes mem_irreducibleComponent
    exact hz.mem_closed isClosed_closure (subset_closure ⟨_, rfl⟩)
  suffices IsReduced (pullback f g) from IsSchemeTheoreticallyDominant.isReduced (pullback.fst f g)
  have H := IsUniversalColimit.isPullback_of_isColimit_left
    (X := fun Z ↦ Spec (pt Z))
    (FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct _))
    (fun Z ↦ Y.fromSpecStalk _) g f _ _ (fun _ ↦ .of_hasPullback _ _) (coproductIsCoproduct _)
  apply +allowSynthFailures @isReduced_of_isOpenImmersion (f := H.isoPullback.inv)
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := sigmaOpenCover _)
  exact fun i ↦ GeometricallyReduced.geometrically_isReduced _ _ _ (.of_hasPullback _ _)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetheria
n** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.GeometricallyReduced`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Geometri
callyReduced f] [AlgebraicGeometry.Flat f]   [AlgebraicGeometry.IsReduced Y] [Al
gebraicGeometry.IsLocallyNoetherian Y], AlgebraicGeometry.IsReduced X
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsReduced.of_openCover`：∀ (X : AlgebraicGeometry.Schem
e) (𝒰 : X.OpenCover) [∀ (i : 𝒰.I₀), AlgebraicGeometry.IsReduced (𝒰.X i)],   Alge
braicGeometry.IsReduced X
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.isReduced_of_isOpenImmersion`：isReduced_of_isOpenImmer
sion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] [IsReduced Y] : IsReduced X
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.instIsLocallyNoetherianXScheme`：∀ {X : AlgebraicGeomet
ry.Scheme} {U : X.OpenCover} (i : U.I₀) [AlgebraicGeometry.IsLocallyNoetherian X
],   AlgebraicGeometry.IsLocallyNoethe…
· 使用定理 `AlgebraicGeometry.Scheme.compactSpace_of_isAffine`：∀ (X : AlgebraicGeome
try.Scheme) [AlgebraicGeometry.IsAffine X], CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
· 使用定理 `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`：∀ {α : Ty
pe u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianSpace α], (irred
ucibleComponents α).Finite
· 使用定理 `AlgebraicGeometry.IsNoetherian.noetherianSpace`：∀ {X : AlgebraicGeometry
.Scheme} [AlgebraicGeometry.IsNoetherian X], TopologicalSpace.NoetherianSpace ↥X
· 使用定理 `AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_finite_irred
ucibleComponents`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeome
try.GeometricallyReduced f] [AlgebraicGeometry.Flat f]   [AlgebraicGeometry.Is…
· 使用定理 `AlgebraicGeometry.instGeometricallyReducedSndScheme`：∀ {X Y S : Algebrai
cGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.GeometricallyReduce
d f],   AlgebraicGeometry.GeometricallyRe…
· 使用定理 `AlgebraicGeometry.Flat.instSndScheme`：∀ {X Y Z : AlgebraicGeometry.Schem
e} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.Flat f],   AlgebraicGeometry.Flat 
(CategoryTheory.Limits.pul…
-/
lemma GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (f : X ⟶ Y) [GeometricallyReduced f] [Flat f]
    [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced X := by
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := Y.affineCover.pullback₁ f)
  intro i
  have : IsReduced (Y.affineCover.X i) := isReduced_of_isOpenImmersion (Y.affineCover.f i)
  have : Finite ↑(irreducibleComponents ↥(Y.affineCover.X i)) := by
    let : IsNoetherian (Y.affineCover.X i) := {}
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  exact isReduced_of_flat_of_finite_irreducibleComponents (pullback.snd _ _)

/-- If `X` is geometrically reduced over `S`, and `Y` is both reduced and locally noetherian,
then `X ×ₛ Y` is also reduced.

TODO: get rid of the noetherian hypothesis. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is geometrically reduced over `S`, and `Y` is both reduced and locally no
etherian,
then `X ×ₛ Y` is also reduced.

TODO: get rid of the noetherian hypothesis.
-/
instance [GeometricallyReduced f] [Flat f] [IsReduced Y] [IsLocallyNoetherian Y] :
    IsReduced (pullback f g) :=
  GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.snd _ _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyReduced g] [Flat g] [IsReduced X] [IsLocallyNoetherian X] :
    IsReduced (pullback f g) :=
  GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.fst _ _)

end AlgebraicGeometry

