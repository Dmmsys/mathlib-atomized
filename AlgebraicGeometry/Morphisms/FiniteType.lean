/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Small
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Morphisms of finite type

A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.

A morphism of schemes is of finite type if it is both locally of finite type and quasi-compact.

We show that these properties are local, and are stable under compositions and base change.

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.
-/
@[mk_iff]
/-
**AlgebraicGeometry.LocallyOfFiniteType** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：LocallyOfFiniteType (f : X ⟶ Y) : Prop where finiteType_appLE (f) : forall
 {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <=
 f ⁻¹ᵁ U), (f.appLE U V e).hom.FiniteType  alias Scheme.Hom.finiteType_appLE
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `
U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.
-/
class LocallyOfFiniteType (f : X ⟶ Y) : Prop where
  finiteType_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.FiniteType

alias Scheme.Hom.finiteType_appLE := LocallyOfFiniteType.finiteType_appLE

@[deprecated (since := "2026-01-20")]
alias LocallyOfFiniteType.finiteType_of_affine_subset :=
  Scheme.Hom.finiteType_appLE
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasRingHomProperty @LocallyOfFiniteType RingHom.FiniteType where
  isLocal_ringHomProperty := RingHom.finiteType_isLocal
  eq_affineLocally' := by
    ext X Y f
    rw [locallyOfFiniteType_iff, affineLocally_iff_forall_isAffineOpen]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) locallyOfFiniteType_of_isOpenImmersion [IsOpenImmersion f] :
    LocallyOfFiniteType f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.finiteType_holdsForLocalizationAway.containsIdentities
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsStableUnderComposition @LocallyOfFiniteType :=
  HasRingHomProperty.stableUnderComposition RingHom.finiteType_stableUnderComposition
/-
**AlgebraicGeometry.locallyOfFiniteType_comp** 是 Mathlib 中的一个实例，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：locallyOfFiniteType_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [hf : Lo
callyOfFiniteType f] [hg : LocallyOfFiniteType g] : LocallyOfFiniteType (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `AlgebraicGeometry.instIsStableUnderCompositionSchemeLocallyOfFiniteType`
：CategoryTheory.MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Loc
allyOfFiniteType
-/
instance locallyOfFiniteType_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyOfFiniteType f] [hg : LocallyOfFiniteType g] : LocallyOfFiniteType (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg
/-
**AlgebraicGeometry.locallyOfFiniteType_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：locallyOfFiniteType_of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [Loca
llyOfFiniteType (f ≫ g)] : LocallyOfFiniteType f
参数：f : X ⟶ Y；g : Y ⟶ Z；f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.of_comp`：of_comp (H : forall {R S T
 : Type u} [CommRing R] [CommRing S] [CommRing T], forall (f : R ->+* S) (g : S 
->+* T), Q (g.comp f) -> Q g) {X Y…
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyOfFiniteTypeFiniteType`：A
lgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyOfFiniteType fun {
R S} [CommRing R] [CommRing S] =>   RingHom.FiniteType
· 使用定理 `RingHom.FiniteType.of_comp_finiteType`：of_comp_finiteType {f : A ->+* B}
 {g : B ->+* C} (h : (g.comp f).FiniteType) : g.FiniteType
-/
theorem locallyOfFiniteType_of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ g)] : LocallyOfFiniteType f :=
  HasRingHomProperty.of_comp (fun _ _ ↦ RingHom.FiniteType.of_comp_finiteType) ‹_›
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @LocallyOfFiniteType where
  id_mem _ := inferInstance

open scoped TensorProduct in
/-
**AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange** 是 Mathlib 中的一个
实例，位于命名空间 `AlgebraicGeometry`。
形式化陈述：locallyOfFiniteType_isStableUnderBaseChange : MorphismProperty.IsStableUnd
erBaseChange @LocallyOfFiniteType
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`：isStableUn
derBaseChange (hP : RingHom.IsStableUnderBaseChange Q) : P.IsStableUnderBaseChan
ge
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyOfFiniteTypeFiniteType`：A
lgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyOfFiniteType fun {
R S} [CommRing R] [CommRing S] =>   RingHom.FiniteType
· 使用定理 `RingHom.finiteType_isStableUnderBaseChange`：finiteType_isStableUnderBase
Change : IsStableUnderBaseChange @FiniteType
-/
instance locallyOfFiniteType_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @LocallyOfFiniteType :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.finiteType_isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType g] :
    LocallyOfFiniteType (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [LocallyOfFiniteType f] : LocallyOfFiniteType (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance
/-
**AlgebraicGeometry.LocallyOfFiniteType.stalkMap** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.LocallyOfFiniteType`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyO
fFiniteType f] (x : ↥X),   (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.st
alkMap f x)).EssFiniteType
参数：f : X ⟶ Y；x : ↥X；CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap f
 x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.stalkMap_of_respectsIso`：stalkMap_o
f_respectsIso {Q' : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) 
-> Prop} (hQ' : RingHom.RespectsIso Q') (hQ : fora…
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyOfFiniteTypeFiniteType`：A
lgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyOfFiniteType fun {
R S} [CommRing R] [CommRing S] =>   RingHom.FiniteType
· 使用引理 `RingHom.EssFiniteType.respectsIso`：respectsIso : RespectsIso EssFiniteTy
pe
· 使用引理 `RingHom.HoldsForLocalization.localRingHom`：RingHom.HoldsForLocalization.
localRingHom (hPc : StableUnderComposition P) (hPp : LocalizationPreserves P) (h
Pl : HoldsForLocalization P) {R…
· 使用引理 `RingHom.EssFiniteType.stableUnderComposition`：stableUnderComposition : S
tableUnderComposition EssFiniteType
· 使用引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`：RingHom.IsStableU
nderBaseChange.localizationPreserves : LocalizationPreserves P
· 使用引理 `RingHom.EssFiniteType.isStableUnderBaseChange`：isStableUnderBaseChange :
 IsStableUnderBaseChange EssFiniteType
· 使用引理 `RingHom.EssFiniteType.holdsForLocalization`：holdsForLocalization : Holds
ForLocalization EssFiniteType
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `RingHom.FiniteType.essFiniteType`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] {f : R →+* S}, f.FiniteType → f.EssFiniteTyp
e
-/
lemma LocallyOfFiniteType.stalkMap [LocallyOfFiniteType f] (x : X) :
    (f.stalkMap x).hom.EssFiniteType :=
  HasRingHomProperty.stalkMap_of_respectsIso RingHom.EssFiniteType.respectsIso
    (fun f hf _ _ ↦ RingHom.EssFiniteType.holdsForLocalization.localRingHom
      RingHom.EssFiniteType.stableUnderComposition
      RingHom.EssFiniteType.isStableUnderBaseChange.localizationPreserves _
      (RingHom.FiniteType.essFiniteType hf)) ‹_› x
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [CommRing R] [IsJacobsonRing R] : JacobsonSpace <| Spec <| .of R :=
  inferInstanceAs (JacobsonSpace (PrimeSpectrum R))
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : CommRingCat} [IsJacobsonRing R] : JacobsonSpace (Spec R) :=
  inferInstanceAs (JacobsonSpace (PrimeSpectrum R))

set_option backward.isDefEq.respectTransparency.types false in
nonrec lemma LocallyOfFiniteType.jacobsonSpace
    (f : X ⟶ Y) [LocallyOfFiniteType f] [JacobsonSpace Y] : JacobsonSpace X := by
  wlog hY : ∃ S, Y = Spec S
  · rw [(Scheme.OpenCover.isOpenCover_opensRange (Y.affineCover.pullback₁ f)).jacobsonSpace_iff]
    intro i
    have inst : LocallyOfFiniteType (Y.affineCover.pullbackHom f i) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have inst : JacobsonSpace Y := ‹_› -- TC gets stuck on the WLOG hypothesis without it.
    have inst : JacobsonSpace (Y.affineCover.X i) :=
      .of_isOpenEmbedding (Y.affineCover.f i).isOpenEmbedding
    let e := ((Y.affineCover.pullback₁ f).f i).isOpenEmbedding.isEmbedding.toHomeomorph
    have := this (Y.affineCover.pullbackHom f i) ⟨_, rfl⟩
    exact .of_isClosedEmbedding e.symm.isClosedEmbedding
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have inst : JacobsonSpace (Spec R) := ‹_› -- TC gets stuck on the WLOG hypothesis without it.
    rw [X.affineCover.isOpenCover_opensRange.jacobsonSpace_iff]
    intro i
    have := this _ (X.affineCover.f i ≫ f) ⟨_, rfl⟩
    let e := (X.affineCover.f i).isOpenEmbedding.isEmbedding.toHomeomorph
    exact .of_isClosedEmbedding e.symm.isClosedEmbedding
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl : Spec.map φ = f⟩ := Spec.homEquiv.symm.surjective f
  have : RingHom.FiniteType φ.hom := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom]
  have := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr ‹_›
  exact PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp (isJacobsonRing_of_finiteType (A := R))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The category of affine schemes locally of finite type over a fixed base scheme is essentially small.
TODO: extend this to (relatively) quasi-compact schemes.
-/
/-
**AlgebraicGeometry.essentiallySmall_costructuredArrow_Spec** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry`。
形式化陈述：essentiallySmall_costructuredArrow_Spec (P : MorphismProperty Scheme.{u}) 
(hP : P <= @LocallyOfFiniteType) [P.RespectsIso] : EssentiallySmall.{u} (P.Costr
ucturedArrow ⊤ Scheme.Spec X)
参数：P : MorphismProperty Scheme.{u}；hP : P <= @LocallyOfFiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.EssentiallySmall.of_functor`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用引理 `CommRingCat.essentiallySmall_of_finiteType`：essentiallySmall_of_finiteTy
pe [ObjectProperty.EssentiallySmall.{u} Q] (hPQ : forall S, P S -> exists R, Q R
 ∧ exists (f : R ⟶ S), f.hom.Fin…
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallOfSmall`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty C
)   [CategoryTheory.ObjectProperty.Small.{w, v,…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `CommRingCat.essentiallySmall_of_localizationAway`：essentiallySmall_of_lo
calizationAway [ObjectProperty.EssentiallySmall.{u} Q] (hPQ : forall S, P S -> e
xists s : Set S, Ideal.span s = ⊤ ∧ fo…
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallIsoClosure`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectPropert
y C)   [CategoryTheory.ObjectProperty.EssentiallyS…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `CategoryTheory.MorphismProperty.Comma.prop`：∀ {A : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} B] {T : Type u_…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finiteType_appLE`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) [self : AlgebraicGeometry.LocallyOfFiniteType f] {U : Y.Op
ens},   AlgebraicGeometry.IsAffineO…
· 使用引理 `AlgebraicGeometry.IsAffineOpen.Spec_basicOpen`：Spec_basicOpen {R : CommR
ingCat} (f : R) : IsAffineOpen (X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `PrimeSpectrum.iSup_basicOpen_eq_top_iff`：iSup_basicOpen_eq_top_iff {ι : 
Type*} {f : ι -> R} : (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) = ⊤ ↔ Ideal.span 
(Set.range f) = ⊤
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen`：∀ (R : Typ
e u) [inst : CommRing R] (r : R),   IsLocalization.Away r ↑((AlgebraicGeometry.S
pec.structureSheaf R).obj.obj (Opposite.op (PrimeS…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.essentiallySmall_unop_iff`：essentiallySmal
l_unop_iff (P : ObjectProperty Cᵒᵖ) : ObjectProperty.EssentiallySmall.{w} P.unop
 ↔ ObjectProperty.EssentiallySmall.{w} P
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
The category of affine schemes locally of finite type over a fixed base scheme i
s essentially small.
TODO: extend this to (relatively) quasi-compact schemes.
-/
lemma essentiallySmall_costructuredArrow_Spec
    (P : MorphismProperty Scheme.{u}) (hP : P ≤ @LocallyOfFiniteType) [P.RespectsIso] :
    EssentiallySmall.{u} (P.CostructuredArrow ⊤ Scheme.Spec X) := by
  let F := MorphismProperty.CostructuredArrow.forget P ⊤ Scheme.Spec X ⋙ CostructuredArrow.proj _ _
  refine .of_functor F ?_ ?_
  · let Q' : ObjectProperty CommRingCat.{u} := fun S ↦
      ∃ R, (R ∈ Set.range fun U ↦ Γ(X, U)) ∧ ∃ (f : R ⟶ S), f.hom.FiniteType
    have : Q'.EssentiallySmall := CommRingCat.essentiallySmall_of_finiteType fun S ↦ id
    suffices ObjectProperty.EssentiallySmall.{u} (· ∈ Set.range (Opposite.unop ∘ F.obj)) by
      rw [← ObjectProperty.essentiallySmall_unop_iff]
      refine .of_le (Q := .isoClosure (· ∈ Set.range (Opposite.unop ∘ F.obj))) ?_
      exact fun R ⟨S, e⟩ ↦ ⟨_, ⟨S, rfl⟩, ⟨e.some.unop⟩⟩
    refine CommRingCat.essentiallySmall_of_localizationAway (Q := Q'.isoClosure) ?_
    rintro _ ⟨S, rfl⟩
    have (q : Spec (F.obj S).unop) : ∃ f, q ∈ PrimeSpectrum.basicOpen f ∧
        Q' Γ(Spec (F.obj S).unop, PrimeSpectrum.basicOpen f) := by
      obtain ⟨_, ⟨U, hU, rfl⟩, hqU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ <| S.hom q) isOpen_univ
      obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hqf, hfU⟩ :=
        PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hqU (S.hom ⁻¹ᵁ U).isOpen
      have : LocallyOfFiniteType S.hom := hP _ S.prop
      exact ⟨f, hqf, _, ⟨U, rfl⟩, S.hom.appLE _ _ hfU,
        (S.hom.finiteType_appLE hU (.Spec_basicOpen _)) _⟩
    choose f hqf hf using this
    refine ⟨Set.range f, PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp ?_, Set.forall_mem_range.mpr ?_⟩
    · exact top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hqf _⟩
    · dsimp
      exact fun q ↦ ⟨_, hf q, ⟨(IsLocalization.algEquiv (.powers (f q)) _
        ((Spec.structureSheaf _).obj.obj (op _))).toRingEquiv.toCommRingCatIso⟩⟩
  · intro R
    refine ⟨.ofObj fun f : { f : Spec R.unop ⟶ X // P f } ↦ .mk _ f.1 f.2, inferInstance, ?_⟩
    refine fun S ⟨e⟩ ↦ ⟨_, .mk ⟨Spec.map e.inv.unop ≫ S.hom, ?_⟩,
      ⟨MorphismProperty.CostructuredArrow.isoMk e trivial trivial ?_⟩⟩
    · simp [← Spec.map_comp_assoc, F]
    · exact (P.cancel_left_of_respectsIso _ _).mpr S.prop

end AlgebraicGeometry

