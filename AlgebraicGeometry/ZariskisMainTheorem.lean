/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.Etale.QuasiFinite

/-!

# Zariski's Main Theorem

In this file we prove Grothendieck's reformulation of Zariski's main theorem, namely if
`f : X ⟶ Y` is separated and of finite type, then the map from the quasi-finite locus `U ⊆ X` of
`f` to the relative normalization `X'` of `Y` in `X` is an open immersion.

We then have the following corollaries
- `Scheme.Hom.isOpen_quasiFiniteAt` : If `f` is separated and of finite type, then the quasi-finite
  locus of `f` is open.
- If `f` is itself quasi-finite, then the map `f.toNormalization : X ⟶ X'` is an open immersion.
  This can be accessed via `inferInstance`.
- `IsFinite.of_isProper_of_locallyQuasiFinite`:
  If `f` is proper and quasi-finite, then the map `f.toNormalization : X ⟶ X'` is an isomorphism,
  which implies that `f` itself is finite.

-/

open CategoryTheory Limits

@[expose] public section

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
-- Note: This is weaker than stacks#02LN but is enough to proof Zariski's main.
-- TODO: generalize this.
/-
**AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry`。
形式化陈述：exists_etale_isCompl_of_quasiFiniteAt [IsSeparated f] {x : X} {s : S} (h :
 f x = s) (hx : f.QuasiFiniteAt x) : exists (U : Scheme) (g : U ⟶ S), Etale g ∧ 
s in Set.range g ∧ exists (V W : (pullback f g).Opens) (v : V), IsCompl V W ∧ Is
Finite (V.ι ≫ pullback.snd f g) ∧ pullback.fst f g v.1 = x
参数：h : f x = s；hx : f.QuasiFiniteAt x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finiteType_appLE`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) [self : AlgebraicGeometry.LocallyOfFiniteType f] {U : Y.Op
ens},   AlgebraicGeometry.IsAffineO…
· 使用定理 `Homeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Injective ⇑h
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.IsAffineOpen.toSpecΓ_isoSpec_inv`：toSpecΓ_isoSpec_inv 
: U.toSpecΓ ≫ hU.isoSpec.inv = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)   (hUV : V ≤ (Topologic
alSpace.Opens.map f.base).obj U),   Catego…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`：resLE_comp_ι : f.resLE U V e 
≫ U.ι = V.ι ≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt.quasiFiniteAt`：∀ {X Y : Algeb
raicGeometry.Scheme} {f : X ⟶ Y} {x : ↥X},   AlgebraicGeometry.Scheme.Hom.QuasiF
initeAt f x →     ∀ {V : X.Opens} (hV : Algebr…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用引理 `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`：Algebra.exists
_etale_isIdempotentElem_forall_liesOver_eq {R : Type u} {S : Type v} [CommRing R
] [CommRing S] [Algebra R S] [Algebra.FiniteTy…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RingHom.finite_algebraMap`：finite_algebraMap [Algebra A B] : (algebraMap
 A B).Finite ↔ Module.Finite A B
（共 75 条，此处仅展示前 30 条）
-/
theorem exists_etale_isCompl_of_quasiFiniteAt [IsSeparated f]
    {x : X} {s : S} (h : f x = s) (hx : f.QuasiFiniteAt x) :
    ∃ (U : Scheme) (g : U ⟶ S), Etale g ∧ s ∈ Set.range g ∧
    ∃ (V W : (pullback f g).Opens) (v : V), IsCompl V W ∧ IsFinite (V.ι ≫ pullback.snd f g) ∧
      pullback.fst f g v.1 = x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hUV : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  have : (f.appLE U V hUV).hom.FiniteType := f.finiteType_appLE hU hV hUV
  algebraize [(f.appLE U V hUV).hom]
  have : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal := by
    suffices hU.primeIdealOf ⟨f x, hxU⟩ = Spec.map (f.appLE U V hUV) (hV.primeIdealOf ⟨x, hxV⟩) from
      ⟨congr(($this).1)⟩
    apply hU.isoSpec.inv.homeomorph.injective
    apply Subtype.ext
    simp only [IsAffineOpen.primeIdealOf, Scheme.Hom.homeomorph_apply,
      ← Scheme.Hom.comp_apply, ← Scheme.Opens.ι_apply, IsAffineOpen.isoSpec_hom]
    simp
  have : Algebra.QuasiFiniteAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hx.quasiFiniteAt hV hU hUV hxV
  obtain ⟨R, _, _, _, P, _, _, e, _, P', _, _, hP', heP', -, _, -⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
    (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : (algebraMap R (Localization.Away e)).Finite := RingHom.finite_algebraMap.mpr ‹_›
  let φ : Γ(S, U) ⟶ .of R := CommRingCat.ofHom <| algebraMap Γ(S, U) R
  have hφ : φ.hom.Etale := RingHom.etale_algebraMap.mpr ‹_›
  have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff.mpr hφ
  let e₁ : Spec (.of (R ⊗ Γ(X, V))) ≅ pullback (Spec.map (f.appLE U V hUV)) (Spec.map φ) :=
    (pullbackSpecIso _ _ _).symm ≪≫ pullbackSymmetry _ _
  have he₁ : e₁.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
    dsimp [e₁, RingHom.algebraMap_toAlgebra]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullbackSpecIso_inv_snd ..
  let g : Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
    e₁.hom ≫ pullback.map _ _ _ _ hV.fromSpec (𝟙 _) hU.fromSpec
      (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)
  let W₁ := g ''ᵁ PrimeSpectrum.basicOpen e
  have : IsFinite (W₁.ι ≫ pullback.snd f _) := by
    let ι : Spec (.of (Localization.Away e)) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
      Spec.map (CommRingCat.ofHom <| algebraMap _ _) ≫ g
    have : ι.opensRange = W₁ := by
      simp only [Scheme.Hom.opensRange_comp, ι, W₁]
      congr 1
      exact TopologicalSpace.Opens.ext <| PrimeSpectrum.localization_away_comap_range _ _
    rw [← this, ← MorphismProperty.cancel_left_of_respectsIso @IsFinite
      (Scheme.Hom.isoOpensRange _).hom]
    have H : (pullbackSpecIso _ R _).inv ≫ pullback.fst _ (Spec.map (f.appLE U V hUV)) = _ :=
      pullbackSpecIso_inv_fst ..
    simpa [Scheme.Hom.isoOpensRange, ι, g, e₁, RingHom.algebraMap_toAlgebra, φ, H,
      ← Spec.map_comp, IsFinite.SpecMap_iff]
  have : IsFinite W₁.ι := .of_comp _ (pullback.snd f _)
  let W₂ : (pullback f (Spec.map φ ≫ hU.fromSpec)).Opens :=
    ⟨W₁ᶜ, by simpa using W₁.ι.isClosedMap.isClosed_range⟩
  refine ⟨Spec (.of R), Spec.map φ ≫ hU.fromSpec, inferInstance,
    ⟨⟨P, ‹_›⟩, ?_⟩, W₁, W₂, ⟨g ⟨P', ‹_›⟩, ?_⟩, ?_, ‹_›, ?_⟩
  · dsimp [Spec.map_apply]
    convert! hU.fromSpec_primeIdealOf ⟨f x, hxU⟩
    · exact PrimeSpectrum.ext (Ideal.over_def _ _).symm
    · simp [h]
  · exact ⟨⟨P', ‹_›⟩, heP', rfl⟩
  · simp [isCompl_iff, disjoint_iff, codisjoint_iff, W₂, SetLike.ext'_iff]
  · trans hV.fromSpec ⟨P'.comap Algebra.TensorProduct.includeRight.toRingHom, inferInstance⟩
    · simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, g, reassoc_of% he₁]; rfl
    convert! hV.fromSpec_primeIdealOf ⟨x, hxV⟩

variable {X Y S : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.exists_mem_and_isIso_morphismRestrict_toNormaliza
tion** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyO
fFiniteType f]   [inst : AlgebraicGeometry.IsSeparated f] [inst_1 : AlgebraicGeo
metry.QuasiCompact f] (x : ↥X),   AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt f x
 →     ∃ V,       (AlgebraicGeometry.Scheme.Hom.toNormalization f) x ∈ V ∧      
   CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.toNormalization f ∣_ V)
参数：f : X ⟶ Y；x : ↥X；AlgebraicGeometry.Scheme.Hom.toNormalization f；AlgebraicGeom
etry.Scheme.Hom.toNormalization f ∣_ V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.IsSeparated.instQuasiSeparated`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsSeparated f], AlgebraicGeometry.Qu
asiSeparated f
· 使用定理 `AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`：exists_etale_is
Compl_of_quasiFiniteAt [IsSeparated f] {x : X} {s : S} (h : f x = s) (hx : f.Qua
siFiniteAt x) : exists (U : Scheme) (g : U ⟶ …
· 使用定理 `AlgebraicGeometry.instQuasiCompactSndScheme`：∀ {X Y Z : AlgebraicGeometr
y.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.QuasiCompact f],   Algebrai
cGeometry.QuasiCompact (CategoryT…
· 使用定理 `AlgebraicGeometry.instQuasiSeparatedSndScheme`：∀ {X Y S : AlgebraicGeome
try.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.QuasiSeparated f],   Alge
braicGeometry.QuasiSeparated (Categ…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_compl_iff_isCompl`：eq_compl_iff_isCompl : x = yᶜ ↔ IsCompl x y
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `IsCompl.map`：IsCompl.map [BoundedOrder α] [BoundedOrder β] [BoundedLatti
ceHomClass F α β] {a b : α} (f : F) (h : IsCompl a b) : IsCompl (f a) (f b)
· 使用定理 `FrameHomClass.toBoundedLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : C
ompleteLattice β] [FrameHomC…
· 使用定理 `FrameHom.instFrameHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Comp
leteLattice α] [inst_1 : CompleteLattice β],   FrameHomClass (FrameHom α β) α β
· 使用引理 `AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion`：of_isPreimmersion
 {X Y : Scheme} (f : X ⟶ Y) [IsPreimmersion f] (hf : IsClosed (Set.range f)) : I
sClosedImmersion f
· 使用定理 `AlgebraicGeometry.IsImmersion.toIsPreimmersion`：∀ {X Y : AlgebraicGeomet
ry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsImmersion f],   AlgebraicGeom
etry.IsPreimmersion f
· 使用定理 `AlgebraicGeometry.IsImmersion.instOfIsOpenImmersion`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], AlgebraicGeom
etry.IsImmersion f
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Opens.range_ι`：range_ι : Set.range U.ι = U
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_compl_comm`：eq_compl_comm : x = yᶜ ↔ y = xᶜ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用引理 `AlgebraicGeometry.nonempty_isColimit_binaryCofanMk_of_isCompl`：nonempty_
isColimit_binaryCofanMk_of_isCompl {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) 
[IsOpenImmersion f] [IsOpenImmersion g] (hf : IsCom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfUniversallyClosed`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f], Algebraic
Geometry.QuasiCompact f
· 使用定理 `AlgebraicGeometry.IsProper.toUniversallyClosed`：∀ {X Y : AlgebraicGeomet
ry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsProper f],   AlgebraicGeometr
y.UniversallyClosed f
· 使用定理 `AlgebraicGeometry.IsProper.instOfIsFinite`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f], AlgebraicGeometry.IsProper f
（共 127 条，此处仅展示前 30 条）
-/
lemma Scheme.Hom.exists_mem_and_isIso_morphismRestrict_toNormalization
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    (x : X) (hx : f.QuasiFiniteAt x) :
    ∃ V, f.toNormalization x ∈ V ∧ IsIso (f.toNormalization ∣_ V) := by
  obtain ⟨T, fT, _, ⟨u, hu⟩, V, W, v, hVW, _, hv₂⟩ := exists_etale_isCompl_of_quasiFiniteAt _ rfl hx
  obtain ⟨U, hU, _⟩ : ∃ U, (pullback.snd f fT).toNormalization v.1 ∈ U ∧
      IsIso ((pullback.snd f fT).toNormalization ∣_ U) := by
    have hVW' : (W : Set ↑(pullback f fT)) = (↑V)ᶜ :=
      eq_compl_iff_isCompl.mpr (hVW.map TopologicalSpace.Opens.frameHom).symm
    have : IsClosedImmersion V.ι := .of_isPreimmersion _ (by simp [eq_compl_comm.mp hVW', W.isOpen])
    have : IsClosedImmersion W.ι := .of_isPreimmersion _ (by simpa [hVW'] using V.2)
    obtain ⟨H⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl V.ι W.ι (by simpa)
    let e : (pullback.snd f fT).normalization ≅ V ⨿ (W.ι ≫ pullback.snd f fT).normalization :=
      (Scheme.Hom.normalizationCoprodIso (pullback.snd f fT) H).symm ≪≫
        coprod.mapIso (asIso (V.ι ≫ pullback.snd f fT).toNormalization).symm (.refl _)
    let ι : V.toScheme ⟶ V ⨿ (W.ι ≫ pullback.snd f fT).normalization := coprod.inl
    refine ⟨e.hom ⁻¹ᵁ ι.opensRange, ⟨v, ?_⟩, ?_⟩
    · rw [← V.ι_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      congr 5
      rw [← Category.assoc, ← Iso.comp_inv_eq]
      simp [ι, e, Scheme.Hom.normalizationCoprodIso]
    rw [← isIso_comp_right_iff _ (e.hom ∣_ ι.opensRange),
      ← morphismRestrict_comp, ← isIso_comp_right_iff _ ι.isoOpensRange.inv]
    have Heq : (pullback.snd f fT).toNormalization ⁻¹ᵁ e.hom ⁻¹ᵁ Scheme.Hom.opensRange ι = V := by
      apply le_antisymm
      · rintro a ⟨b, hab⟩
        by_contra h
        lift a to W using hVW'.ge h
        replace hab : ι b = ((W.ι ≫ pullback.snd f fT).toNormalization ≫ coprod.inr) a := by
          have : W.ι ≫ (H.coconePointUniqueUpToIso (colimit.isColimit _)).hom = coprod.inr :=
            H.comp_coconePointUniqueUpToIso_hom _ ⟨.right⟩
          simp only [← W.ι_apply, ← Scheme.Hom.comp_apply, Category.assoc, e] at hab
          simpa [-Scheme.Hom.comp_base, Scheme.Hom.normalizationCoprodIso,
            reassoc_of% this] using hab
        exact Set.disjoint_iff_forall_ne.mp
          (isCompl_range_inl_inr V (W.ι ≫ pullback.snd f fT).normalization).1 ⟨_, rfl⟩ ⟨_, rfl⟩ hab
      · rw [← Scheme.Hom.inv_image, ← SetLike.coe_subset_coe]
        simpa [← Scheme.Hom.opensRange_comp, ι, e, Scheme.Hom.normalizationCoprodIso,
          Set.range_comp] using Set.subset_preimage_image _ _
    convert! (inferInstance : IsIso (Scheme.isoOfEq _ Heq).hom)
    rw [Iso.comp_inv_eq, ← Iso.inv_comp_eq, ← cancel_mono (Scheme.Opens.ι _)]
    have : V.ι ≫ (H.coconePointUniqueUpToIso (colimit.isColimit _)).hom = coprod.inl :=
      H.comp_coconePointUniqueUpToIso_hom _ ⟨.left⟩
    simp [e, Scheme.Hom.isoOpensRange, Scheme.Hom.normalizationCoprodIso, reassoc_of% this, ι]
  let fTn : (pullback.snd f fT).normalization ⟶ f.normalization :=
    f.normalizationPullback fT ≫ pullback.fst _ _
  let U' : f.normalization.Opens := ⟨_, fTn.isOpenMap _ U.2⟩
  refine ⟨U', ⟨_, hU, by simp only [← hv₂, ← Scheme.Hom.comp_apply]; simp [fTn]⟩, ?_⟩
  let fTnU : U.toScheme ⟶ U' := fTn.resLE _ _ (Set.subset_preimage_image _ _)
  have : Surjective fTnU := ⟨fun ⟨x, a, ha, e⟩ ↦ ⟨⟨a, ha⟩, Subtype.ext <| by simpa [fTnU] using e⟩⟩
  have H : (pullback.snd f fT).toNormalization ⁻¹ᵁ U ≤
      pullback.fst f fT ⁻¹ᵁ f.toNormalization ⁻¹ᵁ U' := by
    refine fun x hx ↦ ⟨_, hx, ?_⟩
    simp only [← Scheme.Hom.comp_apply]
    congr 5
    simp [fTn]
  have : IsPullback ((pullback.snd f fT).toNormalization ∣_ U)
      ((pullback.fst f fT).resLE _ _ H) fTnU (f.toNormalization ∣_ U') := by
    refine .of_bot (t := isPullback_morphismRestrict ..) ?_ ?_
    · simp only [Scheme.Hom.resLE_comp_ι, fTnU]
      refine .paste_vert (isPullback_morphismRestrict ..) ?_
      have H : IsPullback (pullback.map _ _ _ _ f.toNormalization (𝟙 _) (𝟙 _) (by simp) (by simp))
          (pullback.fst f fT) (pullback.fst f.fromNormalization fT) f.toNormalization :=
        .of_right (t := .flip <| .of_hasPullback ..)
          (by simpa using (.flip <| .of_hasPullback ..)) (by cat_disch)
      exact .of_iso' H (.refl _) (asIso <| f.normalizationPullback fT) (.refl _) (.refl _)
        (by cat_disch) (by simp) (by simp [fTn]) (by simp)
    · simp [← cancel_mono U'.ι, fTnU, fTn]
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := .isomorphisms _)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) this
    ⟨⟨‹_›, inferInstance⟩, inferInstance⟩ ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/--
**Zariski's main theorem**

Recall that any qcqs morphism `f : X ⟶ Y` factors through the relative normalization via
`f.toNormalization : X ⟶ f.normalization` (a dominant morphism) and
`f.fromNormalization : f.normalization ⟶ Y` (an integral morphism).

Let `f : X ⟶ Y` be separated and of finite type.

then there exists `U : f.normalization.Opens`, such that
1. `f.toNormalization ∣_ U` is an isomorphism
2. `f.toNormalization ⁻¹ᵁ U` is the quasi-finite locus of `f`
-/
@[stacks 03GW]
/-
**AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization** 是
 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyO
fFiniteType f]   [inst : AlgebraicGeometry.IsSeparated f] [inst_1 : AlgebraicGeo
metry.QuasiCompact f],   ∃ U,     CategoryTheory.IsIso (AlgebraicGeometry.Scheme
.Hom.toNormalization f ∣_ U) ∧       ((TopologicalSpace.Opens.map (AlgebraicGeom
etry.Scheme.Hom.toNormalization f).base).obj U).carrier =         {x | Algebraic
Geometry.Scheme.Hom.QuasiFiniteAt f x}
参数：f : X ⟶ Y；AlgebraicGeometry.Scheme.Hom.toNormalization f ∣_ U；(TopologicalSpa
ce.Opens.map (AlgebraicGeometry.Scheme.Hom.toNormalization f).base).obj U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsSeparated.instQuasiSeparated`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsSeparated f], AlgebraicGeometry.Qu
asiSeparated f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover`：iff_of_openCo
ver (𝒰 : Y.OpenCover) : P f ↔ forall i, P (𝒰.pullbackHom f i)
· 使用定理 `AlgebraicGeometry.Scheme.instIsLocalAtTargetIsomorphismsZariskiPrecovera
ge`：(CategoryTheory.MorphismProperty.isomorphisms AlgebraicGeometry.Scheme).IsLo
calAtTarget   AlgebraicGeometry.Scheme.zariskiPrecoverage
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.opensRange.congr_simp`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f f_1 : X ⟶ Y) (e_f : f = f_1) [H : AlgebraicGeometry.IsOpenImme
rsion f],   AlgebraicGeometry.Scheme.Hom…
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionHomOfLE`：∀ (X : AlgebraicGeometry.S
cheme) {U V : X.Opens} (e : U ≤ V), AlgebraicGeometry.IsOpenImmersion (X.homOfLE
 e)
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
（共 104 条，此处仅展示前 30 条）

--- 原说明 ---
**Zariski's main theorem**

Recall that any qcqs morphism `f : X ⟶ Y` factors through the relative normaliza
tion via
`f.toNormalization : X ⟶ f.normalization` (a dominant morphism) and
`f.fromNormalization : f.normalization ⟶ Y` (an integral morphism).

Let `f : X ⟶ Y` be separated and of finite type.

then there exists `U : f.normalization.Opens`, such that
1. `f.toNormalization ∣_ U` is an isomorphism
2. `f.toNormalization ⁻¹ᵁ U` is the quasi-finite locus of `f`
-/
lemma Scheme.Hom.exists_isIso_morphismRestrict_toNormalization
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    ∃ U : f.normalization.Opens, IsIso (f.toNormalization ∣_ U) ∧
      (f.toNormalization ⁻¹ᵁ U).1 = { x | f.QuasiFiniteAt x } := by
  choose V hxV hV using fun x : { x // f.QuasiFiniteAt x } ↦
    f.exists_mem_and_isIso_morphismRestrict_toNormalization x x.2
  let 𝒰 := Opens.iSupOpenCover V
  have : IsIso (f.toNormalization ∣_ ⨆ x, V x) := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _) 𝒰).mpr fun x ↦ ?_
    refine (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
      ((morphismRestrictRestrict ..).symm ≪≫ morphismRestrictOpensRange ..)).mp ?_
    have : Opens.ι _ ''ᵁ (𝒰.f x).opensRange = V x := by
      simp only [Opens.iSupOpenCover, 𝒰, ← opensRange_comp, homOfLE_ι, Opens.opensRange_ι]
    convert! hV x
  refine ⟨⨆ x : { x | f.QuasiFiniteAt x }, V x, this, ?_⟩
  ext x
  suffices (∃ i : { x | f.QuasiFiniteAt x }, toNormalization f x ∈ V i) ↔ f.QuasiFiniteAt x by
    simpa
  refine ⟨?_, fun h ↦ ⟨⟨x, h⟩, hxV _⟩⟩
  rintro ⟨y, hxVy⟩
  obtain ⟨U, r, hU, hr, hxV, hrV⟩ :
      ∃ (U : Y.Opens) (r : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)),
      IsAffineOpen U ∧ IsAffineOpen (f.toNormalization ⁻¹ᵁ f.normalization.basicOpen r) ∧
      x ∈ f.toNormalization ⁻¹ᵁ f.normalization.basicOpen r ∧ Scheme.basicOpen _ r ≤ V y := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV : W ≤ _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      hxVy (f.toNormalization ⁻¹ᵁ V y).isOpen
    have : IsAffine W := hW
    let V' := (X.homOfLE hWV ≫ f.toNormalization ∣_ V y ≫ (V y).ι).opensRange
    have hV' : IsAffineOpen V' := isAffineOpen_opensRange _
    have hV'V : V' ≤ V y := by
      simp_rw [V', ← Category.assoc, opensRange_comp]
      exact (image_le_opensRange _ _).trans (by simp)
    have hV'W : f.toNormalization ⁻¹ᵁ V' = W := by
      have : (f.toNormalization ⁻¹ᵁ V y).ι ⁻¹ᵁ f.toNormalization ⁻¹ᵁ V' =
          (f.toNormalization ⁻¹ᵁ V y).ι ⁻¹ᵁ W := by
        rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι]
        simp only [V', opensRange_comp, Scheme.Hom.preimage_image_eq, opensRange_homOfLE]
      simpa only [image_preimage_eq_opensRange_inf, Opens.opensRange_ι, ← preimage_inf,
        inf_eq_right.mpr, hV'V, hWV] using congr((f.toNormalization ⁻¹ᵁ V y).ι ''ᵁ $this)
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨f₁, f₂, e, hxf⟩ := exists_basicOpen_le_affine_inter (hU.preimage f.fromNormalization)
      hV' (f.toNormalization x) ⟨by simpa [← Scheme.Hom.comp_apply], hV'W.ge hxW⟩
    refine ⟨U, f₁, hU, ?_, hxf, (e.trans_le (f.normalization.basicOpen_le _)).trans hV'V⟩
    rw [e, preimage_basicOpen]
    exact IsAffineOpen.basicOpen (hV'W ▸ hW) _
  let W := f.toNormalization ⁻¹ᵁ f.normalization.basicOpen r
  have H : W ≤ f ⁻¹ᵁ U := by
    unfold W
    grw [Scheme.basicOpen_le, ← Scheme.Hom.comp_preimage, f.toNormalization_fromNormalization]
  have H' : f.fromNormalization.appLE _ _ ((normalization f).basicOpen_le _) ≫
    f.toNormalization.app _ = f.appLE U W H := by
    simp only [app_eq_appLE]
    exact (appLE_comp_appLE _ _ _ _ _ _ _).trans (by simp [W])
  have : IsIso ((toNormalization f).app ((normalization f).basicOpen r)) := by
    have H : (f.toNormalization ∣_ V y) ⁻¹ᵁ (V y).ι ⁻¹ᵁ (normalization f).basicOpen r =
        (Scheme.homOfLE _ (f.toNormalization.preimage_mono hrV)).opensRange := by
      apply Scheme.Hom.image_injective (f.toNormalization ∣_ V y)
      simp only [opensRange_homOfLE, image_preimage_eq_opensRange_inf]
      rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι, Scheme.Hom.comp_preimage,
        image_preimage_eq_opensRange_inf]
    have := (inferInstance : IsIso ((toNormalization f ∣_ V y).app
      (Scheme.homOfLE _ hrV).opensRange))
    simp only [Opens.toScheme_presheaf_obj, app_eq_appLE, morphismRestrict_appLE] at this ⊢
    convert! this <;>
      simp [Scheme.Hom.image_preimage_eq_opensRange_inf, -Scheme.preimage_basicOpen,
        f.toNormalization.preimage_mono, hrV, H]
  have : (f.appLE U W H).hom.QuasiFinite := by
    have : (f.appLE U W H).hom.FiniteType := f.finiteType_appLE hU hr H
    rw [← H', CommRingCat.hom_comp, RingHom.finiteType_respectsIso.cancel_right_isIso] at this
    rw [← H', CommRingCat.hom_comp, RingHom.QuasiFinite.respectsIso.cancel_right_isIso]
    exact .of_isIntegral_of_finiteType (IsIntegralHom.isIntegral_app f.fromNormalization _ hU)
      ⟨r, (hU.preimage f.fromNormalization).isLocalization_basicOpen _⟩ this
  have hxU : f x ∈ U := by
    convert! show _ ∈ U from (normalization f).basicOpen_le _ hxV
    rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization]
  refine .of_comp (g := (Y.presheaf.germ U _ hxU).hom) ?_
  rw [← CommRingCat.hom_comp, f.germ_stalkMap, ← X.presheaf.germ_res (homOfLE H) _ hxV,
    app_eq_appLE, appLE_map_assoc, CommRingCat.hom_comp]
  refine .comp ?_ this
  have := hr.isLocalization_stalk ⟨x, hxV⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  rw [← RingHom.algebraMap_toAlgebra (X.presheaf.germ _ _ _).hom, @RingHom.quasiFinite_algebraMap]
  exact .of_isLocalization (hr.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyO
fFiniteType f],   IsOpen {x | AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt f x}
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffineHom f], AlgebraicGeometry.Qua
siCompact f
· 使用定理 `AlgebraicGeometry.IsSeparated.instQuasiSeparated`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsSeparated f], AlgebraicGeometry.Qu
asiSeparated f
· 使用引理 `AlgebraicGeometry.IsSeparated.of_isAffineHom`：of_isAffineHom [h : IsAffi
neHom f] : IsSeparated f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalizati
on`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfF
initeType f]   [inst : AlgebraicGeometry.IsSeparated f] [inst_1 …
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_forall_mem_open`：isOpen_iff_forall_mem_open : IsOpen s ↔ fora
ll x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `AlgebraicGeometry.isAffineHom_of_isAffine`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y],
   AlgebraicGeometry.IsAffineHo…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion`：
∀ {X Y Z : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} {x : ↥X} [Algebraic
Geometry.IsOpenImmersion f],   AlgebraicGeometry.Scheme.Hom.…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`：resLE_comp_ι : f.resLE U V e 
≫ U.ι = V.ι ≫ f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_comp_iff`：∀ {X Y Z : Algebrai
cGeometry.Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} {x : ↥X} [AlgebraicGeometry.LocallyQua
siFinite g],   AlgebraicGeometry.Scheme.H…
· 使用定理 `AlgebraicGeometry.instLocallyQuasiFiniteOfLocallyOfFiniteTypeOfUniversal
lyInjective`：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} [AlgebraicGeometry.L
ocallyOfFiniteType f]   [AlgebraicGeometry.UniversallyInjective f], Algeb…
· 使用定理 `AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation`：
∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [hf : AlgebraicGeometry.LocallyOf
FinitePresentation f],   AlgebraicGeometry.LocallyOfFiniteTy…
· 使用定理 `AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], 
  AlgebraicGeometry.LocallyOfFinitePresentation f
· 使用定理 `AlgebraicGeometry.instUniversallyInjectiveOfMonoScheme`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.Mono f], AlgebraicGeometry.Univer
sallyInjective f
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `AlgebraicGeometry.instLocallyOfFiniteTypeResLE`：∀ {X Y : AlgebraicGeomet
ry.Scheme} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens)   (e : U ≤ (TopologicalSpace.
Opens.map f.base).obj V) [AlgebraicG…
-/
lemma Scheme.Hom.isOpen_quasiFiniteAt [LocallyOfFiniteType f] :
    IsOpen { x | f.QuasiFiniteAt x } := by
  wlog H : IsAffineHom f
  · rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨_, ⟨U : Y.Opens, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      hxU (f ⁻¹ᵁ U).2
    have inst : IsAffineHom (f.resLE U V hVU) :=
      have : IsAffine _ := hU
      have : IsAffine _ := hV
      isAffineHom_of_isAffine _
    refine ⟨_, ?_, V.2.isOpenEmbedding_subtypeVal.isOpenMap _ (this (f.resLE U V hVU) inst), ?_⟩
    · rintro _ ⟨x : V, hx : (f.resLE U V hVU).QuasiFiniteAt _, rfl⟩
      rwa [← quasiFiniteAt_comp_iff (g := U.ι), resLE_comp_ι,
        quasiFiniteAt_comp_iff_of_isOpenImmersion] at hx
    · refine ⟨⟨x, hxV⟩, show (f.resLE _ _ _).QuasiFiniteAt _ from ?_, rfl⟩
      rwa [← quasiFiniteAt_comp_iff (g := U.ι), resLE_comp_ι,
        quasiFiniteAt_comp_iff_of_isOpenImmersion]
  obtain ⟨U, hU, e⟩ := Scheme.Hom.exists_isIso_morphismRestrict_toNormalization f
  exact e ▸ (f.toNormalization ⁻¹ᵁ U).2

/-- The set of quasi-finite points of a morphism `f : X ⟶ Y` as an `X.Opens`. -/
/-
**AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (f : X ⟶ Y) → [AlgebraicGeometry.Locall
yOfFiniteType f] → X.Opens
参数：f : X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f],   IsOpen {x
 | AlgebraicGeometry.Scheme.Hom.QuasiFi…

--- 原说明 ---
The set of quasi-finite points of a morphism `f : X ⟶ Y` as an `X.Opens`.
-/
def Scheme.Hom.quasiFiniteLocus [LocallyOfFiniteType f] : X.Opens :=
  ⟨{ x | f.QuasiFiniteAt x }, f.isOpen_quasiFiniteAt⟩

variable {f} in
@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.mem_quasiFiniteLocus** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} [inst : AlgebraicGeometry.L
ocallyOfFiniteType f] {x : ↥X},   x ∈ AlgebraicGeometry.Scheme.Hom.quasiFiniteLo
cus f ↔ AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Scheme.Hom.mem_quasiFiniteLocus [LocallyOfFiniteType f]
    {x : X} : x ∈ f.quasiFiniteLocus ↔ f.QuasiFiniteAt x := .rfl
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    IsOpenImmersion (f.quasiFiniteLocus.ι ≫ f.toNormalization) := by
  obtain ⟨U, hU, e⟩ := Scheme.Hom.exists_isIso_morphismRestrict_toNormalization f
  convert!
    (inferInstance :
      IsOpenImmersion
        ((X.isoOfEq (U := f.quasiFiniteLocus) (SetLike.coe_injective e.symm)).hom ≫
          f.toNormalization ∣_ U ≫ U.ι)) using 1
  simp
/-
**AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus_eq_top** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQ
uasiFinite f]   [inst : AlgebraicGeometry.LocallyOfFiniteType f], AlgebraicGeome
try.Scheme.Hom.quasiFiniteLocus f = ⊤
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `AlgebraicGeometry.Scheme.Hom.quasiFiniteAt`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQuasiFinite f] (x : ↥X),   Algebrai
cGeometry.Scheme.Hom.QuasiFinite…
-/
lemma Scheme.Hom.quasiFiniteLocus_eq_top [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    f.quasiFiniteLocus = ⊤ :=
  top_le_iff.mp fun x _ ↦ f.quasiFiniteAt x
/-
**AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus_comp** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) {Z : AlgebraicGeometry.Sche
me}   [inst : AlgebraicGeometry.IsOpenImmersion f] (g : Y ⟶ Z) [inst_1 : Algebra
icGeometry.LocallyOfFiniteType g],   AlgebraicGeometry.Scheme.Hom.quasiFiniteLoc
us (CategoryTheory.CategoryStruct.comp f g) =     (TopologicalSpace.Opens.map f.
base).obj (AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus g)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；TopologicalSpace.O
pens.map f.base；AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation`：
∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [hf : AlgebraicGeometry.LocallyOf
FinitePresentation f],   AlgebraicGeometry.LocallyOfFiniteTy…
· 使用定理 `AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], 
  AlgebraicGeometry.LocallyOfFinitePresentation f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Scheme.Hom.quasiFiniteLocus_comp {Z : Scheme} [IsOpenImmersion f]
    (g : Y ⟶ Z) [LocallyOfFiniteType g] :
    (f ≫ g).quasiFiniteLocus = f ⁻¹ᵁ g.quasiFiniteLocus := by
  ext
  simp [quasiFiniteAt_comp_iff_of_isOpenImmersion]
/-
**AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus_eq_top_iff** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.L
ocallyOfFiniteType f],   AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus f = ⊤ ↔ A
lgebraicGeometry.LocallyQuasiFinite f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton`：
∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} [AlgebraicGeometry.LocallyOfFinit
eType f],   AlgebraicGeometry.LocallyQuasiFinite f ↔ ∀ (x : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isDiscrete_iff_discreteTopology`：isDiscrete_iff_discreteTopology : IsDis
crete s ↔ DiscreteTopology s
· 使用定理 `discreteTopology_iff_isOpen_singleton`：discreteTopology_iff_isOpen_singl
eton [TopologicalSpace α] : DiscreteTopology α ↔ (forall a : α, IsOpen ({a} : Se
t α))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.isOpen_image`：isOpen_image (h : X ≃ₜ Y) {s : Set X} : IsOpen 
(h '' s) ↔ IsOpen s
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt.isClopen_singleton_asFiber`：∀
 {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFinite
Type f] {x : ↥X},   AlgebraicGeometry.Scheme.Hom.QuasiFinit…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus_eq_top`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQuasiFinite f]   [inst : 
AlgebraicGeometry.LocallyOfFiniteType f], …
-/
lemma Scheme.Hom.quasiFiniteLocus_eq_top_iff [LocallyOfFiniteType f] :
    f.quasiFiniteLocus = ⊤ ↔ LocallyQuasiFinite f := by
  refine ⟨fun H ↦ locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr fun x ↦ ?_,
    fun _ ↦ f.quasiFiniteLocus_eq_top⟩
  rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
  rintro ⟨a, rfl⟩
  rw [← (f.fiberHomeo _).symm.isOpen_image, Set.image_singleton]
  exact (H.ge (Set.mem_univ a)).isClopen_singleton_asFiber.isOpen
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallyOfFiniteType f] :
    LocallyQuasiFinite (f.quasiFiniteLocus.ι ≫ f) := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, Scheme.Hom.quasiFiniteLocus_comp,
    Scheme.Opens.ι_preimage_self]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    IsOpenImmersion f.toNormalization := by
  convert!
    (inferInstance :
      IsOpenImmersion
        (X.topIso.inv ≫
          (X.isoOfEq f.quasiFiniteLocus_eq_top).inv ≫
            f.quasiFiniteLocus.ι ≫ f.toNormalization)) using 1
  simp

-- In particular it is surjective (by infer_instance), since it is a priori dominant.
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [QuasiSeparated f] [UniversallyClosed f] : UniversallyClosed f.toNormalization :=
  have : UniversallyClosed (f.toNormalization ≫ f.fromNormalization) := by simpa
  .of_comp_of_isSeparated _ f.fromNormalization
/-
**AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.IsFinite`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsProper
 f] [AlgebraicGeometry.LocallyQuasiFinite f],   AlgebraicGeometry.IsFinite f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfUniversallyClosed`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f], Algebraic
Geometry.QuasiCompact f
· 使用定理 `AlgebraicGeometry.IsProper.toUniversallyClosed`：∀ {X Y : AlgebraicGeomet
ry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsProper f],   AlgebraicGeometr
y.UniversallyClosed f
· 使用定理 `AlgebraicGeometry.IsSeparated.instQuasiSeparated`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsSeparated f], AlgebraicGeometry.Qu
asiSeparated f
· 使用定理 `AlgebraicGeometry.IsProper.toIsSeparated`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsProper f], AlgebraicGeometry.IsSepa
rated f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective`：isIso_iff_is
OpenImmersion_and_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso f ↔ IsOpenIm
mersion f ∧ Surjective f
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionToNormalizationOfLocallyQuasiFinite
OfLocallyOfFiniteType`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [Algebraic
Geometry.LocallyQuasiFinite f]   [AlgebraicGeometry.LocallyOfFiniteType f] [inst
 : …
· 使用定理 `AlgebraicGeometry.IsProper.toLocallyOfFiniteType`：∀ {X Y : AlgebraicGeom
etry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsProper f],   AlgebraicGeome
try.LocallyOfFiniteType f
· 使用定理 `AlgebraicGeometry.Surjective.of_universallyClosed_of_isDominant`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f] 
[AlgebraicGeometry.IsDominant f],   AlgebraicGeometry…
· 使用定理 `AlgebraicGeometry.instUniversallyClosedToNormalization`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiSeparated f]   [in
st_1 : AlgebraicGeometry.UniversallyClosed f…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsDominantToNormalization`：∀ {X Y : Alg
ebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiCompact f]   [
inst_1 : AlgebraicGeometry.QuasiSeparated f],   …
· 使用引理 `AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`：if
f_isIntegralHom_and_locallyOfFiniteType : IsFinite f ↔ IsIntegralHom f ∧ Locally
OfFiniteType f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.toNormalization_fromNormalization`：toNormal
ization_fromNormalization : f.toNormalization ≫ f.fromNormalization = f
· 使用定理 `AlgebraicGeometry.IsIntegralHom.instCompScheme`：∀ {X Y Z : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsIntegralHom f]   [Alge
braicGeometry.IsIntegralHom g], Alge…
· 使用定理 `AlgebraicGeometry.IsFinite.instIsIntegralHom`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f], AlgebraicGeometry.IsIntegra
lHom f
· 使用定理 `AlgebraicGeometry.IsFinite.instOfIsClosedImmersion`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f], AlgebraicGeo
metry.IsFinite f
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instOfIsIsoScheme`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.IsClos
edImmersion f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiCompact f
]   [inst_1 : AlgebraicGeometry.QuasiSeparated f],   …
-/
lemma IsFinite.of_isProper_of_locallyQuasiFinite
    [IsProper f] [LocallyQuasiFinite f] : IsFinite f := by
  have : IsIso f.toNormalization :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  refine (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨?_, inferInstance⟩
  rw [← f.toNormalization_fromNormalization]
  infer_instance

@[stacks 02LS "(1) <=> (3)"]
/-
**AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicGeometry.IsFinite`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.IsFini
te f ↔ AlgebraicGeometry.IsProper f ∧ AlgebraicGeometry.LocallyQuasiFinite f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsProper.instOfIsFinite`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f], AlgebraicGeometry.IsProper f
· 使用定理 `AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f], AlgebraicGeometry.Loc
allyQuasiFinite f
· 使用定理 `AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`：∀ {X Y : A
lgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] [AlgebraicGe
ometry.LocallyQuasiFinite f],   AlgebraicGeometry.…
-/
lemma IsFinite.iff_isProper_and_locallyQuasiFinite :
    IsFinite f ↔ IsProper f ∧ LocallyQuasiFinite f := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩,
    fun ⟨_, _⟩ ↦ .of_isProper_of_locallyQuasiFinite f⟩
/-
**AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.IsFinite`。
形式化陈述：@AlgebraicGeometry.IsFinite = @AlgebraicGeometry.IsProper ⊓ @AlgebraicGeom
etry.LocallyQuasiFinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.IsFinite f ↔ Algebra
icGeometry.IsProper f ∧ AlgebraicGeometry.LocallyQua…
-/
lemma IsFinite.eq_proper_inf_locallyQuasiFinite :
    @IsFinite = (@IsProper ⊓ @LocallyQuasiFinite : MorphismProperty Scheme) := by
  ext
  exact IsFinite.iff_isProper_and_locallyQuasiFinite ..

@[stacks 04XV "(1) <=> (2)"]
/-
**AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.IsClosedImmersion`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.IsClos
edImmersion f ↔ AlgebraicGeometry.IsProper f ∧ CategoryTheory.Mono f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instLocallyQuasiFiniteOfLocallyOfFiniteTypeOfUniversal
lyInjective`：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} [AlgebraicGeometry.L
ocallyOfFiniteType f]   [AlgebraicGeometry.UniversallyInjective f], Algeb…
· 使用定理 `AlgebraicGeometry.IsProper.toLocallyOfFiniteType`：∀ {X Y : AlgebraicGeom
etry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsProper f],   AlgebraicGeome
try.LocallyOfFiniteType f
· 使用定理 `AlgebraicGeometry.instUniversallyInjectiveOfMonoScheme`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.Mono f], AlgebraicGeometry.Univer
sallyInjective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono`：∀ {X Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.IsClosedImmersion f ↔ Alg
ebraicGeometry.IsFinite f ∧ CategoryTheory.Mono…
· 使用定理 `AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.IsFinite f ↔ Algebra
icGeometry.IsProper f ∧ AlgebraicGeometry.LocallyQua…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IsClosedImmersion.iff_isProper_and_mono :
    IsClosedImmersion f ↔ IsProper f ∧ Mono f := by
  have (_ : Mono f) (_ : IsProper f) : LocallyQuasiFinite f := inferInstance
  rw [IsClosedImmersion.iff_isFinite_and_mono, IsFinite.iff_isProper_and_locallyQuasiFinite]
  aesop
/-
**AlgebraicGeometry.IsClosedImmersion.eq_proper_inf_monomorphisms** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.IsClosedImmersion`。
形式化陈述：@AlgebraicGeometry.IsClosedImmersion =   @AlgebraicGeometry.IsProper ⊓ Cat
egoryTheory.MorphismProperty.monomorphisms AlgebraicGeometry.Scheme
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono`：∀ {X Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.IsClosedImmersion f ↔ Alg
ebraicGeometry.IsProper f ∧ CategoryTheory.Mono…
-/
lemma IsClosedImmersion.eq_proper_inf_monomorphisms :
    @IsClosedImmersion = ↑@IsProper ⊓ MorphismProperty.monomorphisms Scheme := by
  ext
  exact IsClosedImmersion.iff_isProper_and_mono ..

set_option backward.isDefEq.respectTransparency.types false in
@[stacks 02UP]
/-
**AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleto
n** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：exists_isFinite_morphismRestrict_of_finite_preimage_singleton [IsProper f]
 (y : Y) (hx : (f ⁻¹' {y}).Finite) : exists V : Y.Opens, y in V ∧ IsFinite (f ∣_
 V)
参数：y : Y；hx : (f ⁻¹' {y}).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsProper.toLocallyOfFiniteType`：∀ {X Y : AlgebraicGeom
etry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsProper f],   AlgebraicGeome
try.LocallyOfFiniteType f
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isClosedMap`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f], IsClosedMap ⇑f
· 使用定理 `AlgebraicGeometry.IsProper.toUniversallyClosed`：∀ {X Y : AlgebraicGeomet
ry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsProper f],   AlgebraicGeometr
y.UniversallyClosed f
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
· 使用定理 `AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`
：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} [AlgebraicGeometry.LocallyOfFini
teType f] {x : ↥X},   AlgebraicGeometry.Scheme.Hom.QuasiFinit…
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `instDiscreteTopologyOfFiniteOfJacobsonSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [Finite X] [JacobsonSpace X], DiscreteTopology X
· 使用定理 `AlgebraicGeometry.instJacobsonSpaceCarrierCarrierCommRingCatFiberOfLocal
lyOfFiniteType`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (y : ↥Y) [Algebra
icGeometry.LocallyOfFiniteType f],   JacobsonSpace ↥(AlgebraicGeometry.Schem…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AlgebraicGeometry.instLocallyOfFiniteTypeMorphismRestrict`：∀ {X Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y) (V : Y.Opens) [AlgebraicGeometry.LocallyOfFini
teType f],   AlgebraicGeometry.LocallyOfFiniteT…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus_eq_top_iff`：∀ {X Y : Algeb
raicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.LocallyOfFiniteType f
],   AlgebraicGeometry.Scheme.Hom.quasiFiniteL…
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
（共 40 条，此处仅展示前 30 条）
-/
lemma exists_isFinite_morphismRestrict_of_finite_preimage_singleton
    [IsProper f] (y : Y) (hx : (f ⁻¹' {y}).Finite) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) := by
  let V : Y.Opens := ⟨_, (f.isClosedMap _ f.quasiFiniteLocus.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · suffices ∀ x, f x = y → f.QuasiFiniteAt x by simpa [V, not_imp_not]
    rintro x rfl
    have : Finite (f.fiber (f x)) := (f.fiberHomeo (f x)).finite_iff.mpr ‹_›
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
  · suffices LocallyQuasiFinite (f ∣_ V) from .of_isProper_of_locallyQuasiFinite _
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    ext x
    have : f.QuasiFiniteAt ((f ⁻¹ᵁ V).ι x) := by by_contra H; exact x.2 ⟨_, H, by simp⟩
    rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, ← morphismRestrict_ι,
      Scheme.Hom.quasiFiniteAt_comp_iff] at this
    simpa

@[stacks 0AH8]
/-
**AlgebraicGeometry.exists_finite_image** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    {X Y S : Scheme} (f : X ⟶ Y) (g : Y ⟶ S) (s : S)
    (H : (f '' ((f ≫ g) ⁻¹' {s})).Finite)
    [IsProper (f ≫ g)] [IsSeparated g] [LocallyOfFiniteType g] :
    ∃ U : S.Opens, s ∈ U ∧ IsFinite ((f.imageι ≫ g) ∣_ U) := by
  have : IsProper f := .of_comp f g
  have : IsProper (f.imageι ≫ g) := by
    suffices UniversallyClosed (f.imageι ≫ g) from ⟨⟩
    have : UniversallyClosed (f.toImage ≫ f.imageι ≫ g) := by
      rw [Scheme.Hom.toImage_imageι_assoc]; infer_instance
    refine .of_comp_surjective f.toImage _
  refine exists_isFinite_morphismRestrict_of_finite_preimage_singleton _ _ ?_
  refine .of_finite_image (f := f.imageι) (H.subset ?_) f.imageι.isClosedEmbedding.injective.injOn
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨x, rfl⟩ := f.toImage.surjective x
  refine ⟨x, ?_, by simp [← Scheme.Hom.comp_apply]⟩
  simpa [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base] using hx

end AlgebraicGeometry

