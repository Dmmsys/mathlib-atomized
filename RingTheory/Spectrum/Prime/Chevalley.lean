/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Spectrum.Prime.ChevalleyComplexity

/-!
# Chevalley's theorem

In this file we provide the usual (algebraic) version of Chevalley's theorem.
For the proof see `Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean`.
-/

public section

variable {R S : Type*} [CommRing R] [CommRing S]

open Function Localization MvPolynomial Polynomial TensorProduct PrimeSpectrum Topology
open scoped Pointwise

namespace PrimeSpectrum

/-
**PrimeSpectrum.isConstructible_comap_C** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum
`。
形式化陈述：isConstructible_comap_C {s : Set (PrimeSpectrum (Polynomial R))} (hs : IsC
onstructible s) : IsConstructible (comap Polynomial.C '' s)
参数：PrimeSpectrum (Polynomial R)；hs : IsConstructible s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PrimeSpectrum.exists_constructibleSetData_iff`：exists_constructibleSetDa
ta_iff {s : Set (PrimeSpectrum R)} : (exists S : ConstructibleSetData R, S.toSet
 = s) ↔ IsConstructible s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `ChevalleyThm.chevalley_polynomialC`：chevalley_polynomialC {R : Type*} [C
ommRing R] (M : Submodule Int R) (hM : 1 in M) (S : ConstructibleSetData R[X]) (
hS : forall C in S, fora…
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.ConstructibleSetData.isConstructible_toSet`：isConstructibl
e_toSet (S : ConstructibleSetData R) : IsConstructible S.toSet
-/
lemma isConstructible_comap_C
    {s : Set (PrimeSpectrum (Polynomial R))} (hs : IsConstructible s) :
    IsConstructible (comap Polynomial.C '' s) := by
  obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  obtain ⟨T, hT, -⟩ := ChevalleyThm.chevalley_polynomialC _ Submodule.mem_top S (by simp)
  rw [hT]
  exact T.isConstructible_toSet

/-- **Chevalley's theorem**: If `f` is of finite presentation,
then the image of a constructible set under `Spec(f)` is constructible. -/
/-
**PrimeSpectrum.isConstructible_comap_image** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpec
trum`。
形式化陈述：isConstructible_comap_image {f : R ->+* S} (hf : f.FinitePresentation) {s 
: Set (PrimeSpectrum S)} (hs : IsConstructible s) : IsConstructible (comap f '' 
s)
参数：hf : f.FinitePresentation；PrimeSpectrum S；hs : IsConstructible s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.FinitePresentation.polynomial_induction`：polynomial_induction (P
 : forall (R : Type u) [CommRing R] (S : Type u) [CommRing S], (R ->+* S) -> Pro
p) (Q : forall (R : Type u) [CommRing…
· 使用引理 `PrimeSpectrum.isConstructible_comap_C`：isConstructible_comap_C {s : Set 
(PrimeSpectrum (Polynomial R))} (hs : IsConstructible s) : IsConstructible (coma
p Polynomial.C '' s)
· 使用定理 `Topology.IsConstructible.image_of_isClosedEmbedding`：∀ {X : Type u_2} {Y
 : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → 
Y} {s : Set X},   Topology.IsClosedEmbedd…
· 使用引理 `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`：isClosedEmbedding_c
omap_of_surjective (hf : Surjective f) : IsClosedEmbedding (comap f) where toIsI
nducing
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `range_comap_of_surjective`：range_comap_of_surjective (hf : Surjective f)
 : Set.range (comap f) = zeroLocus (ker f)
· 使用引理 `PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg`：isRetrocompact_zeroL
ocus_compl_of_fg {I : Ideal R} (hI : I.FG) : IsRetrocompact (zeroLocus (I : Set 
R))ᶜ
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a

--- 原说明 ---
**Chevalley's theorem**: If `f` is of finite presentation,
then the image of a constructible set under `Spec(f)` is constructible.
-/
lemma isConstructible_comap_image
    {f : R →+* S} (hf : f.FinitePresentation)
    {s : Set (PrimeSpectrum S)} (hs : IsConstructible s) :
    IsConstructible (comap f '' s) := by
  refine hf.polynomial_induction
    (fun _ _ _ _ f ↦ ∀ s, IsConstructible s → IsConstructible (comap f '' s))
    (fun _ _ _ _ f ↦ ∀ s, IsConstructible s → IsConstructible (comap f '' s))
    (fun _ _ _ ↦ isConstructible_comap_C) ?_ ?_ f s hs
  · intro R _ S _ f hf hf' s hs
    refine hs.image_of_isClosedEmbedding (isClosedEmbedding_comap_of_surjective _ f hf) ?_
    rw [range_comap_of_surjective _ f hf]
    exact isRetrocompact_zeroLocus_compl_of_fg hf'
  · intro R _ S _ T _ f g H₁ H₂ s hs
    simp only [comap_comp, Set.image_comp]
    exact H₁ _ (H₂ _ hs)
/-
**PrimeSpectrum.isConstructible_range_comap** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpec
trum`。
形式化陈述：isConstructible_range_comap {f : R ->+* S} (hf : f.FinitePresentation) : I
sConstructible (Set.range <| comap f)
参数：hf : f.FinitePresentation。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.isConstructible_comap_image`：isConstructible_comap_image {
f : R ->+* S} (hf : f.FinitePresentation) {s : Set (PrimeSpectrum S)} (hs : IsCo
nstructible s) : IsConstructibl…
· 使用定理 `Topology.IsConstructible.univ`：∀ {X : Type u_2} [inst : TopologicalSpace
 X], Topology.IsConstructible Set.univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
lemma isConstructible_range_comap {f : R →+* S} (hf : f.FinitePresentation) :
    IsConstructible (Set.range <| comap f) :=
  Set.image_univ ▸ isConstructible_comap_image hf .univ

@[stacks 00I1]
/-
**PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation** 是 Mathli
b 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isOpenMap_comap_of_hasGoingDown_of_finitePresentation [Algebra R S] [Algeb
ra.HasGoingDown R S] [Algebra.FinitePresentation R S] : IsOpenMap (comap (algebr
aMap R S))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpenMap_iff`：∀ {α : Type u} {β : T
ype u_1} [t : TopologicalSpace α] [inst : TopologicalSpace β] {B : Set (Set α)},
   TopologicalSpace.IsTopologicalBasis …
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用引理 `PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible`：is
Open_of_stableUnderGeneralization_of_isConstructible {R : Type*} [CommRing R] {s
 : Set (PrimeSpectrum R)} (hs : StableUnderGeneralization …
· 使用定理 `StableUnderGeneralization.image`：∀ {X : Type u_1} {Y : Type u_2} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   GeneralizingMa
p f → ∀ {s : Set X}, …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`：iff_general
izingMap_primeSpectrumComap : Algebra.HasGoingDown R S ↔ GeneralizingMap (PrimeS
pectrum.comap (algebraMap R S))
· 使用引理 `IsOpen.stableUnderGeneralization`：IsOpen.stableUnderGeneralization {s : 
Set X} (hs : IsOpen s) : StableUnderGeneralization s
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用引理 `PrimeSpectrum.isConstructible_comap_image`：isConstructible_comap_image {
f : R ->+* S} (hf : f.FinitePresentation) {s : Set (PrimeSpectrum S)} (hs : IsCo
nstructible s) : IsConstructibl…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RingHom.finitePresentation_algebraMap`：finitePresentation_algebraMap [Al
gebra A B] : (algebraMap A B).FinitePresentation ↔ Algebra.FinitePresentation A 
B
· 使用引理 `PrimeSpectrum.isConstructible_basicOpen`：isConstructible_basicOpen {f : 
R} : IsConstructible (basicOpen f : Set (PrimeSpectrum R))
-/
lemma isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    [Algebra R S] [Algebra.HasGoingDown R S] [Algebra.FinitePresentation R S] :
    IsOpenMap (comap (algebraMap R S)) := by
  rw [isBasis_basic_opens.isOpenMap_iff]
  rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
  exact isOpen_of_stableUnderGeneralization_of_isConstructible
    ((basicOpen f).2.stableUnderGeneralization.image
      (Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp ‹_›))
    (isConstructible_comap_image (RingHom.finitePresentation_algebraMap.mpr ‹_›)
      isConstructible_basicOpen)

open TensorProduct in
@[stacks 037G]
/-
**PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field** 是 Mathlib 中的
一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isOpenMap_comap_algebraMap_tensorProduct_of_field {K A B : Type*} [Field K
] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] : IsOpenMap (PrimeSpectr
um.comap (algebraMap A (A otimes[K] B)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `exists_fg_and_mem_baseChange`：exists_fg_and_mem_baseChange {R A B : Type
*} [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B] (x
 : A otimes[R] B) …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FinitePresentation.of_finiteType`：of_finiteType [IsNoetherianRin
g R] : FiniteType R A ↔ FinitePresentation R A
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subalgebra.fg_top`：fg_top (S : Subalgebra R A) : (⊤ : Subalgebra R S).FG
 ↔ S.FG
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.mem_image_comap_basicOpen`：mem_image_comap_basicOpen (f : 
A) (x) : x in comap (algebraMap R A) '' basicOpen f ↔ ¬ IsNilpotent (algebraMap 
A (A otimes[R] x.asIdeal.Resi…
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `Algebra.TensorProduct.ext_ring`：∀ {R : Type u_4} {S : Type u_5} {A : Typ
e u_6} {B : Type u_7} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_
2 : Semiring A] [ins…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.restrictScalars.congr_simp`：∀ (R : Type u) {S : Type v} {A : Type
 w} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : 
Semiring A] [inst_3 : S…
· 使用定理 `Algebra.TensorProduct.map_comp_includeLeft`：map_comp_includeLeft (f : A 
->ₐ[S] C) (g : B ->ₐ[R] D) : (map f g).comp includeLeft = includeLeft.comp f
（共 53 条，此处仅展示前 30 条）
-/
theorem isOpenMap_comap_algebraMap_tensorProduct_of_field
    {K A B : Type*} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap A (A ⊗[K] B))) := by
  intro U hU
  wlog hU' : ∃ f, U = SetLike.coe (basicOpen f) generalizing U
  · rw [eq_biUnion_of_isOpen hU, Set.image_iUnion₂]
    exact isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ this _ (basicOpen _).isOpen ⟨_, rfl⟩
  obtain ⟨f, rfl⟩ := hU'
  obtain ⟨B', hB, f, rfl⟩ := exists_fg_and_mem_baseChange f
  have : Algebra.FinitePresentation K B' :=
    Algebra.FinitePresentation.of_finiteType.mp ⟨B'.fg_top.mpr hB⟩
  convert!
    isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := A) (S := A ⊗[K] B') _
      (basicOpen f).isOpen using 1
  ext x
  rw [PrimeSpectrum.mem_image_comap_basicOpen, PrimeSpectrum.mem_image_comap_basicOpen,
    not_iff_not]
  let ψ := Algebra.TensorProduct.map
    (Algebra.TensorProduct.map (.id A A) B'.val) (.id A x.asIdeal.ResidueField)
  have hψeq : ψ = (Algebra.TensorProduct.comm _ _ _ |>.toAlgHom.comp <|
    Algebra.TensorProduct.cancelBaseChange K A A _ B |>.symm.toAlgHom.comp <|
    Algebra.TensorProduct.map (.id _ _) B'.val |>.comp <|
    Algebra.TensorProduct.cancelBaseChange K A A _ B' |>.toAlgHom.comp <|
    (Algebra.TensorProduct.comm _ _ _).toAlgHom) := by ext; simp [ψ]
  have hψ : Function.Injective ψ := by
    rw [hψeq]
    dsimp
    simp_rw [EmbeddingLike.comp_injective, ← Function.comp_assoc, EquivLike.injective_comp]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [← IsNilpotent.map_iff hψ]
  rfl

end PrimeSpectrum

