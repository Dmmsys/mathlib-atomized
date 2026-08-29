/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sihan Su, Yongle Hu, Yi Song
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime

/-!
# Local properties about linear maps

In this file, we show that
injectivity, surjectivity, bijectivity and exactness of linear maps are local properties.
More precisely, we show that these can be checked at maximal ideals and on standard covers.
-/

public section

open Submodule LocalizedModule Ideal LinearMap

section isLocalized_maximal

open IsLocalizedModule

variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L]

-- For every maximal ideal `p` of `R`, let `Mₚ` (resp. `Nₚ`, resp. `Lₚ`) the localizations
-- of `M` (resp. `N`, resp. `L`) at `p`.
variable
  (Rₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : forall (P : Ideal R) [P.IsMaximal], M ->ₗ[R] Mₚ P)
  [forall (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (f P)]
  (Nₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], AddCommMonoid (Nₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Module R (Nₚ P)]
  (g : forall (P : Ideal R) [P.IsMaximal], N ->ₗ[R] Nₚ P)
  [forall (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (g P)]
  (Lₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], AddCommMonoid (Lₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Module R (Lₚ P)]
  (h : forall (P : Ideal R) [P.IsMaximal], L ->ₗ[R] Lₚ P)
  [forall (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (h P)]
  (F : M ->ₗ[R] N) (G : N ->ₗ[R] L)

/--
theorem `injective_of_isLocalized_maximal` / 定理 `injective_of_isLocalized_maximal`

English:
theorem injective_of_isLocalized_maximal
  proof: fun x y eq => Module.eq_of_localization_maximal _ f _ _ fun P _ => H P by simp [eq]

中文:
定理 injective_of_isLocalized_maximal
  证明: fun x y eq => Module.eq_of_localization_maximal _ f _ _ fun P _ => H P by simp [eq]

Depends on / 依赖: Module, Module.eq_of_localization_maximal, eq_of_localization_maximal
-/
theorem injective_of_isLocalized_maximal
    (H : forall (P : Ideal R) [P.IsMaximal], Function.Injective (map P.primeCompl (f P) (g P) F)) :
    Function.Injective F :=
fun x y eq => Module.eq_of_localization_maximal _ f _ _ fun P _ => H P by simp [eq]

/--
theorem `surjective_of_isLocalized_maximal` / 定理 `surjective_of_isLocalized_maximal`

English:
theorem surjective_of_isLocalized_maximal
  proof: range_eq_top.mp eq_top_of_localization₀_maximal Nₚ g _
fun P _ => (range_localizedMap_eq_localized₀_range _ (f P) (g P) F).symm.trans
range_eq_top.mpr H P

中文:
定理 surjective_of_isLocalized_maximal
  证明: range_eq_top.mp eq_top_of_localization₀_maximal Nₚ g _
fun P _ => (range_localizedMap_eq_localized₀_range _ (f P) (g P) F).symm.trans
range_eq_top.mpr H P

Depends on / 依赖: range_eq_top, range_eq_top.mp, range_eq_top.mpr, symm.trans
-/
theorem surjective_of_isLocalized_maximal
    (H : forall (P : Ideal R) [P.IsMaximal], Function.Surjective (map P.primeCompl (f P) (g P) F)) :
    Function.Surjective F :=
range_eq_top.mp eq_top_of_localization₀_maximal Nₚ g _
fun P _ => (range_localizedMap_eq_localized₀_range _ (f P) (g P) F).symm.trans
range_eq_top.mpr H P

/--
theorem `bijective_of_isLocalized_maximal` / 定理 `bijective_of_isLocalized_maximal`

English:
theorem bijective_of_isLocalized_maximal
  proof: ⟨injective_of_isLocalized_maximal Mₚ f Nₚ g F fun J _ => (H J).1,
  surjective_of_isLocalized_maximal Mₚ f Nₚ g F fun J _ => (H J).2⟩

中文:
定理 bijective_of_isLocalized_maximal
  证明: ⟨injective_of_isLocalized_maximal Mₚ f Nₚ g F fun J _ => (H J).1,
  surjective_of_isLocalized_maximal Mₚ f Nₚ g F fun J _ => (H J).2⟩

Depends on / 依赖: injective_of_isLocalized_maximal, surjective_of_isLocalized_maximal
-/
theorem bijective_of_isLocalized_maximal
    (H : forall (P : Ideal R) [P.IsMaximal], Function.Bijective (map P.primeCompl (f P) (g P) F)) :
    Function.Bijective F :=
  ⟨injective_of_isLocalized_maximal Mₚ f Nₚ g F fun J _ => (H J).1,
  surjective_of_isLocalized_maximal Mₚ f Nₚ g F fun J _ => (H J).2⟩

/--
theorem `exact_of_isLocalized_maximal` / 定理 `exact_of_isLocalized_maximal`

English:
theorem exact_of_isLocalized_maximal
  statement: (H : forall (J : Ideal R) [J.IsMaximal],
  proof: by
  simp only [LinearMap.exact_iff] at H ⊢
  apply eq_of_localization₀_maximal Nₚ g
  intro J hJ
  rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f J) (g J) F]; rw [← LinearMap.ker_localizedMap_eq_localized₀_ker J.primeCompl (g J) (h J) G]
have := SetLike.ext_iff.mp H J
  ext x
  simp on

中文:
定理 exact_of_isLocalized_maximal
  结论: (H : 对任意 (J : Ideal R) [J.IsMaximal],
  证明: by
  simp only [LinearMap.exact_iff] at H ⊢
  apply eq_of_localization₀_maximal Nₚ g
  intro J hJ
  rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f J) (g J) F]; rw [← LinearMap.ker_localizedMap_eq_localized₀_ker J.primeCompl (g J) (h J) G]
have := SetLike.ext_iff.mp H J
  ext x
  simp on

Depends on / 依赖: J.primeCompl, LinearMap, LinearMap.exact_iff, LinearMap.ker_localizedMap_eq_localized, LinearMap.range_localizedMap_eq_localized, SetLike, SetLike.ext_iff.mp, exact_iff, ext_iff, mem_ker, mem_range, primeCompl
-/
theorem exact_of_isLocalized_maximal (H : forall (J : Ideal R) [J.IsMaximal],
    Function.Exact (map J.primeCompl (f J) (g J) F) (map J.primeCompl (g J) (h J) G)) :
    Function.Exact F G := by
  simp only [LinearMap.exact_iff] at H ⊢
  apply eq_of_localization₀_maximal Nₚ g
  intro J hJ
  rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f J) (g J) F]; rw [← LinearMap.ker_localizedMap_eq_localized₀_ker J.primeCompl (g J) (h J) G]
have := SetLike.ext_iff.mp H J
  ext x
  simp only [mem_range, mem_ker] at this ⊢
  exact this x

/--
theorem `LinearIndependent.of_isLocalized_maximal` / 定理 `LinearIndependent.of_isLocalized_maximal`

English:
theorem LinearIndependent.of_isLocalized_maximal
  statement: {ι} (v : ι -> M)
  proof: injective_of_isLocalized_maximal _ (fun P _ => Finsupp.mapRange.linearMap <|
    Algebra.linearMap R (Rₚ P)) _ f _ fun P _ => by rw [map_linearCombination]; exact H P

中文:
定理 LinearIndependent.of_isLocalized_maximal
  结论: {ι} (v : ι -> M)
  证明: injective_of_isLocalized_maximal _ (fun P _ => Finsupp.mapRange.linearMap <|
    Algebra.linearMap R (Rₚ P)) _ f _ fun P _ => by rw [map_linearCombination]; exact H P

Depends on / 依赖: Algebra, Algebra.linearMap, Finsupp, Finsupp.mapRange.linearMap, injective_of_isLocalized_maximal, linearMap, mapRange, map_linearCombination
-/
theorem LinearIndependent.of_isLocalized_maximal {ι} (v : ι -> M)
    (H : forall (P : Ideal R) [P.IsMaximal], LinearIndependent (Rₚ P) (f P ∘ v)) :
    LinearIndependent R v :=
  injective_of_isLocalized_maximal _ (fun P _ => Finsupp.mapRange.linearMap <|
    Algebra.linearMap R (Rₚ P)) _ f _ fun P _ => by rw [map_linearCombination]; exact H P

end isLocalized_maximal

section localized_maximal

variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L] (f : M ->ₗ[R] N) (g : N ->ₗ[R] L)

/--
theorem `injective_of_localized_maximal` / 定理 `injective_of_localized_maximal`

English:
theorem injective_of_localized_maximal
  proof: injective_of_isLocalized_maximal _ (fun _ _ => mkLinearMap _ _) _ (fun _ _ => mkLinearMap _ _) f h

中文:
定理 injective_of_localized_maximal
  证明: injective_of_isLocalized_maximal _ (fun _ _ => mkLinearMap _ _) _ (fun _ _ => mkLinearMap _ _) f h

Depends on / 依赖: injective_of_isLocalized_maximal, mkLinearMap
-/
theorem injective_of_localized_maximal
    (h : forall (J : Ideal R) [J.IsMaximal], Function.Injective (map J.primeCompl f)) :
    Function.Injective f :=
  injective_of_isLocalized_maximal _ (fun _ _ => mkLinearMap _ _) _ (fun _ _ => mkLinearMap _ _) f h

/--
theorem `surjective_of_localized_maximal` / 定理 `surjective_of_localized_maximal`

English:
theorem surjective_of_localized_maximal
  proof: surjective_of_isLocalized_maximal _ (fun _ _ => mkLinearMap _ _) _ (fun _ _ => mkLinearMap _ _) f h

中文:
定理 surjective_of_localized_maximal
  证明: surjective_of_isLocalized_maximal _ (fun _ _ => mkLinearMap _ _) _ (fun _ _ => mkLinearMap _ _) f h

Depends on / 依赖: mkLinearMap, surjective_of_isLocalized_maximal
-/
theorem surjective_of_localized_maximal
    (h : forall (J : Ideal R) [J.IsMaximal], Function.Surjective (map J.primeCompl f)) :
    Function.Surjective f :=
  surjective_of_isLocalized_maximal _ (fun _ _ => mkLinearMap _ _) _ (fun _ _ => mkLinearMap _ _) f h

/--
theorem `bijective_of_localized_maximal` / 定理 `bijective_of_localized_maximal`

English:
theorem bijective_of_localized_maximal
  proof: ⟨injective_of_localized_maximal _ fun J _ => (h J).1,
  surjective_of_localized_maximal _ fun J _ => (h J).2⟩

中文:
定理 bijective_of_localized_maximal
  证明: ⟨injective_of_localized_maximal _ fun J _ => (h J).1,
  surjective_of_localized_maximal _ fun J _ => (h J).2⟩

Depends on / 依赖: injective_of_localized_maximal, surjective_of_localized_maximal
-/
theorem bijective_of_localized_maximal
    (h : forall (J : Ideal R) [J.IsMaximal], Function.Bijective (map J.primeCompl f)) :
    Function.Bijective f :=
  ⟨injective_of_localized_maximal _ fun J _ => (h J).1,
  surjective_of_localized_maximal _ fun J _ => (h J).2⟩

/--
theorem `exact_of_localized_maximal` / 定理 `exact_of_localized_maximal`

English:
theorem exact_of_localized_maximal
  proof: exact_of_isLocalized_maximal _ (fun _ _ => mkLinearMap _ _) _ (fun _ _ => mkLinearMap _ _)
    _ (fun _ _ => mkLinearMap _ _) f g h

中文:
定理 exact_of_localized_maximal
  证明: exact_of_isLocalized_maximal _ (fun _ _ => mkLinearMap _ _) _ (fun _ _ => mkLinearMap _ _)
    _ (fun _ _ => mkLinearMap _ _) f g h

Depends on / 依赖: exact_of_isLocalized_maximal, mkLinearMap
-/
theorem exact_of_localized_maximal
    (h : forall (J : Ideal R) [J.IsMaximal], Function.Exact (map J.primeCompl f) (map J.primeCompl g)) :
    Function.Exact f g :=
  exact_of_isLocalized_maximal _ (fun _ _ => mkLinearMap _ _) _ (fun _ _ => mkLinearMap _ _)
    _ (fun _ _ => mkLinearMap _ _) f g h

end localized_maximal

section isLocalized_span

open IsLocalizedModule

variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L] (s : Set R) (spn : Ideal.span s = ⊤)
include spn

-- For every element `r ∈ s`, let `Mᵣ` (resp. `Nᵣ`, resp. `Lᵣ`) the localizations
-- of `M` (resp. `N`, resp. `L`) away from `r`.
variable
  (Mₚ : forall _ : s, Type*)
  [forall r : s, AddCommMonoid (Mₚ r)]
  [forall r : s, Module R (Mₚ r)]
  (f : forall r : s, M ->ₗ[R] Mₚ r)
  [forall r : s, IsLocalizedModule.Away r.1 (f r)]
  (Nₚ : forall _ : s, Type*)
  [forall r : s, AddCommMonoid (Nₚ r)]
  [forall r : s, Module R (Nₚ r)]
  (g : forall r : s, N ->ₗ[R] Nₚ r)
  [forall r : s, IsLocalizedModule.Away r.1 (g r)]
  (Lₚ : forall _ : s, Type*)
  [forall r : s, AddCommMonoid (Lₚ r)]
  [forall r : s, Module R (Lₚ r)]
  (h : forall r : s, L ->ₗ[R] Lₚ r)
  [forall r : s, IsLocalizedModule.Away r.1 (h r)]
  (F : M ->ₗ[R] N) (G : N ->ₗ[R] L)

/--
theorem `injective_of_isLocalized_span` / 定理 `injective_of_isLocalized_span`

English:
theorem injective_of_isLocalized_span
  proof: fun x y eq => Module.eq_of_isLocalized_span _ spn _ f _ _ fun P => H P by simp [eq]

中文:
定理 injective_of_isLocalized_span
  证明: fun x y eq => Module.eq_of_isLocalized_span _ spn _ f _ _ fun P => H P by simp [eq]

Depends on / 依赖: Module, Module.eq_of_isLocalized_span, eq_of_isLocalized_span
-/
theorem injective_of_isLocalized_span
    (H : forall r : s, Function.Injective (map (.powers r.1) (f r) (g r) F)) :
    Function.Injective F :=
fun x y eq => Module.eq_of_isLocalized_span _ spn _ f _ _ fun P => H P by simp [eq]

/--
theorem `surjective_of_isLocalized_span` / 定理 `surjective_of_isLocalized_span`

English:
theorem surjective_of_isLocalized_span
  proof: range_eq_top.mp eq_top_of_isLocalized₀_span s spn Nₚ g fun r =>
(range_localizedMap_eq_localized₀_range _ (f r) (g r) F).symm.trans range_eq_top.mpr H r

中文:
定理 surjective_of_isLocalized_span
  证明: range_eq_top.mp eq_top_of_isLocalized₀_span s spn Nₚ g fun r =>
(range_localizedMap_eq_localized₀_range _ (f r) (g r) F).symm.trans range_eq_top.mpr H r

Depends on / 依赖: range_eq_top, range_eq_top.mp, range_eq_top.mpr, symm.trans
-/
theorem surjective_of_isLocalized_span
    (H : forall r : s, Function.Surjective (map (.powers r.1) (f r) (g r) F)) :
    Function.Surjective F :=
range_eq_top.mp eq_top_of_isLocalized₀_span s spn Nₚ g fun r =>
(range_localizedMap_eq_localized₀_range _ (f r) (g r) F).symm.trans range_eq_top.mpr H r

/--
theorem `bijective_of_isLocalized_span` / 定理 `bijective_of_isLocalized_span`

English:
theorem bijective_of_isLocalized_span
  proof: ⟨injective_of_isLocalized_span _ spn Mₚ f Nₚ g F fun r => (H r).1,
  surjective_of_isLocalized_span _ spn Mₚ f Nₚ g F fun r => (H r).2⟩

中文:
定理 bijective_of_isLocalized_span
  证明: ⟨injective_of_isLocalized_span _ spn Mₚ f Nₚ g F fun r => (H r).1,
  surjective_of_isLocalized_span _ spn Mₚ f Nₚ g F fun r => (H r).2⟩

Depends on / 依赖: injective_of_isLocalized_span, surjective_of_isLocalized_span
-/
theorem bijective_of_isLocalized_span
    (H : forall r : s, Function.Bijective (map (.powers r.1) (f r) (g r) F)) :
    Function.Bijective F :=
  ⟨injective_of_isLocalized_span _ spn Mₚ f Nₚ g F fun r => (H r).1,
  surjective_of_isLocalized_span _ spn Mₚ f Nₚ g F fun r => (H r).2⟩

/--
lemma `exact_of_isLocalized_span` / 引理 `exact_of_isLocalized_span`

English:
lemma exact_of_isLocalized_span
  statement: (H : forall r : s, Function.Exact
  proof: by
  simp only [LinearMap.exact_iff] at H ⊢
  apply Submodule.eq_of_isLocalized₀_span s spn Nₚ g
  intro r
  rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f r) (g r) F]
  rw [← LinearMap.ker_localizedMap_eq_localized₀_ker (.powers r.1) (g r) (h r) G]
have := SetLike.ext_iff.mp H r
  ext 

中文:
引理 exact_of_isLocalized_span
  结论: (H : 对任意 r : s, Function.Exact
  证明: by
  simp only [LinearMap.exact_iff] at H ⊢
  apply Submodule.eq_of_isLocalized₀_span s spn Nₚ g
  intro r
  rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f r) (g r) F]
  rw [← LinearMap.ker_localizedMap_eq_localized₀_ker (.powers r.1) (g r) (h r) G]
have := SetLike.ext_iff.mp H r
  ext 

Depends on / 依赖: LinearMap, LinearMap.exact_iff, LinearMap.ker_localizedMap_eq_localized, LinearMap.range_localizedMap_eq_localized, SetLike, SetLike.ext_iff.mp, Submodule, Submodule.eq_of_isLocalized, exact_iff, ext_iff, mem_ker, mem_range, powers
-/
lemma exact_of_isLocalized_span (H : forall r : s, Function.Exact
    (map (.powers r.1) (f r) (g r) F) (map (.powers r.1) (g r) (h r) G)) :
    Function.Exact F G := by
  simp only [LinearMap.exact_iff] at H ⊢
  apply Submodule.eq_of_isLocalized₀_span s spn Nₚ g
  intro r
  rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f r) (g r) F]
  rw [← LinearMap.ker_localizedMap_eq_localized₀_ker (.powers r.1) (g r) (h r) G]
have := SetLike.ext_iff.mp H r
  ext x
  simp only [mem_range, mem_ker] at this ⊢
  exact this x

end isLocalized_span

section localized_span

variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L]
  (s : Set R) (spn : span s = ⊤) (f : M ->ₗ[R] N) (g : N ->ₗ[R] L)
include spn

/--
theorem `injective_of_localized_span` / 定理 `injective_of_localized_span`

English:
theorem injective_of_localized_span
  proof: injective_of_isLocalized_span s spn _ (fun _ => mkLinearMap _ _) _ (fun _ => mkLinearMap _ _) f h

中文:
定理 injective_of_localized_span
  证明: injective_of_isLocalized_span s spn _ (fun _ => mkLinearMap _ _) _ (fun _ => mkLinearMap _ _) f h

Depends on / 依赖: injective_of_isLocalized_span, mkLinearMap
-/
theorem injective_of_localized_span
    (h : forall r : s, Function.Injective (map (.powers r.1) f)) :
    Function.Injective f :=
  injective_of_isLocalized_span s spn _ (fun _ => mkLinearMap _ _) _ (fun _ => mkLinearMap _ _) f h

/--
theorem `surjective_of_localized_span` / 定理 `surjective_of_localized_span`

English:
theorem surjective_of_localized_span
  proof: surjective_of_isLocalized_span s spn _ (fun _ => mkLinearMap _ _) _ (fun _ => mkLinearMap _ _) f h

中文:
定理 surjective_of_localized_span
  证明: surjective_of_isLocalized_span s spn _ (fun _ => mkLinearMap _ _) _ (fun _ => mkLinearMap _ _) f h

Depends on / 依赖: mkLinearMap, surjective_of_isLocalized_span
-/
theorem surjective_of_localized_span
    (h : forall r : s, Function.Surjective (map (.powers r.1) f)) :
    Function.Surjective f :=
  surjective_of_isLocalized_span s spn _ (fun _ => mkLinearMap _ _) _ (fun _ => mkLinearMap _ _) f h

/--
theorem `bijective_of_localized_span` / 定理 `bijective_of_localized_span`

English:
theorem bijective_of_localized_span
  proof: ⟨injective_of_localized_span _ spn _ fun r => (h r).1,
  surjective_of_localized_span _ spn _ fun r => (h r).2⟩

中文:
定理 bijective_of_localized_span
  证明: ⟨injective_of_localized_span _ spn _ fun r => (h r).1,
  surjective_of_localized_span _ spn _ fun r => (h r).2⟩

Depends on / 依赖: injective_of_localized_span, surjective_of_localized_span
-/
theorem bijective_of_localized_span
    (h : forall r : s, Function.Bijective (map (.powers r.1) f)) :
    Function.Bijective f :=
  ⟨injective_of_localized_span _ spn _ fun r => (h r).1,
  surjective_of_localized_span _ spn _ fun r => (h r).2⟩

/--
lemma `exact_of_localized_span` / 引理 `exact_of_localized_span`

English:
lemma exact_of_localized_span
  proof: exact_of_isLocalized_span s spn _ (fun _ => mkLinearMap _ _) _ (fun _ => mkLinearMap _ _)
    _ (fun _ => mkLinearMap _ _) f g h

中文:
引理 exact_of_localized_span
  证明: exact_of_isLocalized_span s spn _ (fun _ => mkLinearMap _ _) _ (fun _ => mkLinearMap _ _)
    _ (fun _ => mkLinearMap _ _) f g h

Depends on / 依赖: exact_of_isLocalized_span, mkLinearMap
-/
lemma exact_of_localized_span
    (h : forall r : s, Function.Exact (map (.powers r.1) f) (map (.powers r.1) g)) :
    Function.Exact f g :=
  exact_of_isLocalized_span s spn _ (fun _ => mkLinearMap _ _) _ (fun _ => mkLinearMap _ _)
    _ (fun _ => mkLinearMap _ _) f g h

end localized_span

section Algebra

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

-- For every maximal ideal `p` of `R`, let `Rₚ` be the localization of `R` at `p`
-- and `Sₚ` the localization of `S` at `p`.
variable
  (Rₚ : forall (p : Ideal R) [p.IsMaximal], Type*)
  [forall (p : Ideal R) [p.IsMaximal], CommSemiring (Rₚ p)]
  [forall (p : Ideal R) [p.IsMaximal], Algebra R (Rₚ p)]
  (Sₚ : forall (p : Ideal R) [p.IsMaximal], Type*)
  [forall (p : Ideal R) [p.IsMaximal], CommSemiring (Sₚ p)]
  [forall (p : Ideal R) [p.IsMaximal], Algebra S (Sₚ p)]
  [forall (p : Ideal R) [p.IsMaximal], Algebra (Rₚ p) (Sₚ p)]
  [forall (p : Ideal R) [p.IsMaximal], Algebra R (Sₚ p)]
  [forall (p : Ideal R) [p.IsMaximal], IsScalarTower R (Rₚ p) (Sₚ p)]
  [forall (p : Ideal R) [p.IsMaximal], IsScalarTower R S (Sₚ p)]
  [forall (p : Ideal R) [p.IsMaximal], IsLocalization.AtPrime (Rₚ p) p]
  [forall (p : Ideal R) [p.IsMaximal],
    IsLocalizedModule.AtPrime p (IsScalarTower.toAlgHom R S (Sₚ p) : S ->ₗ[R] (Sₚ p))]

open TensorProduct

/--
lemma `IsLocalizedModule.map_linearMap_of_isLocalization` / 引理 `IsLocalizedModule.map_linearMap_of_isLocalization`

English:
lemma IsLocalizedModule.map_linearMap_of_isLocalization
  statement: (Rₚ Sₚ : Type*) [CommSemiring Rₚ]
  proof: by
  apply IsLocalizedModule.linearMap_ext p.primeCompl (Algebra.linearMap _ _)
    (IsScalarTower.toAlgHom R S Sₚ : S ->ₗ[R] Sₚ)
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, map_one,
    LinearMap.coe_restrictScalars]
  rw [show 1 = Algebra.linearMap R Rₚ 1 b

中文:
引理 IsLocalizedModule.map_linearMap_of_isLocalization
  结论: (Rₚ Sₚ : 类型) [CommSemiring Rₚ]
  证明: by
  apply IsLocalizedModule.linearMap_ext p.primeCompl (Algebra.linearMap _ _)
    (IsScalarTower.toAlgHom R S Sₚ : S ->ₗ[R] Sₚ)
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, map_one,
    LinearMap.coe_restrictScalars]
  rw [show 1 = Algebra.linearMap R Rₚ 1 b

Depends on / 依赖: Algebra, Algebra.linearMap, Algebra.linearMap_apply, Function, Function.comp_apply, IsLocalizedModule, IsLocalizedModule.linearMap_ext, IsLocalizedModule.map_apply, IsScalarTower, IsScalarTower.toAlgHom, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, coe_comp, coe_restrictScalars, comp_apply, linearMap, linearMap_apply, linearMap_ext, map_apply
-/
lemma IsLocalizedModule.map_linearMap_of_isLocalization (Rₚ Sₚ : Type*) [CommSemiring Rₚ]
    [Algebra R Rₚ] [CommSemiring Sₚ] [Algebra S Sₚ] [Algebra R Sₚ] [IsScalarTower R S Sₚ]
    [Algebra Rₚ Sₚ] [IsScalarTower R Rₚ Sₚ] (p : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime Rₚ p]
    [IsLocalizedModule.AtPrime p (IsScalarTower.toAlgHom R S Sₚ : S ->ₗ[R] Sₚ)] :
    IsLocalizedModule.map p.primeCompl (Algebra.linearMap R Rₚ)
        (IsScalarTower.toAlgHom R S Sₚ : S ->ₗ[R] Sₚ) (Algebra.linearMap R S) =
    (Algebra.linearMap Rₚ Sₚ).restrictScalars R := by
  apply IsLocalizedModule.linearMap_ext p.primeCompl (Algebra.linearMap _ _)
    (IsScalarTower.toAlgHom R S Sₚ : S ->ₗ[R] Sₚ)
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, map_one,
    LinearMap.coe_restrictScalars]
  rw [show 1 = Algebra.linearMap R Rₚ 1 by simp]; rw [IsLocalizedModule.map_apply]
  simp

/--
lemma `injective_of_isLocalization_isMaximal` / 引理 `injective_of_isLocalization_isMaximal`

English:
lemma injective_of_isLocalization_isMaximal
  proof: by
  apply injective_of_isLocalized_maximal (fun P _ => Rₚ P) (fun P _ => Algebra.linearMap _ _)
    (fun P _ => Sₚ P) (fun P _ => IsScalarTower.toAlgHom R S (Sₚ P)) (Algebra.linearMap R S) _
  intro p hp
  convert_to Function.Injective ((Algebra.linearMap (Rₚ p) (Sₚ p)).restrictScalars R)
  · rw [D

中文:
引理 injective_of_isLocalization_isMaximal
  证明: by
  apply injective_of_isLocalized_maximal (fun P _ => Rₚ P) (fun P _ => Algebra.linearMap _ _)
    (fun P _ => Sₚ P) (fun P _ => IsScalarTower.toAlgHom R S (Sₚ P)) (Algebra.linearMap R S) _
  intro p hp
  convert_to Function.Injective ((Algebra.linearMap (Rₚ p) (Sₚ p)).restrictScalars R)
  · rw [D

Depends on / 依赖: Algebra, Algebra.linearMap, DFunLike, DFunLike.coe_fn_eq, Function, Function.Injective, Injective, IsLocalizedModule, IsLocalizedModule.map_linearMap_of_isLocalization, IsScalarTower, IsScalarTower.toAlgHom, coe_fn_eq, convert_to, injective_of_isLocalized_maximal, linearMap, map_linearMap_of_isLocalization, restrictScalars, toAlgHom
-/
lemma injective_of_isLocalization_isMaximal
    (H : forall (p : Ideal R) [p.IsMaximal], Function.Injective (algebraMap (Rₚ p) (Sₚ p))) :
    Function.Injective (algebraMap R S) := by
  apply injective_of_isLocalized_maximal (fun P _ => Rₚ P) (fun P _ => Algebra.linearMap _ _)
    (fun P _ => Sₚ P) (fun P _ => IsScalarTower.toAlgHom R S (Sₚ P)) (Algebra.linearMap R S) _
  intro p hp
  convert_to Function.Injective ((Algebra.linearMap (Rₚ p) (Sₚ p)).restrictScalars R)
  · rw [DFunLike.coe_fn_eq]
    apply IsLocalizedModule.map_linearMap_of_isLocalization
  · exact H p

/--
lemma `surjective_of_isLocalization_isMaximal` / 引理 `surjective_of_isLocalization_isMaximal`

English:
lemma surjective_of_isLocalization_isMaximal
  proof: by
  apply surjective_of_isLocalized_maximal (fun P _ => Rₚ P) (fun P _ => Algebra.linearMap _ _)
    (fun P _ => Sₚ P) (fun P _ => IsScalarTower.toAlgHom R S (Sₚ P)) (Algebra.linearMap R S) _
  intro p hp
  convert_to Function.Surjective ((Algebra.linearMap (Rₚ p) (Sₚ p)).restrictScalars R)
  · rw 

中文:
引理 surjective_of_isLocalization_isMaximal
  证明: by
  apply surjective_of_isLocalized_maximal (fun P _ => Rₚ P) (fun P _ => Algebra.linearMap _ _)
    (fun P _ => Sₚ P) (fun P _ => IsScalarTower.toAlgHom R S (Sₚ P)) (Algebra.linearMap R S) _
  intro p hp
  convert_to Function.Surjective ((Algebra.linearMap (Rₚ p) (Sₚ p)).restrictScalars R)
  · rw 

Depends on / 依赖: Algebra, Algebra.linearMap, DFunLike, DFunLike.coe_fn_eq, Function, Function.Surjective, IsLocalizedModule, IsLocalizedModule.map_linearMap_of_isLocalization, IsScalarTower, IsScalarTower.toAlgHom, Surjective, coe_fn_eq, convert_to, linearMap, map_linearMap_of_isLocalization, restrictScalars, surjective_of_isLocalized_maximal, toAlgHom
-/
lemma surjective_of_isLocalization_isMaximal
    (H : forall (p : Ideal R) [p.IsMaximal], Function.Surjective (algebraMap (Rₚ p) (Sₚ p))) :
    Function.Surjective (algebraMap R S) := by
  apply surjective_of_isLocalized_maximal (fun P _ => Rₚ P) (fun P _ => Algebra.linearMap _ _)
    (fun P _ => Sₚ P) (fun P _ => IsScalarTower.toAlgHom R S (Sₚ P)) (Algebra.linearMap R S) _
  intro p hp
  convert_to Function.Surjective ((Algebra.linearMap (Rₚ p) (Sₚ p)).restrictScalars R)
  · rw [DFunLike.coe_fn_eq]
    apply IsLocalizedModule.map_linearMap_of_isLocalization
  · exact H p

/--
lemma `bijective_of_isLocalization_isMaximal` / 引理 `bijective_of_isLocalization_isMaximal`

English:
lemma bijective_of_isLocalization_isMaximal
  proof: ⟨injective_of_isLocalization_isMaximal _ _ (fun p _ => (H p).1),
    surjective_of_isLocalization_isMaximal _ _ (fun p _ => (H p).2)⟩

中文:
引理 bijective_of_isLocalization_isMaximal
  证明: ⟨injective_of_isLocalization_isMaximal _ _ (fun p _ => (H p).1),
    surjective_of_isLocalization_isMaximal _ _ (fun p _ => (H p).2)⟩

Depends on / 依赖: injective_of_isLocalization_isMaximal, surjective_of_isLocalization_isMaximal
-/
lemma bijective_of_isLocalization_isMaximal
    (H : forall (p : Ideal R) [p.IsMaximal], Function.Bijective (algebraMap (Rₚ p) (Sₚ p))) :
    Function.Bijective (algebraMap R S) :=
  ⟨injective_of_isLocalization_isMaximal _ _ (fun p _ => (H p).1),
    surjective_of_isLocalization_isMaximal _ _ (fun p _ => (H p).2)⟩

end Algebra

section IsLocalization

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {s : Set R} (hs : span s = ⊤)
-- For every element `r ∈ s`, let `Rᵣ` be the localization of `R` away from `r`
-- and `Sᵣ` the localization of `S` away from `f r`.
variable (Rᵣ : s -> Type*) [forall r, CommSemiring (Rᵣ r)] [forall r, Algebra R (Rᵣ r)]
  (Sᵣ : s -> Type*) [forall r, CommSemiring (Sᵣ r)] [forall r, Algebra S (Sᵣ r)]
variable (f : R ->+* S) [forall r, IsLocalization.Away r.val (Rᵣ r)]
    [forall r, IsLocalization.Away (f r.val) (Sᵣ r)]
include hs

/--
lemma `injective_of_isLocalization_of_span_eq_top` / 引理 `injective_of_isLocalization_of_span_eq_top`

English:
lemma injective_of_isLocalization_of_span_eq_top
  proof: by
  algebraize [f]
.toAlgebra let (r : s) : Algebra R (Sᵣ r) := (algebraMap S (Sᵣ r)).comp f
  have (r : s) : IsScalarTower R S (Sᵣ r) := IsScalarTower.of_algebraMap_eq' rfl
  have : forall r, IsLocalization.Away (algebraMap R S r.val) (Sᵣ r) := ‹_›
  let (r : s) : Algebra (Rᵣ r) (Sᵣ r) := localiza

中文:
引理 injective_of_isLocalization_of_span_eq_top
  证明: by
  algebraize [f]
.toAlgebra let (r : s) : Algebra R (Sᵣ r) := (algebraMap S (Sᵣ r)).comp f
  have (r : s) : IsScalarTower R S (Sᵣ r) := IsScalarTower.of_algebraMap_eq' rfl
  have : forall r, IsLocalization.Away (algebraMap R S r.val) (Sᵣ r) := ‹_›
  let (r : s) : Algebra (Rᵣ r) (Sᵣ r) := localiza

Depends on / 依赖: Algebra, Algebra.linearM, IsLocalization, IsLocalization.Away, IsScalarTower, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.algebraMap_toAlgebra, algebraMap, algebraMap_toAlgebra, algebraize, injective_of_isLocalized_span, linearM, localizationAlgebra, of_algebraMap_eq, powers, r.val, toAlgebra
-/
lemma injective_of_isLocalization_of_span_eq_top
    (h : forall r : s, Function.Injective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) :
    Function.Injective f := by
  algebraize [f]
.toAlgebra let (r : s) : Algebra R (Sᵣ r) := (algebraMap S (Sᵣ r)).comp f
  have (r : s) : IsScalarTower R S (Sᵣ r) := IsScalarTower.of_algebraMap_eq' rfl
  have : forall r, IsLocalization.Away (algebraMap R S r.val) (Sᵣ r) := ‹_›
  let (r : s) : Algebra (Rᵣ r) (Sᵣ r) := localizationAlgebra (.powers r.val) S
  have (r : s) : IsScalarTower R (Rᵣ r) (Sᵣ r) :=
.of_algebraMap_eq by simp [RingHom.algebraMap_toAlgebra]
  apply injective_of_isLocalized_span s hs Rᵣ (fun r : s => Algebra.linearMap _ _) _
    (fun r : s => ((IsScalarTower.toAlgHom R S (Sᵣ r)).toLinearMap)) (Algebra.linearMap R S)
  simpa [IsLocalization.map_linearMap_eq_toLinearMap_mapₐ] using! h

/--
lemma `surjective_of_isLocalization_of_span_eq_top` / 引理 `surjective_of_isLocalization_of_span_eq_top`

English:
lemma surjective_of_isLocalization_of_span_eq_top
  proof: by
  algebraize [f]
.toAlgebra let (r : s) : Algebra R (Sᵣ r) := (algebraMap S (Sᵣ r)).comp f
  have (r : s) : IsScalarTower R S (Sᵣ r) := IsScalarTower.of_algebraMap_eq' rfl
  have : forall r, IsLocalization.Away (algebraMap R S r.val) (Sᵣ r) := ‹_›
  let (r : s) : Algebra (Rᵣ r) (Sᵣ r) := localiza

中文:
引理 surjective_of_isLocalization_of_span_eq_top
  证明: by
  algebraize [f]
.toAlgebra let (r : s) : Algebra R (Sᵣ r) := (algebraMap S (Sᵣ r)).comp f
  have (r : s) : IsScalarTower R S (Sᵣ r) := IsScalarTower.of_algebraMap_eq' rfl
  have : forall r, IsLocalization.Away (algebraMap R S r.val) (Sᵣ r) := ‹_›
  let (r : s) : Algebra (Rᵣ r) (Sᵣ r) := localiza

Depends on / 依赖: Algebra, Algebra.linear, IsLocalization, IsLocalization.Away, IsScalarTower, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.algebraMap_toAlgebra, algebraMap, algebraMap_toAlgebra, algebraize, linear, localizationAlgebra, of_algebraMap_eq, powers, r.val, surjective_of_isLocalized_span, toAlgebra
-/
lemma surjective_of_isLocalization_of_span_eq_top
    (h : forall r : s, Function.Surjective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) :
    Function.Surjective f := by
  algebraize [f]
.toAlgebra let (r : s) : Algebra R (Sᵣ r) := (algebraMap S (Sᵣ r)).comp f
  have (r : s) : IsScalarTower R S (Sᵣ r) := IsScalarTower.of_algebraMap_eq' rfl
  have : forall r, IsLocalization.Away (algebraMap R S r.val) (Sᵣ r) := ‹_›
  let (r : s) : Algebra (Rᵣ r) (Sᵣ r) := localizationAlgebra (.powers r.val) S
  have (r : s) : IsScalarTower R (Rᵣ r) (Sᵣ r) :=
.of_algebraMap_eq by simp [RingHom.algebraMap_toAlgebra]
  apply surjective_of_isLocalized_span s hs Rᵣ (fun r : s => Algebra.linearMap _ _) _
    (fun r : s => ((IsScalarTower.toAlgHom R S (Sᵣ r)).toLinearMap)) (Algebra.linearMap R S)
  simpa [IsLocalization.map_linearMap_eq_toLinearMap_mapₐ] using! h

/--
lemma `bijective_of_isLocalization_of_span_eq_top` / 引理 `bijective_of_isLocalization_of_span_eq_top`

English:
lemma bijective_of_isLocalization_of_span_eq_top
  proof: ⟨injective_of_isLocalization_of_span_eq_top hs _ _ _ (fun r => (h r).1),
    surjective_of_isLocalization_of_span_eq_top hs _ _ _ (fun r => (h r).2)⟩

中文:
引理 bijective_of_isLocalization_of_span_eq_top
  证明: ⟨injective_of_isLocalization_of_span_eq_top hs _ _ _ (fun r => (h r).1),
    surjective_of_isLocalization_of_span_eq_top hs _ _ _ (fun r => (h r).2)⟩

Depends on / 依赖: injective_of_isLocalization_of_span_eq_top, surjective_of_isLocalization_of_span_eq_top
-/
lemma bijective_of_isLocalization_of_span_eq_top
    (h : forall r : s, Function.Bijective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) :
    Function.Bijective f :=
  ⟨injective_of_isLocalization_of_span_eq_top hs _ _ _ (fun r => (h r).1),
    surjective_of_isLocalization_of_span_eq_top hs _ _ _ (fun r => (h r).2)⟩

end IsLocalization
