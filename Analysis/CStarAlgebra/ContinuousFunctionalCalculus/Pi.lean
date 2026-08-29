/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.Star.StarAlgHom

/-! # The continuous functional calculus on product types

This file contains results about the continuous functional calculus on (indexed) product types.

## Main theorems

+ `cfc_map_pi` and `cfcₙ_map_pi`: given `a : ∀ i, A i`, then `cfc f a = fun i => cfc f (a i)`
  (and likewise for the non-unital version)
+ `cfc_map_prod` and `cfcₙ_map_prod`: given `a : A` and `b : B`, then
  `cfc f (a, b) = (cfc f a, cfc f b)` (and likewise for the non-unital version)
-/

public section

section nonunital_pi

variable {ι R S : Type*} {A : ι -> Type*} [CommSemiring R] [Nontrivial R] [StarRing R]
  [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [CommRing S] [Algebra R S]
  [forall i, NonUnitalRing (A i)] [forall i, Module S (A i)] [forall i, Module R (A i)]
  [forall i, IsScalarTower R S (A i)] [forall i, SMulCommClass R (A i) (A i)]
  [forall i, IsScalarTower R (A i) (A i)]
  [forall i, StarRing (A i)] [forall i, TopologicalSpace (A i)] {p : (forall i, A i) -> Prop}
  {q : (i : ι) -> A i -> Prop}
  [NonUnitalContinuousFunctionalCalculus R (forall i, A i) p]
  [forall i, NonUnitalContinuousFunctionalCalculus R (A i) (q i)]
  [forall i, ContinuousMapZero.UniqueHom R (A i)]

include S in
/--
lemma `cfcₙ_map_pi` / 引理 `cfcₙ_map_pi`

English:
lemma cfcₙ_map_pi
  statement: (f : R -> R) (a : forall i, A i)
  proof: by
  by_cases hf₀ : f 0 = 0
  · ext i
    have : Nonempty ι := ⟨i⟩
    let φ := Pi.evalNonUnitalStarAlgHom S A i
    exact φ.map_cfcₙ f a (by rwa [Pi.quasispectrum_eq]) hf₀ (continuous_apply i) ha (ha' i)
  · simp only [cfcₙ_apply_of_not_map_zero _ hf₀, Pi.zero_def]

中文:
引理 cfcₙ_map_pi
  结论: (f : R -> R) (a : 对任意 i, A i)
  证明: by
  by_cases hf₀ : f 0 = 0
  · ext i
    have : Nonempty ι := ⟨i⟩
    let φ := Pi.evalNonUnitalStarAlgHom S A i
    exact φ.map_cfcₙ f a (by rwa [Pi.quasispectrum_eq]) hf₀ (continuous_apply i) ha (ha' i)
  · simp only [cfcₙ_apply_of_not_map_zero _ hf₀, Pi.zero_def]

Depends on / 依赖: Nonempty, Pi.evalNonUnitalStarAlgHom, Pi.quasispectrum_eq, Pi.zero_def, cfc_cont_tac, cfc_tac, continuous_apply, evalNonUnitalStarAlgHom, quasispectrum_eq, zero_def
-/
lemma cfcₙ_map_pi (f : R -> R) (a : forall i, A i)
    (hf : ContinuousOn f (⋃ i, quasispectrum R (a i)) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) (ha' : forall i, q i (a i) := by cfc_tac) :
    cfcₙ f a = fun i => cfcₙ f (a i) := by
  by_cases hf₀ : f 0 = 0
  · ext i
    have : Nonempty ι := ⟨i⟩
    let φ := Pi.evalNonUnitalStarAlgHom S A i
    exact φ.map_cfcₙ f a (by rwa [Pi.quasispectrum_eq]) hf₀ (continuous_apply i) ha (ha' i)
  · simp only [cfcₙ_apply_of_not_map_zero _ hf₀, Pi.zero_def]

end nonunital_pi

section nonunital_prod

variable {A B R S : Type*} [CommSemiring R] [CommRing S] [Nontrivial R] [StarRing R]
  [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Algebra R S] [NonUnitalRing A]
  [NonUnitalRing B] [Module S A] [Module R A] [Module R B] [Module S B]
  [SMulCommClass R A A] [SMulCommClass R B B] [IsScalarTower R A A] [IsScalarTower R B B]
  [StarRing A] [StarRing B] [TopologicalSpace A] [TopologicalSpace B]
  [IsScalarTower R S A] [IsScalarTower R S B]
  {pab : A × B -> Prop} {pa : A -> Prop} {pb : B -> Prop}
  [NonUnitalContinuousFunctionalCalculus R (A × B) pab]
  [NonUnitalContinuousFunctionalCalculus R A pa]
  [NonUnitalContinuousFunctionalCalculus R B pb]
  [ContinuousMapZero.UniqueHom R A] [ContinuousMapZero.UniqueHom R B]

include S in
/--
lemma `cfcₙ_map_prod` / 引理 `cfcₙ_map_prod`

English:
lemma cfcₙ_map_prod
  statement: (f : R -> R) (a : A) (b : B)
  proof: by
  by_cases hf₀ : f 0 = 0
  case pos =>
    ext
    case fst =>
      let φ := NonUnitalStarAlgHom.fst S A B
      exact φ.map_cfcₙ f (a, b) (by rwa [Prod.quasispectrum_eq]) hf₀ continuous_fst hab ha
    case snd =>
      let φ := NonUnitalStarAlgHom.snd S A B
      exact φ.map_cfcₙ f (a, b) (by r

中文:
引理 cfcₙ_map_prod
  结论: (f : R -> R) (a : A) (b : B)
  证明: by
  by_cases hf₀ : f 0 = 0
  case pos =>
    ext
    case fst =>
      let φ := NonUnitalStarAlgHom.fst S A B
      exact φ.map_cfcₙ f (a, b) (by rwa [Prod.quasispectrum_eq]) hf₀ continuous_fst hab ha
    case snd =>
      let φ := NonUnitalStarAlgHom.snd S A B
      exact φ.map_cfcₙ f (a, b) (by r

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.fst, NonUnitalStarAlgHom.snd, Prod.quasispectrum_eq, cfc_cont_tac, cfc_tac, continuous_fst, continuous_snd, quasispectrum_eq
-/
lemma cfcₙ_map_prod (f : R -> R) (a : A) (b : B)
    (hf : ContinuousOn f (quasispectrum R a union quasispectrum R b) := by cfc_cont_tac)
    (hab : pab (a, b) := by cfc_tac) (ha : pa a := by cfc_tac) (hb : pb b := by cfc_tac) :
    cfcₙ f (a, b) = (cfcₙ f a, cfcₙ f b) := by
  by_cases hf₀ : f 0 = 0
  case pos =>
    ext
    case fst =>
      let φ := NonUnitalStarAlgHom.fst S A B
      exact φ.map_cfcₙ f (a, b) (by rwa [Prod.quasispectrum_eq]) hf₀ continuous_fst hab ha
    case snd =>
      let φ := NonUnitalStarAlgHom.snd S A B
      exact φ.map_cfcₙ f (a, b) (by rwa [Prod.quasispectrum_eq]) hf₀ continuous_snd hab hb
  case neg =>
    simp [cfcₙ_apply_of_not_map_zero _ hf₀, eqComm]

end nonunital_prod

section unital_pi

variable {ι R S : Type*} {A : ι -> Type*} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [CommRing S] [Algebra R S]
  [forall i, Ring (A i)] [forall i, Algebra S (A i)] [forall i, Algebra R (A i)] [forall i, IsScalarTower R S (A i)]
  [hinst : IsScalarTower R S (forall i, A i)]
  [forall i, StarRing (A i)] [forall i, TopologicalSpace (A i)] {p : (forall i, A i) -> Prop}
  {q : (i : ι) -> A i -> Prop}
  [ContinuousFunctionalCalculus R (forall i, A i) p]
  [forall i, ContinuousFunctionalCalculus R (A i) (q i)]
  [forall i, ContinuousMap.UniqueHom R (A i)]

include S in
/--
lemma `cfc_map_pi` / 引理 `cfc_map_pi`

English:
lemma cfc_map_pi
  statement: (f : R -> R) (a : forall i, A i)
  proof: by
  ext i
  let φ := Pi.evalStarAlgHom S A i
  exact φ.map_cfc f a (by rwa [Pi.spectrum_eq]) (continuous_apply i) ha (ha' i)

中文:
引理 cfc_map_pi
  结论: (f : R -> R) (a : 对任意 i, A i)
  证明: by
  ext i
  let φ := Pi.evalStarAlgHom S A i
  exact φ.map_cfc f a (by rwa [Pi.spectrum_eq]) (continuous_apply i) ha (ha' i)

Depends on / 依赖: Pi.evalStarAlgHom, Pi.spectrum_eq, cfc_cont_tac, cfc_tac, continuous_apply, evalStarAlgHom, map_cfc, spectrum_eq
-/
lemma cfc_map_pi (f : R -> R) (a : forall i, A i)
    (hf : ContinuousOn f (⋃ i, spectrum R (a i)) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) (ha' : forall i, q i (a i) := by cfc_tac) :
    cfc f a = fun i => cfc f (a i) := by
  ext i
  let φ := Pi.evalStarAlgHom S A i
  exact φ.map_cfc f a (by rwa [Pi.spectrum_eq]) (continuous_apply i) ha (ha' i)

end unital_pi

section unital_prod

variable {A B R S : Type*} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [CommRing S] [Algebra R S]
  [Ring A] [Ring B] [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B]
  [IsScalarTower R S A] [IsScalarTower R S B]
  [StarRing A] [StarRing B] [TopologicalSpace A] [TopologicalSpace B] {pab : A × B -> Prop}
  {pa : A -> Prop} {pb : B -> Prop}
  [ContinuousFunctionalCalculus R (A × B) pab]
  [ContinuousFunctionalCalculus R A pa] [ContinuousFunctionalCalculus R B pb]
  [ContinuousMap.UniqueHom R A] [ContinuousMap.UniqueHom R B]

include S in
/--
lemma `cfc_map_prod` / 引理 `cfc_map_prod`

English:
lemma cfc_map_prod
  statement: (f : R -> R) (a : A) (b : B)
  proof: by
  ext
  case fst =>
    let φ := StarAlgHom.fst S A B
    exact φ.map_cfc f (a, b) (by rwa [Prod.spectrum_eq]) continuous_fst hab ha
  case snd =>
    let φ := StarAlgHom.snd S A B
    exact φ.map_cfc f (a, b) (by rwa [Prod.spectrum_eq]) continuous_snd hab hb

中文:
引理 cfc_map_prod
  结论: (f : R -> R) (a : A) (b : B)
  证明: by
  ext
  case fst =>
    let φ := StarAlgHom.fst S A B
    exact φ.map_cfc f (a, b) (by rwa [Prod.spectrum_eq]) continuous_fst hab ha
  case snd =>
    let φ := StarAlgHom.snd S A B
    exact φ.map_cfc f (a, b) (by rwa [Prod.spectrum_eq]) continuous_snd hab hb

Depends on / 依赖: Prod.spectrum_eq, StarAlgHom, StarAlgHom.fst, StarAlgHom.snd, cfc_cont_tac, cfc_tac, continuous_fst, continuous_snd, map_cfc, spectrum_eq
-/
lemma cfc_map_prod (f : R -> R) (a : A) (b : B)
    (hf : ContinuousOn f (spectrum R a union spectrum R b) := by cfc_cont_tac)
    (hab : pab (a, b) := by cfc_tac) (ha : pa a := by cfc_tac) (hb : pb b := by cfc_tac) :
    cfc f (a, b) = (cfc f a, cfc f b) := by
  ext
  case fst =>
    let φ := StarAlgHom.fst S A B
    exact φ.map_cfc f (a, b) (by rwa [Prod.spectrum_eq]) continuous_fst hab ha
  case snd =>
    let φ := StarAlgHom.snd S A B
    exact φ.map_cfc f (a, b) (by rwa [Prod.spectrum_eq]) continuous_snd hab hb

end unital_prod
