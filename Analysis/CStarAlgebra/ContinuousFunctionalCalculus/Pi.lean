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

variable {ι R S : Type*} {A : ι → Type*} [CommSemiring R] [Nontrivial R] [StarRing R]
  [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [CommRing S] [Algebra R S]
  [∀ i, NonUnitalRing (A i)] [∀ i, Module S (A i)] [∀ i, Module R (A i)]
  [∀ i, IsScalarTower R S (A i)] [∀ i, SMulCommClass R (A i) (A i)]
  [∀ i, IsScalarTower R (A i) (A i)]
  [∀ i, StarRing (A i)] [∀ i, TopologicalSpace (A i)] {p : (∀ i, A i) → Prop}
  {q : (i : ι) → A i → Prop}
  [NonUnitalContinuousFunctionalCalculus R (∀ i, A i) p]
  [∀ i, NonUnitalContinuousFunctionalCalculus R (A i) (q i)]
  [∀ i, ContinuousMapZero.UniqueHom R (A i)]

include S in
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙ_map_pi (f : R → R) (a : ∀ i, A i)
    (hf : ContinuousOn f (⋃ i, quasispectrum R (a i)) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) (ha' : ∀ i, q i (a i) := by cfc_tac) :
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
  {pab : A × B → Prop} {pa : A → Prop} {pb : B → Prop}
  [NonUnitalContinuousFunctionalCalculus R (A × B) pab]
  [NonUnitalContinuousFunctionalCalculus R A pa]
  [NonUnitalContinuousFunctionalCalculus R B pb]
  [ContinuousMapZero.UniqueHom R A] [ContinuousMapZero.UniqueHom R B]

include S in
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙ_map_prod (f : R → R) (a : A) (b : B)
    (hf : ContinuousOn f (quasispectrum R a ∪ quasispectrum R b) := by cfc_cont_tac)
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

variable {ι R S : Type*} {A : ι → Type*} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [CommRing S] [Algebra R S]
  [∀ i, Ring (A i)] [∀ i, Algebra S (A i)] [∀ i, Algebra R (A i)] [∀ i, IsScalarTower R S (A i)]
  [hinst : IsScalarTower R S (∀ i, A i)]
  [∀ i, StarRing (A i)] [∀ i, TopologicalSpace (A i)] {p : (∀ i, A i) → Prop}
  {q : (i : ι) → A i → Prop}
  [ContinuousFunctionalCalculus R (∀ i, A i) p]
  [∀ i, ContinuousFunctionalCalculus R (A i) (q i)]
  [∀ i, ContinuousMap.UniqueHom R (A i)]

include S in
/-
**cfc_map_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_map_pi (f : R -> R) (a : forall i, A i) (hf : ContinuousOn f (⋃ i, spe
ctrum R (a i))
参数：f : R -> R；a : forall i, A i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `StarAlgHom.map_cfc`：StarAlgHom.map_cfc (φ : A ->⋆ₐ[S] B) (f : R -> R) (a
 : A) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.spectrum_eq`：Pi.spectrum_eq [CommSemiring R] [forall i, Ring (κ i)] [
forall i, Algebra R (κ i)] (a : forall i, κ i) : spectrum R a = ⋃ i, spectrum R 
(a i…
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
lemma cfc_map_pi (f : R → R) (a : ∀ i, A i)
    (hf : ContinuousOn f (⋃ i, spectrum R (a i)) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) (ha' : ∀ i, q i (a i) := by cfc_tac) :
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
  [StarRing A] [StarRing B] [TopologicalSpace A] [TopologicalSpace B] {pab : A × B → Prop}
  {pa : A → Prop} {pb : B → Prop}
  [ContinuousFunctionalCalculus R (A × B) pab]
  [ContinuousFunctionalCalculus R A pa] [ContinuousFunctionalCalculus R B pb]
  [ContinuousMap.UniqueHom R A] [ContinuousMap.UniqueHom R B]

include S in
/-
**cfc_map_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_map_prod (f : R -> R) (a : A) (b : B) (hf : ContinuousOn f (spectrum R
 a union spectrum R b)
参数：f : R -> R；a : A；b : B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用引理 `StarAlgHom.map_cfc`：StarAlgHom.map_cfc (φ : A ->⋆ₐ[S] B) (f : R -> R) (a
 : A) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Prod.spectrum_eq`：Prod.spectrum_eq [CommSemiring R] [Ring A] [Ring B] [A
lgebra R A] [Algebra R B] (a : A) (b : B) : spectrum R (⟨a, b⟩ : A × B) = spectr
um R a…
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
lemma cfc_map_prod (f : R → R) (a : A) (b : B)
    (hf : ContinuousOn f (spectrum R a ∪ spectrum R b) := by cfc_cont_tac)
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

