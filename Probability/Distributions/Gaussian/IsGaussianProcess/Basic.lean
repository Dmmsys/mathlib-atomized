/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Gaussian processes

This file contains basic properties of Gaussian processes. In particular,
in `IsGaussianProcess.of_isGaussianProcess`, we show that if a stochastic
process `Y : S → Ω → F` is such that for each `s : S`, `Y s` can be written as a linear map
applied to finitely many values of a certain Gaussian process,
then `Y` is itself a Gaussian process.

## Main statement

* `IsGaussianProcess.of_isGaussianProcess`: If a stochastic process `Y : S → Ω → F` is such that
  for each `s : S`, `Y s` can be written as a linear map applied to finitely many values
  of a certain Gaussian process, then `Y` is itself a Gaussian process.

## Tags

Gaussian process
-/

public section

open MeasureTheory Finset

namespace ProbabilityTheory.IsGaussianProcess

variable {S T Ω E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T -> Ω -> E}

section Basic

/-! ### Basic facts -/

variable [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module Real E]

/--
lemma `isProbabilityMeasure` / 引理 `isProbabilityMeasure`

English:
lemma isProbabilityMeasure
  given: (hX : IsGaussianProcess X P)
  proof: .isProbabilityMeasure hX.hasGaussianLaw Classical.ofNonempty

中文:
引理 isProbabilityMeasure
  条件: (hX : IsGaussianProcess X P)
  证明: .isProbabilityMeasure hX.hasGaussianLaw Classical.ofNonempty

Depends on / 依赖: Classical, Classical.ofNonempty, hX.hasGaussianLaw, hasGaussianLaw, isProbabilityMeasure, ofNonempty
-/
lemma isProbabilityMeasure (hX : IsGaussianProcess X P) :
    IsProbabilityMeasure P :=
.isProbabilityMeasure hX.hasGaussianLaw Classical.ofNonempty

/--
lemma `aemeasurable` / 引理 `aemeasurable`

English:
lemma aemeasurable
  given: (hX : IsGaussianProcess X P) (t : T)
  statement: AEMeasurable (X t) P
  proof: AEMeasurable.of_map_ne_zero
.eval ⟨t, by simp⟩ (hX.hasGaussianLaw {t}).isGaussian_map.toIsProbabilityMeasure.ne_zero

中文:
引理 aemeasurable
  条件: (hX : IsGaussianProcess X P) (t : T)
  结论: 几乎处处可测 (X t) P
  证明: AEMeasurable.of_map_ne_zero
.eval ⟨t, by simp⟩ (hX.hasGaussianLaw {t}).isGaussian_map.toIsProbabilityMeasure.ne_zero

Depends on / 依赖: AEMeasurable, AEMeasurable.of_map_ne_zero, hX.hasGaussianLaw, hasGaussianLaw, isGaussian_map, isGaussian_map.toIsProbabilityMeasure.ne_zero, ne_zero, of_map_ne_zero, toIsProbabilityMeasure
-/
lemma aemeasurable (hX : IsGaussianProcess X P) (t : T) : AEMeasurable (X t) P :=
  AEMeasurable.of_map_ne_zero
.eval ⟨t, by simp⟩ (hX.hasGaussianLaw {t}).isGaussian_map.toIsProbabilityMeasure.ne_zero

set_option backward.isDefEq.respectTransparency false in
/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  given: (hX : IsGaussianProcess X P) (hXY : forall t, X t =ᵐ[P] Y t)
  proof: by
    constructor
    rw [map_restrict_eq_of_forall_ae_eq fun t => (hXY t).symm]
    exact (hX.hasGaussianLaw I).isGaussian_map

中文:
引理 congr
  条件: (hX : IsGaussianProcess X P) (hXY : 对任意 t, X t =ᵐ[P] Y t)
  证明: by
    constructor
    rw [map_restrict_eq_of_forall_ae_eq fun t => (hXY t).symm]
    exact (hX.hasGaussianLaw I).isGaussian_map

Depends on / 依赖: hX.hasGaussianLaw, hasGaussianLaw, isGaussian_map, map_restrict_eq_of_forall_ae_eq
-/
lemma congr (hX : IsGaussianProcess X P) (hXY : forall t, X t =ᵐ[P] Y t) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    constructor
    rw [map_restrict_eq_of_forall_ae_eq fun t => (hXY t).symm]
    exact (hX.hasGaussianLaw I).isGaussian_map

end Basic

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

section Maps

/-! ### Gaussian Marginals -/

variable [NormedSpace Real E]

/--
lemma `hasGaussianLaw_eval` / 引理 `hasGaussianLaw_eval`

English:
lemma hasGaussianLaw_eval
  given: (hX : IsGaussianProcess X P) (t : T)
  statement: HasGaussianLaw (X t) P
  proof: by
  -- removing `by exact` fails
  exact (hX.hasGaussianLaw {t}).map (.proj ⟨t, by simp⟩)

中文:
引理 hasGaussianLaw_eval
  条件: (hX : IsGaussianProcess X P) (t : T)
  结论: HasGaussianLaw (X t) P
  证明: by
  -- removing `by exact` fails
  exact (hX.hasGaussianLaw {t}).map (.proj ⟨t, by simp⟩)
-/
lemma hasGaussianLaw_eval (hX : IsGaussianProcess X P) (t : T) : HasGaussianLaw (X t) P := by
  -- removing `by exact` fails
  exact (hX.hasGaussianLaw {t}).map (.proj ⟨t, by simp⟩)

variable [SecondCountableTopology E]

/--
lemma `hasGaussianLaw_prodMk` / 引理 `hasGaussianLaw_prodMk`

English:
lemma hasGaussianLaw_prodMk
  given: (hX : IsGaussianProcess X P) {s t : T}
  proof: by
  classical
  exact (hX.hasGaussianLaw {s, t}).prodMk ⟨s, by simp⟩ ⟨t, by simp⟩

中文:
引理 hasGaussianLaw_prodMk
  条件: (hX : IsGaussianProcess X P) {s t : T}
  证明: by
  classical
  exact (hX.hasGaussianLaw {s, t}).prodMk ⟨s, by simp⟩ ⟨t, by simp⟩

Depends on / 依赖: classical, hX.hasGaussianLaw, hasGaussianLaw, prodMk
-/
lemma hasGaussianLaw_prodMk (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (fun ω => (X s ω, X t ω)) P := by
  classical
  exact (hX.hasGaussianLaw {s, t}).prodMk ⟨s, by simp⟩ ⟨t, by simp⟩

/--
lemma `hasGaussianLaw_add` / 引理 `hasGaussianLaw_add`

English:
lemma hasGaussianLaw_add
  given: (hX : IsGaussianProcess X P) {s t : T}
  proof: hX.hasGaussianLaw_prodMk.add

中文:
引理 hasGaussianLaw_add
  条件: (hX : IsGaussianProcess X P) {s t : T}
  证明: hX.hasGaussianLaw_prodMk.add

Depends on / 依赖: hX.hasGaussianLaw_prodMk.add, hasGaussianLaw_prodMk
-/
lemma hasGaussianLaw_add (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (X s + X t) P := hX.hasGaussianLaw_prodMk.add

/--
lemma `hasGaussianLaw_fun_add` / 引理 `hasGaussianLaw_fun_add`

English:
lemma hasGaussianLaw_fun_add
  given: (hX : IsGaussianProcess X P) {s t : T}
  proof: hX.hasGaussianLaw_add

中文:
引理 hasGaussianLaw_fun_add
  条件: (hX : IsGaussianProcess X P) {s t : T}
  证明: hX.hasGaussianLaw_add

Depends on / 依赖: hX.hasGaussianLaw_add, hasGaussianLaw_add
-/
lemma hasGaussianLaw_fun_add (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (fun ω => X s ω + X t ω) P := hX.hasGaussianLaw_add

/--
lemma `hasGaussianLaw_sub` / 引理 `hasGaussianLaw_sub`

English:
lemma hasGaussianLaw_sub
  given: (hX : IsGaussianProcess X P) {s t : T}
  proof: hX.hasGaussianLaw_prodMk.sub

中文:
引理 hasGaussianLaw_sub
  条件: (hX : IsGaussianProcess X P) {s t : T}
  证明: hX.hasGaussianLaw_prodMk.sub

Depends on / 依赖: hX.hasGaussianLaw_prodMk.sub, hasGaussianLaw_prodMk
-/
lemma hasGaussianLaw_sub (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (X s - X t) P := hX.hasGaussianLaw_prodMk.sub

/--
lemma `hasGaussianLaw_fun_sub` / 引理 `hasGaussianLaw_fun_sub`

English:
lemma hasGaussianLaw_fun_sub
  given: (hX : IsGaussianProcess X P) {s t : T}
  proof: hX.hasGaussianLaw_sub

中文:
引理 hasGaussianLaw_fun_sub
  条件: (hX : IsGaussianProcess X P) {s t : T}
  证明: hX.hasGaussianLaw_sub

Depends on / 依赖: hX.hasGaussianLaw_sub, hasGaussianLaw_sub
-/
lemma hasGaussianLaw_fun_sub (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (fun ω => X s ω - X t ω) P := hX.hasGaussianLaw_sub

/--
lemma `hasGaussianLaw_sum` / 引理 `hasGaussianLaw_sum`

English:
lemma hasGaussianLaw_sum
  given: (hX : IsGaussianProcess X P) {I : Finset T}
  proof: by
  convert! (hX.hasGaussianLaw I).sum
  simp [I.sum_attach X]

中文:
引理 hasGaussianLaw_sum
  条件: (hX : IsGaussianProcess X P) {I : 有限集 T}
  证明: by
  convert! (hX.hasGaussianLaw I).sum
  simp [I.sum_attach X]

Depends on / 依赖: I.sum_attach, convert, hX.hasGaussianLaw, hasGaussianLaw, sum_attach
-/
lemma hasGaussianLaw_sum (hX : IsGaussianProcess X P) {I : Finset T} :
    HasGaussianLaw (∑ i in I, X i) P := by
  convert! (hX.hasGaussianLaw I).sum
  simp [I.sum_attach X]

/--
lemma `hasGaussianLaw_fun_sum` / 引理 `hasGaussianLaw_fun_sum`

English:
lemma hasGaussianLaw_fun_sum
  given: (hX : IsGaussianProcess X P) {I : Finset T}
  proof: by
  convert! hX.hasGaussianLaw_sum (I := I)
  simp

中文:
引理 hasGaussianLaw_fun_sum
  条件: (hX : IsGaussianProcess X P) {I : 有限集 T}
  证明: by
  convert! hX.hasGaussianLaw_sum (I := I)
  simp

Depends on / 依赖: convert, hX.hasGaussianLaw_sum, hasGaussianLaw_sum
-/
lemma hasGaussianLaw_fun_sum (hX : IsGaussianProcess X P) {I : Finset T} :
    HasGaussianLaw (fun ω => ∑ i in I, X i ω) P := by
  convert! hX.hasGaussianLaw_sum (I := I)
  simp

/--
lemma `hasGaussianLaw_increments` / 引理 `hasGaussianLaw_increments`

English:
lemma hasGaussianLaw_increments
  given: (hX : IsGaussianProcess X P) {n : Nat} {t : Fin (n + 1) -> T}
  proof: by
  classical
  let L : ((univ.image t) -> E) ->L[Real] Fin n -> E :=
    { toFun x i := x ⟨t i.succ, by simp⟩ - x ⟨t i.castSucc, by simp⟩
      map_add' x y := by ext; simp; abel
      map_smul' m x := by ext; simp; module }
  exact (hX.hasGaussianLaw _).map L

中文:
引理 hasGaussianLaw_increments
  条件: (hX : IsGaussianProcess X P) {n : 自然数} {t : 有限集 (n + 1) -> T}
  证明: by
  classical
  let L : ((univ.image t) -> E) ->L[Real] Fin n -> E :=
    { toFun x i := x ⟨t i.succ, by simp⟩ - x ⟨t i.castSucc, by simp⟩
      map_add' x y := by ext; simp; abel
      map_smul' m x := by ext; simp; module }
  exact (hX.hasGaussianLaw _).map L

Depends on / 依赖: castSucc, classical, hX.hasGaussianLaw, hasGaussianLaw, i.castSucc, i.succ, map_add, map_smul, module, univ.image
-/
lemma hasGaussianLaw_increments (hX : IsGaussianProcess X P) {n : Nat} {t : Fin (n + 1) -> T} :
    HasGaussianLaw (fun ω (i : Fin n) => X (t i.succ) ω - X (t i.castSucc) ω) P := by
  classical
  let L : ((univ.image t) -> E) ->L[Real] Fin n -> E :=
    { toFun x i := x ⟨t i.succ, by simp⟩ - x ⟨t i.castSucc, by simp⟩
      map_add' x y := by ext; simp; abel
      map_smul' m x := by ext; simp; module }
  exact (hX.hasGaussianLaw _).map L

end Maps

section Transformations

/-! ### Operations that preserve Gaussianity -/

variable [NormedSpace Real E] [SecondCountableTopology E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [MeasurableSpace F]
  [BorelSpace F] [SecondCountableTopology F] {Y : S -> Ω -> F}

/--
lemma `of_isGaussianProcess` / 引理 `of_isGaussianProcess`

English:
lemma of_isGaussianProcess
  statement: (hX : IsGaussianProcess X P)
  proof: by
    choose J L hL using h
    classical
    let K : (I.biUnion J -> E) ->L[Real] I -> F :=
      { toFun x s := L s (fun t => x ⟨t.1, mem_biUnion.2 ⟨s.1, s.2, t.2⟩⟩)
        map_add' x y := by ext; simp [← Pi.add_def]
        map_smul' c x := by ext; simp [← Pi.smul_def] }
    have : (fun ω => I.restrict (Y · ω)) = K ∘ (fun ω => (I.biUnion J).restrict (X · ω)) := by
      ext; simp [K, hL, Finset.restrict_def]
    rw [this]
    exact (hX.hasGaussianLaw _).map _

中文:
引理 of_isGaussianProcess
  结论: (hX : IsGaussianProcess X P)
  证明: by
    choose J L hL using h
    classical
    let K : (I.biUnion J -> E) ->L[Real] I -> F :=
      { toFun x s := L s (fun t => x ⟨t.1, mem_biUnion.2 ⟨s.1, s.2, t.2⟩⟩)
        map_add' x y := by ext; simp [← Pi.add_def]
        map_smul' c x := by ext; simp [← Pi.smul_def] }
    have : (fun ω => I.restrict (Y · ω)) = K ∘ (fun ω => (I.biUnion J).restrict (X · ω)) := by
      ext; simp [K, hL, Finset.restrict_def]
    rw [this]
    exact (hX.hasGaussianLaw _).map _

Depends on / 依赖: Finset, Finset.restrict_def, I.biUnion, I.restrict, Pi.add_def, Pi.smul_def, add_def, biUnion, classical, hX.hasGaussianLaw, hasGaussianLaw, map_add, map_smul, mem_biUnion, restrict, restrict_def, smul_def
-/
lemma of_isGaussianProcess (hX : IsGaussianProcess X P)
    (h : forall s, exists I : Finset T, exists L : (I -> E) ->L[Real] F, forall ω, Y s ω = L (I.restrict (X · ω))) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    choose J L hL using h
    classical
    let K : (I.biUnion J -> E) ->L[Real] I -> F :=
      { toFun x s := L s (fun t => x ⟨t.1, mem_biUnion.2 ⟨s.1, s.2, t.2⟩⟩)
        map_add' x y := by ext; simp [← Pi.add_def]
        map_smul' c x := by ext; simp [← Pi.smul_def] }
    have : (fun ω => I.restrict (Y · ω)) = K ∘ (fun ω => (I.biUnion J).restrict (X · ω)) := by
      ext; simp [K, hL, Finset.restrict_def]
    rw [this]
    exact (hX.hasGaussianLaw _).map _

/--
lemma `comp_right` / 引理 `comp_right`

English:
lemma comp_right
  given: (h : IsGaussianProcess X P) (f : S -> T)
  statement: IsGaussianProcess (X ∘ f) P
  proof: h.of_isGaussianProcess fun s => ⟨{f s},
    { toFun x := x ⟨f s, by simp⟩
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

中文:
引理 comp_right
  条件: (h : IsGaussianProcess X P) (f : S -> T)
  结论: IsGaussianProcess (X ∘ f) P
  证明: h.of_isGaussianProcess fun s => ⟨{f s},
    { toFun x := x ⟨f s, by simp⟩
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

Depends on / 依赖: h.of_isGaussianProcess, map_add, map_smul, of_isGaussianProcess
-/
lemma comp_right (h : IsGaussianProcess X P) (f : S -> T) : IsGaussianProcess (X ∘ f) P :=
  h.of_isGaussianProcess fun s => ⟨{f s},
    { toFun x := x ⟨f s, by simp⟩
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

/--
lemma `comp_left` / 引理 `comp_left`

English:
lemma comp_left
  given: (L : T -> E ->L[Real] F) (h : IsGaussianProcess X P)
  proof: h.of_isGaussianProcess fun t => ⟨{t},
    { toFun x := L t (x ⟨t, by simp⟩),
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

中文:
引理 comp_left
  条件: (L : T -> E ->L[实数] F) (h : IsGaussianProcess X P)
  证明: h.of_isGaussianProcess fun t => ⟨{t},
    { toFun x := L t (x ⟨t, by simp⟩),
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

Depends on / 依赖: h.of_isGaussianProcess, map_add, map_smul, of_isGaussianProcess
-/
lemma comp_left (L : T -> E ->L[Real] F) (h : IsGaussianProcess X P) :
    IsGaussianProcess (fun t ω => L t (X t ω)) P :=
  h.of_isGaussianProcess fun t => ⟨{t},
    { toFun x := L t (x ⟨t, by simp⟩),
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  given: (c : T -> Real) (hX : IsGaussianProcess X P)
  proof: hX.comp_left (fun t => .lsmul Real Real (c t))

中文:
引理 smul
  条件: (c : T -> 实数) (hX : IsGaussianProcess X P)
  证明: hX.comp_left (fun t => .lsmul Real Real (c t))

Depends on / 依赖: comp_left, hX.comp_left
-/
lemma smul (c : T -> Real) (hX : IsGaussianProcess X P) :
    IsGaussianProcess (fun t ω => c t • (X t ω)) P :=
  hX.comp_left (fun t => .lsmul Real Real (c t))

/--
lemma `shift` / 引理 `shift`

English:
lemma shift
  given: [Add T] (h : IsGaussianProcess X P) (t₀ : T)
  proof: by
  classical
  exact h.of_isGaussianProcess fun t => ⟨{t₀, t₀ + t},
    { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
      map_add' x y := by simp; abel
      map_smul' c x := by simp; module },
    by simp⟩

中文:
引理 shift
  条件: [加法 T] (h : IsGaussianProcess X P) (t₀ : T)
  证明: by
  classical
  exact h.of_isGaussianProcess fun t => ⟨{t₀, t₀ + t},
    { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
      map_add' x y := by simp; abel
      map_smul' c x := by simp; module },
    by simp⟩

Depends on / 依赖: classical, h.of_isGaussianProcess, map_add, map_smul, module, of_isGaussianProcess
-/
lemma shift [Add T] (h : IsGaussianProcess X P) (t₀ : T) :
    IsGaussianProcess (fun t ω => X (t₀ + t) ω - X t₀ ω) P := by
  classical
  exact h.of_isGaussianProcess fun t => ⟨{t₀, t₀ + t},
    { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
      map_add' x y := by simp; abel
      map_smul' c x := by simp; module },
    by simp⟩

/--
lemma `restrict` / 引理 `restrict`

English:
lemma restrict
  given: (h : IsGaussianProcess X P) (s : Set T)
  proof: h.comp_right Subtype.val

中文:
引理 restrict
  条件: (h : IsGaussianProcess X P) (s : 集合 T)
  证明: h.comp_right Subtype.val

Depends on / 依赖: Subtype, Subtype.val, comp_right, h.comp_right
-/
lemma restrict (h : IsGaussianProcess X P) (s : Set T) :
    IsGaussianProcess (fun t : s => X t) P :=
  h.comp_right Subtype.val

end Transformations

end ProbabilityTheory.IsGaussianProcess
