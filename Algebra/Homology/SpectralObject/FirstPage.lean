/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The first page of the spectral sequence of a spectral object

Let `ι` be a preordered type, `X` a spectral object in an abelian
category indexed by `ι`. Let `data : SpectralSequenceDataCore ι c r₀`.
Assume that `X.HasSpectralSequence data` holds. In this file,
we introduce a property `data.HasFirstPageComputation` which allows
to "compute" the objects of the `r₀`th page of the spectral
sequence attached to `X` in terms of objects of the form `X.H`,
and we compute the differential on the first page in terms of `X.δ`,
see `spectralSequence_first_page_d_eq`.

-/

@[expose] public section

namespace CategoryTheory

open Category ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : Int -> ComplexShape κ} {r₀ : Int}
  (data : SpectralSequenceDataCore ι c r₀)

namespace SpectralSequenceDataCore

/--
Definition of `HasFirstPageComputation` / `HasFirstPageComputation` 的定义

English:
class HasFirstPageComputation
  parameters: : Prop where
  axioms and operations (2):
    - hi₀₁((pq : κ)) : data.i₀ r₀ pq = data.i₁ pq
    - hi₂₃((pq : κ)) : data.i₂ pq = data.i₃ r₀ pq

中文:
类 有FirstPageComputation
  参数: : 命题 where
  公理与运算 (2 个):
    - hi₀₁((pq : κ)) : data.i₀ r₀ pq = data.i₁ pq
    - hi₂₃((pq : κ)) : data.i₂ pq = data.i₃ r₀ pq
-/
class HasFirstPageComputation : Prop where
  hi₀₁ (pq : κ) : data.i₀ r₀ pq = data.i₁ pq
  hi₂₃ (pq : κ) : data.i₂ pq = data.i₃ r₀ pq

export HasFirstPageComputation (hi₀₁ hi₂₃)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: coreE₂Cohomological.HasFirstPageComputation
  body: by dsimp; lia
  hi₂₃ pq := by dsimp; lia

中文:
实例 :
  签名: coreE₂Cohomological.有FirstPageComputation
  定义体: by dsimp; lia
  hi₂₃ pq := by dsimp; lia
-/
instance : coreE₂Cohomological.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; lia
  hi₂₃ pq := by dsimp; lia

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: coreE₂CohomologicalNat.HasFirstPageComputation
  body: by dsimp; lia
  hi₂₃ pq := by dsimp; lia

中文:
实例 :
  签名: coreE₂Cohomological自然数.有FirstPageComputation
  定义体: by dsimp; lia
  hi₂₃ pq := by dsimp; lia
-/
instance : coreE₂CohomologicalNat.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; lia
  hi₂₃ pq := by dsimp; lia

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: coreE₂HomologicalNat.HasFirstPageComputation
  body: by dsimp; lia
  hi₂₃ pq := by dsimp; lia

中文:
实例 :
  签名: coreE₂Homological自然数.有FirstPageComputation
  定义体: by dsimp; lia
  hi₂₃ pq := by dsimp; lia
-/
instance : coreE₂HomologicalNat.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; lia
  hi₂₃ pq := by dsimp; lia

end SpectralSequenceDataCore

variable [data.HasFirstPageComputation] [X.HasSpectralSequence data]

/--
Definition of `spectralSequenceFirstPageXIso` / `spectralSequenceFirstPageXIso` 的定义

English:
definition spectralSequenceFirstPageXIso
  signature: (pq : κ)
  body: X.spectralSequencePageXIso data _ (by rfl) _ _ _ _ _
    (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn ≪≫
      X.EIsoH (homOfLE _) (n - 1) n (n + 1)

@[reassoc]

中文:
定义 spectralSequenceFirstPageXIso
  签名: (pq : κ)
  定义体: X.spectralSequencePageXIso data _ (by rfl) _ _ _ _ _
    (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn ≪≫
      X.EIsoH (homOfLE _) (n - 1) n (n + 1)

@[reassoc]

Depends on / 依赖: X.EIsoH, X.spectralSequencePageXIso, data.hi, homOfLE, spectralSequencePageXIso
-/
noncomputable def spectralSequenceFirstPageXIso (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n : Int) (hn : n = data.deg pq) :
    ((X.spectralSequence data).page r₀).X pq ≅
      (X.H n).obj (mk₁ (homOfLE (data.le₁₂' pq hi₁ hi₂))) :=
  X.spectralSequencePageXIso data _ (by rfl) _ _ _ _ _
    (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn ≪≫
      X.EIsoH (homOfLE _) (n - 1) n (n + 1)

@[reassoc]
/--
lemma `spectralSequenceFirstPageXIso_hom` / 引理 `spectralSequenceFirstPageXIso_hom`

English:
lemma spectralSequenceFirstPageXIso_hom
  statement: (pq : κ)
  proof: by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl := hn₂
  rfl

@[reassoc]

中文:
引理 spectralSequenceFirstPageXIso_hom
  结论: (pq : κ)
  证明: by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl := hn₂
  rfl

@[reassoc]

Depends on / 依赖: X.EIsoH, X.spectralSequenceFirstPageXIso, X.spectralSequencePageXIso, data.hi, spectralSequenceFirstPageXIso, spectralSequencePageXIso
-/
lemma spectralSequenceFirstPageXIso_hom (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n₀ n₁ n₂ : Int) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n₁ hn₁').hom =
      (X.spectralSequencePageXIso data r₀ (by rfl) _ _ _ _ _
        (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn₁').hom ≫
          (X.EIsoH _ n₀ n₁ n₂ hn₁ hn₂).hom := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl := hn₂
  rfl

@[reassoc]
/--
lemma `spectralSequenceFirstPageXIso_inv` / 引理 `spectralSequenceFirstPageXIso_inv`

English:
lemma spectralSequenceFirstPageXIso_inv
  statement: (pq : κ)
  proof: by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl := hn₂
  rfl

@[reassoc]

中文:
引理 spectralSequenceFirstPageXIso_inv
  结论: (pq : κ)
  证明: by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl := hn₂
  rfl

@[reassoc]

Depends on / 依赖: X.EIsoH, X.spectralSequenceFirstPageXIso, X.spectralSequencePageXIso, data.hi, spectralSequenceFirstPageXIso, spectralSequencePageXIso
-/
lemma spectralSequenceFirstPageXIso_inv (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n₀ n₁ n₂ : Int) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n₁ hn₁').inv =
      (X.EIsoH _ n₀ n₁ n₂ hn₁ hn₂).inv ≫
      (X.spectralSequencePageXIso data r₀ (by rfl) _ _ _ _ _
        (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn₁').inv := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl := hn₂
  rfl

@[reassoc]
/--
lemma `spectralSequence_first_page_d_eq` / 引理 `spectralSequence_first_page_d_eq`

English:
lemma spectralSequence_first_page_d_eq
  statement: (pq pq' : κ)
  proof: by
  simpa [X.spectralSequenceFirstPageXIso_hom data pq j k hj hk (n - 1) n n',
    ← X.d_EIsoH_hom_assoc _ _ (n - 1) n n' (n' + 1),
    X.spectralSequenceFirstPageXIso_inv data pq' i j hi _ _ n' _ _ hn' _]
    using spectralSequence_page_d_eq _ _ _ _ _ _ hpq ..

中文:
引理 spectralSequence_first_page_d_eq
  结论: (pq pq' : κ)
  证明: by
  simpa [X.spectralSequenceFirstPageXIso_hom data pq j k hj hk (n - 1) n n',
    ← X.d_EIsoH_hom_assoc _ _ (n - 1) n n' (n' + 1),
    X.spectralSequenceFirstPageXIso_inv data pq' i j hi _ _ n' _ _ hn' _]
    using spectralSequence_page_d_eq _ _ _ _ _ _ hpq ..

Depends on / 依赖: X.spectralSequence, X.spectralSequenceFirstPageXIso, X.spectralSequenceFirstPageXIso_hom, data.hc, data.hi, data.le, homOfLE, spectralSequence, spectralSequenceFirstPageXIso, spectralSequenceFirstPageXIso_hom
-/
lemma spectralSequence_first_page_d_eq (pq pq' : κ)
    (hpq : (c r₀).Rel pq pq') (i j k : ι)
    (hi : i = data.i₁ pq') (hj : j = data.i₁ pq) (hk : k = data.i₂ pq)
    (n n' : Int) (hn : n = data.deg pq) (hn' : n + 1 = n' := by lia) :
    ((X.spectralSequence data).page r₀).d pq pq' =
      (X.spectralSequenceFirstPageXIso data pq j k hj hk n hn).hom ≫
      X.δ
        (homOfLE
          (by simpa only [hi, hj, data.hc₁₃ r₀ pq pq' hpq, ← data.hi₂₃ pq']
            using data.le₁₂ pq'))
        (homOfLE (by simpa only [hj, hk] using data.le₁₂ pq)) n n' hn' ≫
      (X.spectralSequenceFirstPageXIso data pq' i j hi
        (by rw [hj, ← data.hc₀₂ r₀ pq pq' hpq, data.hi₀₁ pq]) n'
        (by rw [← hn', hn, data.hc r₀ pq pq' hpq])).inv := by
  simpa [X.spectralSequenceFirstPageXIso_hom data pq j k hj hk (n - 1) n n',
    ← X.d_EIsoH_hom_assoc _ _ (n - 1) n n' (n' + 1),
    X.spectralSequenceFirstPageXIso_inv data pq' i j hi _ _ n' _ _ hn' _]
    using spectralSequence_page_d_eq _ _ _ _ _ _ hpq ..

end SpectralObject

end Abelian

end CategoryTheory
