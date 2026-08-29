/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Algebra.Homology.SpectralSequence.ComplexShape
public import Mathlib.Order.Fin.Clamp
public import Mathlib.Order.WithBotTop

/-!
# Shapes of spectral sequences obtained from a spectral object

This file prepares for the construction of the spectral sequence
of a spectral object in an abelian category which shall be conducted
in the file `Mathlib/Algebra/Homology/SpectralObject/SpectralSequence.lean`.

In this file, we introduce a structure `SpectralSequenceDataCore` which
contains a recipe for the construction of the pages of the spectral sequence.
For example, from a spectral object `X` indexed by `EInt` the definition
`coreE₂Cohomological` will allow to construct an `E₂` cohomological
spectral sequence such that the object on position `(p, q)` on the `r`th
page is `E^{p + q}(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)`.
The data (and properties) in the structure `SpectralSequenceDataCore` allow
to define the pages and the differentials directly from the `SpectralObject`
API from the files
`Mathlib/Algebra/Homology/SpectralObject/Page.lean` and
`Mathlib/Algebra/Homology/SpectralObject/Differentials.lean`.
However, the computation of the homology of the differentials in
`Mathlib/Algebra/Homology/SpectralObject/Homology.lean` may not directly
apply: we introduce a typeclass `HasSpectralSequence` which puts
additional conditions on the spectral object so that the homology of a
page identifies to the next page. These conditions are automatically
satisfied for `coreE₂Cohomological`, but this design allows
to obtain a spectral sequence with objects of the pages indexed
by `ℕ × ℕ` instead of `ℤ × ℤ` when suitable conditions are satisfied by
a spectral object indexed by `EInt` (see `coreE₂CohomologicalNat`
and the typeclass `IsFirstQuadrant`).

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : Int -> ComplexShape κ} {r₀ : Int}

variable (ι c r₀) in
/--
Definition of `SpectralSequenceDataCore` / `SpectralSequenceDataCore` 的定义

English:
structure SpectralSequenceDataCore
  parameters: where
  axioms and operations (15):
    - deg : κ -> Int
    - i₀((r : Int) (pq : κ) (hr : r₀ <= r := by lia)) : ι
    - i₁((pq : κ)) : ι
    - i₂((pq : κ)) : ι
    - i₃((r : Int) (pq : κ) (hr : r₀ <= r := by lia)) : ι
    - le₀₁((r : Int) (pq : κ) (hr : r₀ <= r := by lia)) : i₀ r pq <= i₁ pq
    - le₁₂((pq : κ)) : i₁ pq <= i₂ pq
    - le₂₃((r : Int) (pq : κ) (hr : r₀ <= r := by lia)) : i₂ pq <= i₃ r pq
    - hc((r : Int) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hr : r₀ <= r := by lia)) : deg pq + 1 = deg pq'
    - hc₀₂((r : Int) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hr : r₀ <= r := by lia)) : i₀ r pq = i₂ pq'
    - hc₁₃((r : Int) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hr : r₀ <= r := by lia)) : i₁ pq = i₃ r pq'
    - antitone_i₀((r r' : Int) (pq : κ) (hr : r₀ <= r := by lia) (hrr' : r <= r' := by lia)) : i₀ r' pq <= i₀ r pq
    - monotone_i₃((r r' : Int) (pq : κ) (hr : r₀ <= r := by lia) (hrr' : r <= r' := by lia)) : i₃ r pq <= i₃ r' pq
    - i₀_prev((r r' : Int) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)) : i₀ r' pq = i₁ pq'
    - i₃_next((r r' : Int) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)) : i₃ r' pq' = i₂ pq

中文:
结构 SpectralSequenceDataCore
  参数: where
  公理与运算 (15 个):
    - deg : κ -> 整数
    - i₀((r : 整数) (pq : κ) (hr : r₀ <= r := by lia)) : ι
    - i₁((pq : κ)) : ι
    - i₂((pq : κ)) : ι
    - i₃((r : 整数) (pq : κ) (hr : r₀ <= r := by lia)) : ι
    - le₀₁((r : 整数) (pq : κ) (hr : r₀ <= r := by lia)) : i₀ r pq <= i₁ pq
    - le₁₂((pq : κ)) : i₁ pq <= i₂ pq
    - le₂₃((r : 整数) (pq : κ) (hr : r₀ <= r := by lia)) : i₂ pq <= i₃ r pq
    - hc((r : 整数) (pq pq' : κ) (hpq : (c r).关系 pq pq') (hr : r₀ <= r := by lia)) : deg pq + 1 = deg pq'
    - hc₀₂((r : 整数) (pq pq' : κ) (hpq : (c r).关系 pq pq') (hr : r₀ <= r := by lia)) : i₀ r pq = i₂ pq'
    - hc₁₃((r : 整数) (pq pq' : κ) (hpq : (c r).关系 pq pq') (hr : r₀ <= r := by lia)) : i₁ pq = i₃ r pq'
    - antitone_i₀((r r' : 整数) (pq : κ) (hr : r₀ <= r := by lia) (hrr' : r <= r' := by lia)) : i₀ r' pq <= i₀ r pq
    - monotone_i₃((r r' : 整数) (pq : κ) (hr : r₀ <= r := by lia) (hrr' : r <= r' := by lia)) : i₃ r pq <= i₃ r' pq
    - i₀_prev((r r' : 整数) (pq pq' : κ) (hpq : (c r).关系 pq pq') (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)) : i₀ r' pq = i₁ pq'
    - i₃_next((r r' : 整数) (pq pq' : κ) (hpq : (c r).关系 pq pq') (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)) : i₃ r' pq' = i₂ pq
-/
structure SpectralSequenceDataCore where
  /-- The cohomological degree of objects in the pages -/
  deg : κ -> Int
  /-- The zeroth index -/
  i₀ (r : Int) (pq : κ) (hr : r₀ <= r := by lia) : ι
  /-- The first index -/
  i₁ (pq : κ) : ι
  /-- The second index -/
  i₂ (pq : κ) : ι
  /-- The third index -/
  i₃ (r : Int) (pq : κ) (hr : r₀ <= r := by lia) : ι
  le₀₁ (r : Int) (pq : κ) (hr : r₀ <= r := by lia) : i₀ r pq <= i₁ pq
  le₁₂ (pq : κ) : i₁ pq <= i₂ pq
  le₂₃ (r : Int) (pq : κ) (hr : r₀ <= r := by lia) : i₂ pq <= i₃ r pq
  hc (r : Int) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hr : r₀ <= r := by lia) : deg pq + 1 = deg pq'
  hc₀₂ (r : Int) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hr : r₀ <= r := by lia) : i₀ r pq = i₂ pq'
  hc₁₃ (r : Int) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hr : r₀ <= r := by lia) : i₁ pq = i₃ r pq'
  antitone_i₀ (r r' : Int) (pq : κ) (hr : r₀ <= r := by lia) (hrr' : r <= r' := by lia) :
      i₀ r' pq <= i₀ r pq
  monotone_i₃ (r r' : Int) (pq : κ) (hr : r₀ <= r := by lia) (hrr' : r <= r' := by lia) :
      i₃ r pq <= i₃ r' pq
  i₀_prev (r r' : Int) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hrr' : r + 1 = r' := by lia)
      (hr : r₀ <= r := by lia) :
      i₀ r' pq = i₁ pq'
  i₃_next (r r' : Int) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hrr' : r + 1 = r' := by lia)
      (hr : r₀ <= r := by lia) :
      i₃ r' pq' = i₂ pq

namespace SpectralSequenceDataCore

variable (data : SpectralSequenceDataCore ι c r₀)

/--
lemma `i₀_le` / 引理 `i₀_le`

English:
lemma i₀_le
  given: (r r' : Int) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)
  proof: data.antitone_i₀ r r' pq

中文:
引理 i₀_le
  条件: (r r' : 整数) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)
  证明: data.antitone_i₀ r r' pq

Depends on / 依赖: data.antitone_i, data.i
-/
lemma i₀_le (r r' : Int) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia) :
    data.i₀ r' pq <= data.i₀ r pq :=
  data.antitone_i₀ r r' pq

/--
lemma `i₃_le` / 引理 `i₃_le`

English:
lemma i₃_le
  given: (r r' : Int) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)
  proof: data.monotone_i₃ r r' pq

中文:
引理 i₃_le
  条件: (r r' : 整数) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)
  证明: data.monotone_i₃ r r' pq

Depends on / 依赖: data.i, data.monotone_i
-/
lemma i₃_le (r r' : Int) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia) :
    data.i₃ r pq <= data.i₃ r' pq :=
  data.monotone_i₃ r r' pq

/--
lemma `i₀_le'` / 引理 `i₀_le'`

English:
lemma i₀_le'
  statement: {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ)
  proof: by
  rw [hi₀']; rw [hi₀]
  exact data.antitone_i₀ r r' pq'

中文:
引理 i₀_le'
  结论: {r r' : 整数} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ)
  证明: by
  rw [hi₀']; rw [hi₀]
  exact data.antitone_i₀ r r' pq'

Depends on / 依赖: data.antitone_i
-/
lemma i₀_le' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ)
    {i₀' i₀ : ι} (hi₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq') :
    i₀' <= i₀ := by
  rw [hi₀']; rw [hi₀]
  exact data.antitone_i₀ r r' pq'

/--
lemma `le₀₁'` / 引理 `le₀₁'`

English:
lemma le₀₁'
  statement: (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι}
  proof: by
  have := data.le₀₁ r pq'
  simpa only [hi₀, hi₁] using data.le₀₁ r pq'

中文:
引理 le₀₁'
  结论: (r : 整数) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι}
  证明: by
  have := data.le₀₁ r pq'
  simpa only [hi₀, hi₁] using data.le₀₁ r pq'

Depends on / 依赖: data.le
-/
lemma le₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι}
    (hi₀ : i₀ = data.i₀ r pq')
    (hi₁ : i₁ = data.i₁ pq') :
    i₀ <= i₁ := by
  have := data.le₀₁ r pq'
  simpa only [hi₀, hi₁] using data.le₀₁ r pq'

/--
lemma `le₁₂'` / 引理 `le₁₂'`

English:
lemma le₁₂'
  given: (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq')
  proof: by
  simpa only [hi₁, hi₂] using data.le₁₂ pq'

中文:
引理 le₁₂'
  条件: (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq')
  证明: by
  simpa only [hi₁, hi₂] using data.le₁₂ pq'

Depends on / 依赖: data.le
-/
lemma le₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') :
    i₁ <= i₂ := by
  simpa only [hi₁, hi₂] using data.le₁₂ pq'

/--
lemma `le₂₃'` / 引理 `le₂₃'`

English:
lemma le₂₃'
  statement: (r : Int) (hr : r₀ <= r) (pq' : κ)
  proof: by
  simpa only [hi₂, hi₃] using data.le₂₃ r pq'

中文:
引理 le₂₃'
  结论: (r : 整数) (hr : r₀ <= r) (pq' : κ)
  证明: by
  simpa only [hi₂, hi₃] using data.le₂₃ r pq'

Depends on / 依赖: data.le
-/
lemma le₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ)
    {i₂ i₃ : ι}
    (hi₂ : i₂ = data.i₂ pq')
    (hi₃ : i₃ = data.i₃ r pq') :
    i₂ <= i₃ := by
  simpa only [hi₂, hi₃] using data.le₂₃ r pq'

/--
lemma `le₃₃'` / 引理 `le₃₃'`

English:
lemma le₃₃'
  statement: {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ)
  proof: by
  simpa only [hi₃, hi₃'] using data.monotone_i₃ r r' pq'

中文:
引理 le₃₃'
  结论: {r r' : 整数} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ)
  证明: by
  simpa only [hi₃, hi₃'] using data.monotone_i₃ r r' pq'

Depends on / 依赖: data.monotone_i
-/
lemma le₃₃' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ)
    {i₃ i₃' : ι}
    (hi₃ : i₃ = data.i₃ r pq')
    (hi₃' : i₃' = data.i₃ r' pq') :
    i₃ <= i₃' := by
  simpa only [hi₃, hi₃'] using data.monotone_i₃ r r' pq'

end SpectralSequenceDataCore

/-- The data which allows to construct an `E₂`-cohomological spectral sequence
indexed by `ℤ × ℤ` from a spectral object indexed by `EInt`. -/
@[simps!]
/--
Definition of `coreE₂Cohomological` / `coreE₂Cohomological` 的定义

English:
definition coreE₂Cohomological
  signature: :
  body: pq.1 + pq.2
  i₀ r pq hr := (pq.2 - r + 2 :)
  i₁ pq := pq.2
  i₂ pq := (pq.2 + 1 :)
  i₃ r pq hr := (pq.2 + r - 1 :)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc := by rintro r pq _ rfl _; dsimp; lia
  hc₀₂ := by rintro r pq hr rfl _; simp; lia
  hc₁₃ := by rintro r pq hr rfl _; simp; lia
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev := by
    rintro r r' hr pq rfl _ _
    dsimp
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  i₃_next := by
    rintro r r' hr pq rfl _ _
    dsimp
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc

中文:
定义 coreE₂Cohomological
  签名: :
  定义体: pq.1 + pq.2
  i₀ r pq hr := (pq.2 - r + 2 :)
  i₁ pq := pq.2
  i₂ pq := (pq.2 + 1 :)
  i₃ r pq hr := (pq.2 + r - 1 :)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc := by rintro r pq _ rfl _; dsimp; lia
  hc₀₂ := by rintro r pq hr rfl _; simp; lia
  hc₁₃ := by rintro r pq hr rfl _; simp; lia
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev := by
    rintro r r' hr pq rfl _ _
    dsimp
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  i₃_next := by
    rintro r r' hr pq rfl _ _
    dsimp
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
-/
def coreE₂Cohomological :
    SpectralSequenceDataCore EInt (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : Int × Int)) 2 where
  deg pq := pq.1 + pq.2
  i₀ r pq hr := (pq.2 - r + 2 :)
  i₁ pq := pq.2
  i₂ pq := (pq.2 + 1 :)
  i₃ r pq hr := (pq.2 + r - 1 :)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc := by rintro r pq _ rfl _; dsimp; lia
  hc₀₂ := by rintro r pq hr rfl _; simp; lia
  hc₁₃ := by rintro r pq hr rfl _; simp; lia
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev := by
    rintro r r' hr pq rfl _ _
    dsimp
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  i₃_next := by
    rintro r r' hr pq rfl _ _
    dsimp
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc

/-- The data which allows to construct an `E₂`-cohomological spectral sequence
indexed by `ℕ × ℕ` from a spectral object indexed by `EInt`. (Note: additional
assumptions on the spectral object are required for the construction of
the spectral sequence from this.) -/
@[simps!]
/--
Definition of `coreE₂CohomologicalNat` / `coreE₂CohomologicalNat` 的定义

English:
definition coreE₂CohomologicalNat
  signature: :
  body: pq.1 + pq.2
  i₀ r pq hr := (pq.2 - r + 2 :)
  i₁ pq := (pq.2 : Int)
  i₂ pq := (pq.2 + 1 : Int)
  i₃ r pq hr := (pq.2 + r - 1 : Int)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc r pq pq' hpq hr := by simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq; lia
  hc₀₂ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  hc₁₃ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  i₃_next r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc

中文:
定义 coreE₂Cohomological自然数
  签名: :
  定义体: pq.1 + pq.2
  i₀ r pq hr := (pq.2 - r + 2 :)
  i₁ pq := (pq.2 : Int)
  i₂ pq := (pq.2 + 1 : Int)
  i₃ r pq hr := (pq.2 + r - 1 : Int)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc r pq pq' hpq hr := by simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq; lia
  hc₀₂ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  hc₁₃ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  i₃_next r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
-/
def coreE₂CohomologicalNat :
    SpectralSequenceDataCore EInt
    (fun r => ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩) 2 where
  deg pq := pq.1 + pq.2
  i₀ r pq hr := (pq.2 - r + 2 :)
  i₁ pq := (pq.2 : Int)
  i₂ pq := (pq.2 + 1 : Int)
  i₃ r pq hr := (pq.2 + r - 1 : Int)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc r pq pq' hpq hr := by simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq; lia
  hc₀₂ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  hc₁₃ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  i₃_next r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc

/-- The data which allows to construct an `E₂`-cohomological spectral sequence
indexed by `ℤ × Fin l` from a spectral object indexed by `Fin (l + 1)`. -/
@[simps deg i₀ i₁ i₂ i₃]
/--
Definition of `coreE₂CohomologicalFin` / `coreE₂CohomologicalFin` 的定义

English:
definition coreE₂CohomologicalFin
  signature: (l : Nat)
  body: pq.1 + pq.2.1
  i₀ r pq hr := ⟨(pq.2.1 - (r - 2)).toNat, by grind⟩
  i₁ pq := pq.2.castSucc
  i₂ pq := pq.2.succ
  i₃ r pq hr := Fin.clamp (pq.2.1 + (r - 1)).toNat _
  le₀₁ := by rintro r ⟨p, q, hq⟩ hr; simp; lia
  le₁₂ pq := by simp [Fin.le_iff_val_le_val]
  le₂₃ r pq hr := by
    simp only [Fin.le_iff_val_le_val, Fin.val_succ, le_min_iff, Fin.clamp]
    grind
  hc _ _ _ := fun ⟨h₁, h₂⟩ => by lia
  hc₀₂ r := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩ hr
    grind
  hc₁₃ r := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩ hr
    rw [Fin.ext_iff]
    dsimp
    grind
  antitone_i₀ := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ hr hrr'
    rw [Fin.mk_le_mk]
    lia
  monotone_i₃ := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ hr hrr'
    rw [Fin.mk_le_mk]
    exact Fin.clamp_monotone (by lia)
  i₀_prev := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ ⟨b, ⟨b', _⟩⟩ ⟨h₁, h₂⟩ hrr' hr
    ext
    dsimp
    lia
  i₃_next := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ ⟨b, ⟨b', _⟩⟩ ⟨h₁, h₂⟩ hrr' hr
    ext
    dsimp
    grind

中文:
定义 coreE₂CohomologicalFin
  签名: (l : 自然数)
  定义体: pq.1 + pq.2.1
  i₀ r pq hr := ⟨(pq.2.1 - (r - 2)).toNat, by grind⟩
  i₁ pq := pq.2.castSucc
  i₂ pq := pq.2.succ
  i₃ r pq hr := Fin.clamp (pq.2.1 + (r - 1)).toNat _
  le₀₁ := by rintro r ⟨p, q, hq⟩ hr; simp; lia
  le₁₂ pq := by simp [Fin.le_iff_val_le_val]
  le₂₃ r pq hr := by
    simp only [Fin.le_iff_val_le_val, Fin.val_succ, le_min_iff, Fin.clamp]
    grind
  hc _ _ _ := fun ⟨h₁, h₂⟩ => by lia
  hc₀₂ r := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩ hr
    grind
  hc₁₃ r := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩ hr
    rw [Fin.ext_iff]
    dsimp
    grind
  antitone_i₀ := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ hr hrr'
    rw [Fin.mk_le_mk]
    lia
  monotone_i₃ := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ hr hrr'
    rw [Fin.mk_le_mk]
    exact Fin.clamp_monotone (by lia)
  i₀_prev := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ ⟨b, ⟨b', _⟩⟩ ⟨h₁, h₂⟩ hrr' hr
    ext
    dsimp
    lia
  i₃_next := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ ⟨b, ⟨b', _⟩⟩ ⟨h₁, h₂⟩ hrr' hr
    ext
    dsimp
    grind
-/
def coreE₂CohomologicalFin (l : Nat) :
    SpectralSequenceDataCore (Fin (l + 1))
    (fun r => ComplexShape.spectralSequenceFin l ⟨r, 1 - r⟩) 2 where
  deg pq := pq.1 + pq.2.1
  i₀ r pq hr := ⟨(pq.2.1 - (r - 2)).toNat, by grind⟩
  i₁ pq := pq.2.castSucc
  i₂ pq := pq.2.succ
  i₃ r pq hr := Fin.clamp (pq.2.1 + (r - 1)).toNat _
  le₀₁ := by rintro r ⟨p, q, hq⟩ hr; simp; lia
  le₁₂ pq := by simp [Fin.le_iff_val_le_val]
  le₂₃ r pq hr := by
    simp only [Fin.le_iff_val_le_val, Fin.val_succ, le_min_iff, Fin.clamp]
    grind
  hc _ _ _ := fun ⟨h₁, h₂⟩ => by lia
  hc₀₂ r := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩ hr
    grind
  hc₁₃ r := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩ hr
    rw [Fin.ext_iff]
    dsimp
    grind
  antitone_i₀ := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ hr hrr'
    rw [Fin.mk_le_mk]
    lia
  monotone_i₃ := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ hr hrr'
    rw [Fin.mk_le_mk]
    exact Fin.clamp_monotone (by lia)
  i₀_prev := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ ⟨b, ⟨b', _⟩⟩ ⟨h₁, h₂⟩ hrr' hr
    ext
    dsimp
    lia
  i₃_next := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ ⟨b, ⟨b', _⟩⟩ ⟨h₁, h₂⟩ hrr' hr
    ext
    dsimp
    grind

/-- The data which allows to construct an `E₂`-homological spectral sequence
indexed by `ℕ × ℕ` from a spectral object indexed by `EInt`. (Note: additional
assumptions on the spectral object are required for the construction of
the spectral sequence from this.) -/
@[simps!]
/--
Definition of `coreE₂HomologicalNat` / `coreE₂HomologicalNat` 的定义

English:
definition coreE₂HomologicalNat
  signature: :
  body: - pq.1 - pq.2
  i₀ r pq hr := (-pq.2 - r + 2 :)
  i₁ pq := (-pq.2 : Int)
  i₂ pq := (-pq.2 + 1 : Int)
  i₃ r pq hr := (-pq.2 + r - 1 :)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  hc₀₂ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  hc₁₃ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  i₃_next r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc

中文:
定义 coreE₂Homological自然数
  签名: :
  定义体: - pq.1 - pq.2
  i₀ r pq hr := (-pq.2 - r + 2 :)
  i₁ pq := (-pq.2 : Int)
  i₂ pq := (-pq.2 + 1 : Int)
  i₃ r pq hr := (-pq.2 + r - 1 :)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  hc₀₂ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  hc₁₃ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  i₃_next r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
-/
def coreE₂HomologicalNat :
    SpectralSequenceDataCore EInt
    (fun r => ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 2 where
  deg pq := - pq.1 - pq.2
  i₀ r pq hr := (-pq.2 - r + 2 :)
  i₁ pq := (-pq.2 : Int)
  i₂ pq := (-pq.2 + 1 : Int)
  i₃ r pq hr := (-pq.2 + r - 1 :)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  hc₀₂ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  hc₁₃ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc
  i₃_next r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc

variable (X : SpectralObject C ι) (data : SpectralSequenceDataCore ι c r₀)

/--
Definition of `HasSpectralSequence` / `HasSpectralSequence` 的定义

English:
class HasSpectralSequence
  parameters: : Prop where
  axioms and operations (2):
    - isZero_H_obj_mk₁_i₀_le((r r' : Int) (pq : κ) (hpq : forall (pq' : κ), ¬ ((c r).Rel pq pq')) (n : Int) (hn : n = data.deg pq + 1) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)) : IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₀_le r r' pq))))
    - isZero_H_obj_mk₁_i₃_le((r r' : Int) (pq : κ) (hpq : forall (pq' : κ), ¬ ((c r).Rel pq' pq)) (n : Int) (hn : n = data.deg pq - 1) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)) : IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₃_le r r' pq))))

中文:
类 有谱序列
  参数: : 命题 where
  公理与运算 (2 个):
    - isZero_H_obj_mk₁_i₀_le((r r' : 整数) (pq : κ) (hpq : 对任意 (pq' : κ), ¬ ((c r).关系 pq pq')) (n : 整数) (hn : n = data.deg pq + 1) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)) : 是零 ((X.H n).obj (mk₁ (homOfLE (data.i₀_le r r' pq))))
    - isZero_H_obj_mk₁_i₃_le((r r' : 整数) (pq : κ) (hpq : 对任意 (pq' : κ), ¬ ((c r).关系 pq' pq)) (n : 整数) (hn : n = data.deg pq - 1) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)) : 是零 ((X.H n).obj (mk₁ (homOfLE (data.i₃_le r r' pq))))

Depends on / 依赖: IsZero, data.deg, data.i, homOfLE
-/
class HasSpectralSequence : Prop where
  isZero_H_obj_mk₁_i₀_le (r r' : Int) (pq : κ) (hpq : forall (pq' : κ), ¬ ((c r).Rel pq pq'))
    (n : Int) (hn : n = data.deg pq + 1)
    (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia) :
      IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₀_le r r' pq))))
  isZero_H_obj_mk₁_i₃_le (r r' : Int) (pq : κ) (hpq : forall (pq' : κ), ¬ ((c r).Rel pq' pq))
    (n : Int) (hn : n = data.deg pq - 1)
    (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia) :
      IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₃_le r r' pq))))

variable [X.HasSpectralSequence data]

/--
lemma `isZero_H_obj_mk₁_i₀_le` / 引理 `isZero_H_obj_mk₁_i₀_le`

English:
lemma isZero_H_obj_mk₁_i₀_le
  statement: (r r' : Int) (hrr' : r + 1 = r') (hr : r₀ <= r)
  proof: HasSpectralSequence.isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn

中文:
引理 isZero_H_obj_mk₁_i₀_le
  结论: (r r' : 整数) (hrr' : r + 1 = r') (hr : r₀ <= r)
  证明: HasSpectralSequence.isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn

Depends on / 依赖: HasSpectralSequence, HasSpectralSequence.isZero_H_obj_mk
-/
lemma isZero_H_obj_mk₁_i₀_le (r r' : Int) (hrr' : r + 1 = r') (hr : r₀ <= r)
    (pq : κ) (hpq : forall (pq' : κ), ¬ ((c r).Rel pq pq'))
    (n : Int) (hn : n = data.deg pq + 1) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₀_le r r' pq)))) :=
  HasSpectralSequence.isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn

/--
lemma `isZero_H_obj_mk₁_i₀_le'` / 引理 `isZero_H_obj_mk₁_i₀_le'`

English:
lemma isZero_H_obj_mk₁_i₀_le'
  statement: (r r' : Int) (hrr' : r + 1 = r') (hr : r₀ <= r)
  proof: by
  subst hi₀' hi₀
  exact HasSpectralSequence.isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn

中文:
引理 isZero_H_obj_mk₁_i₀_le'
  结论: (r r' : 整数) (hrr' : r + 1 = r') (hr : r₀ <= r)
  证明: by
  subst hi₀' hi₀
  exact HasSpectralSequence.isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn

Depends on / 依赖: HasSpectralSequence, HasSpectralSequence.isZero_H_obj_mk
-/
lemma isZero_H_obj_mk₁_i₀_le' (r r' : Int) (hrr' : r + 1 = r') (hr : r₀ <= r)
    (pq : κ) (hpq : forall (pq' : κ), ¬ ((c r).Rel pq pq'))
    (n : Int) (hn : n = data.deg pq + 1) (i₀' i₀ : ι)
    (hi₀' : i₀' = data.i₀ r' pq)
    (hi₀ : i₀ = data.i₀ r pq) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (show i₀' <= i₀ by
      simpa only [hi₀', hi₀] using data.i₀_le r r' pq)))) := by
  subst hi₀' hi₀
  exact HasSpectralSequence.isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn

/--
lemma `isZero_H_obj_mk₁_i₃_le` / 引理 `isZero_H_obj_mk₁_i₃_le`

English:
lemma isZero_H_obj_mk₁_i₃_le
  statement: (r r' : Int) (hrr' : r + 1 = r') (hr : r₀ <= r)
  proof: HasSpectralSequence.isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn

中文:
引理 isZero_H_obj_mk₁_i₃_le
  结论: (r r' : 整数) (hrr' : r + 1 = r') (hr : r₀ <= r)
  证明: HasSpectralSequence.isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn

Depends on / 依赖: HasSpectralSequence, HasSpectralSequence.isZero_H_obj_mk
-/
lemma isZero_H_obj_mk₁_i₃_le (r r' : Int) (hrr' : r + 1 = r') (hr : r₀ <= r)
    (pq : κ) (hpq : forall (pq' : κ), ¬ ((c r).Rel pq' pq))
    (n : Int) (hn : n = data.deg pq - 1) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₃_le r r' pq)))) :=
  HasSpectralSequence.isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn

/--
lemma `isZero_H_obj_mk₁_i₃_le'` / 引理 `isZero_H_obj_mk₁_i₃_le'`

English:
lemma isZero_H_obj_mk₁_i₃_le'
  statement: (r r' : Int) (hrr' : r + 1 = r') (hr : r₀ <= r)
  proof: by
  subst hi₃ hi₃'
  exact HasSpectralSequence.isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn

中文:
引理 isZero_H_obj_mk₁_i₃_le'
  结论: (r r' : 整数) (hrr' : r + 1 = r') (hr : r₀ <= r)
  证明: by
  subst hi₃ hi₃'
  exact HasSpectralSequence.isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn

Depends on / 依赖: HasSpectralSequence, HasSpectralSequence.isZero_H_obj_mk
-/
lemma isZero_H_obj_mk₁_i₃_le' (r r' : Int) (hrr' : r + 1 = r') (hr : r₀ <= r)
    (pq : κ) (hpq : forall (pq' : κ), ¬ ((c r).Rel pq' pq))
    (n : Int) (hn : n = data.deg pq - 1) (i₃ i₃' : ι)
    (hi₃ : i₃ = data.i₃ r pq)
    (hi₃' : i₃' = data.i₃ r' pq) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (show i₃ <= i₃' by
      simpa only [hi₃, hi₃'] using data.i₃_le r r' pq)))) := by
  subst hi₃ hi₃'
  exact HasSpectralSequence.isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn

instance (E : SpectralObject C EInt) : E.HasSpectralSequence coreE₂Cohomological where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq _ rfl
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq (pq - (r, 1 - r)) (by simp)

set_option backward.defeqAttrib.useBackward true in
instance {l : Nat} (E : SpectralObject C (Fin (l + 1))) :
    E.HasSpectralSequence (coreE₂CohomologicalFin l) where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr := by
    have : (coreE₂CohomologicalFin l).i₀ r' pq =
        (coreE₂CohomologicalFin l).i₀ r pq := by
      subst hrr'
      obtain ⟨k, rfl⟩ := Int.le.dest hr
      obtain ⟨p, q, hq⟩ := pq
      ext
      have h : q <= k := by
        by_contra!
        simp only [ComplexShape.spectralSequenceFin_rel_iff, not_and, Prod.forall] at hpq
        obtain ⟨t, rfl⟩ := Nat.le.dest (Nat.add_one_le_of_lt this)
        exact hpq _ ⟨t, by lia⟩ rfl (by simp; lia)
      simp_all
      lia
    have := isIso_homOfLE this
    apply E.isZero_H_map_mk₁_of_isIso
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr := by
    have : (coreE₂CohomologicalFin l).i₃ r pq = (coreE₂CohomologicalFin l).i₃ r' pq := by
      subst hrr'
      obtain ⟨p, q, hq⟩ := pq
      have h : l < q + r := by
        by_contra!
        obtain ⟨t, ht⟩ := Int.le.dest this
        simp only [ComplexShape.spectralSequenceFin_rel_iff, not_and, Prod.forall] at hpq
        exact hpq (p - r) ⟨l - 1 - t, by lia⟩ (by lia) (by lia)
      dsimp
      rw [add_sub_cancel_right]; rw [Fin.clamp_eq_last _ _ (by lia)]; rw [Fin.clamp_eq_last _ _ (by lia)]
    have := isIso_homOfLE this
    apply E.isZero_H_map_mk₁_of_isIso

section

variable (Y : SpectralObject C EInt)

/--
Definition of `IsFirstQuadrant` / `IsFirstQuadrant` 的定义

English:
class IsFirstQuadrant
  parameters: : Prop where
  axioms and operations (2):
    - isZero₁((i j : EInt) (hij : i <= j) (hj : j <= (0 : Int)) (n : Int)) : IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))
    - isZero₂((i j : EInt) (hij : i <= j) (n : Int) (hi : n < i)) : IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))

中文:
类 是FirstQuadrant
  参数: : 命题 where
  公理与运算 (2 个):
    - isZero₁((i j : E整数) (hij : i <= j) (hj : j <= (0 : 整数)) (n : 整数)) : 是零 ((Y.H n).obj (mk₁ (homOfLE hij)))
    - isZero₂((i j : E整数) (hij : i <= j) (n : 整数) (hi : n < i)) : 是零 ((Y.H n).obj (mk₁ (homOfLE hij)))
-/
class IsFirstQuadrant : Prop where
  isZero₁ (i j : EInt) (hij : i <= j) (hj : j <= (0 : Int)) (n : Int) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))
  isZero₂ (i j : EInt) (hij : i <= j) (n : Int) (hi : n < i) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))

variable [Y.IsFirstQuadrant]

/--
lemma `isZero₁_of_isFirstQuadrant` / 引理 `isZero₁_of_isFirstQuadrant`

English:
lemma isZero₁_of_isFirstQuadrant
  given: (i j : EInt) (hij : i <= j) (hj : j <= (0 : Int)) (n : Int)
  proof: IsFirstQuadrant.isZero₁ i j hij hj n

中文:
引理 isZero₁_of_isFirstQuadrant
  条件: (i j : E整数) (hij : i <= j) (hj : j <= (0 : 整数)) (n : 整数)
  证明: IsFirstQuadrant.isZero₁ i j hij hj n

Depends on / 依赖: IsFirstQuadrant, IsFirstQuadrant.isZero
-/
lemma isZero₁_of_isFirstQuadrant (i j : EInt) (hij : i <= j) (hj : j <= (0 : Int)) (n : Int) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij))) :=
  IsFirstQuadrant.isZero₁ i j hij hj n

/--
lemma `isZero₂_of_isFirstQuadrant` / 引理 `isZero₂_of_isFirstQuadrant`

English:
lemma isZero₂_of_isFirstQuadrant
  given: (i j : EInt) (hij : i <= j) (n : Int) (hi : n < i)
  proof: IsFirstQuadrant.isZero₂ i j hij n hi

中文:
引理 isZero₂_of_isFirstQuadrant
  条件: (i j : E整数) (hij : i <= j) (n : 整数) (hi : n < i)
  证明: IsFirstQuadrant.isZero₂ i j hij n hi

Depends on / 依赖: IsFirstQuadrant, IsFirstQuadrant.isZero
-/
lemma isZero₂_of_isFirstQuadrant (i j : EInt) (hij : i <= j) (n : Int) (hi : n < i) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij))) :=
  IsFirstQuadrant.isZero₂ i j hij n hi

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Y.HasSpectralSequence coreE₂CohomologicalNat
  body: by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₁_of_isFirstQuadrant
    simp only [coreE₂CohomologicalNat_i₀, WithBotTop.coe_le_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= p + r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= q + 1 - r by lia)
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)
  isZero_H_obj_mk₁_i₃_le := by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₂_of_isFirstQuadrant
    simp only [coreE₂CohomologicalNat_deg, coreE₂CohomologicalNat_i₃, WithBotTop.coe_lt_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= p - r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= q - 1 + r by lia)
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)

中文:
实例 :
  签名: Y.有谱序列 coreE₂Cohomological自然数
  定义体: by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₁_of_isFirstQuadrant
    simp only [coreE₂CohomologicalNat_i₀, WithBotTop.coe_le_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= p + r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= q + 1 - r by lia)
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)
  isZero_H_obj_mk₁_i₃_le := by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₂_of_isFirstQuadrant
    simp only [coreE₂CohomologicalNat_deg, coreE₂CohomologicalNat_i₃, WithBotTop.coe_lt_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= p - r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= q - 1 + r by lia)
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)

Depends on / 依赖: Int.eq_ofNat_of_zero_le, WithBotT, WithBotTop, WithBotTop.coe_le_coe, coe_le_coe, eq_ofNat_of_zero_le
-/
instance : Y.HasSpectralSequence coreE₂CohomologicalNat where
  isZero_H_obj_mk₁_i₀_le := by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₁_of_isFirstQuadrant
    simp only [coreE₂CohomologicalNat_i₀, WithBotTop.coe_le_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= p + r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= q + 1 - r by lia)
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)
  isZero_H_obj_mk₁_i₃_le := by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₂_of_isFirstQuadrant
    simp only [coreE₂CohomologicalNat_deg, coreE₂CohomologicalNat_i₃, WithBotTop.coe_lt_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= p - r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= q - 1 + r by lia)
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)

end

section

variable (Y : SpectralObject C EInt)

/--
Definition of `IsThirdQuadrant` / `IsThirdQuadrant` 的定义

English:
class IsThirdQuadrant
  parameters: where
  axioms and operations (2):
    - isZero₁((i j : EInt) (hij : i <= j) (hi : (0 : Int) < i) (n : Int)) : IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))
    - isZero₂((i j : EInt) (hij : i <= j) (n : Int) (hj : j <= n)) : IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))

中文:
类 是ThirdQuadrant
  参数: where
  公理与运算 (2 个):
    - isZero₁((i j : E整数) (hij : i <= j) (hi : (0 : 整数) < i) (n : 整数)) : 是零 ((Y.H n).obj (mk₁ (homOfLE hij)))
    - isZero₂((i j : E整数) (hij : i <= j) (n : 整数) (hj : j <= n)) : 是零 ((Y.H n).obj (mk₁ (homOfLE hij)))
-/
class IsThirdQuadrant where
  isZero₁ (i j : EInt) (hij : i <= j) (hi : (0 : Int) < i) (n : Int) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))
  isZero₂ (i j : EInt) (hij : i <= j) (n : Int) (hj : j <= n) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))

variable [Y.IsThirdQuadrant]

/--
lemma `isZero₁_of_isThirdQuadrant` / 引理 `isZero₁_of_isThirdQuadrant`

English:
lemma isZero₁_of_isThirdQuadrant
  given: (i j : EInt) (hij : i <= j) (hi : (0 : Int) < i) (n : Int)
  proof: IsThirdQuadrant.isZero₁ i j hij hi n

中文:
引理 isZero₁_of_isThirdQuadrant
  条件: (i j : E整数) (hij : i <= j) (hi : (0 : 整数) < i) (n : 整数)
  证明: IsThirdQuadrant.isZero₁ i j hij hi n

Depends on / 依赖: IsThirdQuadrant, IsThirdQuadrant.isZero
-/
lemma isZero₁_of_isThirdQuadrant (i j : EInt) (hij : i <= j) (hi : (0 : Int) < i) (n : Int) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij))) :=
  IsThirdQuadrant.isZero₁ i j hij hi n

/--
lemma `isZero₂_of_isThirdQuadrant` / 引理 `isZero₂_of_isThirdQuadrant`

English:
lemma isZero₂_of_isThirdQuadrant
  given: (i j : EInt) (hij : i <= j) (n : Int) (hj : j <= n)
  proof: IsThirdQuadrant.isZero₂ i j hij n hj

中文:
引理 isZero₂_of_isThirdQuadrant
  条件: (i j : E整数) (hij : i <= j) (n : 整数) (hj : j <= n)
  证明: IsThirdQuadrant.isZero₂ i j hij n hj

Depends on / 依赖: IsThirdQuadrant, IsThirdQuadrant.isZero
-/
lemma isZero₂_of_isThirdQuadrant (i j : EInt) (hij : i <= j) (n : Int) (hj : j <= n) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij))) :=
  IsThirdQuadrant.isZero₂ i j hij n hj

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Y.HasSpectralSequence coreE₂HomologicalNat
  body: by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₂_of_isThirdQuadrant
    simp only [coreE₂HomologicalNat_i₀, coreE₂HomologicalNat_deg, WithBotTop.coe_le_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= p - r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= q + r - 1 by lia)
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)
  isZero_H_obj_mk₁_i₃_le := by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₁_of_isThirdQuadrant
    simp only [coreE₂HomologicalNat_i₃, WithBotTop.coe_lt_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= p + r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= q + 1 - r by lia)
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)

中文:
实例 :
  签名: Y.有谱序列 coreE₂Homological自然数
  定义体: by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₂_of_isThirdQuadrant
    simp only [coreE₂HomologicalNat_i₀, coreE₂HomologicalNat_deg, WithBotTop.coe_le_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= p - r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= q + r - 1 by lia)
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)
  isZero_H_obj_mk₁_i₃_le := by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₁_of_isThirdQuadrant
    simp only [coreE₂HomologicalNat_i₃, WithBotTop.coe_lt_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= p + r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= q + 1 - r by lia)
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)

Depends on / 依赖: Int.eq_ofNat_of_zero_le, WithBotTop, WithBotTop.coe, WithBotTop.coe_le_coe, coe_le_coe, eq_ofNat_of_zero_le
-/
instance : Y.HasSpectralSequence coreE₂HomologicalNat where
  isZero_H_obj_mk₁_i₀_le := by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₂_of_isThirdQuadrant
    simp only [coreE₂HomologicalNat_i₀, coreE₂HomologicalNat_deg, WithBotTop.coe_le_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= p - r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= q + r - 1 by lia)
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)
  isZero_H_obj_mk₁_i₃_le := by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₁_of_isThirdQuadrant
    simp only [coreE₂HomologicalNat_i₃, WithBotTop.coe_lt_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= p + r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= q + 1 - r by lia)
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)

end

end SpectralObject

end Abelian

end CategoryTheory
