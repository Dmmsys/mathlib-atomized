/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The Zariski topology on the maximal spectrum of a commutative (semi)ring

## Implementation notes

The Zariski topology on the maximal spectrum is defined as the subspace topology induced by the
natural inclusion into the prime spectrum to avoid API duplication for zero loci.
-/

public section


noncomputable section

universe u v

variable (R : Type u) [CommRing R]

variable {R}

namespace MaximalSpectrum

open PrimeSpectrum Set

/--
theorem `toPrimeSpectrum_range` / 定理 `toPrimeSpectrum_range`

English:
theorem toPrimeSpectrum_range
  proof: by
  simp only [isClosed_singleton_iff_isMaximal]
  ext ⟨x, _⟩
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.isMaximal, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

中文:
定理 toPrimeSpectrum_range
  证明: by
  simp only [isClosed_singleton_iff_isMaximal]
  ext ⟨x, _⟩
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.isMaximal, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

Depends on / 依赖: isClosed_singleton_iff_isMaximal, isMaximal, y.isMaximal
-/
theorem toPrimeSpectrum_range :
    Set.range (@toPrimeSpectrum R _) = { x | IsClosed ({x} : Set <| PrimeSpectrum R) } := by
  simp only [isClosed_singleton_iff_isMaximal]
  ext ⟨x, _⟩
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.isMaximal, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/--
Instance `zariskiTopology` / 实例 `zariskiTopology`

English:
instance zariskiTopology
  signature: : TopologicalSpace MaximalSpectrum R
  body: PrimeSpectrum.zariskiTopology.induced toPrimeSpectrum

中文:
实例 zariskiTopology
  签名: : TopologicalSpace MaximalSpectrum R
  定义体: PrimeSpectrum.zariskiTopology.induced toPrimeSpectrum

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.zariskiTopology.induced, induced, toPrimeSpectrum, zariskiTopology
-/
instance zariskiTopology : TopologicalSpace MaximalSpectrum R :=
  PrimeSpectrum.zariskiTopology.induced toPrimeSpectrum

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T1Space MaximalSpectrum R
  body: ⟨fun x => isClosed_induced_iff.mpr
    ⟨{toPrimeSpectrum x}, (isClosed_singleton_iff_isMaximal _).mpr x.isMaximal, by
      simpa only [← image_singleton] using preimage_image_eq {x} toPrimeSpectrum_injective⟩⟩

中文:
实例 :
  签名: T1Space MaximalSpectrum R
  定义体: ⟨fun x => isClosed_induced_iff.mpr
    ⟨{toPrimeSpectrum x}, (isClosed_singleton_iff_isMaximal _).mpr x.isMaximal, by
      simpa only [← image_singleton] using preimage_image_eq {x} toPrimeSpectrum_injective⟩⟩

Depends on / 依赖: image_singleton, isClosed_induced_iff, isClosed_induced_iff.mpr, isClosed_singleton_iff_isMaximal, isMaximal, preimage_image_eq, toPrimeSpectrum, toPrimeSpectrum_injective, x.isMaximal
-/
instance : T1Space MaximalSpectrum R :=
  ⟨fun x => isClosed_induced_iff.mpr
    ⟨{toPrimeSpectrum x}, (isClosed_singleton_iff_isMaximal _).mpr x.isMaximal, by
      simpa only [← image_singleton] using preimage_image_eq {x} toPrimeSpectrum_injective⟩⟩

/--
theorem `toPrimeSpectrum_continuous` / 定理 `toPrimeSpectrum_continuous`

English:
theorem toPrimeSpectrum_continuous
  statement: Continuous @toPrimeSpectrum R _
  proof: continuous_induced_dom

中文:
定理 toPrimeSpectrum_continuous
  结论: Continuous @toPrimeSpectrum R _
  证明: continuous_induced_dom

Depends on / 依赖: continuous_induced_dom
-/
theorem toPrimeSpectrum_continuous : Continuous @toPrimeSpectrum R _ :=
  continuous_induced_dom

end MaximalSpectrum
