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

/-
**MaximalSpectrum.toPrimeSpectrum_range** 是 Mathlib 中的一个定理，位于命名空间 `MaximalSpectr
um`。
形式化陈述：toPrimeSpectrum_range : Set.range (@toPrimeSpectrum R _) = { x | IsClosed 
({x} : Set <| PrimeSpectrum R) }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
-/
theorem toPrimeSpectrum_range :
    Set.range (@toPrimeSpectrum R _) = { x | IsClosed ({x} : Set <| PrimeSpectrum R) } := by
  simp only [isClosed_singleton_iff_isMaximal]
  ext ⟨x, _⟩
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.isMaximal, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/-- The Zariski topology on the maximal spectrum of a commutative ring is defined as the subspace
topology induced by the natural inclusion into the prime spectrum. -/
/-
**MaximalSpectrum.zariskiTopology** 是 Mathlib 中的一个实例，位于命名空间 `MaximalSpectrum`。
形式化陈述：zariskiTopology : TopologicalSpace MaximalSpectrum R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Zariski topology on the maximal spectrum of a commutative ring is defined as
 the subspace
topology induced by the natural inclusion into the prime spectrum.
-/
instance zariskiTopology : TopologicalSpace <| MaximalSpectrum R :=
  PrimeSpectrum.zariskiTopology.induced toPrimeSpectrum
/-
**MaximalSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `MaximalSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T1Space <| MaximalSpectrum R :=
  ⟨fun x => isClosed_induced_iff.mpr
    ⟨{toPrimeSpectrum x}, (isClosed_singleton_iff_isMaximal _).mpr x.isMaximal, by
      simpa only [← image_singleton] using preimage_image_eq {x} toPrimeSpectrum_injective⟩⟩
/-
**MaximalSpectrum.toPrimeSpectrum_continuous** 是 Mathlib 中的一个定理，位于命名空间 `MaximalS
pectrum`。
形式化陈述：toPrimeSpectrum_continuous : Continuous @toPrimeSpectrum R _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem toPrimeSpectrum_continuous : Continuous <| @toPrimeSpectrum R _ :=
  continuous_induced_dom

end MaximalSpectrum

