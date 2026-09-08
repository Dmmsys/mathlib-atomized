/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Order.Ring.Idempotent
public import Mathlib.Order.Heyting.Hom
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Spectrum.Maximal.Localization
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Spectral.Basic

/-!
# The Zariski topology on the prime spectrum of a commutative (semi)ring

## Conventions

We denote subsets of (semi)rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from <https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

## Main definitions

* `PrimeSpectrum.zariskiTopology`: the Zariski topology on the prime spectrum, whose closed sets
  are zero loci (`zeroLocus`).

* `PrimeSpectrum.basicOpen`: the complement of the zero locus of a single element.
  The `basicOpen`s form a topological basis of the Zariski topology:
  `PrimeSpectrum.isTopologicalBasis_basic_opens`.

* `PrimeSpectrum.comap`: the continuous map between prime spectra induced by a ring homomorphism.

* `IsLocalRing.closedPoint`: the maximal ideal of a local ring is the unique closed point in its
  prime spectrum.

## Main results

* `PrimeSpectrum.instSpectralSpace`: every prime spectrum is a spectral space, i.e. it is
  quasi-compact, sober (in particular T0), quasi-separated, and its compact open subsets form
  a topological basis.

* `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`: the prime spectrum of a
  commutative semiring is discrete iff it is finite and the semiring has zero Krull dimension
  or is trivial.

* `PrimeSpectrum.localization_comap_range`, `PrimeSpectrum.localization_comap_isEmbedding`:
  localization at a submonoid of a commutative semiring induces an embedding between the prime
  spectra, with range consisting of prime ideals disjoint from the submonoid.

* `PrimeSpectrum.localization_away_comap_range`: for localization away from an element, the
  range of the embedding is the `basicOpen` associated to the element.

* `PrimeSpectrum.comap_isEmbedding_of_surjective`: a surjective ring homomorphism between
  commutative semirings induces an embedding between the prime spectra.

* `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`: a surjective ring homomorphism between
  commutative rings induces a closed embedding between the prime spectra.

* `PrimeSpectrum.primeSpectrumProdHomeo`: the prime spectrum of a product semiring is homeomorphic
  to the disjoint union of the prime spectra.

* `PrimeSpectrum.stableUnderSpecialization_range_iff`: the range of `PrimeSpectrum.comap _` is
  closed iff it is stable under specialization.

* `PrimeSpectrum.denseRange_comap_iff_minimalPrimes`,
  `PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical`: the range of `comap f` is dense
  iff it contains all minimal primes, iff the kernel of `f` is contained in the nilradical.

* `PrimeSpectrum.isClosedMap_comap_of_isIntegral`: `comap f` is a closed map if `f` is integral.

* `PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom`: `f : R →+* S` is integral if
  `comap (Polynomial.mapRingHom f : R[X] →+* S[X])` is a closed map.

In the prime spectrum of a commutative semiring:

* `PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal`, `PrimeSpectrum.isRadical_vanishingIdeal`,
  `PrimeSpectrum.zeroLocus_eq_iff`, `PrimeSpectrum.vanishingIdeal_anti_mono_iff`:
  closed subsets correspond to radical ideals.

* `PrimeSpectrum.isClosed_singleton_iff_isMaximal`: closed points correspond to maximal ideals.

* `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`: irreducible closed subsets correspond
  to prime ideals.

* `minimalPrimes.equivIrreducibleComponents`: irreducible components correspond to minimal primes.

* `PrimeSpectrum.mulZeroAddOneEquivClopens`: clopen subsets correspond to pairs of elements
  that add up to 1 and multiply to 0 in the semiring.

* `PrimeSpectrum.isIdempotentElemEquivClopens`: (if the semiring is a ring) clopen subsets
  correspond to idempotents in the ring.

-/

@[expose] public section

open Topology

noncomputable section

universe u v

variable (R : Type u) (S : Type v)

namespace PrimeSpectrum

section CommSemiring

variable [CommSemiring R] [CommSemiring S]
variable {R S}

/-- The Zariski topology on the prime spectrum of a commutative (semi)ring is defined
via the closed sets of the topology: they are exactly those sets that are the zero locus
of a subset of the ring. -/
/-
**PrimeSpectrum.zariskiTopology** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
形式化陈述：zariskiTopology : TopologicalSpace (PrimeSpectrum R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Zariski topology on the prime spectrum of a commutative (semi)ring is define
d
via the closed sets of the topology: they are exactly those sets that are the ze
ro locus
of a subset of the ring.
-/
instance zariskiTopology : TopologicalSpace (PrimeSpectrum R) :=
  TopologicalSpace.ofClosed (Set.range PrimeSpectrum.zeroLocus) ⟨Set.univ, by simp⟩
    (by
      intro Zs h
      rw [Set.sInter_eq_iInter]
      choose f hf using fun i : Zs => h i.prop
      simp only [← hf]
      exact ⟨_, zeroLocus_iUnion _⟩)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zeroLocus s t).symm⟩)
/-
**PrimeSpectrum.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isOpen_iff (U : Set (PrimeSpectrum R)) : IsOpen U ↔ exists s, Uᶜ = zeroLoc
us s
参数：U : Set (PrimeSpectrum R)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_iff (U : Set (PrimeSpectrum R)) : IsOpen U ↔ ∃ s, Uᶜ = zeroLocus s := by
  simp only [@eq_comm _ Uᶜ]; rfl
/-
**PrimeSpectrum.isClosed_iff_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`
。
形式化陈述：isClosed_iff_zeroLocus (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ exists s
, Z = zeroLocus s
参数：Z : Set (PrimeSpectrum R)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `PrimeSpectrum.isOpen_iff`：isOpen_iff (U : Set (PrimeSpectrum R)) : IsOpe
n U ↔ exists s, Uᶜ = zeroLocus s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClosed_iff_zeroLocus (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ ∃ s, Z = zeroLocus s := by
  rw [← isOpen_compl_iff, isOpen_iff, compl_compl]
/-
**PrimeSpectrum.isClosed_iff_zeroLocus_ideal** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpe
ctrum`。
形式化陈述：isClosed_iff_zeroLocus_ideal (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ ex
ists I : Ideal R, Z = zeroLocus I
参数：Z : Set (PrimeSpectrum R)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PrimeSpectrum.isClosed_iff_zeroLocus`：isClosed_iff_zeroLocus (Z : Set (P
rimeSpectrum R)) : IsClosed Z ↔ exists s, Z = zeroLocus s
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
-/
theorem isClosed_iff_zeroLocus_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ I : Ideal R, Z = zeroLocus I :=
  (isClosed_iff_zeroLocus _).trans
    ⟨fun ⟨s, hs⟩ => ⟨_, (zeroLocus_span s).substr hs⟩, fun ⟨I, hI⟩ => ⟨I, hI⟩⟩
/-
**PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal** 是 Mathlib 中的一个定理，位于命名空间 `
PrimeSpectrum`。
形式化陈述：isClosed_iff_zeroLocus_radical_ideal (Z : Set (PrimeSpectrum R)) : IsClose
d Z ↔ exists I : Ideal R, I.IsRadical ∧ Z = zeroLocus I
参数：Z : Set (PrimeSpectrum R)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PrimeSpectrum.isClosed_iff_zeroLocus_ideal`：isClosed_iff_zeroLocus_ideal
 (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ exists I : Ideal R, Z = zeroLocus I
· 使用定理 `Ideal.radical_isRadical`：radical_isRadical : (radical I).IsRadical
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `PrimeSpectrum.zeroLocus_radical`：zeroLocus_radical (I : Ideal R) : zeroL
ocus (I.radical : Set R) = zeroLocus I
-/
theorem isClosed_iff_zeroLocus_radical_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ I : Ideal R, I.IsRadical ∧ Z = zeroLocus I :=
  (isClosed_iff_zeroLocus_ideal _).trans
    ⟨fun ⟨I, hI⟩ => ⟨_, I.radical_isRadical, (zeroLocus_radical I).substr hI⟩, fun ⟨I, _, hI⟩ =>
      ⟨I, hI⟩⟩
/-
**PrimeSpectrum.isClosed_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isClosed_zeroLocus (s : Set R) : IsClosed (zeroLocus s)
参数：s : Set R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.isClosed_iff_zeroLocus`：isClosed_iff_zeroLocus (Z : Set (P
rimeSpectrum R)) : IsClosed Z ↔ exists s, Z = zeroLocus s
-/
theorem isClosed_zeroLocus (s : Set R) : IsClosed (zeroLocus s) := by
  rw [isClosed_iff_zeroLocus]
  exact ⟨s, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `P
rimeSpectrum`。
形式化陈述：zeroLocus_vanishingIdeal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocu
s (vanishingIdeal t : Set R) = closure t
参数：t : Set (PrimeSpectrum R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isClosed_iff_zeroLocus`：isClosed_iff_zeroLocus (Z : Set (P
rimeSpectrum R)) : IsClosed Z ↔ exists s, Z = zeroLocus s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
· 使用定理 `PrimeSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal`：subset_zeroLoc
us_iff_subset_vanishingIdeal (t : Set (PrimeSpectrum R)) (s : Set R) : t subsete
q zeroLocus s ↔ s subseteq vanishingIdeal t
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `PrimeSpectrum.subset_zeroLocus_vanishingIdeal`：subset_zeroLocus_vanishin
gIdeal (t : Set (PrimeSpectrum R)) : t subseteq zeroLocus (vanishingIdeal t)
-/
theorem zeroLocus_vanishingIdeal_eq_closure (t : Set (PrimeSpectrum R)) :
    zeroLocus (vanishingIdeal t : Set R) = closure t := by
  rcases isClosed_iff_zeroLocus (closure t) |>.mp isClosed_closure with ⟨I, hI⟩
  rw [subset_antisymm_iff, (isClosed_zeroLocus _).closure_subset_iff, hI,
      subset_zeroLocus_iff_subset_vanishingIdeal, (gc R).u_l_u_eq_u,
      ← subset_zeroLocus_iff_subset_vanishingIdeal, ← hI]
  exact ⟨subset_closure, subset_zeroLocus_vanishingIdeal t⟩
/-
**PrimeSpectrum.vanishingIdeal_closure** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`
。
形式化陈述：vanishingIdeal_closure (t : Set (PrimeSpectrum R)) : vanishingIdeal (closu
re t) = vanishingIdeal t
参数：t : Set (PrimeSpectrum R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用定理 `PrimeSpectrum.gc`：gc : @GaloisConnection (Ideal R) (Set (PrimeSpectrum R
))ᵒᵈ _ _ (fun I => zeroLocus I) fun t => vanishingIdeal t
· 使用定理 `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanishingId
eal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocus (vanishingIdeal t : Set R
) = closure t
-/
theorem vanishingIdeal_closure (t : Set (PrimeSpectrum R)) :
    vanishingIdeal (closure t) = vanishingIdeal t :=
  zeroLocus_vanishingIdeal_eq_closure t ▸ (gc R).u_l_u_eq_u t
/-
**PrimeSpectrum.closure_singleton** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：closure_singleton (x) : closure ({x} : Set (PrimeSpectrum R)) = zeroLocus 
x.asIdeal
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanishingId
eal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocus (vanishingIdeal t : Set R
) = closure t
· 使用定理 `PrimeSpectrum.vanishingIdeal_singleton`：vanishingIdeal_singleton (x : Pr
imeSpectrum R) : vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal
-/
theorem closure_singleton (x) : closure ({x} : Set (PrimeSpectrum R)) = zeroLocus x.asIdeal := by
  rw [← zeroLocus_vanishingIdeal_eq_closure, vanishingIdeal_singleton]
/-
**PrimeSpectrum.isClosed_singleton_iff_isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `Prim
eSpectrum`。
形式化陈述：isClosed_singleton_iff_isMaximal (x : PrimeSpectrum R) : IsClosed ({x} : S
et (PrimeSpectrum R)) ↔ x.asIdeal.IsMaximal
参数：x : PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_subset_iff_isClosed`：closure_subset_iff_isClosed : closure s sub
seteq s ↔ IsClosed s
· 使用定理 `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanishingId
eal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocus (vanishingIdeal t : Set R
) = closure t
· 使用定理 `PrimeSpectrum.vanishingIdeal_singleton`：vanishingIdeal_singleton (x : Pr
imeSpectrum R) : vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
-/
theorem isClosed_singleton_iff_isMaximal (x : PrimeSpectrum R) :
    IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asIdeal.IsMaximal := by
  rw [← closure_subset_iff_isClosed, ← zeroLocus_vanishingIdeal_eq_closure,
      vanishingIdeal_singleton]
  constructor <;> intro H
  · rcases x.asIdeal.exists_le_maximal x.2.1 with ⟨m, hm, hxm⟩
    exact (congr_arg asIdeal (@H ⟨m, hm.isPrime⟩ hxm)) ▸ hm
  · exact fun p hp ↦ PrimeSpectrum.ext (H.eq_of_le p.2.1 hp).symm
/-
**PrimeSpectrum.isRadical_vanishingIdeal** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectru
m`。
形式化陈述：isRadical_vanishingIdeal (s : Set (PrimeSpectrum R)) : (vanishingIdeal s).
IsRadical
参数：s : Set (PrimeSpectrum R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.vanishingIdeal_closure`：vanishingIdeal_closure (t : Set (P
rimeSpectrum R)) : vanishingIdeal (closure t) = vanishingIdeal t
· 使用定理 `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanishingId
eal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocus (vanishingIdeal t : Set R
) = closure t
· 使用定理 `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`：vanishingIdeal_zeroLo
cus_eq_radical (I : Ideal R) : vanishingIdeal (zeroLocus (I : Set R)) = I.radica
l
· 使用定理 `Ideal.radical_isRadical`：radical_isRadical : (radical I).IsRadical
-/
theorem isRadical_vanishingIdeal (s : Set (PrimeSpectrum R)) : (vanishingIdeal s).IsRadical := by
  rw [← vanishingIdeal_closure, ← zeroLocus_vanishingIdeal_eq_closure,
    vanishingIdeal_zeroLocus_eq_radical]
  apply Ideal.radical_isRadical
/-
**PrimeSpectrum.zeroLocus_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_eq_iff {I J : Ideal R} : zeroLocus (I : Set R) = zeroLocus J ↔ I
.radical = J.radical
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.zeroLocus_radical`：zeroLocus_radical (I : Ideal R) : zeroL
ocus (I.radical : Set R) = zeroLocus I
-/
theorem zeroLocus_eq_iff {I J : Ideal R} :
    zeroLocus (I : Set R) = zeroLocus J ↔ I.radical = J.radical := by
  constructor
  · intro h; simp_rw [← vanishingIdeal_zeroLocus_eq_radical, h]
  · intro h; rw [← zeroLocus_radical, h, zeroLocus_radical]
/-
**PrimeSpectrum.vanishingIdeal_anti_mono_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpe
ctrum`。
形式化陈述：vanishingIdeal_anti_mono_iff {s t : Set (PrimeSpectrum R)} (ht : IsClosed 
t) : s subseteq t ↔ vanishingIdeal t <= vanishingIdeal s
参数：PrimeSpectrum R；ht : IsClosed t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.vanishingIdeal_anti_mono`：vanishingIdeal_anti_mono {s t : 
Set (PrimeSpectrum R)} (h : s subseteq t) : vanishingIdeal t <= vanishingIdeal s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanishingId
eal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocus (vanishingIdeal t : Set R
) = closure t
· 使用定理 `PrimeSpectrum.zeroLocus_anti_mono_ideal`：zeroLocus_anti_mono_ideal {s t 
: Ideal R} (h : s <= t) : zeroLocus (t : Set R) subseteq zeroLocus (s : Set R)
-/
theorem vanishingIdeal_anti_mono_iff {s t : Set (PrimeSpectrum R)} (ht : IsClosed t) :
    s ⊆ t ↔ vanishingIdeal t ≤ vanishingIdeal s :=
  ⟨vanishingIdeal_anti_mono, fun h => by
    rw [← ht.closure_subset_iff, ← ht.closure_eq]
    convert! ← zeroLocus_anti_mono_ideal h <;> apply zeroLocus_vanishingIdeal_eq_closure⟩
/-
**PrimeSpectrum.vanishingIdeal_strict_anti_mono_iff** 是 Mathlib 中的一个定理，位于命名空间 `P
rimeSpectrum`。
形式化陈述：vanishingIdeal_strict_anti_mono_iff {s t : Set (PrimeSpectrum R)} (hs : Is
Closed s) (ht : IsClosed t) : s ⊂ t ↔ vanishingIdeal t < vanishingIdeal s
参数：PrimeSpectrum R；hs : IsClosed s；ht : IsClosed t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ssubset_def`：ssubset_def : (s ⊂ t) = (s subseteq t ∧ ¬t subseteq s)
· 使用定理 `PrimeSpectrum.vanishingIdeal_anti_mono_iff`：vanishingIdeal_anti_mono_iff
 {s t : Set (PrimeSpectrum R)} (ht : IsClosed t) : s subseteq t ↔ vanishingIdeal
 t <= vanishingIdeal s
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem vanishingIdeal_strict_anti_mono_iff {s t : Set (PrimeSpectrum R)} (hs : IsClosed s)
    (ht : IsClosed t) : s ⊂ t ↔ vanishingIdeal t < vanishingIdeal s := by
  rw [Set.ssubset_def, vanishingIdeal_anti_mono_iff hs, vanishingIdeal_anti_mono_iff ht,
    lt_iff_le_not_ge]

/-- The antitone order embedding of closed subsets of `Spec R` into ideals of `R`. -/
/-
**PrimeSpectrum.closedsEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：closedsEmbedding (R : Type*) [CommSemiring R] : (TopologicalSpace.Closeds 
<| PrimeSpectrum R)ᵒᵈ ↪o Ideal R
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The antitone order embedding of closed subsets of `Spec R` into ideals of `R`.
-/
def closedsEmbedding (R : Type*) [CommSemiring R] :
    (TopologicalSpace.Closeds <| PrimeSpectrum R)ᵒᵈ ↪o Ideal R :=
  OrderEmbedding.ofMapLEIff (fun s => vanishingIdeal ↑(OrderDual.ofDual s)) fun s _ =>
    (vanishingIdeal_anti_mono_iff s.2).symm
/-
**PrimeSpectrum.t1Space_iff_isField** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：t1Space_iff_isField [IsDomain R] : T1Space (PrimeSpectrum R) ↔ IsField R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Ring.ne_bot_of_isMaximal_of_not_isField`：ne_bot_of_isMaximal_of_not_isFi
eld [Nontrivial R] {M : Ideal R} (max : M.IsMaximal) (not_field : ¬IsField R) : 
M != ⊥
· 使用定理 `PrimeSpectrum.isClosed_singleton_iff_isMaximal`：isClosed_singleton_iff_i
sMaximal (x : PrimeSpectrum R) : IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asId
eal.IsMaximal
· 使用定理 `T1Space.t1`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T1Space X
] (x : X), IsClosed {x}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.bot_isMaximal`：bot_isMaximal : IsMaximal (⊥ : Ideal K)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.not_isField_iff_exists_prime`：not_isField_iff_exists_prime [Nontriv
ial R] : ¬IsField R ↔ exists p : Ideal R, p != ⊥ ∧ p.IsPrime
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem t1Space_iff_isField [IsDomain R] : T1Space (PrimeSpectrum R) ↔ IsField R := by
  refine ⟨?_, fun h => ?_⟩
  · intro h
    exact
      Classical.not_not.1
        (mt
          (Ring.ne_bot_of_isMaximal_of_not_isField <|
            (isClosed_singleton_iff_isMaximal _).1 (T1Space.t1 ⟨⊥, inferInstance⟩))
          (by simp))
  · refine ⟨fun x => (isClosed_singleton_iff_isMaximal x).2 ?_⟩
    by_cases hx : x.asIdeal = ⊥
    · let := h.toSemifield
      exact hx.symm ▸ Ideal.bot_isMaximal
    · exact absurd h (Ring.not_isField_iff_exists_prime.2 ⟨x.asIdeal, ⟨hx, x.2⟩⟩)

local notation "Z(" a ")" => zeroLocus (a : Set R)
/-
**PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical** 是 Mathlib 中的一个定理，位于命名空间
 `PrimeSpectrum`。
形式化陈述：isIrreducible_zeroLocus_iff_of_radical (I : Ideal R) (hI : I.IsRadical) : 
IsIrreducible (zeroLocus (I : Set R)) ↔ I.IsPrime
参数：I : Ideal R；hI : I.IsRadical。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.isPrime_iff`：isPrime_iff {I : Ideal α} : IsPrime I ↔ I != ⊤ ∧ fora
ll {x y : α}, x * y in I -> x in I ∨ y in I
· 使用定理 `IsIrreducible.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : Se
t X), IsIrreducible s = (s.Nonempty ∧ IsPreirreducible s)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `PrimeSpectrum.zeroLocus_empty_iff_eq_top`：zeroLocus_empty_iff_eq_top {I 
: Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`：vanishingIdeal_zeroLo
cus_eq_radical (I : Ideal R) : vanishingIdeal (zeroLocus (I : Set R)) = I.radica
l
· 使用定理 `Ideal.IsRadical.radical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ide
al R}, I.IsRadical → I.radical = I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsRadical.radical_le_iff`：∀ {R : Type u} [inst : CommSemiring R] {
I J : Ideal R}, J.IsRadical → (I.radical ≤ J ↔ I ≤ J)
· 使用定理 `Ideal.radical_inf`：radical_inf : radical (I ⊓ J) = radical I ⊓ radical J
· 使用定理 `Ideal.radical_mul`：radical_mul : radical (I * J) = radical I ⊓ radical J
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
-/
theorem isIrreducible_zeroLocus_iff_of_radical (I : Ideal R) (hI : I.IsRadical) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.IsPrime := by
  rw [Ideal.isPrime_iff, IsIrreducible]
  apply and_congr
  · rw [Set.nonempty_iff_ne_empty, Ne, zeroLocus_empty_iff_eq_top]
  · trans ∀ x y : Ideal R, Z(I) ⊆ Z(x) ∪ Z(y) → Z(I) ⊆ Z(x) ∨ Z(I) ⊆ Z(y)
    · simp_rw [isPreirreducible_iff_isClosed_union_isClosed, isClosed_iff_zeroLocus_ideal]
      constructor
      · rintro h x y
        exact h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
      · rintro h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact h x y
    · simp_rw [← zeroLocus_inf, subset_zeroLocus_iff_le_vanishingIdeal,
        vanishingIdeal_zeroLocus_eq_radical, hI.radical]
      constructor
      · simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Ideal.span_le, ←
          Ideal.span_singleton_mul_span_singleton]
        refine fun h x y h' => h _ _ ?_
        rw [← hI.radical_le_iff] at h' ⊢
        simpa only [Ideal.radical_inf, Ideal.radical_mul] using h'
      · simp_rw [or_iff_not_imp_left, SetLike.not_le_iff_exists]
        rintro h s t h' ⟨x, hx, hx'⟩ y hy
        exact h (h' ⟨Ideal.mul_mem_right _ _ hx, Ideal.mul_mem_left _ _ hy⟩) hx'
/-
**PrimeSpectrum.isIrreducible_zeroLocus_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpec
trum`。
形式化陈述：isIrreducible_zeroLocus_iff (I : Ideal R) : IsIrreducible (zeroLocus (I : 
Set R)) ↔ I.radical.IsPrime
参数：I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical`：isIrreducible_zero
Locus_iff_of_radical (I : Ideal R) (hI : I.IsRadical) : IsIrreducible (zeroLocus
 (I : Set R)) ↔ I.IsPrime
· 使用定理 `Ideal.radical_isRadical`：radical_isRadical : (radical I).IsRadical
· 使用定理 `PrimeSpectrum.zeroLocus_radical`：zeroLocus_radical (I : Ideal R) : zeroL
ocus (I.radical : Set R) = zeroLocus I
-/
theorem isIrreducible_zeroLocus_iff (I : Ideal R) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.radical.IsPrime :=
  zeroLocus_radical I ▸ isIrreducible_zeroLocus_iff_of_radical _ I.radical_isRadical
/-
**PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime** 是 Mathlib 中的一个定理，位于命名
空间 `PrimeSpectrum`。
形式化陈述：isIrreducible_iff_vanishingIdeal_isPrime {s : Set (PrimeSpectrum R)} : IsI
rreducible s ↔ (vanishingIdeal s).IsPrime
参数：PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isIrreducible_iff_closure`：isIrreducible_iff_closure : IsIrreducible (cl
osure s) ↔ IsIrreducible s
· 使用定理 `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanishingId
eal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocus (vanishingIdeal t : Set R
) = closure t
· 使用定理 `PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical`：isIrreducible_zero
Locus_iff_of_radical (I : Ideal R) (hI : I.IsRadical) : IsIrreducible (zeroLocus
 (I : Set R)) ↔ I.IsPrime
· 使用定理 `PrimeSpectrum.isRadical_vanishingIdeal`：isRadical_vanishingIdeal (s : Se
t (PrimeSpectrum R)) : (vanishingIdeal s).IsRadical
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isIrreducible_iff_vanishingIdeal_isPrime {s : Set (PrimeSpectrum R)} :
    IsIrreducible s ↔ (vanishingIdeal s).IsPrime := by
  rw [← isIrreducible_iff_closure, ← zeroLocus_vanishingIdeal_eq_closure,
    isIrreducible_zeroLocus_iff_of_radical _ (isRadical_vanishingIdeal s)]
/-
**PrimeSpectrum.vanishingIdeal_isIrreducible** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpe
ctrum`。
形式化陈述：vanishingIdeal_isIrreducible : vanishingIdeal (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`：isIrreducible_if
f_vanishingIdeal_isPrime {s : Set (PrimeSpectrum R)} : IsIrreducible s ↔ (vanish
ingIdeal s).IsPrime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical`：isIrreducible_zero
Locus_iff_of_radical (I : Ideal R) (hI : I.IsRadical) : IsIrreducible (zeroLocus
 (I : Set R)) ↔ I.IsPrime
· 使用定理 `Ideal.IsPrime.isRadical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ide
al R}, I.IsPrime → I.IsRadical
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`：vanishingIdeal_zeroLo
cus_eq_radical (I : Ideal R) : vanishingIdeal (zeroLocus (I : Set R)) = I.radica
l
· 使用定理 `Ideal.IsPrime.radical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ideal
 R}, I.IsPrime → I.radical = I
-/
lemma vanishingIdeal_isIrreducible :
    vanishingIdeal (R := R) '' {s | IsIrreducible s} = {P | P.IsPrime} :=
  Set.ext fun I ↦ ⟨fun ⟨_, hs, e⟩ ↦ e ▸ isIrreducible_iff_vanishingIdeal_isPrime.mp hs,
    fun h ↦ ⟨zeroLocus I, (isIrreducible_zeroLocus_iff_of_radical _ h.isRadical).mpr h,
      (vanishingIdeal_zeroLocus_eq_radical I).trans h.radical⟩⟩
/-
**PrimeSpectrum.vanishingIdeal_isClosed_isIrreducible** 是 Mathlib 中的一个引理，位于命名空间 
`PrimeSpectrum`。
形式化陈述：vanishingIdeal_isClosed_isIrreducible : vanishingIdeal (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsIrreducible.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s :
 Set X}, IsIrreducible s → IsIrreducible (closure s)
· 使用定理 `PrimeSpectrum.vanishingIdeal_closure`：vanishingIdeal_closure (t : Set (P
rimeSpectrum R)) : vanishingIdeal (closure t) = vanishingIdeal t
· 使用引理 `PrimeSpectrum.vanishingIdeal_isIrreducible`：vanishingIdeal_isIrreducible
 : vanishingIdeal (R
-/
lemma vanishingIdeal_isClosed_isIrreducible :
    vanishingIdeal (R := R) '' {s | IsClosed s ∧ IsIrreducible s} = {P | P.IsPrime} := by
  refine (subset_antisymm ?_ ?_).trans vanishingIdeal_isIrreducible
  · exact Set.image_mono fun _ ↦ And.right
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨closure s, ⟨isClosed_closure, hs.closure⟩, vanishingIdeal_closure s⟩
/-
**PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical** 是 Mathlib 中的一个引理，位于命名空
间 `PrimeSpectrum`。
形式化陈述：irreducibleSpace_iff_isPrime_nilradical : IrreducibleSpace (PrimeSpectrum 
R) ↔ (nilradical R).IsPrime
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.vanishingIdeal_univ`：∀ {R : Type u} [inst : CommSemiring R
], PrimeSpectrum.vanishingIdeal Set.univ = nilradical R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma irreducibleSpace_iff_isPrime_nilradical :
    IrreducibleSpace (PrimeSpectrum R) ↔ (nilradical R).IsPrime := by
  simp [irreducibleSpace_def, isIrreducible_iff_vanishingIdeal_isPrime]
/-
**PrimeSpectrum.irreducibleSpace** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
形式化陈述：irreducibleSpace [IsDomain R] : IrreducibleSpace (PrimeSpectrum R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nilradical_eq_zero`：nilradical_eq_zero (R : Type*) [CommSemiring R] [IsR
educed R] : nilradical R = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
instance irreducibleSpace [IsDomain R] : IrreducibleSpace (PrimeSpectrum R) := by
  simpa [irreducibleSpace_iff_isPrime_nilradical] using Ideal.isPrime_bot
/-
**PrimeSpectrum.quasiSober** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
形式化陈述：quasiSober : QuasiSober (PrimeSpectrum R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`：isIrreducible_if
f_vanishingIdeal_isPrime {s : Set (PrimeSpectrum R)} : IsIrreducible s ↔ (vanish
ingIdeal s).IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGenericPoint.eq_1`：∀ {α : Type u_1} [inst : TopologicalSpace α] (x : α
) (S : Set α), IsGenericPoint x S = (closure {x} = S)
· 使用定理 `PrimeSpectrum.closure_singleton`：closure_singleton (x) : closure ({x} : 
Set (PrimeSpectrum R)) = zeroLocus x.asIdeal
· 使用定理 `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanishingId
eal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocus (vanishingIdeal t : Set R
) = closure t
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
instance quasiSober : QuasiSober (PrimeSpectrum R) :=
  ⟨fun {S} h₁ h₂ =>
    ⟨⟨_, isIrreducible_iff_vanishingIdeal_isPrime.1 h₁⟩, by
      rw [IsGenericPoint, closure_singleton, zeroLocus_vanishingIdeal_eq_closure, h₂.closure_eq]⟩⟩
/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : Set R) : QuasiSober (zeroLocus I) :=
  (isClosed_zeroLocus I).isClosedEmbedding_subtypeVal.quasiSober

/-- The prime spectrum of a commutative (semi)ring is a compact topological space. -/
/-
**PrimeSpectrum.compactSpace** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
形式化陈述：compactSpace : CompactSpace (PrimeSpectrum R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `compactSpace_of_finite_subfamily_closed`：compactSpace_of_finite_subfamil
y_closed (h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i)) -
> ⋂ i, t i = ∅ -> exists u : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CompleteLattice.IsCompactElement.exists_finset_of_le_iSup`：∀ (α : Type u
_2) [inst : CompleteLattice α] {k : α},   IsCompactElement k → ∀ {ι : Type u_3} 
(f : ι → α), k ≤ ⨆ i, f i → ∃ s, k ≤ ⨆ i ∈ s, f…
· 使用定理 `Ideal.isCompactElement_top`：isCompactElement_top : IsCompactElement (⊤ :
 Ideal α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isClosed_iff_zeroLocus_ideal`：isClosed_iff_zeroLocus_ideal
 (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ exists I : Ideal R, Z = zeroLocus I
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
The prime spectrum of a commutative (semi)ring is a compact topological space.
-/
instance compactSpace : CompactSpace (PrimeSpectrum R) := by
  refine compactSpace_of_finite_subfamily_closed fun S S_closed S_empty ↦ ?_
  choose I hI using fun i ↦ (isClosed_iff_zeroLocus_ideal (S i)).mp (S_closed i)
  simp_rw [hI, ← zeroLocus_iSup, zeroLocus_empty_iff_eq_top, ← top_le_iff] at S_empty ⊢
  exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _
    Ideal.isCompactElement_top _ S_empty

/-- The prime spectrum of a commutative semiring has discrete Zariski topology iff it is finite and
the semiring has Krull dimension zero or is trivial. -/
/-
**PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero** 是 Mathlib 中的一个
定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：discreteTopology_iff_finite_and_krullDimLE_zero : DiscreteTopology (PrimeS
pectrum R) ↔ Finite (PrimeSpectrum R) ∧ Ring.KrullDimLE 0 R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_of_compact_of_discrete`：finite_of_compact_of_discrete [CompactSpa
ce X] [DiscreteTopology X] : Finite X
· 使用引理 `Ring.KrullDimLE.mk₀`：Ring.KrullDimLE.mk₀ (H : forall I : Ideal R, I.IsPr
ime -> I.IsMaximal) : Ring.KrullDimLE 0 R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isClosed_singleton_iff_isMaximal`：isClosed_singleton_iff_i
sMaximal (x : PrimeSpectrum R) : IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asId
eal.IsMaximal
· 使用定理 `discreteTopology_iff_forall_isClosed`：discreteTopology_iff_forall_isClos
ed [TopologicalSpace α] : DiscreteTopology α ↔ forall s : Set α, IsClosed s
· 使用定理 `DiscreteTopology.of_finite_of_isClosed_singleton`：DiscreteTopology.of_fi
nite_of_isClosed_singleton [TopologicalSpace α] [Finite α] (h : forall a : α, Is
Closed {a}) : DiscreteTopology α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instIsMaximalOfIsPrimeOfKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : Com
mSemiring R] (I : Ideal R) [I.IsPrime] [Ring.KrullDimLE 0 R], I.IsMaximal
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime

--- 原说明 ---
The prime spectrum of a commutative semiring has discrete Zariski topology iff i
t is finite and
the semiring has Krull dimension zero or is trivial.
-/
theorem discreteTopology_iff_finite_and_krullDimLE_zero : DiscreteTopology (PrimeSpectrum R) ↔
    Finite (PrimeSpectrum R) ∧ Ring.KrullDimLE 0 R :=
  ⟨fun _ ↦ ⟨finite_of_compact_of_discrete, .mk₀ fun I h ↦ isClosed_singleton_iff_isMaximal ⟨I, h⟩
    |>.mp <| discreteTopology_iff_forall_isClosed.mp ‹_› _⟩, fun ⟨_, _⟩ ↦
    .of_finite_of_isClosed_singleton fun p ↦ (isClosed_singleton_iff_isMaximal p).mpr inferInstance⟩

/-- The prime spectrum of a semiring has discrete Zariski topology iff there are only
finitely many maximal ideals and their intersection is contained in the nilradical. -/
/-
**PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical** 是
 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical : letI s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`：discreteT
opology_iff_finite_and_krullDimLE_zero : DiscreteTopology (PrimeSpectrum R) ↔ Fi
nite (PrimeSpectrum R) ∧ Ring.KrullDimLE 0 R
· 使用引理 `Ring.krullDimLE_zero_iff`：Ring.krullDimLE_zero_iff : Ring.KrullDimLE 0 R
 ↔ forall I : Ideal R, I.IsPrime -> I.IsMaximal
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.coe_ofPred`：Set.coe_ofPred (p : α -> Prop) : ↥{ x | p x } = { x // p
 x }
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `nilradical_eq_sInf`：nilradical_eq_sInf (R : Type*) [CommSemiring R] : ni
lradical R = sInf { J : Ideal R | J.IsPrime }
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `nilradical_le_prime`：nilradical_le_prime (J : Ideal R) [H : J.IsPrime] :
 nilradical R <= J
· 使用定理 `Ideal.IsPrime.inf_le'`：∀ {R : Type u} {ι : Type u_1} [inst : CommSemirin
g R] {s : Finset ι} {f : ι → Ideal R} {P : Ideal R},   P.IsPrime → (s.inf f ≤ P 
↔ ∃ i ∈ s, …
· 使用定理 `Finset.inf_id_eq_sInf`：∀ {α : Type u_2} [inst : CompleteLattice α] (s : 
Finset α), s.inf id = sInf ↑s
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤

--- 原说明 ---
The prime spectrum of a semiring has discrete Zariski topology iff there are onl
y
finitely many maximal ideals and their intersection is contained in the nilradic
al.
-/
theorem discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical :
    letI s := {I : Ideal R | I.IsMaximal}
    DiscreteTopology (PrimeSpectrum R) ↔ Finite s ∧ sInf s ≤ nilradical R := by
  rw [discreteTopology_iff_finite_and_krullDimLE_zero, Ring.krullDimLE_zero_iff,
    (equivSubtype R).finite_iff, ← Set.coe_ofPred, Set.finite_coe_iff, Set.finite_coe_iff]
  refine ⟨fun h ↦ ⟨h.1.subset fun _ h ↦ h.isPrime, nilradical_eq_sInf R ▸ sInf_le_sInf h.2⟩,
    fun ⟨fin, le⟩ ↦ ?_⟩
  have hpm (I : Ideal R) (hI : I.IsPrime) : I.IsMaximal := by
    replace le := le.trans (nilradical_le_prime I)
    rw [← fin.coe_toFinset, ← Finset.inf_id_eq_sInf, hI.inf_le'] at le
    have ⟨M, hM, hMI⟩ := le
    rw [fin.mem_toFinset] at hM
    rwa [← hM.eq_of_le hI.1 hMI]
  exact ⟨fin.subset hpm, hpm⟩
/-
**PrimeSpectrum.discreteTopology_of_toLocalization_surjective** 是 Mathlib 中的一个定理
，位于命名空间 `PrimeSpectrum`。
形式化陈述：discreteTopology_of_toLocalization_surjective (surj : Function.Surjective 
(toPiLocalization R)) : DiscreteTopology (PrimeSpectrum R)
参数：surj : Function.Surjective (toPiLocalization R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`：discreteT
opology_iff_finite_and_krullDimLE_zero : DiscreteTopology (PrimeSpectrum R) ↔ Fi
nite (PrimeSpectrum R) ∧ Ring.KrullDimLE 0 R
· 使用定理 `PrimeSpectrum.finite_of_toPiLocalization_surjective`：finite_of_toPiLocal
ization_surjective (surj : Function.Surjective (toPiLocalization R)) : Finite (P
rimeSpectrum R)
· 使用引理 `Ring.KrullDimLE.mk₀`：Ring.KrullDimLE.mk₀ (H : forall I : Ideal R, I.IsPr
ime -> I.IsMaximal) : Ring.KrullDimLE 0 R
· 使用定理 `PrimeSpectrum.isMaximal_of_toPiLocalization_surjective`：isMaximal_of_toP
iLocalization_surjective (surj : Function.Surjective (toPiLocalization R)) (I : 
PrimeSpectrum R) : I.1.IsMaximal
-/
theorem discreteTopology_of_toLocalization_surjective
    (surj : Function.Surjective (toPiLocalization R)) :
    DiscreteTopology (PrimeSpectrum R) :=
  discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨finite_of_toPiLocalization_surjective
    surj, .mk₀ fun I prime ↦ isMaximal_of_toPiLocalization_surjective surj ⟨I, prime⟩⟩

section Comap

variable {S' : Type*} [CommSemiring S']

@[fun_prop]
/-
**PrimeSpectrum.continuous_comap** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：continuous_comap (f : R ->+* S) : Continuous (comap f)
参数：f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PrimeSpectrum.preimage_comap_zeroLocus_aux`：preimage_comap_zeroLocus_aux
 (f : R ->+* S) (s : Set R) : comap f ⁻¹' zeroLocus s = zeroLocus (f '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma continuous_comap (f : R →+* S) : Continuous (comap f) := by
  simp only [continuous_iff_isClosed, isClosed_iff_zeroLocus]
  rintro _ ⟨s, rfl⟩
  exact ⟨_, preimage_comap_zeroLocus_aux f s⟩

variable (f : R →+* S)

variable (S)
/-
**PrimeSpectrum.localization_comap_injective** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpe
ctrum`。
形式化陈述：localization_comap_injective [Algebra R S] (M : Submonoid R) [IsLocalizati
on M S] : Function.Injective (comap (algebraMap R S))
参数：M : Submonoid R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.map_under`：map_under (J : Ideal S) : Ideal.map (algebraMa
p R S) (J.under R) = J
-/
theorem localization_comap_injective [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Function.Injective (comap (algebraMap R S)) := by
  intro p q h
  replace h := _root_.congr_arg (fun x : PrimeSpectrum R => Ideal.map (algebraMap R S) x.asIdeal) h
  dsimp only [comap] at h
  rw [IsLocalization.map_under M S, IsLocalization.map_under M S] at h
  ext1
  exact h
/-
**PrimeSpectrum.localization_comap_range** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectru
m`。
形式化陈述：localization_comap_range [Algebra R S] (M : Submonoid R) [IsLocalization M
 S] : Set.range (comap (algebraMap R S)) = { p | Disjoint (M : Set R) p.asIdeal 
}
参数：M : Submonoid R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.isPrime_iff_isPrime_disjoint`：isPrime_iff_isPrime_disjoin
t (J : Ideal S) : J.IsPrime ↔ (J.under R).IsPrime ∧ Disjoint (M : Set R) (J.unde
r R)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsLocalization.isPrime_of_isPrime_disjoint`：isPrime_of_isPrime_disjoint 
(I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) : (Ideal.map (alge
braMap R S) I).IsPrime
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
-/
theorem localization_comap_range [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Set.range (comap (algebraMap R S)) = { p | Disjoint (M : Set R) p.asIdeal } := by
  refine Set.ext fun x ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨p, rfl⟩
    exact ((IsLocalization.isPrime_iff_isPrime_disjoint ..).mp p.2).2
  · use ⟨x.asIdeal.map (algebraMap R S), IsLocalization.isPrime_of_isPrime_disjoint M S _ x.2 h⟩
    ext1
    exact IsLocalization.under_map_of_isPrime_disjoint M S x.2 h
/-
**PrimeSpectrum.localization_comap_isInducing** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSp
ectrum`。
形式化陈述：localization_comap_isInducing [Algebra R S] (M : Submonoid R) [IsLocalizat
ion M S] : IsInducing (comap (algebraMap R S))
参数：M : Submonoid R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext_isClosed`：∀ {X : Type u_2} {t₁ t₂ : TopologicalSpac
e X}, (∀ (s : Set X), IsClosed s ↔ IsClosed s) → t₁ = t₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `PrimeSpectrum.preimage_comap_zeroLocus`：preimage_comap_zeroLocus (s : Se
t R) : comap f ⁻¹' zeroLocus s = zeroLocus (f '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
· 使用定理 `Ideal.map.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semir
ing R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   (I : Ideal R), I
deal…
· 使用定理 `IsLocalization.map_under`：map_under (J : Ideal S) : Ideal.map (algebraMa
p R S) (J.under R) = J
-/
theorem localization_comap_isInducing [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    IsInducing (comap (algebraMap R S)) := by
  refine ⟨TopologicalSpace.ext_isClosed fun Z ↦ ?_⟩
  simp_rw [isClosed_induced_iff, isClosed_iff_zeroLocus, @eq_comm _ _ (zeroLocus _),
    exists_exists_eq_and, preimage_comap_zeroLocus]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨(Ideal.span s).comap (algebraMap R S), ?_⟩
    rw [← zeroLocus_span, ← zeroLocus_span s, ← Ideal.map, IsLocalization.map_under M S]
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩
/-
**PrimeSpectrum.localization_comap_isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `PrimeS
pectrum`。
形式化陈述：localization_comap_isEmbedding [Algebra R S] (M : Submonoid R) [IsLocaliza
tion M S] : IsEmbedding (comap (algebraMap R S))
参数：M : Submonoid R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.localization_comap_isInducing`：localization_comap_isInduci
ng [Algebra R S] (M : Submonoid R) [IsLocalization M S] : IsInducing (comap (alg
ebraMap R S))
· 使用定理 `PrimeSpectrum.localization_comap_injective`：localization_comap_injective
 [Algebra R S] (M : Submonoid R) [IsLocalization M S] : Function.Injective (coma
p (algebraMap R S))
-/
theorem localization_comap_isEmbedding [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    IsEmbedding (comap (algebraMap R S)) :=
  ⟨localization_comap_isInducing S M, localization_comap_injective S M⟩

open Function RingHom
/-
**PrimeSpectrum.comap_isInducing_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `PrimeS
pectrum`。
形式化陈述：comap_isInducing_of_surjective (hf : Surjective f) : IsInducing (comap f) 
where eq_induced
参数：hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PrimeSpectrum.preimage_comap_zeroLocus`：preimage_comap_zeroLocus (s : Se
t R) : comap f ⁻¹' zeroLocus s = zeroLocus (f '' s)
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem comap_isInducing_of_surjective (hf : Surjective f) : IsInducing (comap f) where
  eq_induced := by
    simp only [TopologicalSpace.ext_iff, ← isClosed_compl_iff, isClosed_iff_zeroLocus,
      isClosed_induced_iff]
    refine fun s =>
      ⟨fun ⟨F, hF⟩ =>
        ⟨zeroLocus (f ⁻¹' F), ⟨f ⁻¹' F, rfl⟩, by
          rw [preimage_comap_zeroLocus, Function.Surjective.image_preimage hf, hF]⟩,
        ?_⟩
    rintro ⟨-, ⟨F, rfl⟩, hF⟩
    exact ⟨f '' F, hF.symm.trans (preimage_comap_zeroLocus f F)⟩

/-- The embedding has closed range if the domain (and therefore the codomain) is a ring,
  see `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`.
  On the other hand, `comap (Nat.castRingHom (ZMod 2))` does not have closed range. -/
/-
**PrimeSpectrum.isEmbedding_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Prime
Spectrum`。
形式化陈述：isEmbedding_comap_of_surjective (hf : Surjective f) : IsEmbedding (comap f
)
参数：hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.isEmbedding_iff`：∀ {X : Type u_1} {Y : Type u_2} [tX : Topologi
calSpace X] [tY : TopologicalSpace Y] (f : X → Y),   Topology.IsEmbedding f ↔ To
pology.IsInduc…
· 使用定理 `PrimeSpectrum.comap_isInducing_of_surjective`：comap_isInducing_of_surjec
tive (hf : Surjective f) : IsInducing (comap f) where eq_induced
· 使用定理 `PrimeSpectrum.comap_injective_of_surjective`：comap_injective_of_surjecti
ve (f : R ->+* S) (hf : Function.Surjective f) : Function.Injective (comap f)

--- 原说明 ---
The embedding has closed range if the domain (and therefore the codomain) is a r
ing,
  see `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`.
  On the other hand, `comap (Nat.castRingHom (ZMod 2))` does not have closed ran
ge.
-/
theorem isEmbedding_comap_of_surjective (hf : Surjective f) : IsEmbedding (comap f) :=
  (isEmbedding_iff _).2 ⟨comap_isInducing_of_surjective _ _ hf, comap_injective_of_surjective f hf⟩

end Comap

/-- Homeomorphism between prime spectra induced by an isomorphism of semirings. -/
/-
**PrimeSpectrum.homeomorphOfRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：homeomorphOfRingEquiv (e : R ≃+* S) : PrimeSpectrum R ≃ₜ PrimeSpectrum S w
here toFun
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homeomorphism between prime spectra induced by an isomorphism of semirings.
-/
def homeomorphOfRingEquiv (e : R ≃+* S) : PrimeSpectrum R ≃ₜ PrimeSpectrum S where
  toFun := comap (e.symm : S →+* R)
  invFun := comap (e : R →+* S)
  left_inv _ := (comap_comp_apply ..).symm.trans (by simp)
  right_inv _ := (comap_comp_apply ..).symm.trans (by simp)
/-
**PrimeSpectrum.isHomeomorph_comap_of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Prime
Spectrum`。
形式化陈述：isHomeomorph_comap_of_bijective {f : R ->+* S} (hf : Function.Bijective f)
 : IsHomeomorph (comap f)
参数：hf : Function.Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
lemma isHomeomorph_comap_of_bijective {f : R →+* S} (hf : Function.Bijective f) :
    IsHomeomorph (comap f) := (homeomorphOfRingEquiv (.ofBijective f hf)).symm.isHomeomorph

end CommSemiring

section SpecOfSurjective

/-! The comap of a surjective ring homomorphism is a closed embedding between the prime spectra. -/


open Function RingHom

variable [CommRing R] [CommRing S]
variable (f : R →+* S)
variable {R}

/-
**PrimeSpectrum.comap_singleton_isClosed_of_surjective** 是 Mathlib 中的一个定理，位于命名空间
 `PrimeSpectrum`。
形式化陈述：comap_singleton_isClosed_of_surjective (f : R ->+* S) (hf : Function.Surje
ctive f) (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) : I
sClosed ({comap f x} : Set (PrimeSpectrum R))
参数：f : R ->+* S；hf : Function.Surjective f；x : PrimeSpectrum S；hx : IsClosed ({x
} : Set (PrimeSpectrum S))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrimeSpectrum.isClosed_singleton_iff_isMaximal`：isClosed_singleton_iff_i
sMaximal (x : PrimeSpectrum R) : IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asId
eal.IsMaximal
· 使用定理 `Ideal.comap_isMaximal_of_surjective`：comap_isMaximal_of_surjective (hf :
 Function.Surjective f) {K : Ideal S} [H : IsMaximal K] : IsMaximal (comap f K)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem comap_singleton_isClosed_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) :
    IsClosed ({comap f x} : Set (PrimeSpectrum R)) :=
  haveI : x.asIdeal.IsMaximal := (isClosed_singleton_iff_isMaximal x).1 hx
  (isClosed_singleton_iff_isMaximal _).2 (Ideal.comap_isMaximal_of_surjective f hf)
/-
**PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical** 是 Mathlib 中的一个引理，位
于命名空间 `PrimeSpectrum`。
形式化陈述：comap_quotientMk_bijective_of_le_nilradical {I : Ideal R} (hle : I <= nilr
adical R) : Function.Bijective (comap <| Ideal.Quotient.mk I)
参数：hle : I <= nilradical R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `PrimeSpectrum.comap_injective_of_surjective`：comap_injective_of_surjecti
ve (f : R ->+* S) (hf : Function.Surjective f) : Function.Injective (comap f)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `range_comap_of_surjective`：range_comap_of_surjective (hf : Surjective f)
 : Set.range (comap f) = zeroLocus (ker f)
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
-/
lemma comap_quotientMk_bijective_of_le_nilradical {I : Ideal R} (hle : I ≤ nilradical R) :
    Function.Bijective (comap <| Ideal.Quotient.mk I) := by
  refine ⟨comap_injective_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  simpa [← Set.range_eq_univ, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    zeroLocus_eq_univ_iff]
/-
**PrimeSpectrum.isClosed_range_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Pr
imeSpectrum`。
形式化陈述：isClosed_range_comap_of_surjective (hf : Surjective f) : IsClosed (Set.ran
ge (comap f))
参数：hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `range_comap_of_surjective`：range_comap_of_surjective (hf : Surjective f)
 : Set.range (comap f) = zeroLocus (ker f)
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
-/
theorem isClosed_range_comap_of_surjective (hf : Surjective f) :
    IsClosed (Set.range (comap f)) := by
  rw [range_comap_of_surjective _ f hf]
  exact isClosed_zeroLocus _
/-
**PrimeSpectrum.isClosedEmbedding_comap_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 
`PrimeSpectrum`。
形式化陈述：isClosedEmbedding_comap_of_surjective (hf : Surjective f) : IsClosedEmbedd
ing (comap f) where toIsInducing
参数：hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.comap_isInducing_of_surjective`：comap_isInducing_of_surjec
tive (hf : Surjective f) : IsInducing (comap f) where eq_induced
· 使用定理 `PrimeSpectrum.comap_injective_of_surjective`：comap_injective_of_surjecti
ve (f : R ->+* S) (hf : Function.Surjective f) : Function.Injective (comap f)
· 使用定理 `PrimeSpectrum.isClosed_range_comap_of_surjective`：isClosed_range_comap_o
f_surjective (hf : Surjective f) : IsClosed (Set.range (comap f))
-/
lemma isClosedEmbedding_comap_of_surjective (hf : Surjective f) : IsClosedEmbedding (comap f) where
  toIsInducing := comap_isInducing_of_surjective S f hf
  injective := comap_injective_of_surjective f hf
  isClosed_range := isClosed_range_comap_of_surjective S f hf

end SpecOfSurjective

section SpecProd

variable {R S} [CommSemiring R] [CommSemiring S]

/-
**PrimeSpectrum.primeSpectrumProd_symm_inl** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpect
rum`。
形式化陈述：primeSpectrumProd_symm_inl (x) : (primeSpectrumProd R S).symm (.inl x) = c
omap (RingHom.fst R S) x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PrimeSpectrum.primeSpectrumProd_symm_inl_asIdeal`：primeSpectrumProd_symm
_inl_asIdeal (x : PrimeSpectrum R) : ((primeSpectrumProd R S).symm <| Sum.inl x)
.asIdeal = Ideal.prod x.asIdeal ⊤
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma primeSpectrumProd_symm_inl (x) :
    (primeSpectrumProd R S).symm (.inl x) = comap (RingHom.fst R S) x := by
  ext; simp [Ideal.prod]
/-
**PrimeSpectrum.primeSpectrumProd_symm_inr** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpect
rum`。
形式化陈述：primeSpectrumProd_symm_inr (x) : (primeSpectrumProd R S).symm (.inr x) = c
omap (RingHom.snd R S) x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PrimeSpectrum.primeSpectrumProd_symm_inr_asIdeal`：primeSpectrumProd_symm
_inr_asIdeal (x : PrimeSpectrum S) : ((primeSpectrumProd R S).symm <| Sum.inr x)
.asIdeal = Ideal.prod ⊤ x.asIdeal
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma primeSpectrumProd_symm_inr (x) :
    (primeSpectrumProd R S).symm (.inr x) = comap (RingHom.snd R S) x := by
  ext; simp [Ideal.prod]
/-
**PrimeSpectrum.range_comap_fst** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：range_comap_fst : Set.range (comap (RingHom.fst R S)) = zeroLocus (RingHom
.ker (RingHom.fst R S))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.ideal_prod_prime`：ideal_prod_prime (I : Ideal (R × S)) : I.IsPrime
 ↔ (exists p : Ideal R, p.IsPrime ∧ I = Ideal.prod p ⊤) ∨ exists p : Ideal S, p.
IsPrime ∧ I …
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_comap_fst :
    Set.range (comap (RingHom.fst R S)) = zeroLocus (RingHom.ker (RingHom.fst R S)) := by
  refine Set.ext fun p ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨I, hI, rfl⟩; exact Ideal.comap_mono bot_le
  obtain ⟨p, hp, eq⟩ | ⟨p, hp, eq⟩ := p.1.ideal_prod_prime.mp p.2
  · exact ⟨⟨p, hp⟩, PrimeSpectrum.ext <| by simpa [Ideal.prod] using eq.symm⟩
  · refine (hp.ne_top <| (Ideal.eq_top_iff_one _).mpr ?_).elim
    simpa [eq] using h (show (0, 1) ∈ RingHom.ker (RingHom.fst R S) by simp)
/-
**PrimeSpectrum.range_comap_snd** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：range_comap_snd : Set.range (comap (RingHom.snd R S)) = zeroLocus (RingHom
.ker (RingHom.snd R S))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.ideal_prod_prime`：ideal_prod_prime (I : Ideal (R × S)) : I.IsPrime
 ↔ (exists p : Ideal R, p.IsPrime ∧ I = Ideal.prod p ⊤) ∨ exists p : Ideal S, p.
IsPrime ∧ I …
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
-/
lemma range_comap_snd :
    Set.range (comap (RingHom.snd R S)) = zeroLocus (RingHom.ker (RingHom.snd R S)) := by
  refine Set.ext fun p ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨I, hI, rfl⟩; exact Ideal.comap_mono bot_le
  obtain ⟨p, hp, eq⟩ | ⟨p, hp, eq⟩ := p.1.ideal_prod_prime.mp p.2
  · refine (hp.ne_top <| (Ideal.eq_top_iff_one _).mpr ?_).elim
    simpa [eq] using h (show (1, 0) ∈ RingHom.ker (RingHom.snd R S) by simp)
  · exact ⟨⟨p, hp⟩, PrimeSpectrum.ext <| by simpa [Ideal.prod] using eq.symm⟩
/-
**PrimeSpectrum.isClosedEmbedding_comap_fst** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpec
trum`。
形式化陈述：isClosedEmbedding_comap_fst : IsClosedEmbedding (comap (RingHom.fst R S))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.isClosedEmbedding_iff`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] (f : X → Y),   Topology.IsClosedEmbe
dding f ↔ Topology.I…
· 使用定理 `PrimeSpectrum.isEmbedding_comap_of_surjective`：isEmbedding_comap_of_surj
ective (hf : Surjective f) : IsEmbedding (comap f)
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.range_comap_fst`：range_comap_fst : Set.range (comap (RingH
om.fst R S)) = zeroLocus (RingHom.ker (RingHom.fst R S))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma isClosedEmbedding_comap_fst : IsClosedEmbedding (comap (RingHom.fst R S)) :=
  (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.fst_surjective, by
    simp_rw [range_comap_fst, isClosed_zeroLocus]⟩
/-
**PrimeSpectrum.isClosedEmbedding_comap_snd** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpec
trum`。
形式化陈述：isClosedEmbedding_comap_snd : IsClosedEmbedding (comap (RingHom.snd R S))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.isClosedEmbedding_iff`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] (f : X → Y),   Topology.IsClosedEmbe
dding f ↔ Topology.I…
· 使用定理 `PrimeSpectrum.isEmbedding_comap_of_surjective`：isEmbedding_comap_of_surj
ective (hf : Surjective f) : IsEmbedding (comap f)
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.range_comap_snd`：range_comap_snd : Set.range (comap (RingH
om.snd R S)) = zeroLocus (RingHom.ker (RingHom.snd R S))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma isClosedEmbedding_comap_snd : IsClosedEmbedding (comap (RingHom.snd R S)) :=
  (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.snd_surjective, by
    simp_rw [range_comap_snd, isClosed_zeroLocus]⟩

/-- The prime spectrum of `R × S` is homeomorphic
to the disjoint union of `PrimeSpectrum R` and `PrimeSpectrum S`. -/
noncomputable
/-
**PrimeSpectrum.primeSpectrumProdHomeo** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`
。
形式化陈述：primeSpectrumProdHomeo : PrimeSpectrum (R × S) ≃ₜ PrimeSpectrum R oplus Pr
imeSpectrum S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def primeSpectrumProdHomeo :
    PrimeSpectrum (R × S) ≃ₜ PrimeSpectrum R ⊕ PrimeSpectrum S := by
  refine ((primeSpectrumProd R S).symm.toHomeomorphOfIsInducing ?_).symm
  refine (IsClosedEmbedding.of_continuous_injective_isClosedMap ?_
    (Equiv.injective _) ?_).isInducing
  · rw [continuous_sum_dom]
    simp only [Function.comp_def, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
    exact ⟨continuous_comap _, continuous_comap _⟩
  · simp_rw [isClosedMap_sum, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
    exact ⟨isClosedEmbedding_comap_fst.isClosedMap, isClosedEmbedding_comap_snd.isClosedMap⟩

end SpecProd

section CommSemiring

variable [CommSemiring R] [CommSemiring S]
variable {R S}

section BasicOpen

/-- `basicOpen r` is the open subset containing all prime ideals not containing `r`. -/
/-
**PrimeSpectrum.basicOpen** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：basicOpen (r : R) : TopologicalSpace.Opens (PrimeSpectrum R) where carrier
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`basicOpen r` is the open subset containing all prime ideals not containing `r`.
-/
def basicOpen (r : R) : TopologicalSpace.Opens (PrimeSpectrum R) where
  carrier := { x | r ∉ x.asIdeal }
  is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans <| Classical.not_not.symm⟩

@[simp]
/-
**PrimeSpectrum.mem_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：mem_basicOpen (f : R) (x : PrimeSpectrum R) : x in basicOpen f ↔ f ∉ x.asI
deal
参数：f : R；x : PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_basicOpen (f : R) (x : PrimeSpectrum R) : x ∈ basicOpen f ↔ f ∉ x.asIdeal :=
  Iff.rfl
/-
**PrimeSpectrum.isOpen_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isOpen_basicOpen {a : R} : IsOpen (basicOpen a : Set (PrimeSpectrum R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
-/
theorem isOpen_basicOpen {a : R} : IsOpen (basicOpen a : Set (PrimeSpectrum R)) :=
  (basicOpen a).isOpen

@[simp]
/-
**PrimeSpectrum.basicOpen_eq_zeroLocus_compl** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpe
ctrum`。
形式化陈述：basicOpen_eq_zeroLocus_compl (r : R) : (basicOpen r : Set (PrimeSpectrum R
)) = (zeroLocus {r})ᶜ
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem basicOpen_eq_zeroLocus_compl (r : R) :
    (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ :=
  Set.ext fun x => by simp only [SetLike.mem_coe, mem_basicOpen, Set.mem_compl_iff, mem_zeroLocus,
    Set.singleton_subset_iff]

@[simp]
/-
**PrimeSpectrum.basicOpen_one** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：basicOpen_one : basicOpen (1 : R) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `PrimeSpectrum.zeroLocus_singleton_one`：zeroLocus_singleton_one : zeroLoc
us ({1} : Set R) = ∅
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basicOpen_one : basicOpen (1 : R) = ⊤ :=
  TopologicalSpace.Opens.ext <| by simp

@[simp]
/-
**PrimeSpectrum.basicOpen_zero** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：basicOpen_zero : basicOpen (0 : R) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `PrimeSpectrum.zeroLocus_singleton_zero`：zeroLocus_singleton_zero : zeroL
ocus ({0} : Set R) = Set.univ
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basicOpen_zero : basicOpen (0 : R) = ⊥ :=
  TopologicalSpace.Opens.ext <| by simp
/-
**PrimeSpectrum.basicOpen_le_basicOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpect
rum`。
形式化陈述：basicOpen_le_basicOpen_iff (f g : R) : basicOpen f <= basicOpen g ↔ f in (
Ideal.span ({g} : Set R)).radical
参数：f g : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `PrimeSpectrum.zeroLocus_subset_zeroLocus_singleton_iff`：zeroLocus_subset
_zeroLocus_singleton_iff (f g : R) : zeroLocus ({f} : Set R) subseteq zeroLocus 
{g} ↔ g in (Ideal.span ({f} : Set R)).radica…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem basicOpen_le_basicOpen_iff (f g : R) :
    basicOpen f ≤ basicOpen g ↔ f ∈ (Ideal.span ({g} : Set R)).radical := by
  rw [← SetLike.coe_subset_coe, basicOpen_eq_zeroLocus_compl, basicOpen_eq_zeroLocus_compl,
    Set.compl_subset_compl, zeroLocus_subset_zeroLocus_singleton_iff]
/-
**PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit** 是 Mathlib 中的一个定理，
位于命名空间 `PrimeSpectrum`。
形式化陈述：basicOpen_le_basicOpen_iff_algebraMap_isUnit {f g : R} [Algebra R S] [IsLo
calization.Away f S] : basicOpen f <= basicOpen g ↔ IsUnit (algebraMap R S g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsLocalization.Away.algebraMap_isUnit_iff`：algebraMap_isUnit_iff {y : R}
 : IsUnit (algebraMap R S y) ↔ exists n, y ∣ x ^ n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem basicOpen_le_basicOpen_iff_algebraMap_isUnit {f g : R} [Algebra R S]
    [IsLocalization.Away f S] : basicOpen f ≤ basicOpen g ↔ IsUnit (algebraMap R S g) := by
  simp_rw [basicOpen_le_basicOpen_iff, Ideal.mem_radical_iff, Ideal.mem_span_singleton,
    IsLocalization.Away.algebraMap_isUnit_iff f]
/-
**PrimeSpectrum.basicOpen_mul** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：basicOpen_mul (f g : R) : basicOpen (f * g) = basicOpen f ⊓ basicOpen g
参数：f g : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `PrimeSpectrum.zeroLocus_singleton_mul`：zeroLocus_singleton_mul (f g : R)
 : zeroLocus ({f * g} : Set R) = zeroLocus {f} union zeroLocus {g}
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basicOpen_mul (f g : R) : basicOpen (f * g) = basicOpen f ⊓ basicOpen g :=
  TopologicalSpace.Opens.ext <| by simp [zeroLocus_singleton_mul]
/-
**PrimeSpectrum.basicOpen_mul_le_left** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：basicOpen_mul_le_left (f g : R) : basicOpen (f * g) <= basicOpen f
参数：f g : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.basicOpen_mul`：basicOpen_mul (f g : R) : basicOpen (f * g)
 = basicOpen f ⊓ basicOpen g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem basicOpen_mul_le_left (f g : R) : basicOpen (f * g) ≤ basicOpen f := by
  rw [basicOpen_mul f g]
  exact inf_le_left
/-
**PrimeSpectrum.basicOpen_mul_le_right** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`
。
形式化陈述：basicOpen_mul_le_right (f g : R) : basicOpen (f * g) <= basicOpen g
参数：f g : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.basicOpen_mul`：basicOpen_mul (f g : R) : basicOpen (f * g)
 = basicOpen f ⊓ basicOpen g
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem basicOpen_mul_le_right (f g : R) : basicOpen (f * g) ≤ basicOpen g := by
  rw [basicOpen_mul f g]
  exact inf_le_right

@[simp]
/-
**PrimeSpectrum.basicOpen_pow** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：basicOpen_pow (f : R) (n : Nat) (hn : 0 < n) : basicOpen (f ^ n) = basicOp
en f
参数：f : R；n : Nat；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `PrimeSpectrum.zeroLocus_singleton_pow`：zeroLocus_singleton_pow (f : R) (
n : Nat) (hn : 0 < n) : zeroLocus ({f ^ n} : Set R) = zeroLocus {f}
-/
theorem basicOpen_pow (f : R) (n : ℕ) (hn : 0 < n) : basicOpen (f ^ n) = basicOpen f :=
  TopologicalSpace.Opens.ext <| by simpa using zeroLocus_singleton_pow f n hn
/-
**PrimeSpectrum.le_basicOpen_pow** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：le_basicOpen_pow (r : R) (n : Nat) : basicOpen r <= basicOpen (r ^ n)
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `PrimeSpectrum.basicOpen_one`：basicOpen_one : basicOpen (1 : R) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.basicOpen_pow`：basicOpen_pow (f : R) (n : Nat) (hn : 0 < n
) : basicOpen (f ^ n) = basicOpen f
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma le_basicOpen_pow (r : R) (n : ℕ) : basicOpen r ≤ basicOpen (r ^ n) := by
  cases n <;> simp
/-
**PrimeSpectrum.isTopologicalBasis_basic_opens** 是 Mathlib 中的一个定理，位于命名空间 `PrimeS
pectrum`。
形式化陈述：isTopologicalBasis_basic_opens : TopologicalSpace.IsTopologicalBasis (Set.
range fun r : R => (basicOpen r : Set (PrimeSpectrum R)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `PrimeSpectrum.isOpen_basicOpen`：isOpen_basicOpen {a : R} : IsOpen (basic
Open a : Set (PrimeSpectrum R))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `PrimeSpectrum.mem_zeroLocus`：mem_zeroLocus (x : PrimeSpectrum R) (s : Se
t R) : x in zeroLocus s ↔ s subseteq x.asIdeal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `PrimeSpectrum.zeroLocus_anti_mono`：zeroLocus_anti_mono {s t : Set R} (h 
: s subseteq t) : zeroLocus t subseteq zeroLocus s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem isTopologicalBasis_basic_opens :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun r : R => (basicOpen r : Set (PrimeSpectrum R))) := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact isOpen_basicOpen
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U, Set.mem_compl_iff, ← hs, mem_zeroLocus, Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine ⟨basicOpen f, ⟨f, rfl⟩, hfp, ?_⟩
    rw [← Set.compl_subset_compl, ← hs, basicOpen_eq_zeroLocus_compl, compl_compl]
    exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr hfs)
/-
**PrimeSpectrum.eq_biUnion_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：eq_biUnion_of_isOpen {s : Set (PrimeSpectrum R)} (hs : IsOpen s) : s = ⋃ (
r : R) (_ : ↑(basicOpen r) subseteq s), basicOpen r
参数：PrimeSpectrum R；hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion'`：∀ {α : Type u} [t :
 TopologicalSpace α] {B : Set (Set α)},   TopologicalSpace.IsTopologicalBasis B 
→ ∀ {u : Set α}, IsOpen u → u = ⋃₀ {s | s…
· 使用定理 `PrimeSpectrum.isTopologicalBasis_basic_opens`：isTopologicalBasis_basic_o
pens : TopologicalSpace.IsTopologicalBasis (Set.range fun r : R => (basicOpen r 
: Set (PrimeSpectrum R)))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_biUnion_of_isOpen {s : Set (PrimeSpectrum R)} (hs : IsOpen s) :
    s = ⋃ (r : R) (_ : ↑(basicOpen r) ⊆ s), basicOpen r :=
  (isTopologicalBasis_basic_opens.open_eq_sUnion' hs).trans <| by aesop
/-
**PrimeSpectrum.isBasis_basic_opens** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isBasis_basic_opens : TopologicalSpace.Opens.IsBasis (Set.range (@basicOpe
n R _))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `PrimeSpectrum.isTopologicalBasis_basic_opens`：isTopologicalBasis_basic_o
pens : TopologicalSpace.IsTopologicalBasis (Set.range fun r : R => (basicOpen r 
: Set (PrimeSpectrum R)))
-/
theorem isBasis_basic_opens : TopologicalSpace.Opens.IsBasis (Set.range (@basicOpen R _)) := by
  unfold TopologicalSpace.Opens.IsBasis
  convert! isTopologicalBasis_basic_opens (R := R)
  rw [← Set.range_comp]
  rfl

@[simp]
/-
**PrimeSpectrum.basicOpen_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：basicOpen_eq_bot_iff (f : R) : basicOpen f = ⊥ ↔ IsNilpotent f
参数：f : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.coe_inj`：coe_inj {U V : Opens α} : (U : Set α) = 
V ↔ U = V
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem basicOpen_eq_bot_iff (f : R) : basicOpen f = ⊥ ↔ IsNilpotent f := by
  rw [← TopologicalSpace.Opens.coe_inj, basicOpen_eq_zeroLocus_compl]
  simp only [Set.eq_univ_iff_forall, Set.singleton_subset_iff, TopologicalSpace.Opens.coe_bot,
    nilpotent_iff_mem_prime, Set.compl_empty_iff, mem_zeroLocus, SetLike.mem_coe]
  exact ⟨fun h I hI => h ⟨I, hI⟩, fun h ⟨I, hI⟩ => h I hI⟩
/-
**PrimeSpectrum.localization_away_comap_range** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSp
ectrum`。
形式化陈述：localization_away_comap_range (S : Type v) [CommSemiring S] [Algebra R S] 
(r : R) [IsLocalization.Away r S] : Set.range (comap (algebraMap R S)) = basicOp
en r
参数：S : Type v；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.localization_comap_range`：localization_comap_range [Algebr
a R S] (M : Submonoid R) [IsLocalization M S] : Set.range (comap (algebraMap R S
)) = { p | Disjoint (M : Set…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `Submonoid.mem_powers`：mem_powers (n : M) : n in powers n
· 使用定理 `Ideal.IsPrime.mem_of_pow_mem`：∀ {α : Type u} [inst : Semiring α] {I : Id
eal α}, I.IsPrime → ∀ {r : α} (n : ℕ), r ^ n ∈ I → r ∈ I
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem localization_away_comap_range (S : Type v) [CommSemiring S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] : Set.range (comap (algebraMap R S)) = basicOpen r := by
  rw [localization_comap_range S (Submonoid.powers r)]
  ext x
  simp only [mem_zeroLocus, basicOpen_eq_zeroLocus_compl, SetLike.mem_coe, Set.mem_ofPred_eq,
    Set.singleton_subset_iff, Set.mem_compl_iff, disjoint_iff_inf_le]
  constructor
  · intro h₁ h₂
    exact h₁ ⟨Submonoid.mem_powers r, h₂⟩
  · rintro h₁ _ ⟨⟨n, rfl⟩, h₃⟩
    exact h₁ (x.2.mem_of_pow_mem _ h₃)
/-
**PrimeSpectrum.localization_away_isOpenEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Pri
meSpectrum`。
形式化陈述：localization_away_isOpenEmbedding (S : Type v) [CommSemiring S] [Algebra R
 S] (r : R) [IsLocalization.Away r S] : IsOpenEmbedding (comap (algebraMap R S))
 where toIsEmbedding
参数：S : Type v；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.localization_comap_isEmbedding`：localization_comap_isEmbed
ding [Algebra R S] (M : Submonoid R) [IsLocalization M S] : IsEmbedding (comap (
algebraMap R S))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
· 使用定理 `PrimeSpectrum.isOpen_basicOpen`：isOpen_basicOpen {a : R} : IsOpen (basic
Open a : Set (PrimeSpectrum R))
-/
theorem localization_away_isOpenEmbedding (S : Type v) [CommSemiring S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] : IsOpenEmbedding (comap (algebraMap R S)) where
  toIsEmbedding := localization_comap_isEmbedding S (Submonoid.powers r)
  isOpen_range := by
    rw [localization_away_comap_range S r]
    exact isOpen_basicOpen
/-
**PrimeSpectrum.isCompact_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isCompact_basicOpen (f : R) : IsCompact (basicOpen f : Set (PrimeSpectrum 
R))
参数：f : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用引理 `PrimeSpectrum.continuous_comap`：continuous_comap (f : R ->+* S) : Contin
uous (comap f)
-/
theorem isCompact_basicOpen (f : R) : IsCompact (basicOpen f : Set (PrimeSpectrum R)) := by
  rw [← localization_away_comap_range (Localization (Submonoid.powers f))]
  exact isCompact_range (continuous_comap _)
/-
**PrimeSpectrum.comap_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：comap_basicOpen (f : R ->+* S) (x : R) : TopologicalSpace.Opens.comap ⟨com
ap f, continuous_comap f⟩ (basicOpen x) = basicOpen (f x)
参数：f : R ->+* S；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.continuous_comap`：continuous_comap (f : R ->+* S) : Contin
uous (comap f)
-/
lemma comap_basicOpen (f : R →+* S) (x : R) :
    TopologicalSpace.Opens.comap ⟨comap f, continuous_comap f⟩ (basicOpen x) = basicOpen (f x) :=
  rfl

open TopologicalSpace in
/-
**PrimeSpectrum.iSup_basicOpen_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectr
um`。
形式化陈述：iSup_basicOpen_eq_top_iff {ι : Type*} {f : ι -> R} : (⨆ i : ι, PrimeSpectr
um.basicOpen (f i)) = ⊤ ↔ Ideal.span (Set.range f) = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.zeroLocus_empty_iff_eq_top`：zeroLocus_empty_iff_eq_top {I 
: Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I = ⊤
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `compl_involutive`：compl_involutive : Function.Involutive (compl : α -> α
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iSup_basicOpen_eq_top_iff {ι : Type*} {f : ι → R} :
    (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) = ⊤ ↔ Ideal.span (Set.range f) = ⊤ := by
  rw [SetLike.ext'_iff, Opens.coe_iSup]
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Opens.coe_top, ← Set.compl_iInter,
    ← PrimeSpectrum.zeroLocus_iUnion]
  rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top, compl_involutive.eq_iff]
  simp only [Set.iUnion_singleton_eq_range, Set.compl_univ, PrimeSpectrum.zeroLocus_span]
/-
**PrimeSpectrum.iSup_basicOpen_eq_top_iff'** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpect
rum`。
形式化陈述：iSup_basicOpen_eq_top_iff' {s : Set R} : (⨆ i in s, PrimeSpectrum.basicOpe
n i) = ⊤ ↔ Ideal.span s = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用引理 `PrimeSpectrum.iSup_basicOpen_eq_top_iff`：iSup_basicOpen_eq_top_iff {ι : 
Type*} {f : ι -> R} : (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) = ⊤ ↔ Ideal.span 
(Set.range f) = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iSup_basicOpen_eq_top_iff' {s : Set R} :
    (⨆ i ∈ s, PrimeSpectrum.basicOpen i) = ⊤ ↔ Ideal.span s = ⊤ := by
  conv_rhs => rw [← Subtype.range_val (s := s), ← iSup_basicOpen_eq_top_iff]
  simp
/-
**PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton** 是 Ma
thlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton [Algebra R S] {f
 : R} {p : PrimeSpectrum R} (h : (basicOpen f).1 = {p}) : IsLocalization.Away f 
S ↔ IsLocalization.AtPrime S p.1
参数：h : (basicOpen f).1 = {p}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsLocalization.of_le_of_exists_dvd`：of_le_of_exists_dvd (N : Submonoid R
) (h₁ : M <= N) (h₂ : forall n in N, exists m in M, n ∣ m) : IsLocalization N S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Ideal.exists_le_prime_disjoint`：exists_le_prime_disjoint (S : Submonoid 
α) (disjoint : Disjoint (I : Set α) S) : exists p : Ideal α, p.IsPrime ∧ I <= p 
∧ Disjoint (p : Set …
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.mem_powers`：mem_powers (n : M) : n in powers n
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `IsLocalization.isLocalization_iff_of_isLocalization`：isLocalization_iff_
of_isLocalization [IsLocalization M S] [IsLocalization N S] [Algebra R P] : IsLo
calization M P ↔ IsLocalization N P
-/
theorem isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton [Algebra R S]
    {f : R} {p : PrimeSpectrum R} (h : (basicOpen f).1 = {p}) :
    IsLocalization.Away f S ↔ IsLocalization.AtPrime S p.1 :=
  have : IsLocalization.AtPrime (Localization.Away f) p.1 := by
    refine .of_le_of_exists_dvd (.powers f) _
      (Submonoid.powers_le.mpr <| by apply h ▸ Set.mem_singleton p) fun r hr ↦ ?_
    contrapose! hr
    simp_rw [← Ideal.mem_span_singleton] at hr
    have ⟨q, prime, le, disj⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {r})
      (.powers f) (Set.disjoint_right.mpr hr)
    have : ⟨q, prime⟩ ∈ (basicOpen f).1 := Set.disjoint_right.mp disj (Submonoid.mem_powers f)
    rw [h, Set.mem_singleton_iff] at this
    rw [← this]
    exact not_not.mpr (q.span_singleton_le_iff_mem.mp le)
  IsLocalization.isLocalization_iff_of_isLocalization _ _ (Localization.Away f)

open Localization Polynomial Set in
/-
**PrimeSpectrum.range_comap_algebraMap_localization_compl_eq_range_comap_quotien
tMk** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk {R : T
ype*} [CommRing R] (c : R) : letI
参数：c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `Polynomial.isLocalization`：isLocalization {R} [CommSemiring R] (S : Subm
onoid R) (A) [CommSemiring A] [Algebra R A] [IsLocalization S A] : IsLocalizatio
n (S.map C) A[X…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.map_surjective`：map_surjective (hf : Function.Surjective f) :
 Function.Surjective (map f)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `range_comap_of_surjective`：range_comap_of_surjective (hf : Surjective f)
 : Set.range (comap f) = zeroLocus (ker f)
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
· 使用定理 `Submonoid.map_powers`：map_powers {N : Type*} {F : Type*} [Monoid N] [Fun
Like F M N] [MonoidHomClass F M N] (f : F) (m : M) : (powers m).map f = powers (
f m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Polynomial.ker_mapRingHom`：∀ {R : Type u} {S : Type u_1} [inst : CommSem
iring R] [inst_1 : Semiring S] (f : R →+* S),   RingHom.ker (Polynomial.mapRingH
om f) = Ideal.m…
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk
    {R : Type*} [CommRing R] (c : R) :
    letI := (mapRingHom (algebraMap R (Away c))).toAlgebra
    (range (comap (algebraMap R[X] (Away c)[X])))ᶜ
      = range (comap (mapRingHom (Ideal.Quotient.mk (.span {c})))) := by
  let := (mapRingHom (algebraMap R (Away c))).toAlgebra
  have := Polynomial.isLocalization (.powers c) (Away c)
  rw [Submonoid.map_powers] at this
  have surj : Function.Surjective (mapRingHom (Ideal.Quotient.mk (.span {c}))) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  rw [range_comap_of_surjective _ _ surj, localization_away_comap_range _ (C c)]
  simp [Polynomial.ker_mapRingHom, Ideal.map_span]
/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : QuasiSeparatedSpace (PrimeSpectrum R) :=
  .of_isTopologicalBasis isTopologicalBasis_basic_opens fun i j ↦ by
    simpa [← TopologicalSpace.Opens.coe_inf, ← basicOpen_mul, -basicOpen_eq_zeroLocus_compl]
      using isCompact_basicOpen _

end BasicOpen

section Pi

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]

/-
**PrimeSpectrum.comap_evalRingHom_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpec
trum`。
形式化陈述：comap_evalRingHom_basicOpen [DecidableEq ι] (i : ι) (f : R i) : comap (Pi.
evalRingHom R i) '' basicOpen f = basicOpen (Pi.single i f)
参数：i : ι；f : R i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `Pi.evalRingHom_apply`：∀ {I : Type u} (f : I → Type v) [inst : (i : I) → 
NonAssocSemiring (f i)] (i : I) (g : (i : I) → f i),   (Pi.evalRingHom f i) g = 
g i
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `range_comap_of_surjective`：range_comap_of_surjective (hf : Surjective f)
 : Set.range (comap f) = zeroLocus (ker f)
· 使用定理 `RingHom.surjective`：RingHom.surjective (σ : R₁ ->+* R₂) [t : RingHomSurj
ective σ] : Function.Surjective σ
· 使用定理 `instRingHomSurjectiveForallEvalRingHom`：∀ {I : Type u} (f : I → Type u_1
) [inst : (i : I) → Semiring (f i)] (i : I), RingHomSurjective (Pi.evalRingHom f
 i)
· 使用定理 `PrimeSpectrum.mem_zeroLocus`：mem_zeroLocus (x : PrimeSpectrum R) (s : Se
t R) : x in zeroLocus s ↔ s subseteq x.asIdeal
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Ideal.IsPrime.mem_or_mem_of_mul_eq_zero`：∀ {α : Type u} [inst : Semiring
 α] {I : Ideal α}, I.IsPrime → ∀ {x y : α}, x * y = 0 → x ∈ I ∨ y ∈ I
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma comap_evalRingHom_basicOpen [DecidableEq ι] (i : ι) (f : R i) :
    comap (Pi.evalRingHom R i) '' basicOpen f = basicOpen (Pi.single i f) := by
  ext p
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    simpa
  · intro hp
    have : p ∈ Set.range (PrimeSpectrum.comap (Pi.evalRingHom R i)) := by
      rw [range_comap_of_surjective _ _ (RingHom.surjective _), mem_zeroLocus,
        SetLike.coe_subset_coe]
      intro x hx
      rw [RingHom.mem_ker, Pi.evalRingHom_apply] at hx
      have : Pi.single i f * x = 0 := by
        ext j
        by_cases h : i = j
        · subst h
          simp [hx]
        · simp [h]
      obtain (h | h) := Ideal.IsPrime.mem_or_mem_of_mul_eq_zero p.isPrime this <;> tauto
    obtain ⟨q, rfl⟩ := this
    exact ⟨q, by simpa using hp, by ext; simp⟩
/-
**PrimeSpectrum.sigmaToPi_mk_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`
。
形式化陈述：sigmaToPi_mk_basicOpen [DecidableEq ι] (i : ι) (f : R i) : sigmaToPi R '' 
Sigma.mk i '' basicOpen f = basicOpen (Pi.single i f)
参数：i : ι；f : R i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用引理 `PrimeSpectrum.comap_evalRingHom_basicOpen`：comap_evalRingHom_basicOpen [
DecidableEq ι] (i : ι) (f : R i) : comap (Pi.evalRingHom R i) '' basicOpen f = b
asicOpen (Pi.single i f)
-/
lemma sigmaToPi_mk_basicOpen [DecidableEq ι] (i : ι) (f : R i) :
    sigmaToPi R '' Sigma.mk i '' basicOpen f = basicOpen (Pi.single i f) := by
  simp only [Set.image_image, sigmaToPi_apply]
  exact PrimeSpectrum.comap_evalRingHom_basicOpen _ _

variable (R) in
/-
**PrimeSpectrum.isOpenEmbedding_sigmaToPi** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectr
um`。
形式化陈述：isOpenEmbedding_sigmaToPi : Topology.IsOpenEmbedding (sigmaToPi R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`：∀ {X : Type 
u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologica
lSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_sigma_iff`：continuous_sigma_iff {f : Sigma σ -> X} : Continuo
us f ↔ forall i, Continuous fun a => f ⟨i, a⟩
· 使用引理 `PrimeSpectrum.continuous_comap`：continuous_comap (f : R ->+* S) : Contin
uous (comap f)
· 使用定理 `PrimeSpectrum.sigmaToPi_injective`：sigmaToPi_injective : (sigmaToPi R).I
njective
· 使用定理 `isOpenMap_sigma`：isOpenMap_sigma {f : Sigma σ -> X} : IsOpenMap f ↔ fora
ll i, IsOpenMap fun a => f ⟨i, a⟩
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpenMap_iff`：∀ {α : Type u} {β : T
ype u_1} [t : TopologicalSpace α] [inst : TopologicalSpace β] {B : Set (Set α)},
   TopologicalSpace.IsTopologicalBasis …
· 使用定理 `PrimeSpectrum.isTopologicalBasis_basic_opens`：isTopologicalBasis_basic_o
pens : TopologicalSpace.IsTopologicalBasis (Set.range fun r : R => (basicOpen r 
: Set (PrimeSpectrum R)))
· 使用引理 `PrimeSpectrum.comap_evalRingHom_basicOpen`：comap_evalRingHom_basicOpen [
DecidableEq ι] (i : ι) (f : R i) : comap (Pi.evalRingHom R i) '' basicOpen f = b
asicOpen (Pi.single i f)
· 使用定理 `PrimeSpectrum.isOpen_basicOpen`：isOpen_basicOpen {a : R} : IsOpen (basic
Open a : Set (PrimeSpectrum R))
-/
lemma isOpenEmbedding_sigmaToPi : Topology.IsOpenEmbedding (sigmaToPi R) := by
  classical
  refine .of_continuous_injective_isOpenMap ?_ ?_ ?_
  · rw [continuous_sigma_iff]
    intro i
    exact continuous_comap (Pi.evalRingHom R i)
  · exact sigmaToPi_injective R
  · rw [isOpenMap_sigma]
    intro i
    simp only [sigmaToPi_apply, PrimeSpectrum.isTopologicalBasis_basic_opens.isOpenMap_iff]
    rintro - ⟨f, rfl⟩
    rw [PrimeSpectrum.comap_evalRingHom_basicOpen]
    exact isOpen_basicOpen

/-- If `ι` is finite, the disjoint union of the prime spectra of the `R i` is homeomorphic
to the prime spectrum of the product. -/
/-
**PrimeSpectrum.sigmaToPiHomeo** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：sigmaToPiHomeo {ι : Type*} (R : ι -> Type*) [forall i, CommRing (R i)] [Fi
nite ι] : (Σ i, PrimeSpectrum (R i)) ≃ₜ PrimeSpectrum (Π i, R i)
参数：R : ι -> Type*；R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ι` is finite, the disjoint union of the prime spectra of the `R i` is homeom
orphic
to the prime spectrum of the product.
-/
noncomputable def sigmaToPiHomeo {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)] [Finite ι] :
    (Σ i, PrimeSpectrum (R i)) ≃ₜ PrimeSpectrum (Π i, R i) :=
  (isOpenEmbedding_sigmaToPi R).toHomeomorphOfSurjective (sigmaToPi_bijective R).surjective

@[simp]
/-
**PrimeSpectrum.sigmaToPiHomeo_apply** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：sigmaToPiHomeo_apply [Finite ι] (p : Σ i, PrimeSpectrum (R i)) : sigmaToPi
Homeo R p = sigmaToPi R p
参数：p : Σ i, PrimeSpectrum (R i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sigmaToPiHomeo_apply [Finite ι] (p : Σ i, PrimeSpectrum (R i)) :
    sigmaToPiHomeo R p = sigmaToPi R p :=
  rfl

end Pi

section DiscreteTopology

variable (R) [DiscreteTopology (PrimeSpectrum R)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**PrimeSpectrum.toPiLocalization_surjective_of_discreteTopology** 是 Mathlib 中的一个
定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：toPiLocalization_surjective_of_discreteTopology : Function.Surjective (toP
iLocalization R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen_iff`：∀ {α : Type u} [t : Topo
logicalSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalB
asis b → (IsOpen s ↔ ∀ a ∈ s, ∃ t ∈ …
· 使用定理 `PrimeSpectrum.isTopologicalBasis_basic_opens`：isTopologicalBasis_basic_o
pens : TopologicalSpace.IsTopologicalBasis (Set.range fun r : R => (basicOpen r 
: Set (PrimeSpectrum R)))
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.singleton_injective`：singleton_injective : Injective (singleton : α 
-> Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`
：isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton [Algebra R S] {f : R}
 {p : PrimeSpectrum R} (h : (basicOpen f).1 = {p}) : IsLocali…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_ofInjective_symm`：apply_ofInjective_symm {α β} {f : α -> β} 
(hf : Injective f) (b : range f) : f ((ofInjective f hf).symm b) = b
· 使用引理 `PrimeSpectrum.iSup_basicOpen_eq_top_iff`：iSup_basicOpen_eq_top_iff {ι : 
Type*} {f : ι -> R} : (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) = ⊤ ↔ Ideal.span 
(Set.range f) = ⊤
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Localization.existsUnique_algebraMap_eq_of_span_eq_top`：existsUnique_alg
ebraMap_eq_of_span_eq_top (s : Set R) (span_eq : Ideal.span s = ⊤) (f : Π a : s,
 Away a.1) (h : forall a b : s, Away.awayToA…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `PrimeSpectrum.basicOpen_eq_bot_iff`：basicOpen_eq_bot_iff (f : R) : basic
Open f = ⊥ ↔ IsNilpotent f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PrimeSpectrum.basicOpen_mul`：basicOpen_mul (f g : R) : basicOpen (f * g)
 = basicOpen f ⊓ basicOpen g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
（共 37 条，此处仅展示前 30 条）
-/
theorem toPiLocalization_surjective_of_discreteTopology :
    Function.Surjective (toPiLocalization R) := fun x ↦ by
  have (p : PrimeSpectrum R) : ∃ f, (basicOpen f : Set _) = {p} :=
    have ⟨_, ⟨f, rfl⟩, hpf, hfp⟩ := isTopologicalBasis_basic_opens.isOpen_iff.mp
      (isOpen_discrete {p}) p rfl
    ⟨f, hfp.antisymm <| Set.singleton_subset_iff.mpr hpf⟩
  choose f hf using this
  let e := Equiv.ofInjective f fun p q eq ↦ Set.singleton_injective (hf p ▸ eq ▸ hf q)
  have loc a : IsLocalization.AtPrime (Localization.Away a.1) (e.symm a).1 :=
    (isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton <| hf _).mp <| by
      simp_rw [e, Equiv.apply_ofInjective_symm]; infer_instance
  let algE a := IsLocalization.algEquiv (e.symm a).1.primeCompl
    (Localization.AtPrime (e.symm a).1) (Localization.Away a.1)
  have span_eq : Ideal.span (Set.range f) = ⊤ := iSup_basicOpen_eq_top_iff.mp <| top_unique
    fun p _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨p, (hf p).ge rfl⟩
  replace hf a : (basicOpen a.1 : Set _) = {e.symm a} := by
    simp_rw [e, ← hf, Equiv.apply_ofInjective_symm]
  obtain ⟨r, eq, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top _ span_eq
    (fun a ↦ algE a (x _)) fun a b ↦ by
      obtain rfl | ne := eq_or_ne a b; · rfl
      have nil : IsNilpotent (a * b : R) := (basicOpen_eq_bot_iff _).mp <| by
        simp_rw [basicOpen_mul, SetLike.ext'_iff, TopologicalSpace.Opens.coe_inf, hf]
        exact bot_unique (fun _ ⟨ha, hb⟩ ↦ ne <| e.symm.injective (ha.symm.trans hb))
      apply (IsLocalization.subsingleton (M := .powers (a * b : R)) nil).elim
  refine ⟨r, funext fun I ↦ ?_⟩
  have := eq (e I)
  rwa [← AlgEquiv.symm_apply_eq, AlgEquiv.commutes, e.symm_apply_apply] at this
/-
**PrimeSpectrum.maximalSpectrumToPiLocalization_surjective_of_discreteTopology**
 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：maximalSpectrumToPiLocalization_surjective_of_discreteTopology : Function.
Surjective (MaximalSpectrum.toPiLocalization R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.piLocalizationToMaximal_comp_toPiLocalization`：piLocalizat
ionToMaximal_comp_toPiLocalization : (piLocalizationToMaximal R).comp (toPiLocal
ization R) = MaximalSpectrum.toPiLocalization R
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `PrimeSpectrum.piLocalizationToMaximal_surjective`：piLocalizationToMaxima
l_surjective : Function.Surjective (piLocalizationToMaximal R)
· 使用定理 `PrimeSpectrum.toPiLocalization_surjective_of_discreteTopology`：toPiLocal
ization_surjective_of_discreteTopology : Function.Surjective (toPiLocalization R
)
-/
theorem maximalSpectrumToPiLocalization_surjective_of_discreteTopology :
    Function.Surjective (MaximalSpectrum.toPiLocalization R) := by
  rw [← piLocalizationToMaximal_comp_toPiLocalization]
  exact (piLocalizationToMaximal_surjective R).comp
    (toPiLocalization_surjective_of_discreteTopology R)

/-- If the prime spectrum of a commutative semiring R has discrete Zariski topology, then R is
canonically isomorphic to the product of its localizations at the (finitely many) maximal ideals. -/
@[stacks 00JA
"See also `PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical`."]
/-
**PrimeSpectrum._root_.MaximalSpectrum.toPiLocalizationEquiv** 是 Mathlib 中的一个定义，
位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.MaximalSpectrum.toPiLocalizationEquiv :
    R ≃ₐ[R] MaximalSpectrum.PiLocalization R :=
  .ofBijective _ ⟨MaximalSpectrum.toPiLocalization_injective R,
    maximalSpectrumToPiLocalization_surjective_of_discreteTopology R⟩

@[simp]
/-
**PrimeSpectrum._root_.MaximalSpectrum.toPiLocalizationEquiv_apply** 是 Mathlib 中
的一个定理，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MaximalSpectrum.toPiLocalizationEquiv_apply (x : R) :
    MaximalSpectrum.toPiLocalizationEquiv R x = algebraMap R _ x :=
  rfl

@[simp]
/-
**PrimeSpectrum._root_.MaximalSpectrum.toPiLocalizationEquiv_apply_apply** 是 Mat
hlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MaximalSpectrum.toPiLocalizationEquiv_apply_apply (x : R) (I : MaximalSpectrum R) :
    MaximalSpectrum.toPiLocalizationEquiv R x I = algebraMap R _ x :=
  rfl
/-
**PrimeSpectrum.discreteTopology_iff_toPiLocalization_surjective** 是 Mathlib 中的一
个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：discreteTopology_iff_toPiLocalization_surjective {R} [CommSemiring R] : Di
screteTopology (PrimeSpectrum R) ↔ Function.Surjective (toPiLocalization R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `PrimeSpectrum.toPiLocalization_surjective_of_discreteTopology`：toPiLocal
ization_surjective_of_discreteTopology : Function.Surjective (toPiLocalization R
)
· 使用定理 `PrimeSpectrum.discreteTopology_of_toLocalization_surjective`：discreteTop
ology_of_toLocalization_surjective (surj : Function.Surjective (toPiLocalization
 R)) : DiscreteTopology (PrimeSpectrum R)
-/
theorem discreteTopology_iff_toPiLocalization_surjective {R} [CommSemiring R] :
    DiscreteTopology (PrimeSpectrum R) ↔ Function.Surjective (toPiLocalization R) :=
  ⟨fun _ ↦ toPiLocalization_surjective_of_discreteTopology _,
    discreteTopology_of_toLocalization_surjective⟩
/-
**PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective** 是 Mathlib 中的一个
定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：discreteTopology_iff_toPiLocalization_bijective {R} [CommSemiring R] : Dis
creteTopology (PrimeSpectrum R) ↔ Function.Bijective (toPiLocalization R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `PrimeSpectrum.discreteTopology_iff_toPiLocalization_surjective`：discrete
Topology_iff_toPiLocalization_surjective {R} [CommSemiring R] : DiscreteTopology
 (PrimeSpectrum R) ↔ Function.Surjective (toPiLocali…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `PrimeSpectrum.toPiLocalization_injective`：toPiLocalization_injective : F
unction.Injective (toPiLocalization R)
-/
theorem discreteTopology_iff_toPiLocalization_bijective {R} [CommSemiring R] :
    DiscreteTopology (PrimeSpectrum R) ↔ Function.Bijective (toPiLocalization R) :=
  discreteTopology_iff_toPiLocalization_surjective.trans
    (and_iff_right <| toPiLocalization_injective _).symm

variable {R} in
/-
**PrimeSpectrum.toPiLocalization_bijective** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpect
rum`。
形式化陈述：toPiLocalization_bijective : Function.Bijective (toPiLocalization R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective`：discreteT
opology_iff_toPiLocalization_bijective {R} [CommSemiring R] : DiscreteTopology (
PrimeSpectrum R) ↔ Function.Bijective (toPiLocaliza…
-/
lemma toPiLocalization_bijective : Function.Bijective (toPiLocalization R) :=
  discreteTopology_iff_toPiLocalization_bijective.mp inferInstance

/-- If the prime spectrum of a commutative semiring R has discrete Zariski topology, then R is
canonically isomorphic to the product of its localizations at the (finitely many) prime ideals. -/
/-
**PrimeSpectrum.toPiLocalizationEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：toPiLocalizationEquiv : R ≃ₐ[R] PiLocalization R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `PrimeSpectrum.toPiLocalization_bijective`：toPiLocalization_bijective : F
unction.Bijective (toPiLocalization R)

--- 原说明 ---
If the prime spectrum of a commutative semiring R has discrete Zariski topology,
 then R is
canonically isomorphic to the product of its localizations at the (finitely many
) prime ideals.
-/
def toPiLocalizationEquiv : R ≃ₐ[R] PiLocalization R :=
  .ofBijective _ toPiLocalization_bijective

@[simp]
/-
**PrimeSpectrum.toPiLocalizationEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpec
trum`。
形式化陈述：toPiLocalizationEquiv_apply (x : R) : toPiLocalizationEquiv R x = algebraM
ap R _ x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem toPiLocalizationEquiv_apply (x : R) : toPiLocalizationEquiv R x = algebraMap R _ x :=
  rfl

@[simp]
/-
**PrimeSpectrum.toPiLocalizationEquiv_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pri
meSpectrum`。
形式化陈述：toPiLocalizationEquiv_apply_apply (x : R) (I : PrimeSpectrum R) : toPiLoca
lizationEquiv R x I = algebraMap R _ x
参数：x : R；I : PrimeSpectrum R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem toPiLocalizationEquiv_apply_apply (x : R) (I : PrimeSpectrum R) :
    toPiLocalizationEquiv R x I = algebraMap R _ x :=
  rfl

end DiscreteTopology

section Order

/-!
## The specialization order

We endow `PrimeSpectrum R` with a partial order, where `x ≤ y` if and only if `y ∈ closure {x}`.
-/

/-
**PrimeSpectrum.le_iff_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：le_iff_mem_closure (x y : PrimeSpectrum R) : x <= y ↔ y in closure ({x} : 
Set (PrimeSpectrum R))
参数：x y : PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.asIdeal_le_asIdeal`：asIdeal_le_asIdeal (x y : PrimeSpectru
m R) : x.asIdeal <= y.asIdeal ↔ x <= y
· 使用定理 `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanishingId
eal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocus (vanishingIdeal t : Set R
) = closure t
· 使用定理 `PrimeSpectrum.mem_zeroLocus`：mem_zeroLocus (x : PrimeSpectrum R) (s : Se
t R) : x in zeroLocus s ↔ s subseteq x.asIdeal
· 使用定理 `PrimeSpectrum.vanishingIdeal_singleton`：vanishingIdeal_singleton (x : Pr
imeSpectrum R) : vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
## The specialization order

We endow `PrimeSpectrum R` with a partial order, where `x ≤ y` if and only if `y
 ∈ closure {x}`.
-/
theorem le_iff_mem_closure (x y : PrimeSpectrum R) :
    x ≤ y ↔ y ∈ closure ({x} : Set (PrimeSpectrum R)) := by
  rw [← asIdeal_le_asIdeal, ← zeroLocus_vanishingIdeal_eq_closure, mem_zeroLocus,
    vanishingIdeal_singleton, SetLike.coe_subset_coe]
/-
**PrimeSpectrum.le_iff_specializes** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：le_iff_specializes (x y : PrimeSpectrum R) : x <= y ↔ x ⤳ y
参数：x y : PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PrimeSpectrum.le_iff_mem_closure`：le_iff_mem_closure (x y : PrimeSpectru
m R) : x <= y ↔ y in closure ({x} : Set (PrimeSpectrum R))
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `specializes_iff_mem_closure`：specializes_iff_mem_closure : x ⤳ y ↔ y in 
closure ({x} : Set X)
-/
theorem le_iff_specializes (x y : PrimeSpectrum R) : x ≤ y ↔ x ⤳ y :=
  (le_iff_mem_closure x y).trans specializes_iff_mem_closure.symm

/-- `nhds` as an order embedding. -/
@[simps!]
/-
**PrimeSpectrum.nhdsOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：nhdsOrderEmbedding : PrimeSpectrum R ↪o Filter (PrimeSpectrum R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`nhds` as an order embedding.
-/
def nhdsOrderEmbedding : PrimeSpectrum R ↪o Filter (PrimeSpectrum R) :=
  OrderEmbedding.ofMapLEIff nhds fun a b => (le_iff_specializes a b).symm
/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T0Space (PrimeSpectrum R) :=
  ⟨nhdsOrderEmbedding.inj'⟩
/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PrespectralSpace (PrimeSpectrum R) :=
  .of_isTopologicalBasis' isTopologicalBasis_basic_opens isCompact_basicOpen
/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SpectralSpace (PrimeSpectrum R) where

end Order

/-- If `x` specializes to `y`, then there is a natural map from the localization of `y` to the
localization of `x`. -/
/-
**PrimeSpectrum.localizationMapOfSpecializes** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpe
ctrum`。
形式化陈述：localizationMapOfSpecializes {x y : PrimeSpectrum R} (h : x ⤳ y) : Localiz
ation.AtPrime y.asIdeal ->+* Localization.AtPrime x.asIdeal
参数：h : x ⤳ y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime

--- 原说明 ---
If `x` specializes to `y`, then there is a natural map from the localization of 
`y` to the
localization of `x`.
-/
def localizationMapOfSpecializes {x y : PrimeSpectrum R} (h : x ⤳ y) :
    Localization.AtPrime y.asIdeal →+* Localization.AtPrime x.asIdeal :=
  @IsLocalization.lift _ _ _ _ _ _ _ _ Localization.isLocalization
    (algebraMap R (Localization.AtPrime x.asIdeal))
    (by
      rintro ⟨a, ha⟩
      rw [← PrimeSpectrum.le_iff_specializes, ← asIdeal_le_asIdeal, ← SetLike.coe_subset_coe, ←
        Set.compl_subset_compl] at h
      exact (IsLocalization.map_units (Localization.AtPrime x.asIdeal)
        ⟨a, show a ∈ x.asIdeal.primeCompl from h ha⟩ :))

section stableUnderSpecialization

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)

/-
**PrimeSpectrum.isClosed_image_of_stableUnderSpecialization** 是 Mathlib 中的一个引理，位
于命名空间 `PrimeSpectrum`。
形式化陈述：isClosed_image_of_stableUnderSpecialization (Z : Set (PrimeSpectrum S)) (h
Z : IsClosed Z) (hf : StableUnderSpecialization (comap f '' Z)) : IsClosed (coma
p f '' Z)
参数：Z : Set (PrimeSpectrum S)；hZ : IsClosed Z；hf : StableUnderSpecialization (com
ap f '' Z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isClosed_iff_zeroLocus_ideal`：isClosed_iff_zeroLocus_ideal
 (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ exists I : Ideal R, Z = zeroLocus I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrimeSpectrum.isClosed_iff_zeroLocus`：isClosed_iff_zeroLocus (Z : Set (P
rimeSpectrum R)) : IsClosed Z ↔ exists s, Z = zeroLocus s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用引理 `Ideal.exists_ideal_comap_le_prime`：exists_ideal_comap_le_prime {S} [Comm
Semiring S] [FunLike F R S] [RingHomClass F R S] {f : F} (P : Ideal R) [P.IsPrim
e] (I : Ideal S) (le : …
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `PrimeSpectrum.le_iff_specializes`：le_iff_specializes (x y : PrimeSpectru
m R) : x <= y ↔ x ⤳ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isClosed_image_of_stableUnderSpecialization
    (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z)
    (hf : StableUnderSpecialization (comap f '' Z)) :
    IsClosed (comap f '' Z) := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
  refine (isClosed_iff_zeroLocus _).mpr ⟨I.comap f, le_antisymm ?_ fun p hp ↦ ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact Ideal.comap_mono hq
  · obtain ⟨q, hqI, hq, hqle⟩ := p.asIdeal.exists_ideal_comap_le_prime I hp
    exact hf ((le_iff_specializes ⟨q.comap f, inferInstance⟩ p).mp hqle) ⟨⟨q, hq⟩, hqI, rfl⟩

@[stacks 00HY]
/-
**PrimeSpectrum.isClosed_range_of_stableUnderSpecialization** 是 Mathlib 中的一个引理，位
于命名空间 `PrimeSpectrum`。
形式化陈述：isClosed_range_of_stableUnderSpecialization (hf : StableUnderSpecializatio
n (Set.range (comap f))) : IsClosed (Set.range (comap f))
参数：hf : StableUnderSpecialization (Set.range (comap f))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用引理 `PrimeSpectrum.isClosed_image_of_stableUnderSpecialization`：isClosed_imag
e_of_stableUnderSpecialization (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z) (hf
 : StableUnderSpecialization (comap f '' Z)) : …
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
-/
lemma isClosed_range_of_stableUnderSpecialization
    (hf : StableUnderSpecialization (Set.range (comap f))) :
    IsClosed (Set.range (comap f)) := by
  rw [← Set.image_univ] at hf ⊢
  exact isClosed_image_of_stableUnderSpecialization _ _ isClosed_univ hf

variable {f} in
@[stacks 00HY]
/-
**PrimeSpectrum.stableUnderSpecialization_range_iff** 是 Mathlib 中的一个引理，位于命名空间 `P
rimeSpectrum`。
形式化陈述：stableUnderSpecialization_range_iff : StableUnderSpecialization (Set.range
 (comap f)) ↔ IsClosed (Set.range (comap f))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.isClosed_range_of_stableUnderSpecialization`：isClosed_rang
e_of_stableUnderSpecialization (hf : StableUnderSpecialization (Set.range (comap
 f))) : IsClosed (Set.range (comap f))
· 使用引理 `IsClosed.stableUnderSpecialization`：IsClosed.stableUnderSpecialization {
s : Set X} (hs : IsClosed s) : StableUnderSpecialization s
-/
lemma stableUnderSpecialization_range_iff :
    StableUnderSpecialization (Set.range (comap f)) ↔ IsClosed (Set.range (comap f)) :=
  ⟨isClosed_range_of_stableUnderSpecialization f, fun h ↦ h.stableUnderSpecialization⟩
/-
**PrimeSpectrum.stableUnderSpecialization_image_iff** 是 Mathlib 中的一个引理，位于命名空间 `P
rimeSpectrum`。
形式化陈述：stableUnderSpecialization_image_iff (Z : Set (PrimeSpectrum S)) (hZ : IsCl
osed Z) : StableUnderSpecialization (comap f '' Z) ↔ IsClosed (comap f '' Z)
参数：Z : Set (PrimeSpectrum S)；hZ : IsClosed Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.isClosed_image_of_stableUnderSpecialization`：isClosed_imag
e_of_stableUnderSpecialization (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z) (hf
 : StableUnderSpecialization (comap f '' Z)) : …
· 使用引理 `IsClosed.stableUnderSpecialization`：IsClosed.stableUnderSpecialization {
s : Set X} (hs : IsClosed s) : StableUnderSpecialization s
-/
lemma stableUnderSpecialization_image_iff
    (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z) :
    StableUnderSpecialization (comap f '' Z) ↔ IsClosed (comap f '' Z) :=
  ⟨isClosed_image_of_stableUnderSpecialization f Z hZ, fun h ↦ h.stableUnderSpecialization⟩

end stableUnderSpecialization

section IsQuotientMap

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R →+* S}
  (h₁ : Function.Surjective (comap f))

include h₁

/-- If `f : Spec S → Spec R` is specializing and surjective, the topology on `Spec R` is the
quotient topology induced by `f`. -/
/-
**PrimeSpectrum.isQuotientMap_of_specializingMap** 是 Mathlib 中的一个引理，位于命名空间 `Prim
eSpectrum`。
形式化陈述：isQuotientMap_of_specializingMap (h₂ : SpecializingMap (comap f)) : Topolo
gy.IsQuotientMap (comap f)
参数：h₂ : SpecializingMap (comap f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.isQuotientMap_iff_isClosed`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sQuotientMap f ↔ Function…
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用引理 `PrimeSpectrum.continuous_comap`：continuous_comap (f : R ->+* S) : Contin
uous (comap f)
· 使用引理 `PrimeSpectrum.isClosed_image_of_stableUnderSpecialization`：isClosed_imag
e_of_stableUnderSpecialization (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z) (hf
 : StableUnderSpecialization (comap f '' Z)) : …
· 使用引理 `SpecializingMap.stableUnderSpecialization_image`：SpecializingMap.stableU
nderSpecialization_image (hf : SpecializingMap f) {s : Set X} (hs : StableUnderS
pecialization s) : StableUnderSpecial…
· 使用引理 `IsClosed.stableUnderSpecialization`：IsClosed.stableUnderSpecialization {
s : Set X} (hs : IsClosed s) : StableUnderSpecialization s
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s

--- 原说明 ---
If `f : Spec S → Spec R` is specializing and surjective, the topology on `Spec R
` is the
quotient topology induced by `f`.
-/
lemma isQuotientMap_of_specializingMap (h₂ : SpecializingMap (comap f)) :
    Topology.IsQuotientMap (comap f) := by
  rw [Topology.isQuotientMap_iff_isClosed]
  exact ⟨h₁, fun s ↦ ⟨fun hs ↦ hs.preimage (continuous_comap f),
    fun hsc ↦ Set.image_preimage_eq s h₁ ▸ isClosed_image_of_stableUnderSpecialization _ _ hsc
      (h₂.stableUnderSpecialization_image hsc.stableUnderSpecialization)⟩⟩

/-- If `f : Spec S → Spec R` is generalizing and surjective, the topology on `Spec R` is the
quotient topology induced by `f`. -/
/-
**PrimeSpectrum.isQuotientMap_of_generalizingMap** 是 Mathlib 中的一个引理，位于命名空间 `Prim
eSpectrum`。
形式化陈述：isQuotientMap_of_generalizingMap (h₂ : GeneralizingMap (comap f)) : Topolo
gy.IsQuotientMap (comap f)
参数：h₂ : GeneralizingMap (comap f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.isQuotientMap_iff_isClosed`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sQuotientMap f ↔ Function…
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用引理 `PrimeSpectrum.continuous_comap`：continuous_comap (f : R ->+* S) : Contin
uous (comap f)
· 使用引理 `PrimeSpectrum.isClosed_image_of_stableUnderSpecialization`：isClosed_imag
e_of_stableUnderSpecialization (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z) (hf
 : StableUnderSpecialization (comap f '' Z)) : …
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `stableUnderGeneralization_compl_iff`：stableUnderGeneralization_compl_iff
 {s : Set X} : StableUnderGeneralization sᶜ ↔ StableUnderSpecialization s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用引理 `GeneralizingMap.stableUnderGeneralization_image`：GeneralizingMap.stableU
nderGeneralization_image (hf : GeneralizingMap f) {s : Set X} (hs : StableUnderG
eneralization s) : StableUnderGeneral…
· 使用引理 `IsOpen.stableUnderGeneralization`：IsOpen.stableUnderGeneralization {s : 
Set X} (hs : IsOpen s) : StableUnderGeneralization s
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ

--- 原说明 ---
If `f : Spec S → Spec R` is generalizing and surjective, the topology on `Spec R
` is the
quotient topology induced by `f`.
-/
lemma isQuotientMap_of_generalizingMap (h₂ : GeneralizingMap (comap f)) :
    Topology.IsQuotientMap (comap f) := by
  rw [Topology.isQuotientMap_iff_isClosed]
  refine ⟨h₁, fun s ↦ ⟨fun hs ↦ hs.preimage (continuous_comap f),
    fun hsc ↦ Set.image_preimage_eq s h₁ ▸ ?_⟩⟩
  apply isClosed_image_of_stableUnderSpecialization _ _ hsc
  rw [Set.image_preimage_eq s h₁, ← stableUnderGeneralization_compl_iff]
  convert! h₂.stableUnderGeneralization_image hsc.isOpen_compl.stableUnderGeneralization
  rw [← Set.preimage_compl, Set.image_preimage_eq _ h₁]

end IsQuotientMap

section denseRange

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)

/-
**PrimeSpectrum.vanishingIdeal_range_comap** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpect
rum`。
形式化陈述：vanishingIdeal_range_comap : vanishingIdeal (Set.range (comap f)) = (RingH
om.ker f).radical
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_radical`：comap_radical : comap f (radical K) = radical (coma
p f K)
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
lemma vanishingIdeal_range_comap :
    vanishingIdeal (Set.range (comap f)) = (RingHom.ker f).radical := by
  ext x
  rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_radical, Ideal.radical_eq_sInf]
  simp only [mem_vanishingIdeal, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    comap_asIdeal, Ideal.mem_comap, bot_le, true_and, Submodule.mem_sInf, Set.mem_ofPred_eq]
  exact ⟨fun H I hI ↦ H ⟨I, hI⟩, fun H I ↦ H I.1 I.2⟩
/-
**PrimeSpectrum.closure_range_comap** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：closure_range_comap : closure (Set.range (comap f)) = zeroLocus (RingHom.k
er f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanishingId
eal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocus (vanishingIdeal t : Set R
) = closure t
· 使用引理 `PrimeSpectrum.vanishingIdeal_range_comap`：vanishingIdeal_range_comap : v
anishingIdeal (Set.range (comap f)) = (RingHom.ker f).radical
· 使用定理 `PrimeSpectrum.zeroLocus_radical`：zeroLocus_radical (I : Ideal R) : zeroL
ocus (I.radical : Set R) = zeroLocus I
-/
lemma closure_range_comap :
    closure (Set.range (comap f)) = zeroLocus (RingHom.ker f) := by
  rw [← zeroLocus_vanishingIdeal_eq_closure, vanishingIdeal_range_comap, zeroLocus_radical]
/-
**PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical** 是 Mathlib 中的一个引理，位于命名空间
 `PrimeSpectrum`。
形式化陈述：denseRange_comap_iff_ker_le_nilRadical : DenseRange (comap f) ↔ RingHom.ke
r f <= nilradical R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `denseRange_iff_closure_range`：denseRange_iff_closure_range : DenseRange 
f ↔ closure (range f) = univ
· 使用引理 `PrimeSpectrum.closure_range_comap`：closure_range_comap : closure (Set.ra
nge (comap f)) = zeroLocus (RingHom.ker f)
· 使用定理 `PrimeSpectrum.zeroLocus_eq_univ_iff`：zeroLocus_eq_univ_iff (s : Set R) :
 zeroLocus s = Set.univ ↔ s subseteq nilradical R
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma denseRange_comap_iff_ker_le_nilRadical :
    DenseRange (comap f) ↔ RingHom.ker f ≤ nilradical R := by
  rw [denseRange_iff_closure_range, closure_range_comap, zeroLocus_eq_univ_iff,
    SetLike.coe_subset_coe]

@[stacks 00FL]
/-
**PrimeSpectrum.denseRange_comap_iff_minimalPrimes** 是 Mathlib 中的一个引理，位于命名空间 `Pr
imeSpectrum`。
形式化陈述：denseRange_comap_iff_minimalPrimes : DenseRange (comap f) ↔ forall I (h : 
I in minimalPrimes R), ⟨I, h.1.1⟩ in Set.range (comap f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical`：denseRange_comap_i
ff_ker_le_nilRadical : DenseRange (comap f) ↔ RingHom.ker f <= nilradical R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.IsPrime.radical_le_iff`：∀ {R : Type u} [inst : CommSemiring R] {I 
J : Ideal R}, J.IsPrime → (I.radical ≤ J ↔ I ≤ J)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.IsMinimalPrime.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (I p
 : Ideal R), I.IsMinimalPrime p = Minimal (fun q => q.IsPrime ∧ I ≤ q) p
· 使用定理 `Ideal.exists_comap_eq_of_mem_minimalPrimes`：Ideal.exists_comap_eq_of_mem
_minimalPrimes {I : Ideal S} (f : R ->+* S) (p) (H : p in (I.comap f).minimalPri
mes) : exists p' : Ideal S, p'.I…
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Specializes.mem_closed`：Specializes.mem_closed (h : x ⤳ y) (hs : IsClose
d s) (hx : x in s) : y in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.le_iff_specializes`：le_iff_specializes (x y : PrimeSpectru
m R) : x <= y ↔ x ⤳ y
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
lemma denseRange_comap_iff_minimalPrimes :
    DenseRange (comap f) ↔ ∀ I (h : I ∈ minimalPrimes R), ⟨I, h.1.1⟩ ∈ Set.range (comap f) := by
  constructor
  · intro H I hI
    have : I ∈ (RingHom.ker f).minimalPrimes := by
      rw [denseRange_comap_iff_ker_le_nilRadical] at H
      simp only [Set.mem_ofPred, Ideal.IsMinimalPrime] at hI ⊢
      convert! hI using 2 with p
      exact ⟨fun h ↦ ⟨h.1, bot_le⟩, fun h ↦ ⟨h.1, H.trans (h.1.radical_le_iff.mpr bot_le)⟩⟩
    obtain ⟨p, hp, _, rfl⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f (I := ⊥) I this
    exact ⟨⟨p, hp⟩, rfl⟩
  · intro H p
    obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
    exact ((le_iff_specializes ⟨q, hq.1.1⟩ p).mp hq').mem_closed isClosed_closure
      (subset_closure (H q hq))

end denseRange

variable (R) in
/--
Zero loci of prime ideals are closed irreducible sets in the Zariski topology and any closed
irreducible set is a zero locus of some prime ideal.
-/
/-
**PrimeSpectrum.pointsEquivIrreducibleCloseds** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSp
ectrum`。
形式化陈述：(R : Type u) → [inst : CommSemiring R] → PrimeSpectrum R ≃o (TopologicalSp
ace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ
参数：PrimeSpectrum R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `PrimeSpectrum.instT0Space`：∀ {R : Type u} [inst : CommSemiring R], T0Spa
ce (PrimeSpectrum R)

--- 原说明 ---
Zero loci of prime ideals are closed irreducible sets in the Zariski topology an
d any closed
irreducible set is a zero locus of some prime ideal.
-/
protected def pointsEquivIrreducibleCloseds :
    PrimeSpectrum R ≃o (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ where
  __ := irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} :=
    (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans (le_iff_specializes p q).symm

/--
Zero loci of prime ideals are closed irreducible sets in the Zariski topology and any closed
irreducible set is a zero locus of some prime ideal.
-/
/-
**PrimeSpectrum.zeroLocusEquivIrreducibleCloseds** 是 Mathlib 中的一个定义，位于命名空间 `Prim
eSpectrum`。
形式化陈述：{R : Type u} →   [inst : CommSemiring R] →     (I : Set R) → ↑(PrimeSpectr
um.zeroLocus I) ≃o (TopologicalSpace.IrreducibleCloseds ↑(PrimeSpectrum.zeroLocu
s I))ᵒᵈ
参数：I : Set R；PrimeSpectrum.zeroLocus I；TopologicalSpace.IrreducibleCloseds ↑(Pri
meSpectrum.zeroLocus I)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `PrimeSpectrum.instQuasiSoberElemZeroLocus`：∀ {R : Type u} [inst : CommSe
miring R] (I : Set R), QuasiSober ↑(PrimeSpectrum.zeroLocus I)

--- 原说明 ---
Zero loci of prime ideals are closed irreducible sets in the Zariski topology an
d any closed
irreducible set is a zero locus of some prime ideal.
-/
protected def zeroLocusEquivIrreducibleCloseds (I : Set R) :
    zeroLocus I ≃o (TopologicalSpace.IrreducibleCloseds (zeroLocus I))ᵒᵈ where
  __ := irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} := (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans
    ((subtype_specializes_iff p q).trans (le_iff_specializes p.1 q.1).symm)
/-
**PrimeSpectrum.stableUnderSpecialization_singleton** 是 Mathlib 中的一个引理，位于命名空间 `P
rimeSpectrum`。
形式化陈述：stableUnderSpecialization_singleton {x : PrimeSpectrum R} : StableUnderSpe
cialization {x} ↔ x.asIdeal.IsMaximal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma stableUnderSpecialization_singleton {x : PrimeSpectrum R} :
    StableUnderSpecialization {x} ↔ x.asIdeal.IsMaximal := by
  simp_rw [← isMax_iff, StableUnderSpecialization, ← le_iff_specializes, Set.mem_singleton_iff,
    @forall_comm _ (_ = _), forall_eq]
  exact ⟨fun H a h ↦ (H a h).le, fun H a h ↦ le_antisymm (H h) h⟩
/-
**PrimeSpectrum.stableUnderGeneralization_singleton** 是 Mathlib 中的一个引理，位于命名空间 `P
rimeSpectrum`。
形式化陈述：stableUnderGeneralization_singleton {x : PrimeSpectrum R} : StableUnderGen
eralization {x} ↔ x.asIdeal in minimalPrimes R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma stableUnderGeneralization_singleton {x : PrimeSpectrum R} :
    StableUnderGeneralization {x} ↔ x.asIdeal ∈ minimalPrimes R := by
  simp_rw [← isMin_iff, StableUnderGeneralization, ← le_iff_specializes, Set.mem_singleton_iff,
    @forall_comm _ (_ = _), forall_eq]
  exact ⟨fun H a h ↦ (H a h).ge, fun H a h ↦ le_antisymm h (H h)⟩
/-
**PrimeSpectrum.isCompact_isOpen_iff** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isCompact_isOpen_iff {s : Set (PrimeSpectrum R)} : IsCompact s ∧ IsOpen s 
↔ exists t : Finset R, (zeroLocus t)ᶜ = s
参数：PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis`：isCompact_ope
n_iff_eq_finite_iUnion_of_isTopologicalBasis (b : ι -> Set X) (hb : IsTopologica
lBasis (Set.range b)) (hb' : forall i, IsCompac…
· 使用定理 `PrimeSpectrum.isTopologicalBasis_basic_opens`：isTopologicalBasis_basic_o
pens : TopologicalSpace.IsTopologicalBasis (Set.range fun r : R => (basicOpen r 
: Set (PrimeSpectrum R)))
· 使用定理 `PrimeSpectrum.isCompact_basicOpen`：isCompact_basicOpen (f : R) : IsCompa
ct (basicOpen f : Set (PrimeSpectrum R))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
lemma isCompact_isOpen_iff {s : Set (PrimeSpectrum R)} :
    IsCompact s ∧ IsOpen s ↔ ∃ t : Finset R, (zeroLocus t)ᶜ = s := by
  rw [isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis _
    isTopologicalBasis_basic_opens isCompact_basicOpen]
  simp only [basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter₂, ← zeroLocus_iUnion₂,
    Set.biUnion_of_singleton]
  exact ⟨fun ⟨s, hs, e⟩ ↦ ⟨hs.toFinset, by simpa using e.symm⟩,
    fun ⟨s, e⟩ ↦ ⟨s, s.finite_toSet, by simpa using e.symm⟩⟩
/-
**PrimeSpectrum.isCompact_isOpen_iff_ideal** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpect
rum`。
形式化陈述：isCompact_isOpen_iff_ideal {s : Set (PrimeSpectrum R)} : IsCompact s ∧ IsO
pen s ↔ exists I : Ideal R, I.FG ∧ (zeroLocus I)ᶜ = s
参数：PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.isCompact_isOpen_iff`：isCompact_isOpen_iff {s : Set (Prime
Spectrum R)} : IsCompact s ∧ IsOpen s ↔ exists t : Finset R, (zeroLocus t)ᶜ = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isCompact_isOpen_iff_ideal {s : Set (PrimeSpectrum R)} :
    IsCompact s ∧ IsOpen s ↔ ∃ I : Ideal R, I.FG ∧ (zeroLocus I)ᶜ = s := by
  rw [isCompact_isOpen_iff]
  exact ⟨fun ⟨s, e⟩ ↦ ⟨.span s, ⟨s, rfl⟩, by simpa using e⟩,
    fun ⟨I, ⟨s, hs⟩, e⟩ ↦ ⟨s, by simpa [hs.symm] using e⟩⟩
/-
**PrimeSpectrum.basicOpen_eq_zeroLocus_of_mul_add** 是 Mathlib 中的一个引理，位于命名空间 `Pri
meSpectrum`。
形式化陈述：basicOpen_eq_zeroLocus_of_mul_add (e f : R) (mul : e * f = 0) (add : e + f
 = 1) : basicOpen e = zeroLocus {f}
参数：e f : R；mul : e * f = 0；add : e + f = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ideal.IsPrime.mem_or_mem_of_mul_eq_zero`：∀ {α : Type u} [inst : Semiring
 α] {I : Ideal α}, I.IsPrime → ∀ {x y : α}, x * y = 0 → x ∈ I ∨ y ∈ I
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
-/
lemma basicOpen_eq_zeroLocus_of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) :
    basicOpen e = zeroLocus {f} := by
  ext p
  suffices e ∉ p.asIdeal ↔ f ∈ p.asIdeal by simpa
  refine ⟨(p.2.mem_or_mem_of_mul_eq_zero mul).resolve_left, fun h₁ h₂ ↦ p.2.1 ?_⟩
  rw [Ideal.eq_top_iff_one, ← add]
  exact add_mem h₂ h₁
/-
**PrimeSpectrum.zeroLocus_eq_basicOpen_of_mul_add** 是 Mathlib 中的一个引理，位于命名空间 `Pri
meSpectrum`。
形式化陈述：zeroLocus_eq_basicOpen_of_mul_add (e f : R) (mul : e * f = 0) (add : e + f
 = 1) : zeroLocus {e} = basicOpen f
参数：e f : R；mul : e * f = 0；add : e + f = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.basicOpen_eq_zeroLocus_of_mul_add`：basicOpen_eq_zeroLocus_
of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) : basicOpen e = zeroLoc
us {f}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma zeroLocus_eq_basicOpen_of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) :
    zeroLocus {e} = basicOpen f := by
  rw [basicOpen_eq_zeroLocus_of_mul_add f e] <;> simp only [mul, add, mul_comm, add_comm]
/-
**PrimeSpectrum.isClopen_basicOpen_of_mul_add** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSp
ectrum`。
形式化陈述：isClopen_basicOpen_of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1
) : IsClopen (basicOpen e : Set (PrimeSpectrum R))
参数：e f : R；mul : e * f = 0；add : e + f = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PrimeSpectrum.basicOpen_eq_zeroLocus_of_mul_add`：basicOpen_eq_zeroLocus_
of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) : basicOpen e = zeroLoc
us {f}
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
-/
lemma isClopen_basicOpen_of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) :
    IsClopen (basicOpen e : Set (PrimeSpectrum R)) :=
  ⟨basicOpen_eq_zeroLocus_of_mul_add e f mul add ▸ isClosed_zeroLocus _, (basicOpen e).2⟩
/-
**PrimeSpectrum.basicOpen_injOn_isIdempotentElem** 是 Mathlib 中的一个引理，位于命名空间 `Prim
eSpectrum`。
形式化陈述：basicOpen_injOn_isIdempotentElem : {e : R | IsIdempotentElem e}.InjOn basi
cOpen
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_span_singleton'`：mem_span_singleton' {x y : α} : x in span ({y
} : Set α) ↔ exists a, a * y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ideal.exists_le_prime_notMem_of_isIdempotentElem`：exists_le_prime_notMem
_of_isIdempotentElem (a : α) (ha : IsIdempotentElem a) (haI : a ∉ I) : exists p 
: Ideal α, p.IsPrime ∧ I <= p ∧ a ∉ p
· 使用定理 `ne_of_mem_of_not_mem'`：∀ {α : Type u_1} {β : Type u_2} [inst : Membershi
p α β] {s t : β} {a : α}, a ∈ s → a ∉ t → s ≠ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
-/
lemma basicOpen_injOn_isIdempotentElem :
    {e : R | IsIdempotentElem e}.InjOn basicOpen := fun x hx y hy eq ↦ by
  by_contra! ne
  wlog ne' : x * y ≠ x generalizing x y
  · apply this y hy x hx eq.symm ne.symm
    rwa [mul_comm, of_not_not ne']
  have : x ∉ Ideal.span {y} := fun mem ↦ ne' <| by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp mem
    rw [mul_assoc, hy]
  have ⟨p, prime, le, notMem⟩ := Ideal.exists_le_prime_notMem_of_isIdempotentElem _ x hx this
  exact ne_of_mem_of_not_mem' (a := ⟨p, prime⟩) notMem
    (not_not.mpr <| p.span_singleton_le_iff_mem.mp le) eq
/-
**PrimeSpectrum.exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen** 是 Mathl
ib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen {s : Set (PrimeSpec
trum R)} (hs : IsClopen s) : exists e f : R, e * f = 0 ∧ e + f = 1 ∧ s = basicOp
en e ∧ sᶜ = basicOpen f
参数：PrimeSpectrum R；hs : IsClopen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `PrimeSpectrum.instIsEmptyOfSubsingleton`：∀ {R : Type u} [inst : CommSemi
ring R] [Subsingleton R], IsEmpty (PrimeSpectrum R)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `PrimeSpectrum.isCompact_isOpen_iff_ideal`：isCompact_isOpen_iff_ideal {s 
: Set (PrimeSpectrum R)} : IsCompact s ∧ IsOpen s ↔ exists I : Ideal R, I.FG ∧ (
zeroLocus I)ᶜ = s
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.radical_le_radical_iff`：radical_le_radical_iff : radical I <= radi
cal J ↔ I <= radical J
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.zeroLocus_eq_iff`：zeroLocus_eq_iff {I J : Ideal R} : zeroL
ocus (I : Set R) = zeroLocus J ↔ I.radical = J.radical
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `PrimeSpectrum.zeroLocus_bot`：zeroLocus_bot : zeroLocus ((⊥ : Ideal R) : 
Set R) = Set.univ
· 使用定理 `PrimeSpectrum.zeroLocus_mul`：zeroLocus_mul (I J : Ideal R) : zeroLocus (
(I * J : Ideal R) : Set R) = zeroLocus I union zeroLocus J
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.compl_union_self`：compl_union_self (s : Set α) : sᶜ union s = univ
· 使用引理 `Ideal.exists_pow_le_of_le_radical_of_fg`：exists_pow_le_of_le_radical_of_
fg {R : Type*} [CommSemiring R] {I J : Ideal R} (h' : I <= J.radical) (h : I.FG)
 : exists n : Nat, I ^ n <= J
· 使用定理 `Submodule.FG.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R
] [inst_1 : Semiring A] [inst_2 : Algebra R A]   {M N : Submodule R A}, M.FG → N
.FG → …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
（共 54 条，此处仅展示前 30 条）
-/
lemma exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)}
    (hs : IsClopen s) : ∃ e f : R, e * f = 0 ∧ e + f = 1 ∧ s = basicOpen e ∧ sᶜ = basicOpen f := by
  cases subsingleton_or_nontrivial R
  · refine ⟨0, 0, ?_, ?_, ?_, ?_⟩ <;> apply Subsingleton.elim
  obtain ⟨I, hI, hI'⟩ := isCompact_isOpen_iff_ideal.mp ⟨hs.1.isCompact, hs.2⟩
  obtain ⟨J, hJ, hJ'⟩ := isCompact_isOpen_iff_ideal.mp
    ⟨hs.2.isClosed_compl.isCompact, hs.1.isOpen_compl⟩
  simp only [compl_eq_iff_isCompl, ← eq_compl_iff_isCompl, compl_compl] at hI' hJ'
  have : I * J ≤ nilradical R := by
    refine Ideal.radical_le_radical_iff.mp (le_of_eq ?_)
    rw [← zeroLocus_eq_iff, Ideal.zero_eq_bot, zeroLocus_bot,
      zeroLocus_mul, hI', hJ', Set.compl_union_self]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg this (Submodule.FG.mul hI hJ)
  have hnz : n ≠ 0 := by rintro rfl; simp at hn
  rw [mul_pow, Ideal.zero_eq_bot] at hn
  have : I ^ n ⊔ J ^ n = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_pow_eq_top (I ∪ J : Set R) _ n, Ideal.span_le, Set.image_union,
      Set.union_subset_iff]
    constructor
    · rintro _ ⟨x, hx, rfl⟩; exact Ideal.mem_sup_left (Ideal.pow_mem_pow hx n)
    · rintro _ ⟨x, hx, rfl⟩; exact Ideal.mem_sup_right (Ideal.pow_mem_pow hx n)
    · rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq, ← zeroLocus_empty_iff_eq_top,
        zeroLocus_sup, hI', hJ', Set.compl_inter_self]
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at this
  obtain ⟨x, hx, y, hy, add⟩ := this
  have mul : x * y = 0 := hn (Ideal.mul_mem_mul hx hy)
  have : s = basicOpen x := by
    refine subset_antisymm ?_ ?_
    · rw [← hJ', basicOpen_eq_zeroLocus_of_mul_add _ _ mul add]
      exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr <| Ideal.pow_le_self hnz hy)
    · rw [basicOpen_eq_zeroLocus_compl, Set.compl_subset_comm, ← hI']
      exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr <| Ideal.pow_le_self hnz hx)
  refine ⟨x, y, mul, add, this, ?_⟩
  rw [this, basicOpen_eq_zeroLocus_of_mul_add _ _ mul add, basicOpen_eq_zeroLocus_compl]
/-
**PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen** 是 Mathlib 中的一个引理，位于
命名空间 `PrimeSpectrum`。
形式化陈述：exists_idempotent_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)} (hs
 : IsClopen s) : exists e : R, IsIdempotentElem e ∧ s = basicOpen e
参数：PrimeSpectrum R；hs : IsClopen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen`：ex
ists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)}
 (hs : IsClopen s) : exists e f : R, e * f = 0 ∧ e + f = 1…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `IsIdempotentElem.of_mul_add`：of_mul_add (mul : a * b = 0) (add : a + b =
 1) : IsIdempotentElem a ∧ IsIdempotentElem b
-/
lemma exists_idempotent_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)}
    (hs : IsClopen s) : ∃ e : R, IsIdempotentElem e ∧ s = basicOpen e :=
  have ⟨e, _, mul, add, eq, _⟩ := exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen hs
  ⟨e, (IsIdempotentElem.of_mul_add mul add).1, eq⟩

@[stacks 00EE]
/-
**PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen** 是 Mathlib 中的一
个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：existsUnique_idempotent_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R
)} (hs : IsClopen s) : exists! e : R, IsIdempotentElem e ∧ s = basicOpen e
参数：PrimeSpectrum R；hs : IsClopen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用引理 `PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`：exists_idempot
ent_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)} (hs : IsClopen s) : exi
sts e : R, IsIdempotentElem e ∧ s = basicOpen …
· 使用引理 `PrimeSpectrum.basicOpen_injOn_isIdempotentElem`：basicOpen_injOn_isIdempo
tentElem : {e : R | IsIdempotentElem e}.InjOn basicOpen
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma existsUnique_idempotent_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)}
    (hs : IsClopen s) : ∃! e : R, IsIdempotentElem e ∧ s = basicOpen e := by
  refine existsUnique_of_exists_of_unique (exists_idempotent_basicOpen_eq_of_isClopen hs) ?_
  rintro x y ⟨hx, rfl⟩ ⟨hy, eq⟩
  exact basicOpen_injOn_isIdempotentElem hx hy (SetLike.ext' eq)

open TopologicalSpace.Opens in
/-
**PrimeSpectrum.isClopen_iff_mul_add** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isClopen_iff_mul_add {s : Set (PrimeSpectrum R)} : IsClopen s ↔ exists e f
 : R, e * f = 0 ∧ e + f = 1 ∧ s = basicOpen e
参数：PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen`：ex
ists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)}
 (hs : IsClopen s) : exists e f : R, e * f = 0 ∧ e + f = 1…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `PrimeSpectrum.isClopen_basicOpen_of_mul_add`：isClopen_basicOpen_of_mul_a
dd (e f : R) (mul : e * f = 0) (add : e + f = 1) : IsClopen (basicOpen e : Set (
PrimeSpectrum R))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isClopen_iff_mul_add {s : Set (PrimeSpectrum R)} :
    IsClopen s ↔ ∃ e f : R, e * f = 0 ∧ e + f = 1 ∧ s = basicOpen e := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have ⟨e, f, h⟩ := exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen h
    exact ⟨e, f, by simp only [h, and_self]⟩
  rintro ⟨e, f, mul, add, rfl⟩
  exact isClopen_basicOpen_of_mul_add e f mul add
/-
**PrimeSpectrum.isClopen_iff_mul_add_zeroLocus** 是 Mathlib 中的一个引理，位于命名空间 `PrimeS
pectrum`。
形式化陈述：isClopen_iff_mul_add_zeroLocus {s : Set (PrimeSpectrum R)} : IsClopen s ↔ 
exists e f : R, e * f = 0 ∧ e + f = 1 ∧ s = zeroLocus {e}
参数：PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.isClopen_iff_mul_add`：isClopen_iff_mul_add {s : Set (Prime
Spectrum R)} : IsClopen s ↔ exists e f : R, e * f = 0 ∧ e + f = 1 ∧ s = basicOpe
n e
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用定理 `exists₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∃ a b, p a b) ↔ ∃ a b, q a b
)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用引理 `PrimeSpectrum.zeroLocus_eq_basicOpen_of_mul_add`：zeroLocus_eq_basicOpen_
of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) : zeroLocus {e} = basic
Open f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isClopen_iff_mul_add_zeroLocus {s : Set (PrimeSpectrum R)} :
    IsClopen s ↔ ∃ e f : R, e * f = 0 ∧ e + f = 1 ∧ s = zeroLocus {e} := by
  rw [isClopen_iff_mul_add, exists_comm]
  refine exists₂_congr fun e f ↦ ?_
  rw [mul_comm, add_comm, ← and_assoc, ← and_assoc, and_congr_right]
  intro ⟨mul, add⟩
  rw [zeroLocus_eq_basicOpen_of_mul_add e f mul add]

open TopologicalSpace (Clopens)

/-- Clopen subsets in the prime spectrum of a commutative semiring are in order-preserving
bijection with pairs of elements with product 0 and sum 1. (By definition, `(e₁, f₁) ≤ (e₂, f₂)`
iff `e₁ * e₂ = e₁`.) Both elements in such pairs must be idempotents, but there may exists
idempotents that do not form such pairs (does not have a "complement"). For example, in the
semiring `{0, 0.5, 1}` with `⊔` as `+` and `⊓` as `*`, `0.5` has no complement. -/
/-
**PrimeSpectrum.mulZeroAddOneEquivClopens** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectr
um`。
形式化陈述：mulZeroAddOneEquivClopens : {e : R × R // e.1 * e.2 = 0 ∧ e.1 + e.2 = 1} ≃
o Clopens (PrimeSpectrum R) where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Clopen subsets in the prime spectrum of a commutative semiring are in order-pres
erving
bijection with pairs of elements with product 0 and sum 1. (By definition, `(e₁,
 f₁) ≤ (e₂, f₂)`
iff `e₁ * e₂ = e₁`.) Both elements in such pairs must be idempotents, but there 
may exists
idempotents that do not form such pairs (does not have a "complement"). For exam
ple, in the
semiring `{0, 0.5, 1}` with `⊔` as `+` and `⊓` as `*`, `0.5` has no complement.
-/
def mulZeroAddOneEquivClopens :
    {e : R × R // e.1 * e.2 = 0 ∧ e.1 + e.2 = 1} ≃o Clopens (PrimeSpectrum R) where
  toEquiv := .ofBijective
    (fun e ↦ ⟨basicOpen e.1.1, isClopen_iff_mul_add.mpr ⟨_, _, e.2.1, e.2.2, rfl⟩⟩) <| by
      refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ eq ↦ mul_eq_zero_add_eq_one_ext_left ?_, fun s ↦ ?_⟩
      · exact basicOpen_injOn_isIdempotentElem (IsIdempotentElem.of_mul_add hx.1 hx.2).1
          (IsIdempotentElem.of_mul_add hy.1 hy.2).1 <| SetLike.ext' (congr_arg (·.1) eq)
      · have ⟨e, f, mul, add, eq⟩ := isClopen_iff_mul_add.mp s.2
        exact ⟨⟨(e, f), mul, add⟩, SetLike.ext' eq.symm⟩
  map_rel_iff' {a b} := show basicOpen _ ≤ basicOpen _ ↔ _ by
    rw [← inf_eq_left, ← basicOpen_mul]
    refine ⟨fun h ↦ ?_, (by rw [·])⟩
    rw [← inf_eq_left]
    have := (IsIdempotentElem.of_mul_add a.2.1 a.2.2).1
    exact mul_eq_zero_add_eq_one_ext_left (basicOpen_injOn_isIdempotentElem
      (this.mul (IsIdempotentElem.of_mul_add b.2.1 b.2.2).1) this h)
/-
**PrimeSpectrum.isRetrocompact_zeroLocus_compl** 是 Mathlib 中的一个引理，位于命名空间 `PrimeS
pectrum`。
形式化陈述：isRetrocompact_zeroLocus_compl {s : Set R} (hs : s.Finite) : IsRetrocompac
t (zeroLocus s)ᶜ
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuasiSeparatedSpace.isRetrocompact_iff_isCompact`：∀ {X : Type u_2} [inst
 : TopologicalSpace X] {U : Set X} [CompactSpace X] [QuasiSeparatedSpace X],   I
sOpen U → (IsRetrocompact U ↔ IsCompac…
· 使用定理 `PrimeSpectrum.instQuasiSeparatedSpace`：∀ {R : Type u} [inst : CommSemiri
ng R], QuasiSeparatedSpace (PrimeSpectrum R)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `PrimeSpectrum.isCompact_isOpen_iff`：isCompact_isOpen_iff {s : Set (Prime
Spectrum R)} : IsCompact s ∧ IsOpen s ↔ exists t : Finset R, (zeroLocus t)ᶜ = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isRetrocompact_zeroLocus_compl {s : Set R} (hs : s.Finite) :
    IsRetrocompact (zeroLocus s)ᶜ :=
  (QuasiSeparatedSpace.isRetrocompact_iff_isCompact (isClosed_zeroLocus _).isOpen_compl).mpr
    (isCompact_isOpen_iff.mpr ⟨hs.toFinset, by simp⟩).1
/-
**PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg** 是 Mathlib 中的一个引理，位于命名空间 `
PrimeSpectrum`。
形式化陈述：isRetrocompact_zeroLocus_compl_of_fg {I : Ideal R} (hI : I.FG) : IsRetroco
mpact (zeroLocus (I : Set R))ᶜ
参数：hI : I.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
· 使用引理 `PrimeSpectrum.isRetrocompact_zeroLocus_compl`：isRetrocompact_zeroLocus_c
ompl {s : Set R} (hs : s.Finite) : IsRetrocompact (zeroLocus s)ᶜ
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
lemma isRetrocompact_zeroLocus_compl_of_fg {I : Ideal R} (hI : I.FG) :
    IsRetrocompact (zeroLocus (I : Set R))ᶜ := by
  obtain ⟨s, rfl⟩ := hI
  rw [zeroLocus_span]
  exact isRetrocompact_zeroLocus_compl s.finite_toSet
/-
**PrimeSpectrum.isRetrocompact_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectru
m`。
形式化陈述：isRetrocompact_basicOpen {f : R} : IsRetrocompact (basicOpen f : Set (Prim
eSpectrum R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用引理 `PrimeSpectrum.isRetrocompact_zeroLocus_compl`：isRetrocompact_zeroLocus_c
ompl {s : Set R} (hs : s.Finite) : IsRetrocompact (zeroLocus s)ᶜ
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
lemma isRetrocompact_basicOpen {f : R} :
    IsRetrocompact (basicOpen f : Set (PrimeSpectrum R)) := by
  simpa using isRetrocompact_zeroLocus_compl (Set.finite_singleton f)
/-
**PrimeSpectrum.isConstructible_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectr
um`。
形式化陈述：isConstructible_basicOpen {f : R} : IsConstructible (basicOpen f : Set (Pr
imeSpectrum R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRetrocompact.isConstructible`：∀ {X : Type u_2} [inst : TopologicalSpac
e X] {U : Set X}, IsOpen U → IsRetrocompact U → Topology.IsConstructible U
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用引理 `PrimeSpectrum.isRetrocompact_basicOpen`：isRetrocompact_basicOpen {f : R}
 : IsRetrocompact (basicOpen f : Set (PrimeSpectrum R))
-/
lemma isConstructible_basicOpen {f : R} :
    IsConstructible (basicOpen f : Set (PrimeSpectrum R)) :=
  isRetrocompact_basicOpen.isConstructible (basicOpen f).2

section IsIntegral

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

/-
**PrimeSpectrum.isClosedMap_comap_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Prime
Spectrum`。
形式化陈述：isClosedMap_comap_of_isIntegral (hf : f.IsIntegral) : IsClosedMap (comap f
)
参数：hf : f.IsIntegral。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.isClosed_image_of_stableUnderSpecialization`：isClosed_imag
e_of_stableUnderSpecialization (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z) (hf
 : StableUnderSpecialization (comap f '' Z)) : …
· 使用定理 `Ideal.exists_ideal_over_prime_of_isIntegral`：exists_ideal_over_prime_of_
isIntegral [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime P] (I : Ideal S) (hIP
 : I.comap (algebraMap R S) <= P)…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrimeSpectrum.le_iff_specializes`：le_iff_specializes (x y : PrimeSpectru
m R) : x <= y ↔ x ⤳ y
· 使用定理 `Specializes.mem_closed`：Specializes.mem_closed (h : x ⤳ y) (hs : IsClose
d s) (hx : x in s) : y in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
-/
theorem isClosedMap_comap_of_isIntegral (hf : f.IsIntegral) :
    IsClosedMap (comap f) := by
  refine fun s hs ↦ isClosed_image_of_stableUnderSpecialization _ _ hs ?_
  rintro _ y e ⟨x, hx, rfl⟩
  algebraize [f]
  obtain ⟨q, hq₁, hq₂, hq₃⟩ := Ideal.exists_ideal_over_prime_of_isIntegral y.asIdeal x.asIdeal
    ((le_iff_specializes _ _).mpr e)
  refine ⟨⟨q, hq₂⟩, ((le_iff_specializes _ ⟨q, hq₂⟩).mp hq₁).mem_closed hs hx,
    PrimeSpectrum.ext hq₃⟩
/-
**PrimeSpectrum.isClosed_comap_singleton_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间
 `PrimeSpectrum`。
形式化陈述：isClosed_comap_singleton_of_isIntegral (hf : f.IsIntegral) (x : PrimeSpect
rum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) : IsClosed ({comap f x} : S
et (PrimeSpectrum R))
参数：hf : f.IsIntegral；x : PrimeSpectrum S；hx : IsClosed ({x} : Set (PrimeSpectrum
 S))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `PrimeSpectrum.isClosedMap_comap_of_isIntegral`：isClosedMap_comap_of_isIn
tegral (hf : f.IsIntegral) : IsClosedMap (comap f)
-/
theorem isClosed_comap_singleton_of_isIntegral (hf : f.IsIntegral)
    (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) :
    IsClosed ({comap f x} : Set (PrimeSpectrum R)) := by
  simpa using isClosedMap_comap_of_isIntegral f hf _ hx
/-
**PrimeSpectrum.closure_image_comap_zeroLocus** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSp
ectrum`。
形式化陈述：closure_image_comap_zeroLocus (I : Ideal S) : closure (comap f '' zeroLocu
s I) = zeroLocus (I.comap f)
参数：I : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `PrimeSpectrum.preimage_comap_zeroLocus`：preimage_comap_zeroLocus (s : Se
t R) : comap f ⁻¹' zeroLocus s = zeroLocus (f '' s)
· 使用定理 `PrimeSpectrum.zeroLocus_anti_mono`：zeroLocus_anti_mono {s t : Set R} (h 
: s subseteq t) : zeroLocus t subseteq zeroLocus s
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `Ideal.exists_minimalPrimes_le`：Ideal.exists_minimalPrimes_le [J.IsPrime]
 (e : I <= J) : exists p in I.minimalPrimes, p <= J
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.exists_comap_eq_of_mem_minimalPrimes`：Ideal.exists_comap_eq_of_mem
_minimalPrimes {I : Ideal S} (f : R ->+* S) (p) (H : p in (I.comap f).minimalPri
mes) : exists p' : Ideal S, p'.I…
· 使用引理 `IsClosed.stableUnderSpecialization`：IsClosed.stableUnderSpecialization {
s : Set X} (hs : IsClosed s) : StableUnderSpecialization s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.le_iff_specializes`：le_iff_specializes (x y : PrimeSpectru
m R) : x <= y ↔ x ⤳ y
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
lemma closure_image_comap_zeroLocus (I : Ideal S) :
    closure (comap f '' zeroLocus I) = zeroLocus (I.comap f) := by
  apply subset_antisymm
  · rw [(isClosed_zeroLocus _).closure_subset_iff, Set.image_subset_iff, preimage_comap_zeroLocus]
    exact zeroLocus_anti_mono (Set.image_preimage_subset _ _)
  · rintro x (hx : I.comap f ≤ x.asIdeal)
    obtain ⟨q, hq₁, hq₂⟩ := Ideal.exists_minimalPrimes_le hx
    obtain ⟨p', hp', hp'', rfl⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f _ hq₁
    let p'' : PrimeSpectrum S := ⟨p', hp'⟩
    apply isClosed_closure.stableUnderSpecialization ((le_iff_specializes
      (comap f ⟨p', hp'⟩) x).mp hq₂) (subset_closure (by exact ⟨_, hp'', rfl⟩))
/-
**PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom** 是 Mathlib 中的一个引理，位于
命名空间 `PrimeSpectrum`。
形式化陈述：isIntegral_of_isClosedMap_comap_mapRingHom (h : IsClosedMap (comap (mapRin
gHom f))) : f.IsIntegral
参数：h : IsClosedMap (comap (mapRingHom f))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_subsingleton`：∀ (R : Type u_1) (M : Type u_2) [Subsingle
ton R] [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M], IsNoetherian…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `PrimeSpectrum.zeroLocus_empty_iff_eq_top`：zeroLocus_empty_iff_eq_top {I 
: Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I = ⊤
· 使用定理 `PrimeSpectrum.zeroLocus_sup`：zeroLocus_sup (I J : Ideal R) : zeroLocus (
(I ⊔ J : Ideal R) : Set R) = zeroLocus I inter zeroLocus J
· 使用引理 `PrimeSpectrum.closure_image_comap_zeroLocus`：closure_image_comap_zeroLoc
us (I : Ideal S) : closure (comap f '' zeroLocus I) = zeroLocus (I.comap f)
· 使用定理 `closure_eq_iff_isClosed`：closure_eq_iff_isClosed : closure s = s ↔ IsClo
sed s
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_span_singleton_sup`：mem_span_singleton_sup {x y : α} {I : Idea
l α} : x in Ideal.span {y} ⊔ I ↔ exists a : α, exists b in I, a * y + b = x
（共 90 条，此处仅展示前 30 条）
-/
lemma isIntegral_of_isClosedMap_comap_mapRingHom (h : IsClosedMap (comap (mapRingHom f))) :
    f.IsIntegral := by
  algebraize [f]
  suffices Algebra.IsIntegral R S by rwa [Algebra.isIntegral_def] at this
  nontriviality R
  nontriviality S
  constructor
  intro r
  let p : S[X] := C r * X - 1
  have : (1 : R[X]) ∈ Ideal.span {X} ⊔ (Ideal.span {p}).comap (mapRingHom f) := by
    have H := h _ (isClosed_zeroLocus {p})
    rw [← zeroLocus_span, ← closure_eq_iff_isClosed, closure_image_comap_zeroLocus] at H
    rw [← Ideal.eq_top_iff_one, sup_comm, ← zeroLocus_empty_iff_eq_top, zeroLocus_sup, H]
    suffices ∀ (a : PrimeSpectrum S[X]), p ∈ a.asIdeal → X ∉ a.asIdeal by
      simpa [Set.eq_empty_iff_forall_notMem]
    intro q hpq hXq
    have : 1 ∈ q.asIdeal := by simpa [p] using! (sub_mem (q.asIdeal.mul_mem_left (C r) hXq) hpq)
    exact q.2.ne_top (q.asIdeal.eq_top_iff_one.mpr this)
  obtain ⟨a, b, hb, e⟩ := Ideal.mem_span_singleton_sup.mp this
  obtain ⟨c, hc : b.map (algebraMap R S) = _⟩ := Ideal.mem_span_singleton.mp hb
  refine ⟨b.reverse * X ^ (1 + c.natDegree), ?_, ?_⟩
  · refine Monic.mul ?_ (by simp)
    have h : b.coeff 0 = 1 := by simpa using! congr(($e).coeff 0)
    have : b.natTrailingDegree = 0 := by simp [h]
    rw [Monic.def, reverse_leadingCoeff, trailingCoeff, this, h]
  · have : p.natDegree ≤ 1 := by simpa using! natDegree_linear_le (a := r) (b := -1)
    rw [eval₂_eq_eval_map, reverse, Polynomial.map_mul, ← reflect_map, Polynomial.map_pow,
      map_X, ← revAt_zero (1 + _), ← reflect_monomial,
      ← reflect_mul _ _ natDegree_map_le (by simp), pow_zero, mul_one, hc,
      ← add_assoc, reflect_mul _ _ (this.trans (by simp)) le_rfl,
      eval_mul, reflect_sub, reflect_mul _ _ (by simp) (by simp)]
    simp [← pow_succ']

variable (R S) in
/-
**PrimeSpectrum._root_.Algebra.IsIntegral.comap_surjective** 是 Mathlib 中的一个引理，位于
命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Algebra.IsIntegral.comap_surjective [Algebra R S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] :
    Function.Surjective (comap (algebraMap R S)) := by
  intro ⟨p, hp⟩
  have hinj : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨Q, _, hQ, rfl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal S)
    (by simp [Ideal.comap_bot_of_injective (algebraMap R S) hinj])
  exact ⟨⟨Q, hQ⟩, rfl⟩
/-
**PrimeSpectrum._root_.RingHom.IsIntegral.comap_surjective** 是 Mathlib 中的一个引理，位于
命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.RingHom.IsIntegral.comap_surjective {f : R →+* S} (hf : f.IsIntegral)
    (hinj : Function.Injective f) : Function.Surjective (comap f) := by
  algebraize [f]
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  exact Algebra.IsIntegral.comap_surjective _ _

end IsIntegral

/-- Zero loci of minimal prime ideals over `I` are irreducible components in `zeroLocus I` and any
irreducible component is a zero locus of some minimal prime ideal. -/
@[stacks 00ES]
/-
**PrimeSpectrum._root_.Ideal.minimalPrimes.equivIrreducibleComponents** 是 Mathli
b 中的一个定义，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Zero loci of minimal prime ideals over `I` are irreducible components in `zeroLo
cus I` and any
irreducible component is a zero locus of some minimal prime ideal.
-/
protected def _root_.Ideal.minimalPrimes.equivIrreducibleComponents (I : Ideal R) :
    I.minimalPrimes ≃o (irreducibleComponents <| (zeroLocus (I : Set R)))ᵒᵈ := by
  let e : {p : Ideal R | p.IsPrime ∧ I ≤ p} ≃o zeroLocus (I : Set R) :=
    ⟨⟨fun x ↦ ⟨⟨x.1, x.2.1⟩, x.2.2⟩, fun x ↦ ⟨x.1.1, x.1.2, x.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, .rfl⟩
  rw [irreducibleComponents_eq_maximals_closed]
  exact OrderIso.setOfPredMinimalIsoSetOfPredMaximal
    (e.trans ((PrimeSpectrum.zeroLocusEquivIrreducibleCloseds (I : Set R)).trans
    (TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' (zeroLocus (I : Set R))).dual))

variable (R)

/-- Zero loci of minimal prime ideals of `R` are irreducible components in `Spec R` and any
irreducible component is a zero locus of some minimal prime ideal. -/
@[stacks 00ES]
/-
**PrimeSpectrum._root_.minimalPrimes.equivIrreducibleComponents** 是 Mathlib 中的一个
定义，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Zero loci of minimal prime ideals of `R` are irreducible components in `Spec R` 
and any
irreducible component is a zero locus of some minimal prime ideal.
-/
protected def _root_.minimalPrimes.equivIrreducibleComponents :
    minimalPrimes R ≃o (irreducibleComponents <| PrimeSpectrum R)ᵒᵈ := by
  let e : {p : Ideal R | p.IsPrime ∧ ⊥ ≤ p} ≃o PrimeSpectrum R :=
    ⟨⟨fun x ↦ ⟨x.1, x.2.1⟩, fun x ↦ ⟨x.1, x.2, bot_le⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, Iff.rfl⟩
  rw [irreducibleComponents_eq_maximals_closed]
  exact OrderIso.setOfPredMinimalIsoSetOfPredMaximal
    (e.trans ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).trans
    (TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' (PrimeSpectrum R)).dual))
/-
**PrimeSpectrum.vanishingIdeal_irreducibleComponents** 是 Mathlib 中的一个引理，位于命名空间 `
PrimeSpectrum`。
形式化陈述：vanishingIdeal_irreducibleComponents : vanishingIdeal '' (irreducibleCompo
nents <| PrimeSpectrum R) = minimalPrimes R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `irreducibleComponents_eq_maximals_closed`：irreducibleComponents_eq_maxim
als_closed (X : Type*) [TopologicalSpace X] : irreducibleComponents X = { s | Ma
ximal (fun x => IsClosed x ∧ I…
· 使用引理 `minimalPrimes_eq_minimals`：minimalPrimes_eq_minimals : minimalPrimes R =
 {x | Minimal Ideal.IsPrime x}
· 使用定理 `image_antitone_setOfPred_maximal`：∀ {α : Type u_2} {β : Type u_3} {P : α
 → Prop} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β},   (∀ ⦃y x : α⦄, 
P y → P x → (f y ≤ f x…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `PrimeSpectrum.vanishingIdeal_anti_mono_iff`：vanishingIdeal_anti_mono_iff
 {s t : Set (PrimeSpectrum R)} (ht : IsClosed t) : s subseteq t ↔ vanishingIdeal
 t <= vanishingIdeal s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用引理 `PrimeSpectrum.vanishingIdeal_isClosed_isIrreducible`：vanishingIdeal_isCl
osed_isIrreducible : vanishingIdeal (R
-/
lemma vanishingIdeal_irreducibleComponents :
    vanishingIdeal '' (irreducibleComponents <| PrimeSpectrum R) = minimalPrimes R := by
  rw [irreducibleComponents_eq_maximals_closed, minimalPrimes_eq_minimals,
    image_antitone_setOfPred_maximal (fun s t hs _ ↦ (vanishingIdeal_anti_mono_iff hs.1).symm),
    ← funext (@Set.mem_ofPred_eq _ · Ideal.IsPrime), ← vanishingIdeal_isClosed_isIrreducible]
  rfl
/-
**PrimeSpectrum.zeroLocus_minimalPrimes** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum
`。
形式化陈述：zeroLocus_minimalPrimes : zeroLocus ∘ (↑) '' minimalPrimes R = irreducible
Components (PrimeSpectrum R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PrimeSpectrum.vanishingIdeal_irreducibleComponents`：vanishingIdeal_irred
ucibleComponents : vanishingIdeal '' (irreducibleComponents <| PrimeSpectrum R) 
= minimalPrimes R
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.EqOn.image_eq_self`：∀ {α : Type u_1} {s : Set α} {f : α → α}, Set.Eq
On f id s → f '' s = s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanishingId
eal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocus (vanishingIdeal t : Set R
) = closure t
· 使用定理 `isClosed_of_mem_irreducibleComponents`：isClosed_of_mem_irreducibleCompon
ents (s) (H : s in irreducibleComponents X) : IsClosed s
-/
lemma zeroLocus_minimalPrimes :
    zeroLocus ∘ (↑) '' minimalPrimes R = irreducibleComponents (PrimeSpectrum R) := by
  rw [← vanishingIdeal_irreducibleComponents, ← Set.image_comp, Set.EqOn.image_eq_self]
  intro s hs
  simpa [zeroLocus_vanishingIdeal_eq_closure, closure_eq_iff_isClosed]
    using isClosed_of_mem_irreducibleComponents s hs

variable {R}
/-
**PrimeSpectrum.vanishingIdeal_mem_minimalPrimes** 是 Mathlib 中的一个引理，位于命名空间 `Prim
eSpectrum`。
形式化陈述：vanishingIdeal_mem_minimalPrimes {s : Set (PrimeSpectrum R)} : vanishingId
eal s in minimalPrimes R ↔ closure s in irreducibleComponents (PrimeSpectrum R)
参数：PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PrimeSpectrum.zeroLocus_minimalPrimes`：zeroLocus_minimalPrimes : zeroLoc
us ∘ (↑) '' minimalPrimes R = irreducibleComponents (PrimeSpectrum R)
· 使用定理 `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanishingId
eal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocus (vanishingIdeal t : Set R
) = closure t
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `PrimeSpectrum.vanishingIdeal_irreducibleComponents`：vanishingIdeal_irred
ucibleComponents : vanishingIdeal '' (irreducibleComponents <| PrimeSpectrum R) 
= minimalPrimes R
· 使用定理 `PrimeSpectrum.vanishingIdeal_closure`：vanishingIdeal_closure (t : Set (P
rimeSpectrum R)) : vanishingIdeal (closure t) = vanishingIdeal t
-/
lemma vanishingIdeal_mem_minimalPrimes {s : Set (PrimeSpectrum R)} :
    vanishingIdeal s ∈ minimalPrimes R ↔ closure s ∈ irreducibleComponents (PrimeSpectrum R) := by
  constructor
  · rw [← zeroLocus_minimalPrimes, ← zeroLocus_vanishingIdeal_eq_closure]
    exact Set.mem_image_of_mem _
  · rw [← vanishingIdeal_irreducibleComponents, ← vanishingIdeal_closure]
    exact Set.mem_image_of_mem _
/-
**PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents** 是 Mathlib 中的一个引理，位于命
名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_ideal_mem_irreducibleComponents {I : Ideal R} : zeroLocus I in i
rreducibleComponents (PrimeSpectrum R) ↔ I.radical in minimalPrimes R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`：vanishingIdeal_zeroLo
cus_eq_radical (I : Ideal R) : vanishingIdeal (zeroLocus (I : Set R)) = I.radica
l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `PrimeSpectrum.vanishingIdeal_mem_minimalPrimes`：vanishingIdeal_mem_minim
alPrimes {s : Set (PrimeSpectrum R)} : vanishingIdeal s in minimalPrimes R ↔ clo
sure s in irreducibleComponents (Pri…
-/
lemma zeroLocus_ideal_mem_irreducibleComponents {I : Ideal R} :
    zeroLocus I ∈ irreducibleComponents (PrimeSpectrum R) ↔ I.radical ∈ minimalPrimes R := by
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  conv_lhs => rw [← (isClosed_zeroLocus _).closure_eq]
  exact vanishingIdeal_mem_minimalPrimes.symm

end CommSemiring

end PrimeSpectrum

namespace IsLocalRing

variable [CommSemiring R] [IsLocalRing R]

/-- The closed point in the prime spectrum of a local ring. -/
/-
**IsLocalRing.closedPoint** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing`。
形式化陈述：closedPoint : PrimeSpectrum R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closed point in the prime spectrum of a local ring.
-/
def closedPoint : PrimeSpectrum R :=
  ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩
/-
**IsLocalRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop (PrimeSpectrum R) where
  top := closedPoint R
  le_top := fun _ ↦ le_maximalIdeal Ideal.IsPrime.ne_top'
/-
**IsLocalRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDomain R] : BoundedOrder (PrimeSpectrum R) where

@[simp]
/-
**IsLocalRing.PrimeSpectrum.asIdeal_top** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing.P
rimeSpectrum`。
形式化陈述：∀ (R : Type u) [inst : CommSemiring R] [inst_1 : IsLocalRing R], ⊤.asIdeal
 = IsLocalRing.maximalIdeal R
参数：R : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PrimeSpectrum.asIdeal_top : (⊤ : PrimeSpectrum R).asIdeal = IsLocalRing.maximalIdeal R :=
  rfl

variable {R}
/-
**IsLocalRing.isLocalHom_iff_comap_closedPoint** 是 Mathlib 中的一个定理，位于命名空间 `IsLoca
lRing`。
形式化陈述：isLocalHom_iff_comap_closedPoint {S : Type v} [CommSemiring S] [IsLocalRin
g S] (f : R ->+* S) : IsLocalHom f ↔ PrimeSpectrum.comap f (closedPoint S) = clo
sedPoint R
参数：f : R ->+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsLocalRing.local_hom_TFAE`：local_hom_TFAE (f : R ->+* S) : List.TFAE [I
sLocalHom f, f '' maximalIdeal R subseteq maximalIdeal S, (maximalIdeal R).map f
 <= maximalIdeal…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.ext_iff`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : P
rimeSpectrum R}, x = y ↔ x.asIdeal = y.asIdeal
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLocalHom_iff_comap_closedPoint {S : Type v} [CommSemiring S] [IsLocalRing S]
    (f : R →+* S) : IsLocalHom f ↔ PrimeSpectrum.comap f (closedPoint S) = closedPoint R := by
  -- Porting note: inline `this` does **not** work
  have := (local_hom_TFAE f).out 0 4
  rw [this, PrimeSpectrum.ext_iff]
  rfl

@[simp]
/-
**IsLocalRing.comap_closedPoint** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：comap_closedPoint {S : Type v} [CommSemiring S] [IsLocalRing S] (f : R ->+
* S) [IsLocalHom f] : PrimeSpectrum.comap f (closedPoint S) = closedPoint R
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalRing.isLocalHom_iff_comap_closedPoint`：isLocalHom_iff_comap_close
dPoint {S : Type v} [CommSemiring S] [IsLocalRing S] (f : R ->+* S) : IsLocalHom
 f ↔ PrimeSpectrum.comap f (closed…
-/
theorem comap_closedPoint {S : Type v} [CommSemiring S] [IsLocalRing S] (f : R →+* S)
    [IsLocalHom f] : PrimeSpectrum.comap f (closedPoint S) = closedPoint R :=
  (isLocalHom_iff_comap_closedPoint f).mp inferInstance
/-
**IsLocalRing.specializes_closedPoint** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：specializes_closedPoint (x : PrimeSpectrum R) : x ⤳ closedPoint R
参数：x : PrimeSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.le_iff_specializes`：le_iff_specializes (x y : PrimeSpectru
m R) : x <= y ↔ x ⤳ y
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem specializes_closedPoint (x : PrimeSpectrum R) : x ⤳ closedPoint R :=
  (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal x.2.1)
/-
**IsLocalRing.closedPoint_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：closedPoint_mem_iff (U : TopologicalSpace.Opens <| PrimeSpectrum R) : clos
edPoint R in U ↔ U = ⊤
参数：U : TopologicalSpace.Opens <| PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `IsLocalRing.specializes_closedPoint`：specializes_closedPoint (x : PrimeS
pectrum R) : x ⤳ closedPoint R
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用引理 `TopologicalSpace.Opens.mem_top`：mem_top (x : α) : x in (⊤ : Opens α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem closedPoint_mem_iff (U : TopologicalSpace.Opens <| PrimeSpectrum R) :
    closedPoint R ∈ U ↔ U = ⊤ := by
  constructor
  · rw [eq_top_iff]
    exact fun h x _ => (specializes_closedPoint x).mem_open U.2 h
  · rintro rfl
    exact TopologicalSpace.Opens.mem_top _
/-
**IsLocalRing.closed_point_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：closed_point_mem_iff {U : TopologicalSpace.Opens (PrimeSpectrum R)} : clos
edPoint R in U ↔ U = ⊤
参数：PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `IsLocalRing.specializes_closedPoint`：specializes_closedPoint (x : PrimeS
pectrum R) : x ⤳ closedPoint R
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma closed_point_mem_iff {U : TopologicalSpace.Opens (PrimeSpectrum R)} :
    closedPoint R ∈ U ↔ U = ⊤ :=
  ⟨(eq_top_iff.mpr fun x _ ↦ (specializes_closedPoint x).mem_open U.2 ·), (· ▸ trivial)⟩

@[simp]
/-
**IsLocalRing.PrimeSpectrum.comap_residue** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing
.PrimeSpectrum`。
形式化陈述：∀ (T : Type u) [inst : CommRing T] [inst_1 : IsLocalRing T] (x : PrimeSpec
trum (IsLocalRing.ResidueField T)),   PrimeSpectrum.comap (IsLocalRing.residue T
) x = IsLocalRing.closedPoint T
参数：T : Type u；x : PrimeSpectrum (IsLocalRing.ResidueField T)；IsLocalRing.residue
 T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
-/
theorem PrimeSpectrum.comap_residue (T : Type u) [CommRing T] [IsLocalRing T]
    (x : PrimeSpectrum (ResidueField T)) : PrimeSpectrum.comap (residue T) x = closedPoint T := by
  rw [Subsingleton.elim x ⊥]
  ext1
  exact Ideal.mk_ker

variable (R) in
/-
**IsLocalRing.isClosed_singleton_closedPoint** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalR
ing`。
形式化陈述：isClosed_singleton_closedPoint : IsClosed {closedPoint R}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.isClosed_singleton_iff_isMaximal`：isClosed_singleton_iff_i
sMaximal (x : PrimeSpectrum R) : IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asId
eal.IsMaximal
· 使用定理 `IsLocalRing.closedPoint.eq_1`：∀ (R : Type u) [inst : CommSemiring R] [in
st_1 : IsLocalRing R],   IsLocalRing.closedPoint R = { asIdeal := IsLocalRing.ma
ximalIdeal R, isPr…
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
-/
lemma isClosed_singleton_closedPoint : IsClosed {closedPoint R} := by
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal, closedPoint]
  infer_instance
/-
**IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `IsLoca
lRing.Ring.KrullDimLE`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : IsLocalRing R] [inst_2 : 
IsDomain R] [Ring.KrullDimLE 1 R]   (x : PrimeSpectrum R), x = ⊥ ∨ x = ⊤
参数：x : PrimeSpectrum R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Order.krullDim_le_one_iff_of_boundedOrder`：krullDim_le_one_iff_of_bounde
dOrder [BoundedOrder α] : krullDim α <= 1 ↔ forall x : α, x = ⊥ ∨ x = ⊤
· 使用定理 `Order.KrullDimLE.krullDim_le`：∀ {n : ℕ} {α : Type u_1} {inst : Preorder 
α} [self : Order.KrullDimLE n α], Order.krullDim α ≤ ↑n
-/
theorem Ring.KrullDimLE.eq_bot_or_eq_top [IsDomain R] [Ring.KrullDimLE 1 R]
    (x : PrimeSpectrum R) : x = ⊥ ∨ x = ⊤ :=
  Order.krullDim_le_one_iff_of_boundedOrder.mp Order.KrullDimLE.krullDim_le _

end IsLocalRing

section KrullDimension

/-
**PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim [CommSemiring R] : topol
ogicalKrullDim (PrimeSpectrum R) = ringKrullDim R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.krullDim_orderDual`：∀ {α : Type u_1} [inst : Preorder α], Order.kr
ullDim αᵒᵈ = Order.krullDim α
· 使用引理 `Order.krullDim_eq_of_orderIso`：krullDim_eq_of_orderIso (f : α ≃o β) : kr
ullDim α = krullDim β
-/
theorem PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim [CommSemiring R] :
    topologicalKrullDim (PrimeSpectrum R) = ringKrullDim R :=
  Order.krullDim_orderDual.symm.trans <| Order.krullDim_eq_of_orderIso
  (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm

end KrullDimension

section Idempotent

variable {R} [CommRing R]

namespace PrimeSpectrum

@[stacks 00EC]
/-
**PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem** 是 Mathlib 中的一个引理，位于
命名空间 `PrimeSpectrum`。
形式化陈述：basicOpen_eq_zeroLocus_of_isIdempotentElem (e : R) (he : IsIdempotentElem 
e) : basicOpen e = zeroLocus {1 - e}
参数：e : R；he : IsIdempotentElem e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.basicOpen_eq_zeroLocus_of_mul_add`：basicOpen_eq_zeroLocus_
of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) : basicOpen e = zeroLoc
us {f}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
-/
lemma basicOpen_eq_zeroLocus_of_isIdempotentElem
    (e : R) (he : IsIdempotentElem e) :
    basicOpen e = zeroLocus {1 - e} :=
  basicOpen_eq_zeroLocus_of_mul_add _ _ (by simp [mul_sub, he.eq]) (by simp)

@[stacks 00EC]
/-
**PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem** 是 Mathlib 中的一个引理，位于
命名空间 `PrimeSpectrum`。
形式化陈述：zeroLocus_eq_basicOpen_of_isIdempotentElem (e : R) (he : IsIdempotentElem 
e) : zeroLocus {e} = basicOpen (1 - e)
参数：e : R；he : IsIdempotentElem e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem`：basicOpen_eq_z
eroLocus_of_isIdempotentElem (e : R) (he : IsIdempotentElem e) : basicOpen e = z
eroLocus {1 - e}
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
lemma zeroLocus_eq_basicOpen_of_isIdempotentElem
    (e : R) (he : IsIdempotentElem e) :
    zeroLocus {e} = basicOpen (1 - e) := by
  rw [basicOpen_eq_zeroLocus_of_isIdempotentElem _ he.one_sub, sub_sub_cancel]
/-
**PrimeSpectrum.isClopen_iff** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isClopen_iff {s : Set (PrimeSpectrum R)} : IsClopen s ↔ exists e : R, IsId
empotentElem e ∧ s = basicOpen e
参数：PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`：exists_idempot
ent_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)} (hs : IsClopen s) : exi
sts e : R, IsIdempotentElem e ∧ s = basicOpen …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem`：basicOpen_eq_z
eroLocus_of_isIdempotentElem (e : R) (he : IsIdempotentElem e) : basicOpen e = z
eroLocus {1 - e}
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isClopen_iff {s : Set (PrimeSpectrum R)} :
    IsClopen s ↔ ∃ e : R, IsIdempotentElem e ∧ s = basicOpen e := by
  refine ⟨exists_idempotent_basicOpen_eq_of_isClopen, ?_⟩
  rintro ⟨e, he, rfl⟩
  refine ⟨?_, (basicOpen e).2⟩
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  exact isClosed_zeroLocus _
/-
**PrimeSpectrum.isClopen_iff_zeroLocus** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`
。
形式化陈述：isClopen_iff_zeroLocus {s : Set (PrimeSpectrum R)} : IsClopen s ↔ exists e
 : R, IsIdempotentElem e ∧ s = zeroLocus {e}
参数：PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `PrimeSpectrum.isClopen_iff`：isClopen_iff {s : Set (PrimeSpectrum R)} : I
sClopen s ↔ exists e : R, IsIdempotentElem e ∧ s = basicOpen e
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem`：basicOpen_eq_z
eroLocus_of_isIdempotentElem (e : R) (he : IsIdempotentElem e) : basicOpen e = z
eroLocus {1 - e}
· 使用引理 `PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem`：zeroLocus_eq_b
asicOpen_of_isIdempotentElem (e : R) (he : IsIdempotentElem e) : zeroLocus {e} =
 basicOpen (1 - e)
-/
lemma isClopen_iff_zeroLocus {s : Set (PrimeSpectrum R)} :
    IsClopen s ↔ ∃ e : R, IsIdempotentElem e ∧ s = zeroLocus {e} :=
  isClopen_iff.trans <| ⟨fun ⟨e, he, h⟩ ↦ ⟨1 - e, he.one_sub,
    h.trans (basicOpen_eq_zeroLocus_of_isIdempotentElem e he)⟩,
    fun ⟨e, he, h⟩ ↦ ⟨1 - e, he.one_sub, h.trans (zeroLocus_eq_basicOpen_of_isIdempotentElem e he)⟩⟩

open TopologicalSpace (Clopens Opens)

/-- Clopen subsets in the prime spectrum of a commutative ring are in 1-1 correspondence
with idempotent elements in the ring. -/
@[stacks 00EE]
/-
**PrimeSpectrum.isIdempotentElemEquivClopens** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpe
ctrum`。
形式化陈述：isIdempotentElemEquivClopens : {e : R // IsIdempotentElem e} ≃o Clopens (P
rimeSpectrum R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Clopen subsets in the prime spectrum of a commutative ring are in 1-1 correspond
ence
with idempotent elements in the ring.
-/
def isIdempotentElemEquivClopens :
    {e : R // IsIdempotentElem e} ≃o Clopens (PrimeSpectrum R) :=
  .trans .isIdempotentElemMulZeroAddOne mulZeroAddOneEquivClopens
/-
**PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm** 是 Mathlib 中的一个引理，位
于命名空间 `PrimeSpectrum`。
形式化陈述：basicOpen_isIdempotentElemEquivClopens_symm (s) : basicOpen (isIdempotentE
lemEquivClopens (R
参数：s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
-/
lemma basicOpen_isIdempotentElemEquivClopens_symm (s) :
    basicOpen (isIdempotentElemEquivClopens (R := R).symm s).1 = s.toOpens :=
  Opens.ext <| congr_arg (·.1) (isIdempotentElemEquivClopens.apply_symm_apply s)
/-
**PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply** 是 Mathlib 中的一个引理，位于命名空间
 `PrimeSpectrum`。
形式化陈述：coe_isIdempotentElemEquivClopens_apply (e) : (isIdempotentElemEquivClopens
 e : Set (PrimeSpectrum R)) = basicOpen (e.1 : R)
参数：e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_isIdempotentElemEquivClopens_apply (e) :
    (isIdempotentElemEquivClopens e : Set (PrimeSpectrum R)) = basicOpen (e.1 : R) := rfl
/-
**PrimeSpectrum.isIdempotentElemEquivClopens_apply_toOpens** 是 Mathlib 中的一个引理，位于
命名空间 `PrimeSpectrum`。
形式化陈述：isIdempotentElemEquivClopens_apply_toOpens (e) : (isIdempotentElemEquivClo
pens e).toOpens = basicOpen (e.1 : R)
参数：e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIdempotentElemEquivClopens_apply_toOpens (e) :
    (isIdempotentElemEquivClopens e).toOpens = basicOpen (e.1 : R) := rfl
/-
**PrimeSpectrum.isIdempotentElemEquivClopens_mul** 是 Mathlib 中的一个引理，位于命名空间 `Prim
eSpectrum`。
形式化陈述：isIdempotentElemEquivClopens_mul (e₁ e₂ : {e : R | IsIdempotentElem e}) : 
isIdempotentElemEquivClopens ⟨_, e₁.2.mul e₂.2⟩ = isIdempotentElemEquivClopens e
₁ ⊓ isIdempotentElemEquivClopens e₂
参数：e₁ e₂ : {e : R | IsIdempotentElem e}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InfHomClass.map_inf`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Min α} {inst_1 : Min β} {inst_2 : FunLike F α β}   [self : InfHomClass F α β
] (f : F)…
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `OrderIsoClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Typ
e u_3} [inst : EquivLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : OrderTop
 α] [inst_3 : Semila…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
lemma isIdempotentElemEquivClopens_mul (e₁ e₂ : {e : R | IsIdempotentElem e}) :
    isIdempotentElemEquivClopens ⟨_, e₁.2.mul e₂.2⟩ =
      isIdempotentElemEquivClopens e₁ ⊓ isIdempotentElemEquivClopens e₂ :=
  map_inf ..
/-
**PrimeSpectrum.isIdempotentElemEquivClopens_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `
PrimeSpectrum`。
形式化陈述：isIdempotentElemEquivClopens_one_sub (e : {e : R | IsIdempotentElem e}) : 
isIdempotentElemEquivClopens ⟨_, e.2.one_sub⟩ = (isIdempotentElemEquivClopens e)
ᶜ
参数：e : {e : R | IsIdempotentElem e}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_compl`：map_compl (a : α) : f aᶜ = (f a)ᶜ
· 使用定理 `OrderIsoClass.toHeytingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Ty
pe u_3} [inst : EquivLike F α β] [inst_1 : HeytingAlgebra α]   {x : HeytingAlgeb
ra β} [OrderIsoClass …
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
lemma isIdempotentElemEquivClopens_one_sub (e : {e : R | IsIdempotentElem e}) :
    isIdempotentElemEquivClopens ⟨_, e.2.one_sub⟩ = (isIdempotentElemEquivClopens e)ᶜ :=
  map_compl ..
/-
**PrimeSpectrum.isIdempotentElemEquivClopens_symm_inf** 是 Mathlib 中的一个引理，位于命名空间 
`PrimeSpectrum`。
形式化陈述：isIdempotentElemEquivClopens_symm_inf (s₁ s₂) : letI e
参数：s₁ s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InfHomClass.map_inf`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Min α} {inst_1 : Min β} {inst_2 : FunLike F α β}   [self : InfHomClass F α β
] (f : F)…
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `OrderIsoClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Typ
e u_3} [inst : EquivLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : OrderTop
 α] [inst_3 : Semila…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
lemma isIdempotentElemEquivClopens_symm_inf (s₁ s₂) :
    letI e := isIdempotentElemEquivClopens (R := R).symm
    e (s₁ ⊓ s₂) = ⟨_, (e s₁).2.mul (e s₂).2⟩ :=
  map_inf ..
/-
**PrimeSpectrum.isIdempotentElemEquivClopens_symm_compl** 是 Mathlib 中的一个引理，位于命名空
间 `PrimeSpectrum`。
形式化陈述：isIdempotentElemEquivClopens_symm_compl (s : Clopens (PrimeSpectrum R)) : 
isIdempotentElemEquivClopens.symm sᶜ = ⟨_, (isIdempotentElemEquivClopens.symm s)
.2.one_sub⟩
参数：s : Clopens (PrimeSpectrum R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_compl`：map_compl (a : α) : f aᶜ = (f a)ᶜ
· 使用定理 `OrderIsoClass.toHeytingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Ty
pe u_3} [inst : EquivLike F α β] [inst_1 : HeytingAlgebra α]   {x : HeytingAlgeb
ra β} [OrderIsoClass …
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
lemma isIdempotentElemEquivClopens_symm_compl (s : Clopens (PrimeSpectrum R)) :
    isIdempotentElemEquivClopens.symm sᶜ = ⟨_, (isIdempotentElemEquivClopens.symm s).2.one_sub⟩ :=
  map_compl ..
/-
**PrimeSpectrum.isIdempotentElemEquivClopens_symm_top** 是 Mathlib 中的一个引理，位于命名空间 
`PrimeSpectrum`。
形式化陈述：isIdempotentElemEquivClopens_symm_top : isIdempotentElemEquivClopens.symm 
⊤ = ⟨(1 : R), .one⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopHomClass.map_top`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Top α} {inst_1 : Top β}   {inst_2 : FunLike F α β} [se
lf : TopH…
· 使用定理 `InfTopHomClass.toTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Min α] [inst_2 : Min β] [inst_3 : Top α]  
 [inst_4 : Top β] …
· 使用定理 `OrderIsoClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Typ
e u_3} [inst : EquivLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : OrderTop
 α] [inst_3 : Semila…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
lemma isIdempotentElemEquivClopens_symm_top :
    isIdempotentElemEquivClopens.symm ⊤ = ⟨(1 : R), .one⟩ :=
  map_top _
/-
**PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot** 是 Mathlib 中的一个引理，位于命名空间 
`PrimeSpectrum`。
形式化陈述：isIdempotentElemEquivClopens_symm_bot : isIdempotentElemEquivClopens.symm 
⊥ = ⟨(0 : R), .zero⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BotHomClass.map_bot`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Bot α} {inst_1 : Bot β}   {inst_2 : FunLike F α β} [se
lf : BotH…
· 使用定理 `SupBotHomClass.toBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Max α] [inst_2 : Max β] [inst_3 : Bot α]  
 [inst_4 : Bot β] …
· 使用定理 `OrderIsoClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Typ
e u_3} [inst : EquivLike F α β] [inst_1 : SemilatticeSup α]   [inst_2 : OrderBot
 α] [inst_3 : Semila…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
lemma isIdempotentElemEquivClopens_symm_bot :
    isIdempotentElemEquivClopens.symm ⊥ = ⟨(0 : R), .zero⟩ :=
  map_bot _
/-
**PrimeSpectrum.isIdempotentElemEquivClopens_symm_sup** 是 Mathlib 中的一个引理，位于命名空间 
`PrimeSpectrum`。
形式化陈述：isIdempotentElemEquivClopens_symm_sup (s₁ s₂ : Clopens (PrimeSpectrum R)) 
: letI e
参数：s₁ s₂ : Clopens (PrimeSpectrum R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `OrderIsoClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Typ
e u_3} [inst : EquivLike F α β] [inst_1 : SemilatticeSup α]   [inst_2 : OrderBot
 α] [inst_3 : Semila…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
lemma isIdempotentElemEquivClopens_symm_sup (s₁ s₂ : Clopens (PrimeSpectrum R)) :
    letI e := isIdempotentElemEquivClopens (R := R).symm
    e (s₁ ⊔ s₂) = ⟨_, (e s₁).2.add_sub_mul (e s₂).2⟩ :=
  map_sup ..

end PrimeSpectrum

end Idempotent

