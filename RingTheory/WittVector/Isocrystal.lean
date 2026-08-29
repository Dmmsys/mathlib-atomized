/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.RingTheory.WittVector.FrobeniusFractionField

/-!

## F-isocrystals over a perfect field

When `k` is an integral domain, so is `𝕎 k`, and we can consider its field of fractions `K(p, k)`.
The endomorphism `WittVector.frobenius` lifts to `φ : K(p, k) → K(p, k)`; if `k` is perfect, `φ` is
an automorphism.

Let `k` be a perfect integral domain. Let `V` be a vector space over `K(p,k)`.
An *isocrystal* is a bijective map `V → V` that is `φ`-semilinear.
A theorem of Dieudonné and Manin classifies the finite-dimensional isocrystals over algebraically
closed fields. In the one-dimensional case, this classification states that the isocrystal
structures are parametrized by their "slope" `m : ℤ`.
Any one-dimensional isocrystal is isomorphic to `φ(p^m • x) : K(p,k) → K(p,k)` for some `m`.

This file proves this one-dimensional case of the classification theorem.
The construction is described in Dupuis, Lewis, and Macbeth,
[Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022].

## Main declarations

* `WittVector.Isocrystal`: a vector space over the field `K(p, k)` additionally equipped with a
  Frobenius-linear automorphism.
* `WittVector.isocrystal_classification`: a one-dimensional isocrystal admits an isomorphism to one
  of the standard one-dimensional isocrystals.

## Notation

This file introduces notation in the scope `Isocrystal`.
* `K(p, k)`: `FractionRing (WittVector p k)`
* `φ(p, k)`: `WittVector.FractionRing.frobeniusRingHom p k`
* `M →ᶠˡ[p, k] M₂`: `LinearMap (WittVector.FractionRing.frobeniusRingHom p k) M M₂`
* `M ≃ᶠˡ[p, k] M₂`: `LinearEquiv (WittVector.FractionRing.frobeniusRingHom p k) M M₂`
* `Φ(p, k)`: `WittVector.Isocrystal.frobenius p k`
* `M →ᶠⁱ[p, k] M₂`: `WittVector.IsocrystalHom p k M M₂`
* `M ≃ᶠⁱ[p, k] M₂`: `WittVector.IsocrystalEquiv p k M M₂`

## References

* [Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022]
* [Theory of commutative formal groups over fields of finite characteristic][manin1963]
* <https://www.math.ias.edu/~lurie/205notes/Lecture26-Isocrystals.pdf>

-/

@[expose] public section

noncomputable section

open Module

namespace WittVector

variable (p : Nat) [Fact p.Prime]
variable (k : Type*) [CommRing k]

/-- The fraction ring of the space of `p`-Witt vectors on `k` -/
scoped[Isocrystal] notation "K(" p ", " k ")" => FractionRing (WittVector p k)

open Isocrystal

section PerfectRing

variable [IsDomain k] [CharP k p] [PerfectRing k p]

/-! ### Frobenius-linear maps -/


/--
Definition of `FractionRing.frobenius` / `FractionRing.frobenius` 的定义

English:
definition FractionRing.frobenius
  signature: : K(p, k) ≃+* K(p, k)
  body: IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)

中文:
定义 FractionRing.frobenius
  签名: : K(p, k) ≃+* K(p, k)
  定义体: IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)

Depends on / 依赖: IsFractionRing, IsFractionRing.ringEquivOfRingEquiv, frobeniusEquiv, ringEquivOfRingEquiv
-/
def FractionRing.frobenius : K(p, k) ≃+* K(p, k) :=
  IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)

/--
Definition of `FractionRing.frobeniusRingHom` / `FractionRing.frobeniusRingHom` 的定义

English:
definition FractionRing.frobeniusRingHom
  signature: : K(p, k) ->+* K(p, k)
  body: FractionRing.frobenius p k

@[inherit_doc]
scoped[Isocrystal] notation "φ(" p ", " k ")" => WittVector.FractionRing.frobeniusRingHom p k

中文:
定义 FractionRing.frobeniusRingHom
  签名: : K(p, k) ->+* K(p, k)
  定义体: FractionRing.frobenius p k

@[inherit_doc]
scoped[Isocrystal] notation "φ(" p ", " k ")" => WittVector.FractionRing.frobeniusRingHom p k

Depends on / 依赖: FractionRing, FractionRing.frobenius, frobenius
-/
def FractionRing.frobeniusRingHom : K(p, k) ->+* K(p, k) :=
  FractionRing.frobenius p k

@[inherit_doc]
scoped[Isocrystal] notation "φ(" p ", " k ")" => WittVector.FractionRing.frobeniusRingHom p k

/--
Instance `inv_pair₁` / 实例 `inv_pair₁`

English:
instance inv_pair₁
  signature: : RingHomInvPair φ(p, k) (FractionRing.frobenius p k).symm
  body: RingHomInvPair.of_ringEquiv (FractionRing.frobenius p k)

中文:
实例 inv_pair₁
  签名: : RingHomInvPair φ(p, k) (FractionRing.frobenius p k).symm
  定义体: RingHomInvPair.of_ringEquiv (FractionRing.frobenius p k)

Depends on / 依赖: FractionRing, FractionRing.frobenius, RingHomInvPair, RingHomInvPair.of_ringEquiv, frobenius, of_ringEquiv
-/
instance inv_pair₁ : RingHomInvPair φ(p, k) (FractionRing.frobenius p k).symm :=
  RingHomInvPair.of_ringEquiv (FractionRing.frobenius p k)

/--
Instance `inv_pair₂` / 实例 `inv_pair₂`

English:
instance inv_pair₂
  signature: : RingHomInvPair ((FractionRing.frobenius p k).symm : K(p, k) ->+* K(p, k))
  body: RingHomInvPair.of_ringEquiv (FractionRing.frobenius p k).symm

中文:
实例 inv_pair₂
  签名: : RingHomInvPair ((FractionRing.frobenius p k).symm : K(p, k) ->+* K(p, k))
  定义体: RingHomInvPair.of_ringEquiv (FractionRing.frobenius p k).symm

Depends on / 依赖: FractionRing, FractionRing.frobenius, RingHomInvPair, RingHomInvPair.of_ringEquiv, frobenius, of_ringEquiv
-/
instance inv_pair₂ : RingHomInvPair ((FractionRing.frobenius p k).symm : K(p, k) ->+* K(p, k))
    (FractionRing.frobenius p k) :=
  RingHomInvPair.of_ringEquiv (FractionRing.frobenius p k).symm

/-- The Frobenius automorphism of `k`, as a linear map -/
scoped[Isocrystal]
  notation3:50 M " ->ᶠˡ[" p ", " k "] " M₂ =>
    LinearMap (WittVector.FractionRing.frobeniusRingHom p k) M M₂

/-- The Frobenius automorphism of `k`, as a linear equivalence -/
scoped[Isocrystal]
  notation3:50 M " ≃ᶠˡ[" p ", " k "] " M₂ =>
    LinearEquiv (WittVector.FractionRing.frobeniusRingHom p k) M M₂

/-! ### Isocrystals -/


/--
Definition of `Isocrystal` / `Isocrystal` 的定义

English:
class Isocrystal
  parameters: (V : Type*) [AddCommGroup V]
  extends: Module K(p, k) V
  axioms and operations (1):
    - frob : V ≃ᶠˡ[p, k] V

中文:
类 Isocrystal
  参数: (V : 类型) [AddCommGroup V]
  继承: Module K(p, k) V
  公理与运算 (1 个):
    - frob : V ≃ᶠˡ[p, k] V
-/
class Isocrystal (V : Type*) [AddCommGroup V] extends Module K(p, k) V where
  frob : V ≃ᶠˡ[p, k] V

open WittVector

variable (V : Type*) [AddCommGroup V] [Isocrystal p k V]
variable (V₂ : Type*) [AddCommGroup V₂] [Isocrystal p k V₂]

variable {V} in
/--
Definition of `Isocrystal.frobenius` / `Isocrystal.frobenius` 的定义

English:
definition Isocrystal.frobenius
  signature: : V ≃ᶠˡ[p, k] V
  body: Isocrystal.frob (p := p) (k := k) (V := V)

@[inherit_doc] scoped[Isocrystal] notation "Φ(" p ", " k ")" => WittVector.Isocrystal.frobenius p k

中文:
定义 Isocrystal.frobenius
  签名: : V ≃ᶠˡ[p, k] V
  定义体: Isocrystal.frob (p := p) (k := k) (V := V)

@[inherit_doc] scoped[Isocrystal] notation "Φ(" p ", " k ")" => WittVector.Isocrystal.frobenius p k

Depends on / 依赖: Isocrystal, Isocrystal.frob
-/
def Isocrystal.frobenius : V ≃ᶠˡ[p, k] V :=
  Isocrystal.frob (p := p) (k := k) (V := V)

@[inherit_doc] scoped[Isocrystal] notation "Φ(" p ", " k ")" => WittVector.Isocrystal.frobenius p k

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `IsocrystalHom` / `IsocrystalHom` 的定义

English:
structure IsocrystalHom
  parameters: extends V ->ₗ[K(p, k)] V₂
  extends: V ->ₗ[K(p, k)] V₂
  axioms and operations (1):
    - frob_equivariant : forall x : V, Φ(p, k) (toLinearMap x) = toLinearMap (Φ(p, k) x)

中文:
结构 IsocrystalHom
  参数: extends V ->ₗ[K(p, k)] V₂
  继承: V ->ₗ[K(p, k)] V₂
  公理与运算 (1 个):
    - frob_equivariant : 对任意 x : V, Φ(p, k) (toLinearMap x) = toLinearMap (Φ(p, k) x)

Depends on / 依赖: NormalSpace, PseudoMetrizableSpace
-/
structure IsocrystalHom extends V ->ₗ[K(p, k)] V₂ where
  frob_equivariant : forall x : V, Φ(p, k) (toLinearMap x) = toLinearMap (Φ(p, k) x)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `IsocrystalEquiv` / `IsocrystalEquiv` 的定义

English:
structure IsocrystalEquiv
  parameters: extends V ≃ₗ[K(p, k)] V₂
  extends: V ≃ₗ[K(p, k)] V₂
  axioms and operations (1):
    - frob_equivariant : forall x : V, Φ(p, k) (toLinearEquiv x) = toLinearEquiv (Φ(p, k) x)

中文:
结构 IsocrystalEquiv
  参数: extends V ≃ₗ[K(p, k)] V₂
  继承: V ≃ₗ[K(p, k)] V₂
  公理与运算 (1 个):
    - frob_equivariant : 对任意 x : V, Φ(p, k) (toLinearEquiv x) = toLinearEquiv (Φ(p, k) x)

Depends on / 依赖: PerfectlyNormalSpace, PseudoMetrizableSpace
-/
structure IsocrystalEquiv extends V ≃ₗ[K(p, k)] V₂ where
  frob_equivariant : forall x : V, Φ(p, k) (toLinearEquiv x) = toLinearEquiv (Φ(p, k) x)

@[inherit_doc] scoped[Isocrystal]
notation:50 M " ->ᶠⁱ[" p ", " k "] " M₂ => WittVector.IsocrystalHom p k M M₂

@[inherit_doc] scoped[Isocrystal]
notation:50 M " ≃ᶠⁱ[" p ", " k "] " M₂ => WittVector.IsocrystalEquiv p k M M₂

end PerfectRing

open scoped Isocrystal

/-! ### Classification of isocrystals in dimension 1 -/

/-- Type synonym for `K(p, k)` to carry the standard 1-dimensional isocrystal structure
of slope `m : ℤ`.
-/
@[nolint unusedArguments]
/--
Definition of `StandardOneDimIsocrystal` / `StandardOneDimIsocrystal` 的定义

English:
definition StandardOneDimIsocrystal
  signature: (_m : Int)
  body: K(p, k)
deriving AddCommGroup, Module K(p, k)

中文:
定义 StandardOneDimIsocrystal
  签名: (_m : 整数)
  定义体: K(p, k)
deriving AddCommGroup, Module K(p, k)

Depends on / 依赖: MetrizableSpace, T4Space
-/
def StandardOneDimIsocrystal (_m : Int) : Type _ :=
  K(p, k)
deriving AddCommGroup, Module K(p, k)

section PerfectRing

variable [IsDomain k] [CharP k p] [PerfectRing k p]

/-- The standard one-dimensional isocrystal of slope `m : ℤ` is an isocrystal. -/
instance (m : Int) : Isocrystal p k (StandardOneDimIsocrystal p k m) where
  frob :=
    (FractionRing.frobenius p k).toSemilinearEquiv.trans
      (LinearEquiv.smulOfNeZero _ _ _ (zpow_ne_zero m (WittVector.FractionRing.p_nonzero p k)))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `StandardOneDimIsocrystal.frobenius_apply` / 定理 `StandardOneDimIsocrystal.frobenius_apply`

English:
theorem StandardOneDimIsocrystal.frobenius_apply
  given: (m : Int) (x : StandardOneDimIsocrystal p k m)
  proof: rfl

中文:
定理 StandardOneDimIsocrystal.frobenius_apply
  条件: (m : 整数) (x : StandardOneDimIsocrystal p k m)
  证明: rfl

Depends on / 依赖: MetrizableSpace, T6Space
-/
theorem StandardOneDimIsocrystal.frobenius_apply (m : Int) (x : StandardOneDimIsocrystal p k m) :
    Φ(p, k) x = (p : K(p, k)) ^ m • φ(p, k) x := rfl

end PerfectRing

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isocrystal_classification` / 定理 `isocrystal_classification`

English:
theorem isocrystal_classification
  statement: (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] (V : Type*)
  proof: by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h_dim
  obtain ⟨x, hx⟩ : exists x : V, x != 0 := exists_ne 0
  have : Φ(p, k) x != 0 := by simpa only [map_zero] using Φ(p, k).injective.ne hx
  obtain ⟨a, ha, hax⟩ : exists a : K(p, k), a != 0 ∧ Φ(p, k) x = a • x := by
    rw [finrank

中文:
定理 isocrystal_classification
  结论: (k : 类型) [Field k] [IsAlgClosed k] [CharP k p] (V : 类型)
  证明: by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h_dim
  obtain ⟨x, hx⟩ : exists x : V, x != 0 := exists_ne 0
  have : Φ(p, k) x != 0 := by simpa only [map_zero] using Φ(p, k).injective.ne hx
  obtain ⟨a, ha, hax⟩ : exists a : K(p, k), a != 0 ∧ Φ(p, k) x = a • x := by
    rw [finrank

Depends on / 依赖: Module, Module.nontrivial_of_finrank_eq_succ, Nontrivial, WittVector, WittVector.exists_frobenius_solut, exists_frobenius_solut, exists_ne, finrank_eq_one_iff_of_nonzero, h_dim, ha.symm, injective, injective.ne, map_zero, nontrivial_of_finrank_eq_succ, zero_smul
-/
theorem isocrystal_classification (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] (V : Type*)
    [AddCommGroup V] [Isocrystal p k V] (h_dim : finrank K(p, k) V = 1) :
    exists m : Int, Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h_dim
  obtain ⟨x, hx⟩ : exists x : V, x != 0 := exists_ne 0
  have : Φ(p, k) x != 0 := by simpa only [map_zero] using Φ(p, k).injective.ne hx
  obtain ⟨a, ha, hax⟩ : exists a : K(p, k), a != 0 ∧ Φ(p, k) x = a • x := by
    rw [finrank_eq_one_iff_of_nonzero' x hx] at h_dim
    obtain ⟨a, ha⟩ := h_dim (Φ(p, k) x)
    refine ⟨a, ?_, ha.symm⟩
    intro ha'
    apply this
    simp only [← ha, ha', zero_smul]
  obtain ⟨b, hb, m, hmb⟩ := WittVector.exists_frobenius_solution_fractionRing p ha
  replace hmb : φ(p, k) b * a = (p : K(p, k)) ^ m * b := by convert! hmb
  use m
  let F₀ : StandardOneDimIsocrystal p k m ->ₗ[K(p, k)] V := LinearMap.toSpanSingleton K(p, k) V x
  let F : StandardOneDimIsocrystal p k m ≃ₗ[K(p, k)] V := by
    refine LinearEquiv.ofBijective F₀ ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot]
      exact LinearMap.ker_toSpanSingleton K(p, k) hx
    · rw [← LinearMap.range_eq_top]
      rw [← (finrank_eq_one_iff_of_nonzero x hx).mp h_dim]
      rw [LinearMap.span_singleton_eq_range]
  refine ⟨⟨(LinearEquiv.smulOfNeZero K(p, k) _ _ hb).trans F, fun c => ?_⟩⟩
  rw [LinearEquiv.trans_apply]; rw [LinearEquiv.trans_apply]; rw [LinearEquiv.smulOfNeZero_apply]; rw [LinearEquiv.smulOfNeZero_apply]; rw [LinearEquiv.map_smul]; rw [LinearEquiv.map_smul]; rw [LinearEquiv.ofBijective_apply]; rw [LinearEquiv.ofBijective_apply]; rw [StandardOneDimIsocrystal.frobenius_apply]
  unfold StandardOneDimIsocrystal
  rw [LinearMap.toSpanSingleton_apply K(p]; rw [k) V x c]; rw [LinearMap.toSpanSingleton_apply K(p]; rw [k) V x]
  simp only [hax, map_smulₛₗ, smul_eq_mul]
  simp only [← mul_smul]
  congr 1
  linear_combination φ(p, k) c * hmb

end WittVector
