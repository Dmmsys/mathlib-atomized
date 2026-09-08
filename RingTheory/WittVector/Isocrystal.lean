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

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [CommRing k]

/-- The fraction ring of the space of `p`-Witt vectors on `k` -/
scoped[Isocrystal] notation "K(" p ", " k ")" => FractionRing (WittVector p k)

open Isocrystal

section PerfectRing

variable [IsDomain k] [CharP k p] [PerfectRing k p]

/-! ### Frobenius-linear maps -/


/-- The Frobenius automorphism of `k` induces an automorphism of `K`. -/
/-
**WittVector.FractionRing.frobenius** 是 Mathlib 中的一个定义，位于命名空间 `WittVector.Fracti
onRing`。
形式化陈述：(p : ℕ) →   [inst : Fact (Nat.Prime p)] →     (k : Type u_1) →       [inst
_1 : CommRing k] →         [CharP k p] → [PerfectRing k p] → FractionRing (WittV
ector p k) ≃+* FractionRing (WittVector p k)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Frobenius automorphism of `k` induces an automorphism of `K`.
-/
def FractionRing.frobenius : K(p, k) ≃+* K(p, k) :=
  IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)

/-- The Frobenius automorphism of `k` induces an endomorphism of `K`. For notation purposes.
Notation `φ(p, k)` in the `Isocrystal` namespace. -/
/-
**WittVector.FractionRing.frobeniusRingHom** 是 Mathlib 中的一个定义，位于命名空间 `WittVector
.FractionRing`。
形式化陈述：(p : ℕ) →   [inst : Fact (Nat.Prime p)] →     (k : Type u_1) →       [inst
_1 : CommRing k] →         [CharP k p] → [PerfectRing k p] → FractionRing (WittV
ector p k) →+* FractionRing (WittVector p k)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Frobenius automorphism of `k` induces an endomorphism of `K`. For notation p
urposes.
Notation `φ(p, k)` in the `Isocrystal` namespace.
-/
def FractionRing.frobeniusRingHom : K(p, k) →+* K(p, k) :=
  FractionRing.frobenius p k

@[inherit_doc]
scoped[Isocrystal] notation "φ(" p ", " k ")" => WittVector.FractionRing.frobeniusRingHom p k
/-
**WittVector.inv_pair** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inv_pair₁ : RingHomInvPair φ(p, k) (FractionRing.frobenius p k).symm :=
  RingHomInvPair.of_ringEquiv (FractionRing.frobenius p k)
/-
**WittVector.inv_pair** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inv_pair₂ : RingHomInvPair ((FractionRing.frobenius p k).symm : K(p, k) →+* K(p, k))
    (FractionRing.frobenius p k) :=
  RingHomInvPair.of_ringEquiv (FractionRing.frobenius p k).symm

/-- The Frobenius automorphism of `k`, as a linear map -/
scoped[Isocrystal]
  notation3:50 M " →ᶠˡ[" p ", " k "] " M₂ =>
    LinearMap (WittVector.FractionRing.frobeniusRingHom p k) M M₂

/-- The Frobenius automorphism of `k`, as a linear equivalence -/
scoped[Isocrystal]
  notation3:50 M " ≃ᶠˡ[" p ", " k "] " M₂ =>
    LinearEquiv (WittVector.FractionRing.frobeniusRingHom p k) M M₂

/-! ### Isocrystals -/


/-- An isocrystal is a vector space over the field `K(p, k)` additionally equipped with a
Frobenius-linear automorphism.
-/
/-
**WittVector.Isocrystal** 是 Mathlib 中的一个归纳类型，位于命名空间 `WittVector`。
形式化陈述：(p : ℕ) →   [Fact (Nat.Prime p)] →     (k : Type u_1) →       [inst : Comm
Ring k] → [CharP k p] → [PerfectRing k p] → (V : Type u_2) → [AddCommGroup V] → 
Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isocrystal is a vector space over the field `K(p, k)` additionally equipped w
ith a
Frobenius-linear automorphism.
-/
class Isocrystal (V : Type*) [AddCommGroup V] extends Module K(p, k) V where
  frob : V ≃ᶠˡ[p, k] V

open WittVector

variable (V : Type*) [AddCommGroup V] [Isocrystal p k V]
variable (V₂ : Type*) [AddCommGroup V₂] [Isocrystal p k V₂]

variable {V} in
/--
Project the Frobenius automorphism from an isocrystal. Denoted by `Φ(p, k)` when V can be inferred.
-/
/-
**WittVector.Isocrystal.frobenius** 是 Mathlib 中的一个定义，位于命名空间 `WittVector.Isocryst
al`。
形式化陈述：(p : ℕ) →   [inst : Fact (Nat.Prime p)] →     (k : Type u_1) →       [inst
_1 : CommRing k] →         [inst_2 : CharP k p] →           [inst_3 : PerfectRin
g k p] →             {V : Type u_2} →               [inst_4 : AddCommGroup V] → 
                [inst_5 : WittVector.Isocrystal p k V] → V ≃ₛₗ[WittVector.Fracti
onRing.frobeniusRingHom p k] V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Project the Frobenius automorphism from an isocrystal. Denoted by `Φ(p, k)` when
 V can be inferred.
-/
def Isocrystal.frobenius : V ≃ᶠˡ[p, k] V :=
  Isocrystal.frob (p := p) (k := k) (V := V)

@[inherit_doc] scoped[Isocrystal] notation "Φ(" p ", " k ")" => WittVector.Isocrystal.frobenius p k

set_option backward.isDefEq.respectTransparency.types false in
/-- A homomorphism between isocrystals respects the Frobenius map.
Notation `M →ᶠⁱ [p, k]` in the `Isocrystal` namespace. -/
/-
**WittVector.IsocrystalHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `WittVector`。
形式化陈述：(p : ℕ) →   [inst : Fact (Nat.Prime p)] →     (k : Type u_1) →       [inst
_1 : CommRing k] →         [inst_2 : CharP k p] →           [inst_3 : PerfectRin
g k p] →             (V : Type u_2) →               [inst_4 : AddCommGroup V] → 
                [WittVector.Isocrystal p k V] →                   (V₂ : Type u_3
) → [inst_6 : AddCommGroup V₂] → [WittVector.Isocrystal p k V₂] → Type (max u_2 
u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homomorphism between isocrystals respects the Frobenius map.
Notation `M →ᶠⁱ [p, k]` in the `Isocrystal` namespace.
-/
structure IsocrystalHom extends V →ₗ[K(p, k)] V₂ where
  frob_equivariant : ∀ x : V, Φ(p, k) (toLinearMap x) = toLinearMap (Φ(p, k) x)

set_option backward.isDefEq.respectTransparency.types false in
/-- An isomorphism between isocrystals respects the Frobenius map.

Notation `M ≃ᶠⁱ [p, k]` in the `Isocrystal` namespace. -/
/-
**WittVector.IsocrystalEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 `WittVector`。
形式化陈述：(p : ℕ) →   [inst : Fact (Nat.Prime p)] →     (k : Type u_1) →       [inst
_1 : CommRing k] →         [inst_2 : CharP k p] →           [inst_3 : PerfectRin
g k p] →             (V : Type u_2) →               [inst_4 : AddCommGroup V] → 
                [WittVector.Isocrystal p k V] →                   (V₂ : Type u_3
) → [inst_6 : AddCommGroup V₂] → [WittVector.Isocrystal p k V₂] → Type (max u_2 
u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism between isocrystals respects the Frobenius map.

Notation `M ≃ᶠⁱ [p, k]` in the `Isocrystal` namespace.
-/
structure IsocrystalEquiv extends V ≃ₗ[K(p, k)] V₂ where
  frob_equivariant : ∀ x : V, Φ(p, k) (toLinearEquiv x) = toLinearEquiv (Φ(p, k) x)

@[inherit_doc] scoped[Isocrystal]
notation:50 M " →ᶠⁱ[" p ", " k "] " M₂ => WittVector.IsocrystalHom p k M M₂

@[inherit_doc] scoped[Isocrystal]
notation:50 M " ≃ᶠⁱ[" p ", " k "] " M₂ => WittVector.IsocrystalEquiv p k M M₂

end PerfectRing

open scoped Isocrystal

/-! ### Classification of isocrystals in dimension 1 -/

/-- Type synonym for `K(p, k)` to carry the standard 1-dimensional isocrystal structure
of slope `m : ℤ`.
-/
@[nolint unusedArguments]
/-
**WittVector.StandardOneDimIsocrystal** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：StandardOneDimIsocrystal (_m : Int) : Type _
参数：_m : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym for `K(p, k)` to carry the standard 1-dimensional isocrystal struct
ure
of slope `m : ℤ`.
-/
def StandardOneDimIsocrystal (_m : ℤ) : Type _ :=
  K(p, k)
deriving AddCommGroup, Module K(p, k)

section PerfectRing

variable [IsDomain k] [CharP k p] [PerfectRing k p]

/-- The standard one-dimensional isocrystal of slope `m : ℤ` is an isocrystal. -/
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard one-dimensional isocrystal of slope `m : ℤ` is an isocrystal.
-/
instance (m : ℤ) : Isocrystal p k (StandardOneDimIsocrystal p k m) where
  frob :=
    (FractionRing.frobenius p k).toSemilinearEquiv.trans
      (LinearEquiv.smulOfNeZero _ _ _ (zpow_ne_zero m (WittVector.FractionRing.p_nonzero p k)))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**WittVector.StandardOneDimIsocrystal.frobenius_apply** 是 Mathlib 中的一个定理，位于命名空间 
`WittVector.StandardOneDimIsocrystal`。
形式化陈述：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (k : Type u_1) [inst_1 : CommRing k]
 [inst_2 : IsDomain k] [inst_3 : CharP k p]   [inst_4 : PerfectRing k p] (m : ℤ)
 (x : WittVector.StandardOneDimIsocrystal p k m),   (WittVector.Isocrystal.frobe
nius p k) x = ↑p ^ m • (WittVector.FractionRing.frobeniusRingHom p k) x
参数：p : ℕ；Nat.Prime p；k : Type u_1；m : ℤ；x : WittVector.StandardOneDimIsocrystal 
p k m；WittVector.Isocrystal.frobenius p k；WittVector.FractionRing.frobeniusRingH
om p k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem StandardOneDimIsocrystal.frobenius_apply (m : ℤ) (x : StandardOneDimIsocrystal p k m) :
    Φ(p, k) x = (p : K(p, k)) ^ m • φ(p, k) x := rfl

end PerfectRing

set_option backward.isDefEq.respectTransparency false in
/-- A one-dimensional isocrystal over an algebraically closed field
admits an isomorphism to one of the standard (indexed by `m : ℤ`) one-dimensional isocrystals. -/
/-
**WittVector.isocrystal_classification** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：isocrystal_classification (k : Type*) [Field k] [IsAlgClosed k] [CharP k p
] (V : Type*) [AddCommGroup V] [Isocrystal p k V] (h_dim : finrank K(p, k) V = 1
) : exists m : Int, Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V)
参数：k : Type*；V : Type*；h_dim : finrank K(p, k) V = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.perfectField`：∀ (k : Type u) [inst : Field k] [IsAlgClosed k
], PerfectField k
· 使用定理 `Module.nontrivial_of_finrank_eq_succ`：Module.nontrivial_of_finrank_eq_su
cc {n : Nat} (hn : finrank R M = n.succ) : Nontrivial M
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `WittVector.instNontrivial`：∀ {p : ℕ} {R : Type u_1} [CommRing R] [Fact (
Nat.Prime p)] [Nontrivial R], Nontrivial (WittVector p R)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `WittVector.instNoZeroDivisorsOfCharP`：∀ {p : ℕ} {R : Type u_1} [hp : Fac
t (Nat.Prime p)] [inst : CommRing R] [CharP R p] [NoZeroDivisors R],   NoZeroDiv
isors (WittVector p R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `finrank_eq_one_iff_of_nonzero'`：finrank_eq_one_iff_of_nonzero' (v : V) (
nz : v != 0) : finrank K V = 1 ↔ forall w : V, exists c : K, c • v = w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `WittVector.exists_frobenius_solution_fractionRing`：exists_frobenius_solu
tion_fractionRing {a : FractionRing (𝕎 k)} (ha : a != 0) : existsᵉ (b != 0) (m :
 Int), φ b * a = (p : FractionRing (𝕎 k…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 85 条，此处仅展示前 30 条）

--- 原说明 ---
A one-dimensional isocrystal over an algebraically closed field
admits an isomorphism to one of the standard (indexed by `m : ℤ`) one-dimensiona
l isocrystals.
-/
theorem isocrystal_classification (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] (V : Type*)
    [AddCommGroup V] [Isocrystal p k V] (h_dim : finrank K(p, k) V = 1) :
    ∃ m : ℤ, Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h_dim
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := exists_ne 0
  have : Φ(p, k) x ≠ 0 := by simpa only [map_zero] using Φ(p, k).injective.ne hx
  obtain ⟨a, ha, hax⟩ : ∃ a : K(p, k), a ≠ 0 ∧ Φ(p, k) x = a • x := by
    rw [finrank_eq_one_iff_of_nonzero' x hx] at h_dim
    obtain ⟨a, ha⟩ := h_dim (Φ(p, k) x)
    refine ⟨a, ?_, ha.symm⟩
    intro ha'
    apply this
    simp only [← ha, ha', zero_smul]
  obtain ⟨b, hb, m, hmb⟩ := WittVector.exists_frobenius_solution_fractionRing p ha
  replace hmb : φ(p, k) b * a = (p : K(p, k)) ^ m * b := by convert! hmb
  use m
  let F₀ : StandardOneDimIsocrystal p k m →ₗ[K(p, k)] V := LinearMap.toSpanSingleton K(p, k) V x
  let F : StandardOneDimIsocrystal p k m ≃ₗ[K(p, k)] V := by
    refine LinearEquiv.ofBijective F₀ ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot]
      exact LinearMap.ker_toSpanSingleton K(p, k) hx
    · rw [← LinearMap.range_eq_top]
      rw [← (finrank_eq_one_iff_of_nonzero x hx).mp h_dim]
      rw [LinearMap.span_singleton_eq_range]
  refine ⟨⟨(LinearEquiv.smulOfNeZero K(p, k) _ _ hb).trans F, fun c ↦ ?_⟩⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply,
    LinearEquiv.smulOfNeZero_apply, LinearEquiv.map_smul, LinearEquiv.map_smul,
    LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply,
    StandardOneDimIsocrystal.frobenius_apply]
  unfold StandardOneDimIsocrystal
  rw [LinearMap.toSpanSingleton_apply K(p, k) V x c, LinearMap.toSpanSingleton_apply K(p, k) V x]
  simp only [hax, map_smulₛₗ, smul_eq_mul]
  simp only [← mul_smul]
  congr 1
  linear_combination φ(p, k) c * hmb

end WittVector

