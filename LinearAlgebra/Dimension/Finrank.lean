/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Anne Baanen
-/
module

public import Mathlib.SetTheory.Cardinal.ToNat
public import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Finite dimension of vector spaces

Definition of the rank of a module, or dimension of a vector space, as a natural number.

## Main definitions

Defined is `Module.finrank`, the dimension of a finite-dimensional space, returning a
`Nat`, as opposed to `Module.rank`, which returns a `Cardinal`. When the space has infinite
dimension, its `finrank` is by convention set to `0`.

The definition of `finrank` does not assume a `FiniteDimensional` instance, but lemmas might.
Import `LinearAlgebra.FiniteDimensional` to get access to these additional lemmas.

Formulas for the dimension are given for linear equivs, in `LinearEquiv.finrank_eq`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `Dimension.lean`. Not all results have been ported yet.

You should not assume that there has been any effort to state lemmas as generally as possible.
-/

@[expose] public section


universe u v w

open Cardinal Submodule Module Function

variable {R : Type u} {M : Type v} {N : Type w}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Module

section Semiring

/-- The rank of a module as a natural number.

For a finite-dimensional vector space `V` over a field `k`, `Module.finrank k V` is equal to
the dimension of `V` over `k`.

For a general module `M` over a ring `R`, `Module.finrank R M` is defined to be the supremum of the
cardinalities of the `R`-linearly independent subsets of `M`, if this supremum is finite. It is
defined by convention to be `0` if this supremum is infinite. See `Module.rank` for a
cardinal-valued version where infinite rank modules have rank an infinite cardinal.

Note that if `R` is not a field then there can exist modules `M` with `¬(Module.Finite R M)` but
`finrank R M ≠ 0`. For example `ℚ` has `finrank` equal to `1` over `ℤ`, because the nonempty
`ℤ`-linearly independent subsets of `ℚ` are precisely the nonzero singletons. -/
/-
**Module.finrank** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：finrank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : Nat
参数：R M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank of a module as a natural number.

For a finite-dimensional vector space `V` over a field `k`, `Module.finrank k V`
 is equal to
the dimension of `V` over `k`.

For a general module `M` over a ring `R`, `Module.finrank R M` is defined to be 
the supremum of the
cardinalities of the `R`-linearly independent subsets of `M`, if this supremum i
s finite. It is
defined by convention to be `0` if this supremum is infinite. See `Module.rank` 
for a
cardinal-valued version where infinite rank modules have rank an infinite cardin
al.

Note that if `R` is not a field then there can exist modules `M` with `¬(Module.
Finite R M)` but
`finrank R M ≠ 0`. For example `ℚ` has `finrank` equal to `1` over `ℤ`, because 
the nonempty
`ℤ`-linearly independent subsets of `ℚ` are precisely the nonzero singletons.
-/
noncomputable def finrank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : ℕ :=
  Cardinal.toNat (Module.rank R M)
/-
**Module.finrank_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst_1 : AddCommMonoid M]
 [inst_2 : _root_.Module R M]   [Subsingleton R], Module.finrank R M = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
@[simp] theorem finrank_subsingleton [Subsingleton R] : finrank R M = 1 := by
  rw [finrank, rank_subsingleton, map_one]
/-
**Module.finrank_eq_of_rank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_eq_of_rank_eq {n : Nat} (h : Module.rank R M = ↑n) : finrank R M =
 n
参数：h : Module.rank R M = ↑n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finrank_eq_of_rank_eq {n : ℕ} (h : Module.rank R M = ↑n) : finrank R M = n := by
  simp [finrank, h]
/-
**Module.rank_eq_one_iff_finrank_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rank_eq_one_iff_finrank_eq_one : Module.rank R M = 1 ↔ finrank R M = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Cardinal.toNat_eq_one`：toNat_eq_one : toNat c = 1 ↔ c = 1
-/
lemma rank_eq_one_iff_finrank_eq_one : Module.rank R M = 1 ↔ finrank R M = 1 :=
  Cardinal.toNat_eq_one.symm

/-- This is like `rank_eq_one_iff_finrank_eq_one` but works for `2`, `3`, `4`, ... -/
/-
**Module.rank_eq_ofNat_iff_finrank_eq_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rank_eq_ofNat_iff_finrank_eq_ofNat (n : Nat) [Nat.AtLeastTwo n] : Module.r
ank R M = OfNat.ofNat n ↔ finrank R M = OfNat.ofNat n
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Cardinal.toNat_eq_ofNat`：toNat_eq_ofNat {n : Nat} [Nat.AtLeastTwo n] : t
oNat c = OfNat.ofNat n ↔ c = OfNat.ofNat n

--- 原说明 ---
This is like `rank_eq_one_iff_finrank_eq_one` but works for `2`, `3`, `4`, ...
-/
lemma rank_eq_ofNat_iff_finrank_eq_ofNat (n : ℕ) [Nat.AtLeastTwo n] :
    Module.rank R M = OfNat.ofNat n ↔ finrank R M = OfNat.ofNat n :=
  Cardinal.toNat_eq_ofNat.symm
/-
**Module.finrank_le_of_rank_le** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_le_of_rank_le {n : Nat} (h : Module.rank R M <= ↑n) : finrank R M 
<= n
参数：h : Module.rank R M <= ↑n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_le_iff_le_of_lt_aleph0`：toNat_le_iff_le_of_lt_aleph0 (hc 
: c < ℵ₀) (hd : d < ℵ₀) : toNat c <= toNat d ↔ c <= d
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem finrank_le_of_rank_le {n : ℕ} (h : Module.rank R M ≤ ↑n) : finrank R M ≤ n := by
  rwa [← Cardinal.toNat_le_iff_le_of_lt_aleph0, toNat_natCast] at h
  · exact h.trans_lt natCast_lt_aleph0
  · exact natCast_lt_aleph0
/-
**Module.finrank_lt_of_rank_lt** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_lt_of_rank_lt {n : Nat} (h : Module.rank R M < ↑n) : finrank R M <
 n
参数：h : Module.rank R M < ↑n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_lt_iff_lt_of_lt_aleph0`：toNat_lt_iff_lt_of_lt_aleph0 (hc 
: c < ℵ₀) (hd : d < ℵ₀) : toNat c < toNat d ↔ c < d
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem finrank_lt_of_rank_lt {n : ℕ} (h : Module.rank R M < ↑n) : finrank R M < n := by
  rwa [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0, toNat_natCast] at h
  · exact h.trans natCast_lt_aleph0
  · exact natCast_lt_aleph0
/-
**Module.lt_rank_of_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：lt_rank_of_lt_finrank {n : Nat} (h : n < finrank R M) : ↑n < Module.rank R
 M
参数：h : n < finrank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_lt_iff_lt_of_lt_aleph0`：toNat_lt_iff_lt_of_lt_aleph0 (hc 
: c < ℵ₀) (hd : d < ℵ₀) : toNat c < toNat d ↔ c < d
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `Cardinal.toNat_apply_of_aleph0_le`：toNat_apply_of_aleph0_le {c : Cardina
l} (h : ℵ₀ <= c) : toNat c = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
-/
theorem lt_rank_of_lt_finrank {n : ℕ} (h : n < finrank R M) : ↑n < Module.rank R M := by
  rwa [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0, toNat_natCast]
  · exact natCast_lt_aleph0
  · contrapose! h
    rw [finrank, Cardinal.toNat_apply_of_aleph0_le h]
    exact n.zero_le
/-
**Module.one_lt_rank_of_one_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：one_lt_rank_of_one_lt_finrank (h : 1 < finrank R M) : 1 < Module.rank R M
参数：h : 1 < finrank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Module.lt_rank_of_lt_finrank`：lt_rank_of_lt_finrank {n : Nat} (h : n < f
inrank R M) : ↑n < Module.rank R M
-/
theorem one_lt_rank_of_one_lt_finrank (h : 1 < finrank R M) : 1 < Module.rank R M := by
  simpa using lt_rank_of_lt_finrank h
/-
**Module.finrank_le_finrank_of_rank_le_rank** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_le_finrank_of_rank_le_rank (h : lift.{w} (Module.rank R M) <= Card
inal.lift.{v} (Module.rank R N)) (h' : Module.rank R N < ℵ₀) : finrank R M <= fi
nrank R N
参数：h : lift.{w} (Module.rank R M) <= Cardinal.lift.{v} (Module.rank R N)；h' : Mo
dule.rank R N < ℵ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Cardinal.toNat_le_toNat`：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : t
oNat c <= toNat d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_lt_aleph0`：lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c 
< ℵ₀ ↔ c < ℵ₀
-/
theorem finrank_le_finrank_of_rank_le_rank
    (h : lift.{w} (Module.rank R M) ≤ Cardinal.lift.{v} (Module.rank R N))
    (h' : Module.rank R N < ℵ₀) : finrank R M ≤ finrank R N := by
  simpa only [toNat_lift] using! toNat_le_toNat h (lift_lt_aleph0.mpr h')

end Semiring

end Module

/-
**CommSemiring.finrank_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommSemiring.finrank_self (R) [CommSemiring R] : Module.finrank R R = 1
参数：R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用定理 `CommSemiring.rank_self`：CommSemiring.rank_self (R) [CommSemiring R] : Mo
dule.rank R R = 1
-/
theorem CommSemiring.finrank_self (R) [CommSemiring R] : Module.finrank R R = 1 :=
  finrank_eq_of_rank_eq (rank_self R)

open Module

namespace LinearEquiv

/-- The dimension of a finite-dimensional space is preserved under linear equivalence. -/
/-
**LinearEquiv.finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finrank R N
参数：f : M ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')

--- 原说明 ---
The dimension of a finite-dimensional space is preserved under linear equivalenc
e.
-/
theorem finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finrank R N := by
  unfold finrank
  rw [← Cardinal.toNat_lift, f.lift_rank_eq, Cardinal.toNat_lift]

/-- Pushforwards of finite-dimensional submodules along a `LinearEquiv` have the same finrank. -/
/-
**LinearEquiv.finrank_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：finrank_map_eq (f : M ≃ₗ[R] N) (p : Submodule R M) : finrank R (p.map (f :
 M ->ₗ[R] N)) = finrank R p
参数：f : M ≃ₗ[R] N；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N

--- 原说明 ---
Pushforwards of finite-dimensional submodules along a `LinearEquiv` have the sam
e finrank.
-/
theorem finrank_map_eq (f : M ≃ₗ[R] N) (p : Submodule R M) :
    finrank R (p.map (f : M →ₗ[R] N)) = finrank R p :=
  (f.submoduleMap p).finrank_eq.symm

end LinearEquiv

/-- The dimensions of the domain and range of an injective linear map are equal. -/
/-
**LinearMap.finrank_range_of_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.finrank_range_of_inj {f : M ->ₗ[R] N} (hf : Function.Injective f
) : finrank R (LinearMap.range f) = finrank R M
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N

--- 原说明 ---
The dimensions of the domain and range of an injective linear map are equal.
-/
theorem LinearMap.finrank_range_of_inj {f : M →ₗ[R] N} (hf : Function.Injective f) :
    finrank R (LinearMap.range f) = finrank R M := by rw [(LinearEquiv.ofInjective f hf).finrank_eq]

@[simp]
/-
**Submodule.finrank_map_subtype_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.finrank_map_subtype_eq (p : Submodule R M) (q : Submodule R p) :
 finrank R (q.map p.subtype) = finrank R q
参数：p : Submodule R M；q : Submodule R p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
-/
theorem Submodule.finrank_map_subtype_eq (p : Submodule R M) (q : Submodule R p) :
    finrank R (q.map p.subtype) = finrank R q :=
  (Submodule.equivSubtypeMap p q).symm.finrank_eq

variable (R M)

@[simp]
/-
**finrank_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_top`：rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finrank_top : finrank R (⊤ : Submodule R M) = finrank R M := by
  unfold finrank
  simp

namespace Algebra

/-- If `S₀ / R₀` and `S₁ / R₁` are algebras, `i : R₀ ≃+* R₁` and `j : S₀ ≃+* S₁` are
ring isomorphisms, such that `R₀ → R₁ → S₁` and `R₀ → S₀ → S₁` commute,
then the `finrank` of `S₀ / R₀` is equal to the finrank of `S₁ / R₁`. -/
/-
**Algebra.finrank_eq_of_equiv_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：finrank_eq_of_equiv_equiv {R₀ S₀ : Type*} [CommSemiring R₀] [Semiring S₀] 
[Algebra R₀ S₀] {R₁ S₁ : Type*} [CommSemiring R₁] [Semiring S₁] [Algebra R₁ S₁] 
(i : R₀ ≃+* R₁) (j : S₀ ≃+* S₁) (hc : (algebraMap R₁ S₁).comp i.toRingHom = j.to
RingHom.comp (algebraMap R₀ S₀)) : Module.finrank R₀ S₀ = Module.finrank R₁ S₁
参数：i : R₀ ≃+* R₁；j : S₀ ≃+* S₁；hc : (algebraMap R₁ S₁).comp i.toRingHom = j.toRi
ngHom.comp (algebraMap R₀ S₀)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Algebra.lift_rank_eq_of_equiv_equiv`：lift_rank_eq_of_equiv_equiv (i : R 
≃+* R') (j : S ≃+* S') (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.c
omp (algebraMap R S)) : l…

--- 原说明 ---
If `S₀ / R₀` and `S₁ / R₁` are algebras, `i : R₀ ≃+* R₁` and `j : S₀ ≃+* S₁` are
ring isomorphisms, such that `R₀ → R₁ → S₁` and `R₀ → S₀ → S₁` commute,
then the `finrank` of `S₀ / R₀` is equal to the finrank of `S₁ / R₁`.
-/
theorem finrank_eq_of_equiv_equiv {R₀ S₀ : Type*} [CommSemiring R₀] [Semiring S₀] [Algebra R₀ S₀]
    {R₁ S₁ : Type*} [CommSemiring R₁] [Semiring S₁] [Algebra R₁ S₁] (i : R₀ ≃+* R₁) (j : S₀ ≃+* S₁)
    (hc : (algebraMap R₁ S₁).comp i.toRingHom = j.toRingHom.comp (algebraMap R₀ S₀)) :
    Module.finrank R₀ S₀ = Module.finrank R₁ S₁ := by
  simpa using! (congr_arg Cardinal.toNat (lift_rank_eq_of_equiv_equiv i j hc))

end Algebra

