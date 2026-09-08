/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Finite-dimensional vector spaces

Basic properties of finite-dimensional vector spaces, of their dimensions, and
of linear maps on such spaces.

## Main definitions

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules (`FiniteDimensional.finiteDimensional_submodule`)
- quotients (for the dimension of a quotient, see `Submodule.finrank_quotient_add_finrank` in
  `Mathlib/LinearAlgebra/Dimension/RankNullity.lean`)
- linear equivs, in `LinearEquiv.finiteDimensional`

Basic properties of linear maps of a finite-dimensional vector space are given. Notably, the
equivalence of injectivity and surjectivity is proved in `LinearMap.injective_iff_surjective`,
and the equivalence between left-inverse and right-inverse in `LinearMap.mul_eq_one_comm`
and `LinearMap.comp_eq_id_comm`.

## Implementation notes

You should not assume that there has been any effort to state lemmas as generally as possible.

Plenty of the results hold for general finitely generated modules (see
`Mathlib/RingTheory/Finiteness/Basic.lean`) or Noetherian modules (see
`Mathlib/RingTheory/Noetherian/Basic.lean`).
-/

@[expose] public section

universe u v v' w

open Cardinal Function IsNoetherian Module Submodule

variable {K : Type u} {V : Type v}

namespace FiniteDimensional
section DivisionRing
variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-
**FiniteDimensional.finrank_le_iff_rank_le** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDime
nsional`。
形式化陈述：finrank_le_iff_rank_le [FiniteDimensional K V] {n : Nat} : finrank K V <= 
n ↔ Module.rank K V <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_le_iff_le_of_lt_aleph0`：toNat_le_iff_le_of_lt_aleph0 (hc 
: c < ℵ₀) (hd : d < ℵ₀) : toNat c <= toNat d ↔ c <= d
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finrank_le_iff_rank_le [FiniteDimensional K V] {n : ℕ} :
    finrank K V ≤ n ↔ Module.rank K V ≤ n := by
  simp [← Cardinal.toNat_le_iff_le_of_lt_aleph0 (rank_lt_aleph0 K V), finrank]
/-
**FiniteDimensional.finrank_lt_iff_rank_lt** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDime
nsional`。
形式化陈述：finrank_lt_iff_rank_lt [FiniteDimensional K V] {n : Nat} : finrank K V < n
 ↔ Module.rank K V < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_lt_iff_lt_of_lt_aleph0`：toNat_lt_iff_lt_of_lt_aleph0 (hc 
: c < ℵ₀) (hd : d < ℵ₀) : toNat c < toNat d ↔ c < d
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finrank_lt_iff_rank_lt [FiniteDimensional K V] {n : ℕ} :
    finrank K V < n ↔ Module.rank K V < n := by
  simp [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0 (rank_lt_aleph0 K V), finrank]
/-
**FiniteDimensional._root_.LinearIndependent.lt_aleph0_of_finiteDimensional** 是 
Mathlib 中的一个定理，位于命名空间 `FiniteDimensional`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIndependent.lt_aleph0_of_finiteDimensional {ι : Type w} [FiniteDimensional K V]
    {v : ι → V} (h : LinearIndependent K v) : #ι < ℵ₀ :=
  h.lt_aleph0_of_finite

/-- If a submodule has maximal dimension in a finite-dimensional space, then it is equal to the
whole space. -/
/-
**FiniteDimensional._root_.Submodule.eq_top_of_finrank_eq** 是 Mathlib 中的一个定理，位于命
名空间 `FiniteDimensional`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a submodule has maximal dimension in a finite-dimensional space, then it is e
qual to the
whole space.
-/
theorem _root_.Submodule.eq_top_of_finrank_eq [FiniteDimensional K V] {S : Submodule K V}
    (h : finrank K S = finrank K V) : S = ⊤ := by
  set bS := Basis.ofVectorSpace K S with bS_eq
  have : LinearIndepOn K id (Subtype.val '' Basis.ofVectorSpaceIndex K S) := by
    simpa [bS] using bS.linearIndependent.linearIndepOn_id.image
      (f := Submodule.subtype S) (by simp)
  set b := Basis.extend this with b_eq
  let i2 : Fintype (((↑) : S → V) '' Basis.ofVectorSpaceIndex K S) :=
    (LinearIndependent.set_finite_of_isNoetherian this).fintype
  have : (↑) '' Basis.ofVectorSpaceIndex K S = this.extend (Set.subset_univ _) :=
    Set.eq_of_subset_of_card_le (this.subset_extend _)
      (by
        rw [Set.card_image_of_injective _ Subtype.coe_injective, ← finrank_eq_card_basis bS, ←
            finrank_eq_card_basis b, h])
  rw [← b.span_eq, b_eq, Basis.coe_extend, Subtype.range_coe, ← this, ← Submodule.coe_subtype,
    span_image]
  have := bS.span_eq
  rw [bS_eq, Basis.coe_ofVectorSpace, Subtype.range_coe] at this
  rw [this, Submodule.map_top (Submodule.subtype S), range_subtype]
/-
**FiniteDimensional._root_.Submodule.exists_linearEquiv_restrict_eq** 是 Mathlib 
中的一个定理，位于命名空间 `FiniteDimensional`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submodule.exists_linearEquiv_restrict_eq
    {W W' : Submodule K V} [FiniteDimensional K W] (f : W ≃ₗ[K] W') :
    ∃ g : V ≃ₗ[K] V, ∀ x : W, f x = g x := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  let eQ := W.prodEquivOfIsCompl Q hQ
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl W'
  let eQ' := W'.prodEquivOfIsCompl Q' hQ'
  suffices Nonempty (Q ≃ₗ[K] Q') from
    ⟨eQ.symm ≪≫ₗ (LinearEquiv.prodCongr f this.some) ≪≫ₗ eQ', by aesop⟩
  refine Module.nonempty_linearEquiv_iff_rank_eq.mpr ?_
  rw [← Cardinal.add_right_inj_of_lt_aleph0 (γ := Module.rank K W),
    add_comm, ← rank_prod', Module.nonempty_linearEquiv_iff_rank_eq.mp ⟨eQ⟩,
    add_comm, Module.nonempty_linearEquiv_iff_rank_eq.mp ⟨f⟩,
    ← rank_prod', Module.nonempty_linearEquiv_iff_rank_eq.mp ⟨eQ'⟩]
  exact Module.rank_lt_aleph0 K ↥W

section

open Finset

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
variable {W : Type v} [AddCommGroup W] [Module L W]

/-- A slight strengthening of `exists_nontrivial_relation_sum_zero_of_rank_succ_lt_card`
available when working over an ordered field:
we can ensure a positive coefficient, not just a nonzero coefficient.
-/
/-
**FiniteDimensional.exists_relation_sum_zero_pos_coefficient_of_finrank_succ_lt_
card** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDimensional`。
形式化陈述：exists_relation_sum_zero_pos_coefficient_of_finrank_succ_lt_card [FiniteDi
mensional L W] {t : Finset W} (h : finrank L W + 1 < t.card) : exists f : W -> L
, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ exists x in t, 0 < f x
参数：h : finrank L W + 1 < t.card。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card`：Modu
le.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card {t : Finset M} (h
 : finrank R M + 1 < t.card) : exists f : M -> R, ∑ e in…
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Finset.exists_pos_of_sum_zero_of_exists_nonzero`：∀ {ι : Type u_1} {M : T
ype u_4} [inst : AddCommMonoid M] [inst_1 : LinearOrder M] {s : Finset ι}   [IsO
rderedCancelAddMonoid M] (f : ι → M),…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R

--- 原说明 ---
A slight strengthening of `exists_nontrivial_relation_sum_zero_of_rank_succ_lt_c
ard`
available when working over an ordered field:
we can ensure a positive coefficient, not just a nonzero coefficient.
-/
theorem exists_relation_sum_zero_pos_coefficient_of_finrank_succ_lt_card [FiniteDimensional L W]
    {t : Finset W} (h : finrank L W + 1 < t.card) :
    ∃ f : W → L, ∑ e ∈ t, f e • e = 0 ∧ ∑ e ∈ t, f e = 0 ∧ ∃ x ∈ t, 0 < f x := by
  obtain ⟨f, sum, total, nonzero⟩ :=
    Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card h
  exact ⟨f, sum, total, exists_pos_of_sum_zero_of_exists_nonzero f total nonzero⟩


end

set_option backward.isDefEq.respectTransparency false in
/-- In a vector space with dimension 1, each set `{v}` is a basis for `v ≠ 0`. -/
@[simps repr_apply]
/-
**FiniteDimensional.basisSingleton** 是 Mathlib 中的一个定义，位于命名空间 `FiniteDimensional`
。
形式化陈述：basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : 
v != 0) : Basis ι K V
参数：ι : Type*；h : finrank K V = 1；v : V；hv : v != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
In a vector space with dimension 1, each set `{v}` is a basis for `v ≠ 0`.
-/
noncomputable def basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V)
    (hv : v ≠ 0) : Basis ι K V :=
  let b := Module.basisUnique ι h
  have h : b.repr v default ≠ 0 := mt Module.basisUnique_repr_eq_zero_iff.mp hv
  Basis.ofRepr
    { toFun := fun w => Finsupp.single default (b.repr w default / b.repr v default)
      invFun := fun f => f default • v
      map_add' := by simp [add_div]
      map_smul' := by simp [mul_div]
      left_inv := fun w => by
        apply_fun b.repr using b.repr.toEquiv.injective
        apply_fun Finsupp.uniqueEquiv default
        simp only [map_smulₛₗ, Finsupp.coe_smul, Finsupp.single_eq_same,
          smul_eq_mul, Pi.smul_apply, Finsupp.uniqueEquiv_apply]
        exact div_mul_cancel₀ _ h
      right_inv := fun f => by
        ext
        simp only [map_smulₛₗ, Finsupp.coe_smul, Finsupp.single_eq_same,
          RingHom.id_apply, smul_eq_mul, Pi.smul_apply]
        exact mul_div_cancel_right₀ _ h }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**FiniteDimensional.basisSingleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDimens
ional`。
形式化陈述：basisSingleton_apply (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) 
(hv : v != 0) (i : ι) : basisSingleton ι h v hv i = v
参数：ι : Type*；h : finrank K V = 1；v : V；hv : v != 0；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.uniq`：∀ {α : Sort u} (self : Unique α) (a : α), a = default
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basisSingleton_apply (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0)
    (i : ι) : basisSingleton ι h v hv i = v := by
  cases Unique.uniq ‹Unique ι› i
  simp [basisSingleton]

@[simp]
/-
**FiniteDimensional.range_basisSingleton** 是 Mathlib 中的一个定理，位于命名空间 `FiniteDimens
ional`。
形式化陈述：range_basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) 
(hv : v != 0) : Set.range (basisSingleton ι h v hv) = {v}
参数：ι : Type*；h : finrank K V = 1；v : V；hv : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_unique`：range_unique [Unique ι] : range f = {f default}
· 使用定理 `FiniteDimensional.basisSingleton_apply`：basisSingleton_apply (ι : Type*)
 [Unique ι] (h : finrank K V = 1) (v : V) (hv : v != 0) (i : ι) : basisSingleton
 ι h v hv i = v
-/
theorem range_basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) :
    Set.range (basisSingleton ι h v hv) = {v} := by rw [Set.range_unique, basisSingleton_apply]

end DivisionRing

end FiniteDimensional

section ZeroRank

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-
**FiniteDimensional.of_rank_eq_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.of_rank_eq_nat {n : Nat} (h : Module.rank K V = n) : Fin
iteDimensional K V
参数：h : Module.rank K V = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_rank_eq_nat`：Module.finite_of_rank_eq_nat [Module.Free 
R M] {n : Nat} (h : Module.rank R M = n) : Module.Finite R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
theorem FiniteDimensional.of_rank_eq_nat {n : ℕ} (h : Module.rank K V = n) :
    FiniteDimensional K V :=
  Module.finite_of_rank_eq_nat h
/-
**FiniteDimensional.of_rank_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.of_rank_eq_zero (h : Module.rank K V = 0) : FiniteDimens
ional K V
参数：h : Module.rank K V = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_rank_eq_zero`：Module.finite_of_rank_eq_zero (h : Module
.rank R M = 0) : Module.Finite R M
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
theorem FiniteDimensional.of_rank_eq_zero (h : Module.rank K V = 0) : FiniteDimensional K V :=
  Module.finite_of_rank_eq_zero h
/-
**FiniteDimensional.of_rank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.of_rank_eq_one (h : Module.rank K V = 1) : FiniteDimensi
onal K V
参数：h : Module.rank K V = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_rank_eq_one`：Module.finite_of_rank_eq_one [Module.Free 
R M] (h : Module.rank R M = 1) : Module.Finite R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
theorem FiniteDimensional.of_rank_eq_one (h : Module.rank K V = 1) : FiniteDimensional K V :=
  Module.finite_of_rank_eq_one h

variable (K V)
/-
**finiteDimensional_bot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：finiteDimensional_bot : FiniteDimensional K (⊥ : Submodule K V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_rank_eq_zero`：FiniteDimensional.of_rank_eq_zero (h 
: Module.rank K V = 0) : FiniteDimensional K V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance finiteDimensional_bot : FiniteDimensional K (⊥ : Submodule K V) :=
  .of_rank_eq_zero <| by simp

end ZeroRank

namespace Submodule

open IsNoetherian Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A submodule contained in a finite-dimensional submodule is
finite-dimensional. -/
/-
**Submodule.finiteDimensional_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：finiteDimensional_of_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (
h : S₁ <= S₂) : FiniteDimensional K S₁
参数：h : S₁ <= S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_le`：isNoetherian_of_le {s t : Submodule R M} [ht : IsNoe
therian R t] (h : s <= t) : IsNoetherian R s
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
A submodule contained in a finite-dimensional submodule is
finite-dimensional.
-/
theorem finiteDimensional_of_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (h : S₁ ≤ S₂) :
    FiniteDimensional K S₁ :=
  (isNoetherian_of_le h).finite

/-- The inf of two submodules, the first finite-dimensional, is
finite-dimensional. -/
/-
**Submodule.finiteDimensional_inf_left** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：finiteDimensional_inf_left (S₁ S₂ : Submodule K V) [FiniteDimensional K S₁
] : FiniteDimensional K (S₁ ⊓ S₂ : Submodule K V)
参数：S₁ S₂ : Submodule K V。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.finiteDimensional_of_le`：finiteDimensional_of_le {S₁ S₂ : Subm
odule K V} [FiniteDimensional K S₂] (h : S₁ <= S₂) : FiniteDimensional K S₁
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
The inf of two submodules, the first finite-dimensional, is
finite-dimensional.
-/
instance finiteDimensional_inf_left (S₁ S₂ : Submodule K V) [FiniteDimensional K S₁] :
    FiniteDimensional K (S₁ ⊓ S₂ : Submodule K V) :=
  finiteDimensional_of_le inf_le_left

/-- The inf of two submodules, the second finite-dimensional, is
finite-dimensional. -/
/-
**Submodule.finiteDimensional_inf_right** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：finiteDimensional_inf_right (S₁ S₂ : Submodule K V) [FiniteDimensional K S
₂] : FiniteDimensional K (S₁ ⊓ S₂ : Submodule K V)
参数：S₁ S₂ : Submodule K V。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.finiteDimensional_of_le`：finiteDimensional_of_le {S₁ S₂ : Subm
odule K V} [FiniteDimensional K S₂] (h : S₁ <= S₂) : FiniteDimensional K S₁
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b

--- 原说明 ---
The inf of two submodules, the second finite-dimensional, is
finite-dimensional.
-/
instance finiteDimensional_inf_right (S₁ S₂ : Submodule K V) [FiniteDimensional K S₂] :
    FiniteDimensional K (S₁ ⊓ S₂ : Submodule K V) :=
  finiteDimensional_of_le inf_le_right

/-- The sup of two finite-dimensional submodules is
finite-dimensional. -/
/-
**Submodule.finiteDimensional_sup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：finiteDimensional_sup (S₁ S₂ : Submodule K V) [h₁ : FiniteDimensional K S₁
] [h₂ : FiniteDimensional K S₂] : FiniteDimensional K (S₁ ⊔ S₂ : Submodule K V)
参数：S₁ S₂ : Submodule K V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sup of two finite-dimensional submodules is
finite-dimensional.
-/
instance finiteDimensional_sup (S₁ S₂ : Submodule K V) [h₁ : FiniteDimensional K S₁]
    [h₂ : FiniteDimensional K S₂] : FiniteDimensional K (S₁ ⊔ S₂ : Submodule K V) :=
  finite_sup _ _

/-- The submodule generated by a finite supremum of finite-dimensional submodules is
finite-dimensional.

Note that strictly this only needs `∀ i ∈ s, FiniteDimensional K (S i)`, but that doesn't
work well with typeclass search. -/
/-
**Submodule.finiteDimensional_finset_sup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：finiteDimensional_finset_sup {ι : Type*} (s : Finset ι) (S : ι -> Submodul
e K V) [forall i, FiniteDimensional K (S i)] : FiniteDimensional K (s.sup S : Su
bmodule K V)
参数：s : Finset ι；S : ι -> Submodule K V；S i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule generated by a finite supremum of finite-dimensional submodules is
finite-dimensional.

Note that strictly this only needs `∀ i ∈ s, FiniteDimensional K (S i)`, but tha
t doesn't
work well with typeclass search.
-/
instance finiteDimensional_finset_sup {ι : Type*} (s : Finset ι) (S : ι → Submodule K V)
    [∀ i, FiniteDimensional K (S i)] : FiniteDimensional K (s.sup S : Submodule K V) :=
  Submodule.finite_finset_sup _ _

/-- The submodule generated by a supremum of finite-dimensional submodules, indexed by a finite
sort is finite-dimensional. -/
/-
**Submodule.finiteDimensional_iSup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：finiteDimensional_iSup {ι : Sort*} [Finite ι] (S : ι -> Submodule K V) [fo
rall i, FiniteDimensional K (S i)] : FiniteDimensional K ↑(⨆ i, S i)
参数：S : ι -> Submodule K V；S i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule generated by a supremum of finite-dimensional submodules, indexed 
by a finite
sort is finite-dimensional.
-/
instance finiteDimensional_iSup {ι : Sort*} [Finite ι] (S : ι → Submodule K V)
    [∀ i, FiniteDimensional K (S i)] : FiniteDimensional K ↑(⨆ i, S i) :=
  Submodule.finite_iSup _

end DivisionRing

end Submodule

section

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-
**finiteDimensional_finsupp** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：finiteDimensional_finsupp {ι : Type*} [Finite ι] [FiniteDimensional K V] :
 FiniteDimensional K (ι ->₀ V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finiteDimensional_finsupp {ι : Type*} [Finite ι] [FiniteDimensional K V] :
    FiniteDimensional K (ι →₀ V) :=
  Module.Finite.finsupp

end

namespace Submodule
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- If a submodule is contained in a finite-dimensional
submodule with the same or smaller dimension, they are equal. -/
/-
**Submodule.eq_of_le_of_finrank_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：eq_of_le_of_finrank_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (h
le : S₁ <= S₂) (hd : finrank K S₂ <= finrank K S₁) : S₁ = S₂
参数：hle : S₁ <= S₂；hd : finrank K S₂ <= finrank K S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.comap_subtype_eq_top`：comap_subtype_eq_top {p p' : Submodule R
 M} : comap p.subtype p' = ⊤ ↔ p <= p'
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N

--- 原说明 ---
If a submodule is contained in a finite-dimensional
submodule with the same or smaller dimension, they are equal.
-/
theorem eq_of_le_of_finrank_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ ≤ S₂)
    (hd : finrank K S₂ ≤ finrank K S₁) : S₁ = S₂ := by
  rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)] at hd
  exact le_antisymm hle (Submodule.comap_subtype_eq_top.1
    (eq_top_of_finrank_eq (le_antisymm (comap (Submodule.subtype S₂) S₁).finrank_le hd)))

/-- If a submodule is contained in a finite-dimensional
submodule with the same dimension, they are equal. -/
/-
**Submodule.eq_of_le_of_finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：eq_of_le_of_finrank_eq {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (h
le : S₁ <= S₂) (hd : finrank K S₁ = finrank K S₂) : S₁ = S₂
参数：hle : S₁ <= S₂；hd : finrank K S₁ = finrank K S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.eq_of_le_of_finrank_le`：eq_of_le_of_finrank_le {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₂ <= finrank
 K S₁) : S₁ = S₂
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
If a submodule is contained in a finite-dimensional
submodule with the same dimension, they are equal.
-/
theorem eq_of_le_of_finrank_eq {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ ≤ S₂)
    (hd : finrank K S₁ = finrank K S₂) : S₁ = S₂ :=
  eq_of_le_of_finrank_le hle hd.ge

end Submodule

namespace Subalgebra

variable {K L : Type*} [Field K] [Ring L] [Algebra K L] {F E : Subalgebra K L}
  [hfin : FiniteDimensional K E]

/-- If a subalgebra is contained in a finite-dimensional
subalgebra with the same or smaller dimension, they are equal. -/
/-
**Subalgebra.eq_of_le_of_finrank_le** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：eq_of_le_of_finrank_le (h_le : F <= E) (h_finrank : finrank K E <= finrank
 K F) : F = E
参数：h_le : F <= E；h_finrank : finrank K E <= finrank K F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.toSubmodule_injective`：toSubmodule_injective : Function.Injec
tive (toSubmodule : Subalgebra R A -> Submodule R A)
· 使用定理 `Submodule.eq_of_le_of_finrank_le`：eq_of_le_of_finrank_le {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₂ <= finrank
 K S₁) : S₁ = S₂

--- 原说明 ---
If a subalgebra is contained in a finite-dimensional
subalgebra with the same or smaller dimension, they are equal.
-/
theorem eq_of_le_of_finrank_le (h_le : F ≤ E) (h_finrank : finrank K E ≤ finrank K F) : F = E :=
  haveI : Module.Finite K (Subalgebra.toSubmodule E) := hfin
  toSubmodule_injective <| Submodule.eq_of_le_of_finrank_le h_le h_finrank

/-- If a subalgebra is contained in a finite-dimensional
subalgebra with the same dimension, they are equal. -/
/-
**Subalgebra.eq_of_le_of_finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：eq_of_le_of_finrank_eq (h_le : F <= E) (h_finrank : finrank K F = finrank 
K E) : F = E
参数：h_le : F <= E；h_finrank : finrank K F = finrank K E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.eq_of_le_of_finrank_le`：eq_of_le_of_finrank_le (h_le : F <= E
) (h_finrank : finrank K E <= finrank K F) : F = E
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
If a subalgebra is contained in a finite-dimensional
subalgebra with the same dimension, they are equal.
-/
theorem eq_of_le_of_finrank_eq (h_le : F ≤ E) (h_finrank : finrank K F = finrank K E) : F = E :=
  eq_of_le_of_finrank_le h_le h_finrank.ge

end Subalgebra

namespace LinearMap

open Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-- On a finite-dimensional space, an injective linear map is surjective. -/
/-
**LinearMap.surjective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：surjective_of_injective [FiniteDimensional K V] {f : V ->ₗ[K] V} (hinj : I
njective f) : Surjective f
参数：hinj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rank_range_of_injective`：rank_range_of_injective (f : M ->ₗ[R] M₁) (h : 
Injective f) : Module.rank R (LinearMap.range f) = Module.rank R M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
On a finite-dimensional space, an injective linear map is surjective.
-/
theorem surjective_of_injective [FiniteDimensional K V] {f : V →ₗ[K] V} (hinj : Injective f) :
    Surjective f := by
  have h := rank_range_of_injective _ hinj
  rw [← finrank_eq_rank, ← finrank_eq_rank, Nat.cast_inj] at h
  exact range_eq_top.1 (eq_top_of_finrank_eq h)

/-- The image under an onto linear map of a finite-dimensional space is also finite-dimensional. -/
/-
**LinearMap.finiteDimensional_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
`。
形式化陈述：finiteDimensional_of_surjective [FiniteDimensional K V] (f : V ->ₗ[K] V₂) 
(hf : LinearMap.range f = ⊤) : FiniteDimensional K V₂
参数：f : V ->ₗ[K] V₂；hf : LinearMap.range f = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f

--- 原说明 ---
The image under an onto linear map of a finite-dimensional space is also finite-
dimensional.
-/
theorem finiteDimensional_of_surjective [FiniteDimensional K V] (f : V →ₗ[K] V₂)
    (hf : LinearMap.range f = ⊤) : FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f <| range_eq_top.1 hf

/-- The range of a linear map defined on a finite-dimensional space is also finite-dimensional. -/
/-
**LinearMap.finiteDimensional_range** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：finiteDimensional_range [FiniteDimensional K V] (f : V ->ₗ[K] V₂) : Finite
Dimensional K (LinearMap.range f)
参数：f : V ->ₗ[K] V₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a linear map defined on a finite-dimensional space is also finite-d
imensional.
-/
instance finiteDimensional_range [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    FiniteDimensional K (LinearMap.range f) :=
  Module.Finite.range f

/-- On a finite-dimensional space, a linear map is injective if and only if it is surjective. -/
/-
**LinearMap.injective_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：injective_iff_surjective [FiniteDimensional K V] {f : V ->ₗ[K] V} : Inject
ive f ↔ Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.surjective_of_injective`：surjective_of_injective [FiniteDimens
ional K V] {f : V ->ₗ[K] V} (hinj : Injective f) : Surjective f
· 使用定理 `LinearMap.exists_rightInverse_of_surjective`：∀ {R : Type u_1} [inst : Se
miring R] {P : Type u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]
   {M : Type u_3} [inst_3 : AddCo…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Function.leftInverse_of_surjective_of_rightInverse`：∀ {α : Sort u_1} {β 
: Sort u_2} {f : α → β} {g : β → α},   Function.Surjective f → Function.RightInv
erse f g → Function.LeftInverse f g
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f

--- 原说明 ---
On a finite-dimensional space, a linear map is injective if and only if it is su
rjective.
-/
theorem injective_iff_surjective [FiniteDimensional K V] {f : V →ₗ[K] V} :
    Injective f ↔ Surjective f :=
  ⟨surjective_of_injective, fun hsurj =>
    let ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (range_eq_top.2 hsurj)
    have : Function.RightInverse g f := LinearMap.ext_iff.1 hg
    (leftInverse_of_surjective_of_rightInverse (surjective_of_injective this.injective)
        this).injective⟩
/-
**LinearMap.injOn_iff_surjOn** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：injOn_iff_surjOn {p : Submodule K V} [FiniteDimensional K p] {f : V ->ₗ[K]
 V} (h : forall x in p, f x in p) : Set.InjOn f p ↔ Set.SurjOn f p p
参数：h : forall x in p, f x in p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.MapsTo.restrict_surjective_iff`：∀ {α : Type u_1} {β : Type u_2} {s :
 Set α} {t : Set β} {f : α → β} (h : Set.MapsTo f s t),   Function.Surjective (S
et.MapsTo.restrict f s t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma injOn_iff_surjOn {p : Submodule K V} [FiniteDimensional K p]
    {f : V →ₗ[K] V} (h : ∀ x ∈ p, f x ∈ p) :
    Set.InjOn f p ↔ Set.SurjOn f p p := by
  rw [Set.injOn_iff_injective, ← Set.MapsTo.restrict_surjective_iff h]
  change Injective (f.domRestrict p) ↔ Surjective (f.restrict h)
  simp [disjoint_iff, ← injective_iff_surjective]
/-
**LinearMap.ker_eq_bot_iff_range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_eq_bot_iff_range_eq_top [FiniteDimensional K V] {f : V ->ₗ[K] V} : Lin
earMap.ker f = ⊥ ↔ LinearMap.range f = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearMap.injective_iff_surjective`：injective_iff_surjective [FiniteDime
nsional K V] {f : V ->ₗ[K] V} : Injective f ↔ Surjective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ker_eq_bot_iff_range_eq_top [FiniteDimensional K V] {f : V →ₗ[K] V} :
    LinearMap.ker f = ⊥ ↔ LinearMap.range f = ⊤ := by
  rw [range_eq_top, ker_eq_bot, injective_iff_surjective]

/-- Any division ring is stably finite. -/
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any division ring is stably finite.
-/
instance (priority := low) : IsStablyFiniteRing K := by
  refine isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd.mpr fun n ↦ ⟨fun {f g} hfg ↦ ?_⟩
  have ginj : Injective g :=
    HasLeftInverse.injective ⟨f, fun x => show (f * g) x = (1 : End K (Fin n → K)) x by rw [hfg]⟩
  let ⟨i, hi⟩ := g.exists_rightInverse_of_surjective
    (range_eq_top.2 (injective_iff_surjective.1 ginj))
  have : f * (g * i) = f * 1 := congr_arg _ hi
  rw [← mul_assoc, hfg, one_mul, mul_one] at this; rwa [← this]

/-- A domain finitely generated as a module over a field is a field. -/
/-
**LinearMap._root_.IsField.of_isDomain_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A domain finitely generated as a module over a field is a field.
-/
theorem _root_.IsField.of_isDomain_of_finite (K L : Type*) [Field K] [CommRing L] [IsDomain L]
    [Algebra K L] [Module.Finite K L] : IsField L where
  exists_pair_ne := Nontrivial.exists_pair_ne
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := (mulLeft K x).surjective_of_injective (mul_right_injective₀ hx) 1

section Semiring

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [Free R M] [Module.Finite R M]
variable [IsStablyFiniteRing R]

/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStablyFiniteRing (Module.End R M) := by
  let e := (Module.Free.chooseBasis R M).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite ..
  rw [RingEquiv.isStablyFiniteRing_iff e.conjRingEquiv]
  infer_instance

-- TODO: move the whole section to `Module.End` namespace.
/-
**LinearMap._root_.Module.End.injective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 
`LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.End.injective_of_surjective {f : Module.End R M} (hf : Surjective f) :
    Injective f :=
  have ⟨_, eq⟩ := projective_lifting_property _ .id hf
  injective_of_comp_eq_id _ _ (mul_eq_one_symm eq)

/-- In a finite-rank free module over a stably finite semiring, linear maps are inverse to
each other on one side if and only if they are inverse to each other on the other side. -/
/-
**LinearMap.comp_eq_id_comm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_eq_id_comm {f g : M ->ₗ[R] M} : f ∘ₗ g = id ↔ g ∘ₗ f = id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_eq_one_comm`：∀ {M : Type u_2} [inst : MulOne M] [IsDedekindFiniteMon
oid M] {a b : M}, a * b = 1 ↔ b * a = 1
· 使用定理 `instIsDedekindFiniteMonoidOfIsStablyFiniteRing`：∀ (R : Type u_10) [inst 
: NonAssocSemiring R] [IsStablyFiniteRing R], IsDedekindFiniteMonoid R
· 使用定理 `LinearMap.instIsStablyFiniteRingEnd`：∀ (R : Type u_1) (M : Type u_2) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Modu
le.Free R M] [Module.Fini…

--- 原说明 ---
In a finite-rank free module over a stably finite semiring, linear maps are inve
rse to
each other on one side if and only if they are inverse to each other on the othe
r side.
-/
theorem comp_eq_id_comm {f g : M →ₗ[R] M} : f ∘ₗ g = id ↔ g ∘ₗ f = id :=
  mul_eq_one_comm

end Semiring

/-
**LinearMap.comap_eq_sup_ker_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comap_eq_sup_ker_of_disjoint {p : Submodule K V} [FiniteDimensional K p] {
f : V ->ₗ[K] V} (h : forall x in p, f x in p) (h' : Disjoint p (ker f)) : p.coma
p f = p ⊔ ker f
参数：h : forall x in p, f x in p；h' : Disjoint p (ker f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LinearMap.surjective_of_injective`：surjective_of_injective [FiniteDimens
ional K V] {f : V ->ₗ[K] V} (hinj : Injective f) : Surjective f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.injective_restrict_iff`：injective_restrict_iff {p : Submodule 
R M} {q : Submodule R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂} (hf : forall x in p, f x in q) :
 Injective (f.restrict…
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `LinearMap.ker_le_comap`：ker_le_comap {p : Submodule R₂ M₂} (f : M ->ₛₗ[τ
₁₂] M₂) : ker f <= p.comap f
-/
theorem comap_eq_sup_ker_of_disjoint {p : Submodule K V} [FiniteDimensional K p] {f : V →ₗ[K] V}
    (h : ∀ x ∈ p, f x ∈ p) (h' : Disjoint p (ker f)) :
    p.comap f = p ⊔ ker f := by
  refine le_antisymm (fun x hx ↦ ?_) (sup_le_iff.mpr ⟨h, ker_le_comap _⟩)
  obtain ⟨⟨y, hy⟩, hxy⟩ :=
    surjective_of_injective ((injective_restrict_iff h).mpr h') ⟨f x, hx⟩
  replace hxy : f y = f x := by simpa [Subtype.ext_iff] using hxy
  exact Submodule.mem_sup.mpr ⟨y, hy, x - y, by simp [hxy], add_sub_cancel y x⟩
/-
**LinearMap.ker_comp_eq_of_commute_of_disjoint_ker** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap`。
形式化陈述：ker_comp_eq_of_commute_of_disjoint_ker [FiniteDimensional K V] {f g : V ->
ₗ[K] V} (h : Commute f g) (h' : Disjoint (ker f) (ker g)) : ker (f ∘ₗ g) = ker f
 ⊔ ker g
参数：h : Commute f g；h' : Disjoint (ker f) (ker g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
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
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `LinearMap.comap_eq_sup_ker_of_disjoint`：comap_eq_sup_ker_of_disjoint {p 
: Submodule K V} [FiniteDimensional K p] {f : V ->ₗ[K] V} (h : forall x in p, f 
x in p) (h' : Disjoint p (ke…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem ker_comp_eq_of_commute_of_disjoint_ker [FiniteDimensional K V] {f g : V →ₗ[K] V}
    (h : Commute f g) (h' : Disjoint (ker f) (ker g)) :
    ker (f ∘ₗ g) = ker f ⊔ ker g := by
  suffices ∀ x, f x = 0 → f (g x) = 0 by rw [ker_comp, comap_eq_sup_ker_of_disjoint _ h']; simpa
  intro x hx
  rw [← comp_apply, ← Module.End.mul_eq_comp, h.eq, Module.End.mul_apply, hx, map_zero]
/-
**LinearMap.ker_noncommProd_eq_of_supIndep_ker** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：ker_noncommProd_eq_of_supIndep_ker [FiniteDimensional K V] {ι : Type*} {f 
: ι -> V ->ₗ[K] V} (s : Finset ι) (comm) (h : s.SupIndep fun i => ker (f i)) : k
er (s.noncommProd f comm) = ⨆ i in s, ker (f i)
参数：s : Finset ι；comm；h : s.SupIndep fun i => ker (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Finset.SupIndep.subset`：∀ {α : Type u_1} {ι : Type u_3} [inst : Lattice 
α] [inst_1 : OrderBot α] {s t : Finset ι} {f : ι → α},   t.SupIndep f → s ⊆ t → 
s.SupIndep f
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.noncommProd_insert_of_notMem`：noncommProd_insert_of_notMem [Decid
ableEq α] (s : Finset α) (a : α) (f : α -> β) (comm) (ha : a ∉ s) : noncommProd 
(insert a s) f comm = f a…
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用定理 `LinearMap.ker_comp_eq_of_commute_of_disjoint_ker`：ker_comp_eq_of_commute
_of_disjoint_ker [FiniteDimensional K V] {f g : V ->ₗ[K] V} (h : Commute f g) (h
' : Disjoint (ker f) (ker g)) : ker (f…
· 使用定理 `Finset.noncommProd_commute`：noncommProd_commute (s : Finset α) (f : α ->
 β) (comm) (y : β) (h : forall x in s, Commute y (f x)) : Commute y (s.noncommPr
od f comm)
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.supIndep_iff_disjoint_erase`：supIndep_iff_disjoint_erase [Decidab
leEq ι] : s.SupIndep f ↔ forall i in s, Disjoint (f i) ((s.erase i).sup f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.erase_insert_eq_erase`：erase_insert_eq_erase (s : Finset α) (a : 
α) : (insert a s).erase a = s.erase a
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `iSup_insert`：iSup_insert {f : β -> α} {s : Set β} {b : β} : ⨆ x in inser
t b s, f x = f b ⊔ ⨆ x in s, f x
-/
theorem ker_noncommProd_eq_of_supIndep_ker [FiniteDimensional K V] {ι : Type*} {f : ι → V →ₗ[K] V}
    (s : Finset ι) (comm) (h : s.SupIndep fun i ↦ ker (f i)) :
    ker (s.noncommProd f comm) = ⨆ i ∈ s, ker (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | insert i s hi ih =>
    replace ih : ker (Finset.noncommProd s f <| Set.Pairwise.mono (s.subset_insert i) comm) =
        ⨆ x ∈ s, ker (f x) := ih _ (h.subset (s.subset_insert i))
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi, Module.End.mul_eq_comp,
      ker_comp_eq_of_commute_of_disjoint_ker]
    · simp_rw [Finset.mem_insert_coe, iSup_insert, Finset.mem_coe, ih]
    · exact s.noncommProd_commute _ _ _ fun j hj ↦
        comm (s.mem_insert_self i) (Finset.mem_insert_of_mem hj) (by lia)
    · replace h := Finset.supIndep_iff_disjoint_erase.mp h i (s.mem_insert_self i)
      simpa [ih, hi, Finset.sup_eq_iSup] using h

end DivisionRing

end LinearMap

namespace LinearEquiv

open Module

variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- The linear equivalence corresponding to an injective endomorphism. -/
/-
**LinearEquiv.ofInjectiveEndo** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofInjectiveEndo (f : V ->ₗ[K] V) (h_inj : Injective f) : V ≃ₗ[K] V
参数：f : V ->ₗ[K] V；h_inj : Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence corresponding to an injective endomorphism.
-/
noncomputable def ofInjectiveEndo (f : V →ₗ[K] V) (h_inj : Injective f) : V ≃ₗ[K] V :=
  LinearEquiv.ofBijective f ⟨h_inj, LinearMap.injective_iff_surjective.mp h_inj⟩

@[simp]
/-
**LinearEquiv.coe_ofInjectiveEndo** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_ofInjectiveEndo (f : V ->ₗ[K] V) (h_inj : Injective f) : ⇑(ofInjective
Endo f h_inj) = f
参数：f : V ->ₗ[K] V；h_inj : Injective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofInjectiveEndo (f : V →ₗ[K] V) (h_inj : Injective f) :
    ⇑(ofInjectiveEndo f h_inj) = f :=
  rfl

@[simp]
/-
**LinearEquiv.ofInjectiveEndo_right_inv** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofInjectiveEndo_right_inv (f : V ->ₗ[K] V) (h_inj : Injective f) : f * (of
InjectiveEndo f h_inj).symm = 1
参数：f : V ->ₗ[K] V；h_inj : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem ofInjectiveEndo_right_inv (f : V →ₗ[K] V) (h_inj : Injective f) :
    f * (ofInjectiveEndo f h_inj).symm = 1 :=
  LinearMap.ext <| (ofInjectiveEndo f h_inj).apply_symm_apply

@[simp]
/-
**LinearEquiv.ofInjectiveEndo_left_inv** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofInjectiveEndo_left_inv (f : V ->ₗ[K] V) (h_inj : Injective f) : ((ofInje
ctiveEndo f h_inj).symm : V ->ₗ[K] V) * f = 1
参数：f : V ->ₗ[K] V；h_inj : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem ofInjectiveEndo_left_inv (f : V →ₗ[K] V) (h_inj : Injective f) :
    ((ofInjectiveEndo f h_inj).symm : V →ₗ[K] V) * f = 1 :=
  LinearMap.ext <| (ofInjectiveEndo f h_inj).symm_apply_apply

variable {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
omit [FiniteDimensional K V]

/-- An injective linear map between finite-dimensional modules of equal rank
is a linear equivalence.

Unlike `LinearEquiv.ofFinrankEq` (which creates an *abstract* linear equivalence from `V` to `V'`),
this lemma improves a *given* injective linear map to a linear equivalence.
-/
/-
**LinearEquiv.ofInjectiveOfFinrankEq** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofInjectiveOfFinrankEq (f : V ->ₗ[K] V') (hinj : Function.Injective f) (hr
ank : Module.finrank K V = Module.finrank K V') : V ≃ₗ[K] V'
参数：f : V ->ₗ[K] V'；hinj : Function.Injective f；hrank : Module.finrank K V = Modu
le.finrank K V'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injective linear map between finite-dimensional modules of equal rank
is a linear equivalence.

Unlike `LinearEquiv.ofFinrankEq` (which creates an *abstract* linear equivalence
 from `V` to `V'`),
this lemma improves a *given* injective linear map to a linear equivalence.
-/
noncomputable def ofInjectiveOfFinrankEq (f : V →ₗ[K] V') (hinj : Function.Injective f)
    (hrank : Module.finrank K V = Module.finrank K V') : V ≃ₗ[K] V' :=
  haveI : LinearMap.range f = ⊤ :=
    Submodule.eq_top_of_finrank_eq ((LinearMap.finrank_range_of_inj hinj).trans hrank)
  (ofInjective f hinj).trans (ofTop (LinearMap.range f) this)

@[simp]
/-
**LinearEquiv.coe_ofInjectiveOfFinrankEq** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`
。
形式化陈述：coe_ofInjectiveOfFinrankEq (f : V ->ₗ[K] V') (hinj : Function.Injective f)
 (hrank : Module.finrank K V = Module.finrank K V') : (ofInjectiveOfFinrankEq f 
hinj hrank).toLinearMap = f
参数：f : V ->ₗ[K] V'；hinj : Function.Injective f；hrank : Module.finrank K V = Modu
le.finrank K V'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_ofInjectiveOfFinrankEq (f : V →ₗ[K] V') (hinj : Function.Injective f)
    (hrank : Module.finrank K V = Module.finrank K V') :
    (ofInjectiveOfFinrankEq f hinj hrank).toLinearMap = f :=
  rfl
end LinearEquiv

namespace LinearMap

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-
**LinearMap.isUnit_iff_ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isUnit_iff_ker_eq_bot [FiniteDimensional K V] (f : V ->ₗ[K] V) : IsUnit f 
↔ (LinearMap.ker f) = ⊥
参数：f : V ->ₗ[K] V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_eq_bot_of_inverse`：ker_eq_bot_of_inverse {τ₂₁ : R₂ ->+* R}
 [RingHomInvPair τ₁₂ τ₂₁] {f : M ->ₛₗ[τ₁₂] M₂} {g : M₂ ->ₛₗ[τ₂₁] M} (h : (g.comp
 f : M ->ₗ[R] M) = id…
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearEquiv.ofInjectiveEndo_right_inv`：ofInjectiveEndo_right_inv (f : V 
->ₗ[K] V) (h_inj : Injective f) : f * (ofInjectiveEndo f h_inj).symm = 1
· 使用定理 `LinearEquiv.ofInjectiveEndo_left_inv`：ofInjectiveEndo_left_inv (f : V ->
ₗ[K] V) (h_inj : Injective f) : ((ofInjectiveEndo f h_inj).symm : V ->ₗ[K] V) * 
f = 1
-/
theorem isUnit_iff_ker_eq_bot [FiniteDimensional K V] (f : V →ₗ[K] V) :
    IsUnit f ↔ (LinearMap.ker f) = ⊥ := by
  constructor
  · rintro ⟨u, rfl⟩
    exact LinearMap.ker_eq_bot_of_inverse u.inv_mul
  · intro h_inj
    rw [ker_eq_bot] at h_inj
    exact ⟨⟨f, (LinearEquiv.ofInjectiveEndo f h_inj).symm.toLinearMap,
      LinearEquiv.ofInjectiveEndo_right_inv f h_inj, LinearEquiv.ofInjectiveEndo_left_inv f h_inj⟩,
      rfl⟩
/-
**LinearMap.isUnit_iff_range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isUnit_iff_range_eq_top [FiniteDimensional K V] (f : V ->ₗ[K] V) : IsUnit 
f ↔ (LinearMap.range f) = ⊤
参数：f : V ->ₗ[K] V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.isUnit_iff_ker_eq_bot`：isUnit_iff_ker_eq_bot [FiniteDimensiona
l K V] (f : V ->ₗ[K] V) : IsUnit f ↔ (LinearMap.ker f) = ⊥
· 使用定理 `LinearMap.ker_eq_bot_iff_range_eq_top`：ker_eq_bot_iff_range_eq_top [Fini
teDimensional K V] {f : V ->ₗ[K] V} : LinearMap.ker f = ⊥ ↔ LinearMap.range f = 
⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_iff_range_eq_top [FiniteDimensional K V] (f : V →ₗ[K] V) :
    IsUnit f ↔ (LinearMap.range f) = ⊤ := by
  rw [isUnit_iff_ker_eq_bot, ker_eq_bot_iff_range_eq_top]

end LinearMap

open FiniteDimensional Module

section

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-
**finrank_zero_iff_forall_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_zero_iff_forall_zero [FiniteDimensional K V] : finrank K V = 0 ↔ f
orall x : V, x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Module.finrank_zero_iff`：Module.finrank_zero_iff [IsDomain R] [IsTorsion
Free R M] : finrank R M = 0 ↔ Subsingleton M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `subsingleton_iff_forall_eq`：∀ {α : Sort u_1} (x : α), Subsingleton α ↔ ∀
 (y : α), y = x
-/
theorem finrank_zero_iff_forall_zero [FiniteDimensional K V] : finrank K V = 0 ↔ ∀ x : V, x = 0 :=
  Module.finrank_zero_iff.trans (subsingleton_iff_forall_eq 0)

/-- If `ι` is an empty type and `V` is zero-dimensional, there is a unique `ι`-indexed basis. -/
/-
**basisOfFinrankZero** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：basisOfFinrankZero [FiniteDimensional K V] {ι : Type*} [IsEmpty ι] (hV : f
inrank K V = 0) : Basis ι K V
参数：hV : finrank K V = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ι` is an empty type and `V` is zero-dimensional, there is a unique `ι`-index
ed basis.
-/
noncomputable def basisOfFinrankZero [FiniteDimensional K V] {ι : Type*} [IsEmpty ι]
    (hV : finrank K V = 0) : Basis ι K V :=
  haveI : Subsingleton V := finrank_zero_iff.1 hV
  Basis.empty _

end

section

/-
**FiniteDimensional.exists_mul_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FiniteDimensional.exists_mul_eq_one (F : Type*) {K : Type*} [Field F] [Rin
g K] [IsDomain K] [Algebra F K] [FiniteDimensional F K] {x : K} (H : x != 0) : e
xists y, x * y = 1
参数：F : Type*；H : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.injective_iff_surjective`：injective_iff_surjective [FiniteDime
nsional K V] {f : V ->ₗ[K] V} : Injective f ↔ Surjective f
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
-/
lemma FiniteDimensional.exists_mul_eq_one (F : Type*) {K : Type*} [Field F] [Ring K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] {x : K} (H : x ≠ 0) : ∃ y, x * y = 1 := by
  have : Function.Surjective (LinearMap.mulLeft F x) :=
    LinearMap.injective_iff_surjective.1 fun y z => ((mul_right_inj' H).1 : x * y = x * z → y = z)
  exact this 1

/-- A domain that is module-finite as an algebra over a field is a division ring. -/
@[instance_reducible]
/-
**divisionRingOfFiniteDimensional** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：divisionRingOfFiniteDimensional (F K : Type*) [Field F] [Ring K] [IsDomain
 K] [Algebra F K] [FiniteDimensional F K] : DivisionRing K where __
参数：F K : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `FiniteDimensional.exists_mul_eq_one`：FiniteDimensional.exists_mul_eq_one
 (F : Type*) {K : Type*} [Field F] [Ring K] [IsDomain K] [Algebra F K] [FiniteDi
mensional F K] {x : K} (H…

--- 原说明 ---
A domain that is module-finite as an algebra over a field is a division ring.
-/
noncomputable def divisionRingOfFiniteDimensional (F K : Type*) [Field F] [Ring K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] : DivisionRing K where
  __ := ‹IsDomain K›
  inv x :=
    letI := Classical.decEq K
    if H : x = 0 then 0 else Classical.choose <| FiniteDimensional.exists_mul_eq_one F H
  mul_inv_cancel x hx := show x * dite _ (h := _) _ _ = _ by
    rw [dif_neg hx]
    exact (Classical.choose_spec (FiniteDimensional.exists_mul_eq_one F hx) :)
  inv_zero := dif_pos rfl
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
/-
**FiniteDimensional.isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FiniteDimensional.isUnit (F : Type*) {K : Type*} [Field F] [Ring K] [IsDom
ain K] [Algebra F K] [FiniteDimensional F K] {x : K} (H : x != 0) : IsUnit x
参数：F : Type*；H : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma FiniteDimensional.isUnit (F : Type*) {K : Type*} [Field F] [Ring K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] {x : K} (H : x ≠ 0) : IsUnit x :=
  let _ := divisionRingOfFiniteDimensional F K; H.isUnit

/-- An integral domain that is module-finite as an algebra over a field is a field. -/
@[instance_reducible]
/-
**fieldOfFiniteDimensional** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fieldOfFiniteDimensional (F K : Type*) [Field F] [h : CommRing K] [IsDomai
n K] [Algebra F K] [FiniteDimensional F K] : Field K
参数：F K : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DivisionRing.div_eq_mul_inv`：∀ {K : Type u_2} [self : DivisionRing K] (a
 b : K), a / b = a * b⁻¹
· 使用定理 `DivisionRing.zpow_zero'`：∀ {K : Type u_2} [self : DivisionRing K] (a : K
), a ^ 0 = 1
· 使用定理 `DivisionRing.zpow_succ'`：∀ {K : Type u_2} [self : DivisionRing K] (n : ℕ
) (a : K), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `DivisionRing.zpow_neg'`：∀ {K : Type u_2} [self : DivisionRing K] (n : ℕ)
 (a : K), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `DivisionRing.mul_inv_cancel`：∀ {K : Type u_2} [self : DivisionRing K] (a
 : K), a ≠ 0 → a * a⁻¹ = 1
· 使用定理 `DivisionRing.inv_zero`：∀ {K : Type u_2} [self : DivisionRing K], 0⁻¹ = 0
· 使用定理 `DivisionRing.nnratCast_def`：∀ {K : Type u_2} [self : DivisionRing K] (q 
: ℚ≥0), ↑q = ↑q.num / ↑q.den
· 使用定理 `DivisionRing.nnqsmul_def`：∀ {K : Type u_2} [self : DivisionRing K] (q : 
ℚ≥0) (a : K), DivisionRing.nnqsmul q a = ↑q * a
· 使用定理 `DivisionRing.ratCast_def`：∀ {K : Type u_2} [self : DivisionRing K] (q : 
ℚ), ↑q = ↑q.num / ↑q.den
· 使用定理 `DivisionRing.qsmul_def`：∀ {K : Type u_2} [self : DivisionRing K] (a : ℚ)
 (x : K), DivisionRing.qsmul a x = ↑a * x

--- 原说明 ---
An integral domain that is module-finite as an algebra over a field is a field.
-/
noncomputable def fieldOfFiniteDimensional (F K : Type*) [Field F] [h : CommRing K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] : Field K :=
  { divisionRingOfFiniteDimensional F K with
    toCommRing := h }

end
section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

section Span

open Submodule

/-
**finrank_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_span_singleton {v : V} (hv : v != 0) : finrank K (K ∙ v) = 1
参数：hv : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `finrank_span_le_card`：finrank_span_le_card (s : Set M) [Fintype s] : fin
rank R (span R s) <= s.toFinset.card
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Module.finrank_pos_iff`：Module.finrank_pos_iff [IsDomain R] [IsTorsionFr
ee R M] : 0 < finrank R M ↔ Nontrivial M
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem finrank_span_singleton {v : V} (hv : v ≠ 0) : finrank K (K ∙ v) = 1 := by
  apply le_antisymm
  · exact finrank_span_le_card ({v} : Set V)
  · rw [Nat.succ_le_iff, finrank_pos_iff]
    use ⟨v, mem_span_singleton_self v⟩, 0
    apply Subtype.coe_ne_coe.mp
    simp [hv]

/-- A submodule over a division ring is an atom of the submodule lattice iff it has `finrank` 1. -/
/-
**Submodule.isAtom_iff_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.isAtom_iff_finrank_eq_one {S : Submodule K V} : IsAtom S ↔ finra
nk K S = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用引理 `IsAtom.ne_bot`：IsAtom.ne_bot (ha : IsAtom a) : a != ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsAtom.le_iff_eq`：IsAtom.le_iff_eq (ha : IsAtom a) (hb : b != ⊥) : b <= 
a ↔ b = a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FiniteDimensional.of_finrank_eq_succ`：of_finrank_eq_succ {n : Nat} (hn :
 finrank K V = n.succ) : FiniteDimensional K V
· 使用定理 `FiniteDimensional.of_injective`：of_injective (f : V ->ₗ[K] V₂) (w : Func
tion.Injective f) [FiniteDimensional K V₂] : FiniteDimensional K V
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
· 使用定理 `Submodule.finrank_eq_zero`：Submodule.finrank_eq_zero [StrongRankConditio
n R] {S : Submodule R M} [Module.Finite R S] : finrank R S = 0 ↔ S = ⊥
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Submodule.eq_of_le_of_finrank_le`：eq_of_le_of_finrank_le {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₂ <= finrank
 K S₁) : S₁ = S₂

--- 原说明 ---
A submodule over a division ring is an atom of the submodule lattice iff it has 
`finrank` 1.
-/
theorem Submodule.isAtom_iff_finrank_eq_one {S : Submodule K V} :
    IsAtom S ↔ finrank K S = 1 := by
  refine ⟨fun hS ↦ ?_, fun hS ↦ ⟨by aesop, fun T hT ↦ ?_⟩⟩
  · obtain ⟨v : V, hv : v ∈ S, hv_ne : v ≠ 0⟩ := S.ne_bot_iff.mp hS.ne_bot
    suffices K ∙ v = S by rw [← this, finrank_span_singleton hv_ne]
    have : K ∙ v ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨v, mem_span_singleton_self v, hv_ne⟩
    rwa [← hS.le_iff_eq this, span_le, Set.singleton_subset_iff]
  · have : FiniteDimensional K S := .of_finrank_eq_succ hS
    have : FiniteDimensional K T := .of_injective (inclusion hT.le) (inclusion_injective hT.le)
    rw [← finrank_eq_zero (R := K)]
    by_contra h
    exact hT.ne <| eq_of_le_of_finrank_le hT.le <| by lia

/-- In a one-dimensional space, any vector is a multiple of any nonzero vector -/
/-
**exists_smul_eq_of_finrank_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_smul_eq_of_finrank_eq_one (h : finrank K V = 1) {x : V} (hx : x != 
0) (y : V) : exists (c : K), c • x = y
参数：h : finrank K V = 1；hx : x != 0；y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_finrank_eq_succ`：of_finrank_eq_succ {n : Nat} (hn :
 finrank K V = n.succ) : FiniteDimensional K V
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x

--- 原说明 ---
In a one-dimensional space, any vector is a multiple of any nonzero vector
-/
lemma exists_smul_eq_of_finrank_eq_one
    (h : finrank K V = 1) {x : V} (hx : x ≠ 0) (y : V) :
    ∃ (c : K), c • x = y := by
  have : Submodule.span K {x} = ⊤ := by
    have : FiniteDimensional K V := .of_finrank_eq_succ h
    apply eq_top_of_finrank_eq
    rw [h]
    exact finrank_span_singleton hx
  have : y ∈ Submodule.span K {x} := by rw [this]; exact mem_top
  exact mem_span_singleton.1 this

/-- A submodule of finrank 1 is spanned by any of its nonzero elements. -/
/-
**eq_span_singleton_of_mem_of_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_span_singleton_of_mem_of_finrank_eq_one {S : Submodule K V} {w : V} (hS
 : finrank K S = 1) (hw : w in S) (hw0 : w != 0) : S = K ∙ w
参数：hS : finrank K S = 1；hw : w in S；hw0 : w != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_finrank_pos`：finite_of_finrank_pos (h : 0 < finrank R M
) : Module.Finite R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.eq_of_le_of_finrank_le`：eq_of_le_of_finrank_le {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₂ <= finrank
 K S₁) : S₁ = S₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A submodule of finrank 1 is spanned by any of its nonzero elements.
-/
theorem eq_span_singleton_of_mem_of_finrank_eq_one {S : Submodule K V} {w : V}
    (hS : finrank K S = 1) (hw : w ∈ S) (hw0 : w ≠ 0) :
    S = K ∙ w := by
  have : FiniteDimensional K S := Module.finite_of_finrank_pos (by lia)
  exact Eq.symm <| eq_of_le_of_finrank_le (by simpa)
    (by rw [hS, finrank_span_singleton hw0])
/-
**Set.finrank_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.finrank_mono [FiniteDimensional K V] {s t : Set V} (h : s subseteq t) 
: s.finrank K <= t.finrank K
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.finrank_mono`：Submodule.finrank_mono {s t : Submodule R M} [Mo
dule.Finite R t] (hst : s <= t) : finrank R s <= finrank R t
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
-/
theorem Set.finrank_mono [FiniteDimensional K V] {s t : Set V} (h : s ⊆ t) :
    s.finrank K ≤ t.finrank K :=
  Submodule.finrank_mono (span_mono h)

end Span

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/


section finrank_eq_one

/-- A vector space with a nonzero vector `v` has dimension 1 iff `v` spans.
-/
/-
**finrank_eq_one_iff_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_eq_one_iff_of_nonzero (v : V) (nz : v != 0) : finrank K V = 1 ↔ sp
an K ({v} : Set V) = ⊤ where mp h
参数：v : V；nz : v != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteDimensional.range_basisSingleton`：range_basisSingleton (ι : Type*)
 [Unique ι] (h : finrank K V = 1) (v : V) (hv : v != 0) : Set.range (basisSingle
ton ι h v hv) = {v}
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用引理 `LinearIndependent.of_subsingleton`：LinearIndependent.of_subsingleton [Su
bsingleton ι] (i : ι) (hi : v i != 0) : LinearIndependent R v
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.range_cons`：range_cons (x : α) (u : Fin n -> α) : Set.range (vecC
ons x u) = {x} union Set.range u
· 使用定理 `Matrix.range_empty`：range_empty (u : Fin 0 -> α) : Set.range u = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a

--- 原说明 ---
A vector space with a nonzero vector `v` has dimension 1 iff `v` spans.
-/
theorem finrank_eq_one_iff_of_nonzero (v : V) (nz : v ≠ 0) :
    finrank K V = 1 ↔ span K ({v} : Set V) = ⊤ where
  mp h := by simpa using (basisSingleton Unit h v nz).span_eq
  mpr s := finrank_eq_card_basis <| .mk (.of_subsingleton (v := ![v]) 0 nz) <| by simp [← s]

/-- A module with a nonzero vector `v` has dimension 1 iff every vector is a multiple of `v`.
-/
/-
**finrank_eq_one_iff_of_nonzero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_eq_one_iff_of_nonzero' (v : V) (nz : v != 0) : finrank K V = 1 ↔ f
orall w : V, exists c : K, c • v = w
参数：v : V；nz : v != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finrank_eq_one_iff_of_nonzero`：finrank_eq_one_iff_of_nonzero (v : V) (nz
 : v != 0) : finrank K V = 1 ↔ span K ({v} : Set V) = ⊤ where mp h
· 使用定理 `Submodule.span_singleton_eq_top_iff`：span_singleton_eq_top_iff (x : M) :
 R ∙ x = ⊤ ↔ forall v, exists r : R, r • x = v

--- 原说明 ---
A module with a nonzero vector `v` has dimension 1 iff every vector is a multipl
e of `v`.
-/
theorem finrank_eq_one_iff_of_nonzero' (v : V) (nz : v ≠ 0) :
    finrank K V = 1 ↔ ∀ w : V, ∃ c : K, c • v = w := by
  rw [finrank_eq_one_iff_of_nonzero v nz]
  apply span_singleton_eq_top_iff

-- We use the `LinearMap.CompatibleSMul` typeclass here, to encompass two situations:
-- * `A = K`
-- * `[Field K] [Algebra K A] [IsScalarTower K A V] [IsScalarTower K A W]`
/-
**surjective_of_nonzero_of_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjective_of_nonzero_of_finrank_eq_one {W A : Type*} [Semiring A] [Module
 A V] [AddCommGroup W] [Module K W] [Module A W] [LinearMap.CompatibleSMul V W K
 A] (h : finrank K W = 1) {f : V ->ₗ[A] W} (w : f != 0) : Surjective f
参数：h : finrank K W = 1；w : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
· 使用定理 `finrank_eq_one_iff_of_nonzero'`：finrank_eq_one_iff_of_nonzero' (v : V) (
nz : v != 0) : finrank K V = 1 ↔ forall w : V, exists c : K, c • v = w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem surjective_of_nonzero_of_finrank_eq_one {W A : Type*} [Semiring A] [Module A V]
    [AddCommGroup W] [Module K W] [Module A W] [LinearMap.CompatibleSMul V W K A]
    (h : finrank K W = 1) {f : V →ₗ[A] W} (w : f ≠ 0) : Surjective f := by
  change Surjective (f.restrictScalars K)
  obtain ⟨v, n⟩ := DFunLike.ne_iff.mp w
  intro z
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (f v) n).mp h z
  exact ⟨c • v, by simp⟩

end finrank_eq_one

end DivisionRing

section SubalgebraRank

open Module

variable {F E : Type*} [Field F] [Ring E] [Algebra F E]

/-- A `Subalgebra` is `FiniteDimensional` iff it is `FiniteDimensional` as a submodule. -/
/-
**Subalgebra.finiteDimensional_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.finiteDimensional_toSubmodule {S : Subalgebra F E} : FiniteDime
nsional F (Subalgebra.toSubmodule S) ↔ FiniteDimensional F S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A `Subalgebra` is `FiniteDimensional` iff it is `FiniteDimensional` as a submodu
le.
-/
theorem Subalgebra.finiteDimensional_toSubmodule {S : Subalgebra F E} :
    FiniteDimensional F (Subalgebra.toSubmodule S) ↔ FiniteDimensional F S :=
  Iff.rfl

alias ⟨FiniteDimensional.of_subalgebra_toSubmodule, FiniteDimensional.subalgebra_toSubmodule⟩ :=
  Subalgebra.finiteDimensional_toSubmodule
/-
**FiniteDimensional.finiteDimensional_subalgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：FiniteDimensional.finiteDimensional_subalgebra [FiniteDimensional F E] (S 
: Subalgebra F E) : FiniteDimensional F S
参数：S : Subalgebra F E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_subalgebra_toSubmodule`：∀ {F : Type u_1} {E : Type 
u_2} [inst : Field F] [inst_1 : Ring E] [inst_2 : Algebra F E] {S : Subalgebra F
 E},   FiniteDimensional F ↥(Suba…
-/
instance FiniteDimensional.finiteDimensional_subalgebra [FiniteDimensional F E]
    (S : Subalgebra F E) : FiniteDimensional F S :=
  FiniteDimensional.of_subalgebra_toSubmodule inferInstance

end SubalgebraRank

namespace Module

namespace End

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-
**Module.End.ker_pow_constant** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：∀ {K : Type u} {V : Type v} [inst : DivisionRing K] [inst_1 : AddCommGroup
 V] [inst_2 : _root_.Module K V]   {f : Module.End K V} {k : ℕ},   LinearMap.ker
 (f ^ k) = LinearMap.ker (f ^ k.succ) → ∀ (m : ℕ), LinearMap.ker (f ^ k) = Linea
rMap.ker (f ^ (k + m))
参数：f ^ k；f ^ k.succ；m : ℕ；f ^ k；f ^ (k + m)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_pow_constant {f : End K V} {k : ℕ}
    (h : LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ)) :
    ∀ m, LinearMap.ker (f ^ k) = LinearMap.ker (f ^ (k + m))
  | 0 => by simp
  | m + 1 => by
    apply le_antisymm
    · rw [add_comm, pow_add]
      apply LinearMap.ker_le_ker_comp
    · rw [ker_pow_constant h m, add_comm m 1, ← add_assoc, pow_add, pow_add f k m,
        Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.ker_comp, LinearMap.ker_comp, h,
        Nat.add_one]

end End

end Module

/-
**AlgHom.bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.bijective {K S : Type*} [Field K] [Ring S] [IsSimpleRing S] [Algebr
a K S] [FiniteDimensional K S] (f : S ->ₐ[K] S) : Function.Bijective f
参数：f : S ->ₐ[K] S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `IsSimpleRing.instNontrivial`：∀ {R : Type u_1} [inst : NonUnitalNonAssocR
ing R] [IsSimpleRing R], Nontrivial R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.injective_iff_surjective`：injective_iff_surjective [FiniteDime
nsional K V] {f : V ->ₗ[K] V} : Injective f ↔ Surjective f
-/
theorem AlgHom.bijective {K S : Type*} [Field K] [Ring S] [IsSimpleRing S]
    [Algebra K S] [FiniteDimensional K S] (f : S →ₐ[K] S) : Function.Bijective f :=
  ⟨f.toRingHom.injective, f.toLinearMap.injective_iff_surjective.mp f.toRingHom.injective⟩
