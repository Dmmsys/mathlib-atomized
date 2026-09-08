/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Artinian.Module

/-!
# Results on the eigenvalue 0

In this file we provide equivalent characterizations of properties related to the eigenvalue 0,
such as being nilpotent, having determinant equal to 0, having a non-trivial kernel, etc...

## Main results

* `LinearMap.charpoly_nilpotent_tfae`:
  equivalent characterizations of nilpotent endomorphisms
* `LinearMap.hasEigenvalue_zero_tfae`:
  equivalent characterizations of endomorphisms with eigenvalue 0
* `LinearMap.not_hasEigenvalue_zero_tfae`:
  endomorphisms without eigenvalue 0
* `LinearMap.finrank_maxGenEigenspace`:
  the dimension of the maximal generalized eigenspace of an endomorphism
  is the trailing degree of its characteristic polynomial

-/

public section

variable {R K M : Type*} [CommRing R] [IsDomain R] [Field K] [AddCommGroup M]
variable [Module R M] [Module.Finite R M] [Module.Free R M]
variable [Module K M] [Module.Finite K M]

open Module Module.Free Polynomial

/-
**IsNilpotent.charpoly_eq_X_pow_finrank** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNilpotent.charpoly_eq_X_pow_finrank {φ : Module.End R M} (h : IsNilpoten
t φ) : φ.charpoly = X ^ finrank R M
参数：h : IsNilpotent φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `IsNilpotent.eq_zero`：IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced
 R] (h : IsNilpotent x) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent`：isNilpotent_charpoly
_sub_pow_of_isNilpotent (hM : IsNilpotent M) : IsNilpotent (M.charpoly - X ^ (Fi
ntype.card n))
· 使用定理 `IsNilpotent.map`：IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {
r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpot
ent r…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
lemma IsNilpotent.charpoly_eq_X_pow_finrank {φ : Module.End R M} (h : IsNilpotent φ) :
    φ.charpoly = X ^ finrank R M := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [finrank_eq_card_chooseBasisIndex]
  apply Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent
  exact h.map (LinearMap.toMatrixAlgEquiv (chooseBasis R M))

namespace LinearMap

/-
**LinearMap.isNilpotent_iff_charpoly** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：isNilpotent_iff_charpoly (φ : End R M) : IsNilpotent φ ↔ charpoly φ = X ^ 
finrank R M
参数：φ : End R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsNilpotent.charpoly_eq_X_pow_finrank`：IsNilpotent.charpoly_eq_X_pow_fin
rank {φ : Module.End R M} (h : IsNilpotent φ) : φ.charpoly = X ^ finrank R M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_X_pow`：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n)
 = x ^ n
· 使用定理 `LinearMap.aeval_self_charpoly`：aeval_self_charpoly : aeval f f.charpoly 
= 0
-/
lemma isNilpotent_iff_charpoly (φ : End R M) :
    IsNilpotent φ ↔ charpoly φ = X ^ finrank R M :=
  ⟨IsNilpotent.charpoly_eq_X_pow_finrank,
    fun h ↦ ⟨finrank R M, by rw [← @aeval_X_pow R, ← h, aeval_self_charpoly φ]⟩⟩

open Module.Free in
/-
**LinearMap.charpoly_nilpotent_tfae** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：charpoly_nilpotent_tfae [IsNoetherian R M] (φ : Module.End R M) : List.TFA
E [ IsNilpotent φ, φ.charpoly = X ^ finrank R M, forall m : M, exists (n : Nat),
 (φ ^ n) m = 0, natTrailingDegree φ.charpoly = finrank R M ]
参数：φ : Module.End R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsNilpotent.charpoly_eq_X_pow_finrank`：IsNilpotent.charpoly_eq_X_pow_fin
rank {φ : Module.End R M} (h : IsNilpotent φ) : φ.charpoly = X ^ finrank R M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `LinearMap.aeval_self_charpoly`：aeval_self_charpoly : aeval f f.charpoly 
= 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `LinearMap.eventually_iSup_ker_pow_eq`：LinearMap.eventually_iSup_ker_pow_
eq (f : M ->ₗ[R] M) : forallᶠ n in atTop, ⨆ m, LinearMap.ker (f ^ m) = LinearMap
.ker (f ^ n)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
· 使用引理 `LinearMap.charpoly_natDegree`：charpoly_natDegree [StrongRankCondition R]
 : natDegree (charpoly f) = finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `Polynomial.Monic.eq_X_pow_iff_natTrailingDegree_eq_natDegree`：eq_X_pow_i
ff_natTrailingDegree_eq_natDegree (h₁ : p.Monic) : p = X ^ p.natDegree ↔ p.natTr
ailingDegree = p.natDegree
· 使用定理 `LinearMap.charpoly_monic`：charpoly_monic : f.charpoly.Monic
（共 33 条，此处仅展示前 30 条）
-/
lemma charpoly_nilpotent_tfae [IsNoetherian R M] (φ : Module.End R M) :
    List.TFAE [
      IsNilpotent φ,
      φ.charpoly = X ^ finrank R M,
      ∀ m : M, ∃ (n : ℕ), (φ ^ n) m = 0,
      natTrailingDegree φ.charpoly = finrank R M ] := by
  tfae_have 1 → 2 := IsNilpotent.charpoly_eq_X_pow_finrank
  tfae_have 2 → 3
  | h, m => by
    use finrank R M
    suffices φ ^ finrank R M = 0 by simp only [this, LinearMap.zero_apply]
    simpa only [h, map_pow, aeval_X] using φ.aeval_self_charpoly
  tfae_have 3 → 1
  | h => by
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp <| φ.eventually_iSup_ker_pow_eq
    use n
    ext x
    rw [zero_apply, ← mem_ker, ← hn n le_rfl]
    obtain ⟨k, hk⟩ := h x
    rw [← mem_ker] at hk
    exact Submodule.mem_iSup_of_mem _ hk
  tfae_have 2 ↔ 4 := by
    rw [← φ.charpoly_natDegree, φ.charpoly_monic.eq_X_pow_iff_natTrailingDegree_eq_natDegree]
  tfae_finish
/-
**LinearMap.charpoly_eq_X_pow_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：charpoly_eq_X_pow_iff [IsNoetherian R M] (φ : Module.End R M) : φ.charpoly
 = X ^ finrank R M ↔ forall m : M, exists (n : Nat), (φ ^ n) m = 0
参数：φ : Module.End R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `LinearMap.charpoly_nilpotent_tfae`：charpoly_nilpotent_tfae [IsNoetherian
 R M] (φ : Module.End R M) : List.TFAE [ IsNilpotent φ, φ.charpoly = X ^ finrank
 R M, forall m : M, exi…
-/
lemma charpoly_eq_X_pow_iff [IsNoetherian R M] (φ : Module.End R M) :
    φ.charpoly = X ^ finrank R M ↔ ∀ m : M, ∃ (n : ℕ), (φ ^ n) m = 0 :=
  (charpoly_nilpotent_tfae φ).out 1 2

open Module.Free in
/-
**LinearMap.hasEigenvalue_zero_tfae** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：hasEigenvalue_zero_tfae (φ : Module.End K M) : List.TFAE [ Module.End.HasE
igenvalue φ 0, IsRoot (minpoly K φ) 0, constantCoeff φ.charpoly = 0, LinearMap.d
et φ = 0, ⊥ < ker φ, exists (m : M), m != 0 ∧ φ m = 0 ]
参数：φ : Module.End K M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.hasEigenvalue_iff_isRoot`：hasEigenvalue_iff_isRoot : f.HasEig
envalue μ ↔ (minpoly R f).IsRoot μ
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LinearMap.minpoly_dvd_charpoly`：minpoly_dvd_charpoly {K : Type u} {M : T
ype v} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M] (f : M ->
ₗ[K] M) : minpoly K …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.constantCoeff_apply`：∀ {R : Type u} [inst : Semiring R] (p : 
Polynomial R), Polynomial.constantCoeff p = p.coeff 0
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Matrix.det_eq_sign_charpoly_coeff`：det_eq_sign_charpoly_coeff (M : Matri
x n n R) : M.det = (-1) ^ Fintype.card n * M.charpoly.coeff 0
· 使用定理 `LinearMap.charpoly.eq_1`：∀ {R : Type u} {M : Type v} [inst : CommRing R]
 [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_3 : Module.Free 
R M] [inst_4 …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LinearMap.bot_lt_ker_of_det_eq_zero`：bot_lt_ker_of_det_eq_zero [IsDomain
 R] [Free R M] {f : M ->ₗ[R] M} (hf : f.det = 0) : ⊥ < ker f
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Module.End.hasEigenvalue_of_hasEigenvector`：hasEigenvalue_of_hasEigenvec
tor {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x) : HasEigenvalue f μ
· 使用定理 `Module.End.eigenspace_zero`：eigenspace_zero (f : End R M) : f.eigenspace
 0 = LinearMap.ker f
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma hasEigenvalue_zero_tfae (φ : Module.End K M) :
    List.TFAE [
      Module.End.HasEigenvalue φ 0,
      IsRoot (minpoly K φ) 0,
      constantCoeff φ.charpoly = 0,
      LinearMap.det φ = 0,
      ⊥ < ker φ,
      ∃ (m : M), m ≠ 0 ∧ φ m = 0 ] := by
  tfae_have 1 ↔ 2 := Module.End.hasEigenvalue_iff_isRoot
  tfae_have 2 → 3 := by
    obtain ⟨F, hF⟩ := minpoly_dvd_charpoly φ
    simp only [IsRoot.def, constantCoeff_apply, coeff_zero_eq_eval_zero, hF, eval_mul]
    intro h; rw [h, zero_mul]
  tfae_have 3 → 4 := by
    rw [← LinearMap.det_toMatrix (chooseBasis K M), Matrix.det_eq_sign_charpoly_coeff,
      constantCoeff_apply, charpoly]
    intro h; rw [h, mul_zero]
  tfae_have 4 → 5 := bot_lt_ker_of_det_eq_zero
  tfae_have 5 → 6 := by
    contrapose!
    simp only [not_bot_lt_iff, eq_bot_iff]
    intro h x
    simp only [mem_ker, Submodule.mem_bot]
    contrapose!
    apply h
  tfae_have 6 → 1
  | ⟨x, h1, h2⟩ => by
    apply Module.End.hasEigenvalue_of_hasEigenvector ⟨_, h1⟩
    simpa only [Module.End.eigenspace_zero, mem_ker] using h2
  tfae_finish
/-
**LinearMap.charpoly_constantCoeff_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Map`。
形式化陈述：charpoly_constantCoeff_eq_zero_iff (φ : Module.End K M) : constantCoeff φ.
charpoly = 0 ↔ exists (m : M), m != 0 ∧ φ m = 0
参数：φ : Module.End K M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用引理 `LinearMap.hasEigenvalue_zero_tfae`：hasEigenvalue_zero_tfae (φ : Module.E
nd K M) : List.TFAE [ Module.End.HasEigenvalue φ 0, IsRoot (minpoly K φ) 0, cons
tantCoeff φ.charpoly = …
-/
lemma charpoly_constantCoeff_eq_zero_iff (φ : Module.End K M) :
    constantCoeff φ.charpoly = 0 ↔ ∃ (m : M), m ≠ 0 ∧ φ m = 0 :=
  (hasEigenvalue_zero_tfae φ).out 2 5

open Module.Free in
/-
**LinearMap.not_hasEigenvalue_zero_tfae** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：not_hasEigenvalue_zero_tfae (φ : Module.End K M) : List.TFAE [ ¬ Module.En
d.HasEigenvalue φ 0, ¬ IsRoot (minpoly K φ) 0, constantCoeff φ.charpoly != 0, Li
nearMap.det φ != 0, ker φ = ⊥, forall (m : M), φ m = 0 -> m = 0 ]
参数：φ : Module.End K M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `List.TFAE.not`：∀ {l : List Prop}, l.TFAE → (List.map Not l).TFAE
· 使用引理 `LinearMap.hasEigenvalue_zero_tfae`：hasEigenvalue_zero_tfae (φ : Module.E
nd K M) : List.TFAE [ Module.End.HasEigenvalue φ 0, IsRoot (minpoly K φ) 0, cons
tantCoeff φ.charpoly = …
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
-/
lemma not_hasEigenvalue_zero_tfae (φ : Module.End K M) :
    List.TFAE [
      ¬ Module.End.HasEigenvalue φ 0,
      ¬ IsRoot (minpoly K φ) 0,
      constantCoeff φ.charpoly ≠ 0,
      LinearMap.det φ ≠ 0,
      ker φ = ⊥,
      ∀ (m : M), φ m = 0 → m = 0 ] := by
  have := (hasEigenvalue_zero_tfae φ).not
  dsimp only [List.map] at this
  push Not at this
  have aux₁ : ∀ m, (m ≠ 0 → φ m ≠ 0) ↔ (φ m = 0 → m = 0) := by intro m; apply not_imp_not
  have aux₂ : ker φ = ⊥ ↔ ¬ ⊥ < ker φ := by rw [bot_lt_iff_ne_bot, not_not]
  simpa only [aux₁, aux₂] using this

open Module.Free in
/-
**LinearMap.finrank_maxGenEigenspace_zero_eq** 是 Mathlib 中的一个引理，位于命名空间 `LinearMa
p`。
形式化陈述：finrank_maxGenEigenspace_zero_eq (φ : Module.End K M) : finrank K (φ.maxGe
nEigenspace 0) = natTrailingDegree (φ.charpoly)
参数：φ : Module.End K M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Module.End.genEigenspace_nat`：genEigenspace_nat {f : End R M} {μ : R} {k
 : Nat} : f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`：isCompl_iSup_ker_pow_iInf
_range_pow [IsNoetherian R M] (f : M ->ₗ[R] M) : IsCompl (⨆ n, LinearMap.ker (f 
^ n)) (⨅ n, LinearMap.range (f ^ n)…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
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
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.prod_apply`：prod_apply (i) : b.prod b' i = Sum.elim (Linear
Map.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
（共 60 条，此处仅展示前 30 条）
-/
lemma finrank_maxGenEigenspace_zero_eq (φ : Module.End K M) :
    finrank K (φ.maxGenEigenspace 0) = natTrailingDegree (φ.charpoly) := by
  set V := φ.maxGenEigenspace 0
  have hV : V = ⨆ (n : ℕ), ker (φ ^ n) := by
    simp [V, ← Module.End.iSup_genEigenspace_eq, Module.End.genEigenspace_nat]
  let W := ⨅ (n : ℕ), LinearMap.range (φ ^ n)
  have hVW : IsCompl V W := by
    rw [hV]
    exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow φ
  have hφV : ∀ x ∈ V, φ x ∈ V := by
    simp only [V, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero,
      forall_exists_index]
    intro x n hx
    use n
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hx, map_zero]
  have hφW : ∀ x ∈ W, φ x ∈ W := by
    simp only [W, Submodule.mem_iInf, mem_range]
    intro x H n
    obtain ⟨y, rfl⟩ := H n
    use φ y
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
  let F := φ.restrict hφV
  let G := φ.restrict hφW
  let ψ := F.prodMap G
  let e := Submodule.prodEquivOfIsCompl V W hVW
  let bV := chooseBasis K V
  let bW := chooseBasis K W
  let b := bV.prod bW
  have hψ : ψ = e.symm.conj φ := by
    apply b.ext
    simp only [Basis.prod_apply, coe_inl, coe_inr, prodMap_apply, LinearEquiv.conj_apply,
      LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl, coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, coprod_apply, Submodule.coe_subtype, map_add, Sum.forall, Sum.elim_inl,
      map_zero, ZeroMemClass.coe_zero, add_zero, LinearEquiv.eq_symm_apply, and_self,
      Submodule.coe_prodEquivOfIsCompl', coe_restrict_apply, implies_true, Sum.elim_inr, zero_add,
      e, V, W, ψ, F, G, b]
  rw [← e.symm.charpoly_conj φ, ← hψ, charpoly_prodMap,
    natTrailingDegree_mul (charpoly_monic _).ne_zero (charpoly_monic _).ne_zero]
  have hG : natTrailingDegree (charpoly G) = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
    apply ((not_hasEigenvalue_zero_tfae G).out 2 5).mpr
    intro x hx
    apply Subtype.ext
    suffices x.1 ∈ V ⊓ W by rwa [hVW.inf_eq_bot, Submodule.mem_bot] at this
    suffices x.1 ∈ V from ⟨this, x.2⟩
    simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, V]
    use 1
    rw [pow_one]
    rwa [Subtype.ext_iff] at hx
  rw [hG, add_zero, eq_comm]
  apply ((charpoly_nilpotent_tfae F).out 2 3).mp
  simp only [Subtype.forall, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, V, F]
  rintro x ⟨n, hx⟩
  use n
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero]
  refine .trans ?_ hx
  generalize_proofs h'
  clear hx
  induction n <;> simp [pow_succ', *]
/-
**LinearMap.finrank_maxGenEigenspace_eq** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：finrank_maxGenEigenspace_eq (φ : Module.End K M) (μ : K) : finrank K (φ.ma
xGenEigenspace μ) = φ.charpoly.rootMultiplicity μ
参数：φ : Module.End K M；μ : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.maxGenEigenspace_eq_maxGenEigenspace_zero`：maxGenEigenspace_e
q_maxGenEigenspace_zero (f : End R M) (μ : R) : maxGenEigenspace f μ = maxGenEig
enspace (f - μ • 1) 0
· 使用引理 `LinearMap.finrank_maxGenEigenspace_zero_eq`：finrank_maxGenEigenspace_zer
o_eq (φ : Module.End K M) : finrank K (φ.maxGenEigenspace 0) = natTrailingDegree
 (φ.charpoly)
· 使用定理 `Polynomial.rootMultiplicity_eq_natTrailingDegree`：rootMultiplicity_eq_na
tTrailingDegree {p : R[X]} {t : R} : p.rootMultiplicity t = (p.comp (X + C t)).n
atTrailingDegree
· 使用定理 `LinearMap.charpoly_sub_smul`：charpoly_sub_smul (f : Module.End R M) (μ :
 R) : (f - μ • 1).charpoly = f.charpoly.comp (X + C μ)
-/
lemma finrank_maxGenEigenspace_eq (φ : Module.End K M) (μ : K) :
    finrank K (φ.maxGenEigenspace μ) = φ.charpoly.rootMultiplicity μ := by
  rw [φ.maxGenEigenspace_eq_maxGenEigenspace_zero, finrank_maxGenEigenspace_zero_eq,
    Polynomial.rootMultiplicity_eq_natTrailingDegree, LinearMap.charpoly_sub_smul]
/-
**LinearMap.finrank_genEigenspace_le** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：finrank_genEigenspace_le (φ : Module.End K M) (μ : K) (k : Nat) : finrank 
K (φ.genEigenspace μ k) <= φ.charpoly.rootMultiplicity μ
参数：φ : Module.End K M；μ : K；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Submodule.finrank_mono`：Submodule.finrank_mono {s t : Submodule R M} [Mo
dule.Finite R t] (hst : s <= t) : finrank R s <= finrank R t
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Module.End.genEigenspace_le_maximal`：genEigenspace_le_maximal (f : End R
 M) (μ : R) (k : Nat) : f.genEigenspace μ k <= f.maxGenEigenspace μ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.finrank_maxGenEigenspace_eq`：finrank_maxGenEigenspace_eq (φ : 
Module.End K M) (μ : K) : finrank K (φ.maxGenEigenspace μ) = φ.charpoly.rootMult
iplicity μ
-/
lemma finrank_genEigenspace_le (φ : Module.End K M) (μ : K) (k : ℕ) :
    finrank K (φ.genEigenspace μ k) ≤ φ.charpoly.rootMultiplicity μ := by
  grw [Submodule.finrank_mono (φ.genEigenspace_le_maximal μ k), finrank_maxGenEigenspace_eq]

/-- The geometric multiplicity of an eigenvalue is at most the algebraic multiplicity. -/
/-
**LinearMap.finrank_eigenspace_le** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：finrank_eigenspace_le (φ : Module.End K M) (μ : K) : finrank K (φ.eigenspa
ce μ) <= φ.charpoly.rootMultiplicity μ
参数：φ : Module.End K M；μ : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.finrank_genEigenspace_le`：finrank_genEigenspace_le (φ : Module
.End K M) (μ : K) (k : Nat) : finrank K (φ.genEigenspace μ k) <= φ.charpoly.root
Multiplicity μ

--- 原说明 ---
The geometric multiplicity of an eigenvalue is at most the algebraic multiplicit
y.
-/
lemma finrank_eigenspace_le (φ : Module.End K M) (μ : K) :
    finrank K (φ.eigenspace μ) ≤ φ.charpoly.rootMultiplicity μ :=
  finrank_genEigenspace_le ..

end LinearMap

