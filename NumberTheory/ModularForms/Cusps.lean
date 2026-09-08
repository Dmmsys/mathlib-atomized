/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Cusps

We define the cusps of a subgroup of `GL(2, ℝ)` as the fixed points of parabolic elements.
-/

@[expose] public section

open Matrix SpecialLinearGroup GeneralLinearGroup Filter Polynomial OnePoint

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace OnePoint

variable {K : Type*} [Field K] [DecidableEq K]

/-- The modular group `SL(2, A)` acts transitively on `OnePoint K`, if `A` is a PID whose fraction
field is `K`. (This includes the case `A = ℤ`, `K = ℚ`.) -/
/-
**OnePoint.exists_mem_SL2** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：exists_mem_SL2 (A : Type*) [CommRing A] [IsDomain A] [Algebra A K] [IsFrac
tionRing A K] [IsPrincipalIdealRing A] (c : OnePoint K) : exists g : SL(2, A), (
mapGL K g) • ∞ = c
参数：A : Type*；c : OnePoint K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用引理 `IsCoprime.exists_SL2_col`：exists_SL2_col {a b : R} (hab : IsCoprime a b)
 (j : Fin 2) : exists g : SL(2, R), g 0 j = a ∧ g 1 j = b
· 使用定理 `IsRelPrime.isCoprime`：∀ {R : Type u} [inst : CommRing R] {x y : R} [Subm
odule.IsPrincipal (Ideal.span {x, y})], IsRelPrime x y → IsCoprime x y
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `IsFractionRing.num_den_reduced`：num_den_reduced (x : K) : IsRelPrime (nu
m A x) (den A x)
· 使用引理 `OnePoint.smul_infty_eq_ite`：smul_infty_eq_ite (g : GL (Fin 2) K) : g • (
∞ : OnePoint K) = if g 1 0 = 0 then ∞ else g 0 0 / g 1 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsFractionRing.mk'_num_den'`：∀ (A : Type u_1) [inst : CommRing A] [inst_
1 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_3 
: Field K] [inst_…

--- 原说明 ---
The modular group `SL(2, A)` acts transitively on `OnePoint K`, if `A` is a PID 
whose fraction
field is `K`. (This includes the case `A = ℤ`, `K = ℚ`.)
-/
lemma exists_mem_SL2 (A : Type*) [CommRing A] [IsDomain A] [Algebra A K] [IsFractionRing A K]
    [IsPrincipalIdealRing A] (c : OnePoint K) :
    ∃ g : SL(2, A), (mapGL K g) • ∞ = c := by
  cases c with
  | infty => exact ⟨1, by simp⟩
  | coe q =>
    obtain ⟨g, hg0, hg1⟩ := (IsFractionRing.num_den_reduced A q).isCoprime.exists_SL2_col 0
    exact ⟨g, by simp [hg0, hg1, smul_infty_eq_ite]⟩

end OnePoint

namespace Subgroup.HasDetPlusMinusOne

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {𝒢 : Subgroup (GL (Fin 2) K)} [𝒢.HasDetPlusMinusOne]

/-
**Subgroup.HasDetPlusMinusOne.isParabolic_iff_of_upperTriangular** 是 Mathlib 中的一
个引理，位于命名空间 `Subgroup.HasDetPlusMinusOne`。
形式化陈述：isParabolic_iff_of_upperTriangular {g} (hg : g in 𝒢) (hg10 : g 1 0 = 0) : 
g.IsParabolic ↔ (exists x != 0, g = upperRightHom x) ∨ (exists x != (0 : K), g =
 -upperRightHom x)
参数：hg : g in 𝒢；hg10 : g 1 0 = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Matrix.GeneralLinearGroup.isParabolic_iff_of_upperTriangular_of_det`：isP
arabolic_iff_of_upperTriangular_of_det [LinearOrder K] [IsStrictOrderedRing K] {
g : GL (Fin 2) K} (h_det : g.det = 1 ∨ g.det = -1) (hg10 …
· 使用定理 `Subgroup.HasDetPlusMinusOne.det_eq`：∀ {n : Type u_1} {inst : Fintype n} 
{inst_1 : DecidableEq n} {R : Type u_2} {inst_2 : CommRing R}   {Γ : Subgroup (G
L n R)} [self : Γ.HasDet…
-/
lemma isParabolic_iff_of_upperTriangular {g} (hg : g ∈ 𝒢) (hg10 : g 1 0 = 0) :
    g.IsParabolic ↔ (∃ x ≠ 0, g = upperRightHom x) ∨ (∃ x ≠ (0 : K), g = -upperRightHom x) :=
  isParabolic_iff_of_upperTriangular_of_det (HasDetPlusMinusOne.det_eq hg) hg10

end Subgroup.HasDetPlusMinusOne

section IsCusp

/-- The *cusps* of a subgroup of `GL(2, ℝ)` are the fixed points of parabolic elements of `g`. -/
/-
**IsCusp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCusp (c : OnePoint Real) (𝒢 : Subgroup (GL (Fin 2) Real)) : Prop
参数：c : OnePoint Real；𝒢 : Subgroup (GL (Fin 2) Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *cusps* of a subgroup of `GL(2, ℝ)` are the fixed points of parabolic elemen
ts of `g`.
-/
def IsCusp (c : OnePoint ℝ) (𝒢 : Subgroup (GL (Fin 2) ℝ)) : Prop :=
  ∃ g ∈ 𝒢, g.IsParabolic ∧ g • c = c

open scoped Pointwise in
/-
**IsCusp.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCusp.smul {c : OnePoint Real} {𝒢 : Subgroup (GL (Fin 2) Real)} (hc : IsC
usp c 𝒢) (g : GL (Fin 2) Real) : IsCusp (g • c) (ConjAct.toConjAct g • 𝒢)
参数：GL (Fin 2) Real；hc : IsCusp c 𝒢；g : GL (Fin 2) Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.smul_mem_pointwise_smul`：smul_mem_pointwise_smul (m : G) (a : α
) (S : Subgroup G) : m in S -> a • m in a • S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsCusp.smul {c : OnePoint ℝ} {𝒢 : Subgroup (GL (Fin 2) ℝ)} (hc : IsCusp c 𝒢)
    (g : GL (Fin 2) ℝ) : IsCusp (g • c) (ConjAct.toConjAct g • 𝒢) := by
  obtain ⟨p, hp𝒢, hpp, hpc⟩ := hc
  refine ⟨_, 𝒢.smul_mem_pointwise_smul _ _ hp𝒢, ?_, ?_⟩
  · simpa [ConjAct.toConjAct_smul] using hpp
  · simp [ConjAct.toConjAct_smul, mul_smul, hpc]
/-
**IsCusp.smul_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCusp.smul_of_mem {c : OnePoint Real} {𝒢 : Subgroup (GL (Fin 2) Real)} (h
c : IsCusp c 𝒢) {g : GL (Fin 2) Real} (hg : g in 𝒢) : IsCusp (g • c) 𝒢
参数：GL (Fin 2) Real；hc : IsCusp c 𝒢；Fin 2；hg : g in 𝒢。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.mem_pointwise_smul_iff_inv_smul_mem`：mem_pointwise_smul_iff_inv
_smul_mem {a : α} {S : Subgroup G} {x : G} : x in a • S ↔ a⁻¹ • x in S
· 使用定理 `ConjAct.toConjAct_inv`：toConjAct_inv (x : G) : toConjAct x⁻¹ = (toConjAc
t x)⁻¹
· 使用定理 `ConjAct.toConjAct_smul`：toConjAct_smul (g h : G) : toConjAct g • h = g *
 h * g⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Subgroup.mul_mem_cancel_right`：∀ {G : Type u_1} [inst : Group G] (H : Su
bgroup G) {x y : G}, x ∈ H → (y * x ∈ H ↔ y ∈ H)
· 使用定理 `Subgroup.mul_mem_cancel_left`：∀ {G : Type u_1} [inst : Group G] (H : Sub
group G) {x y : G}, x ∈ H → (x * y ∈ H ↔ y ∈ H)
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `IsCusp.smul`：IsCusp.smul {c : OnePoint Real} {𝒢 : Subgroup (GL (Fin 2) R
eal)} (hc : IsCusp c 𝒢) (g : GL (Fin 2) Real) : IsCusp (g • c) (ConjAct.toConjAc
t…
-/
lemma IsCusp.smul_of_mem {c : OnePoint ℝ} {𝒢 : Subgroup (GL (Fin 2) ℝ)} (hc : IsCusp c 𝒢)
    {g : GL (Fin 2) ℝ} (hg : g ∈ 𝒢) : IsCusp (g • c) 𝒢 := by
  convert! hc.smul g
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul, inv_inv, Subgroup.mul_mem_cancel_right _ hg,
    Subgroup.mul_mem_cancel_left _ (inv_mem hg)]
/-
**isCusp_iff_of_relIndex_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCusp_iff_of_relIndex_ne_zero {𝒢 𝒢' : Subgroup (GL (Fin 2) Real)} (h𝒢 : 𝒢
' <= 𝒢) (h𝒢' : 𝒢'.relIndex 𝒢 != 0) (c : OnePoint Real) : IsCusp c 𝒢' ↔ IsCusp c 
𝒢
参数：GL (Fin 2) Real；h𝒢 : 𝒢' <= 𝒢；h𝒢' : 𝒢'.relIndex 𝒢 != 0；c : OnePoint Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.exists_pow_mem_of_relIndex_ne_zero`：exists_pow_mem_of_relIndex_
ne_zero (h : H.relIndex K != 0) {a : G} (ha : a in K) : exists n, 0 < n ∧ n <= H
.relIndex K ∧ a ^ n in H ⊓ K
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.mem_inf`：mem_inf {p p' : Subgroup G} {x : G} : x in p ⊓ p' ↔ x 
in p ∧ x in p'
· 使用定理 `Matrix.GeneralLinearGroup.IsParabolic.pow`：∀ {K : Type u_2} [inst : Fiel
d K] {g : GL (Fin 2) K},   g.IsParabolic → ∀ [CharZero K] {n : ℕ}, n ≠ 0 → (g ^ 
n).IsParabolic
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.IsParabolic.smul_eq_self_iff`：∀ {K : Type u_1}
 [inst : Field K] [inst_1 : DecidableEq K] {g : GL (Fin 2) K},   g.IsParabolic →
 ∀ [NeZero 2] {c : OnePoint K}, g • c = c ↔ …
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Matrix.GeneralLinearGroup.IsParabolic.parabolicFixedPoint_pow`：∀ {K : Ty
pe u_1} [inst : Field K] [inst_1 : DecidableEq K] {g : GL (Fin 2) K},   g.IsPara
bolic → ∀ [CharZero K] {n : ℕ}, n ≠ 0 → (g ^ n).par…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isCusp_iff_of_relIndex_ne_zero {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)}
    (h𝒢 : 𝒢' ≤ 𝒢) (h𝒢' : 𝒢'.relIndex 𝒢 ≠ 0) (c : OnePoint ℝ) :
    IsCusp c 𝒢' ↔ IsCusp c 𝒢 := by
  refine ⟨fun ⟨g, hg, hgp, hgc⟩ ↦ ⟨g, h𝒢 hg, hgp, hgc⟩, fun ⟨g, hg, hgp, hgc⟩ ↦ ?_⟩
  obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero h𝒢' hg
  refine ⟨g ^ n, (Subgroup.mem_inf.mpr hgn).1, hgp.pow hn.ne', ?_⟩
  rw [Nat.pos_iff_ne_zero] at hn
  rwa [(hgp.pow hn).smul_eq_self_iff, hgp.parabolicFixedPoint_pow hn, ← hgp.smul_eq_self_iff]
/-
**Subgroup.Commensurable.isCusp_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.Commensurable.isCusp_iff {𝒢 𝒢' : Subgroup (GL (Fin 2) Real)} (h𝒢 
: Commensurable 𝒢 𝒢') {c : OnePoint Real} : IsCusp c 𝒢 ↔ IsCusp c 𝒢'
参数：GL (Fin 2) Real；h𝒢 : Commensurable 𝒢 𝒢'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isCusp_iff_of_relIndex_ne_zero`：isCusp_iff_of_relIndex_ne_zero {𝒢 𝒢' : S
ubgroup (GL (Fin 2) Real)} (h𝒢 : 𝒢' <= 𝒢) (h𝒢' : 𝒢'.relIndex 𝒢 != 0) (c : OnePoi
nt Real) : IsCusp c …
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.inf_relIndex_left`：inf_relIndex_left : (H ⊓ K).relIndex H = K.r
elIndex H
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Subgroup.inf_relIndex_right`：inf_relIndex_right : (H ⊓ K).relIndex K = H
.relIndex K
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Subgroup.Commensurable.isCusp_iff {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)}
    (h𝒢 : Commensurable 𝒢 𝒢') {c : OnePoint ℝ} :
    IsCusp c 𝒢 ↔ IsCusp c 𝒢' := by
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_left, isCusp_iff_of_relIndex_ne_zero inf_le_right]
  · simpa [Subgroup.inf_relIndex_right] using h𝒢.1
  · simpa [Subgroup.inf_relIndex_left] using h𝒢.2
/-
**IsCusp.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCusp.mono {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {c : OnePoint Real} (hGH : 
𝒢 <= ℋ) (hc : IsCusp c 𝒢) : IsCusp c ℋ
参数：GL (Fin 2) Real；hGH : 𝒢 <= ℋ；hc : IsCusp c 𝒢。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsCusp.mono {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {c : OnePoint ℝ} (hGH : 𝒢 ≤ ℋ)
    (hc : IsCusp c 𝒢) : IsCusp c ℋ :=
  match hc with | ⟨h, hh, hp, hc⟩ => ⟨h, hGH hh, hp, hc⟩
/-
**IsCusp.of_isFiniteRelIndex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCusp.of_isFiniteRelIndex {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {c : OnePoin
t Real} [𝒢.IsFiniteRelIndex ℋ] (hc : IsCusp c ℋ) : IsCusp c 𝒢
参数：GL (Fin 2) Real；hc : IsCusp c ℋ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.relIndex_ne_zero`：∀ {G : Type u_1} [inst : Group G] {H K : Subg
roup G} [H.IsFiniteRelIndex K], H.relIndex K ≠ 0
· 使用引理 `IsCusp.mono`：IsCusp.mono {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {c : OnePoin
t Real} (hGH : 𝒢 <= ℋ) (hc : IsCusp c 𝒢) : IsCusp c ℋ
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isCusp_iff_of_relIndex_ne_zero`：isCusp_iff_of_relIndex_ne_zero {𝒢 𝒢' : S
ubgroup (GL (Fin 2) Real)} (h𝒢 : 𝒢' <= 𝒢) (h𝒢' : 𝒢'.relIndex 𝒢 != 0) (c : OnePoi
nt Real) : IsCusp c …
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Subgroup.inf_relIndex_right`：inf_relIndex_right : (H ⊓ K).relIndex K = H
.relIndex K
-/
lemma IsCusp.of_isFiniteRelIndex {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {c : OnePoint ℝ}
    [𝒢.IsFiniteRelIndex ℋ] (hc : IsCusp c ℋ) : IsCusp c 𝒢 := by
  have hGH : 𝒢.relIndex ℋ ≠ 0 := 𝒢.relIndex_ne_zero
  rw [← Subgroup.inf_relIndex_right] at hGH
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_right hGH] at hc
  exact hc.mono inf_le_left

open scoped Pointwise in
/-- Variant version of `IsCusp.of_isFiniteRelIndex`. -/
/-
**IsCusp.of_isFiniteRelIndex_conj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCusp.of_isFiniteRelIndex_conj {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {c : On
ePoint Real} [𝒢.IsFiniteRelIndex ℋ] (hc : IsCusp c ℋ) {h} (hh : h in ℋ) : IsCusp
 c (ConjAct.toConjAct h • 𝒢)
参数：GL (Fin 2) Real；hc : IsCusp c ℋ；hh : h in ℋ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subgroup.conjAct_pointwise_smul_eq_self`：conjAct_pointwise_smul_eq_self 
{H : Subgroup G} {g : G} (hg : g in normalizer H) : ConjAct.toConjAct g • H = H
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用引理 `Subgroup.relIndex_pointwise_smul`：Subgroup.relIndex_pointwise_smul [Grou
p G] [MulDistribMulAction H G] (J K : Subgroup G) : (h • J).relIndex (h • K) = J
.relIndex K
· 使用定理 `Subgroup.relIndex_ne_zero`：∀ {G : Type u_1} [inst : Group G] {H K : Subg
roup G} [H.IsFiniteRelIndex K], H.relIndex K ≠ 0
· 使用引理 `IsCusp.of_isFiniteRelIndex`：IsCusp.of_isFiniteRelIndex {𝒢 ℋ : Subgroup (
GL (Fin 2) Real)} {c : OnePoint Real} [𝒢.IsFiniteRelIndex ℋ] (hc : IsCusp c ℋ) :
 IsCusp c 𝒢

--- 原说明 ---
Variant version of `IsCusp.of_isFiniteRelIndex`.
-/
lemma IsCusp.of_isFiniteRelIndex_conj {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {c : OnePoint ℝ}
    [𝒢.IsFiniteRelIndex ℋ] (hc : IsCusp c ℋ) {h} (hh : h ∈ ℋ) :
    IsCusp c (ConjAct.toConjAct h • 𝒢) := by
  suffices (ConjAct.toConjAct h • 𝒢).IsFiniteRelIndex ℋ from hc.of_isFiniteRelIndex
  constructor
  rw [← ℋ.conjAct_pointwise_smul_eq_self (ℋ.le_normalizer hh), 𝒢.relIndex_pointwise_smul]
  exact 𝒢.relIndex_ne_zero

set_option backward.isDefEq.respectTransparency false in
/-- The cusps of `SL(2, ℤ)` are precisely the elements of `ℙ¹(ℚ)`. -/
/-
**isCusp_SL2Z_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCusp_SL2Z_iff {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ c in Set.range (OnePoi
nt.map Rat.cast)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.GeneralLinearGroup.IsParabolic.smul_eq_self_iff`：∀ {K : Type u_1}
 [inst : Field K] [inst_1 : DecidableEq K] {g : GL (Fin 2) K},   g.IsParabolic →
 ∀ [NeZero 2] {c : OnePoint K}, g • c = c ↔ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_sub`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p - q) = ↑p - ↑q
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `Rat.cast_ofNat`：∀ {α : Type u_3} [inst : DivisionRing α] (n : ℕ) [inst_1
 : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `OnePoint.exists_mem_SL2`：exists_mem_SL2 (A : Type*) [CommRing A] [IsDoma
in A] [Algebra A K] [IsFractionRing A K] [IsPrincipalIdealRing A] (c : OnePoint 
K) : exists g…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用引理 `zero_ne_one'`：zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) != 1
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
The cusps of `SL(2, ℤ)` are precisely the elements of `ℙ¹(ℚ)`.
-/
lemma isCusp_SL2Z_iff {c : OnePoint ℝ} : IsCusp c 𝒮ℒ ↔ c ∈ Set.range (OnePoint.map Rat.cast) := by
  constructor
  · rintro ⟨-, ⟨g, rfl⟩, hgp, hgc⟩
    simpa only [hgp.smul_eq_self_iff.mp hgc] using ⟨(mapGL ℚ g).parabolicFixedPoint,
      by simp [GeneralLinearGroup.parabolicFixedPoint, apply_ite]⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨a, rfl⟩ := c.exists_mem_SL2 ℤ
    refine ⟨_, ⟨a * ModularGroup.T * a⁻¹, rfl⟩, ?_, ?_⟩
    · suffices (mapGL ℝ ModularGroup.T).IsParabolic by simpa
      refine ⟨fun ⟨a, ha⟩ ↦ zero_ne_one' ℝ (by simpa [ModularGroup.T] using congr_fun₂ ha 0 1), ?_⟩
      simp [discr_fin_two, trace_fin_two, det_fin_two, ModularGroup.T]
      norm_num
    · rw [← Rat.coe_castHom, ← (Rat.castHom ℝ).algebraMap_toAlgebra]
      simp [OnePoint.map_smul, mul_smul, smul_infty_eq_self_iff, ModularGroup.T]

set_option backward.isDefEq.respectTransparency false in
/-- The cusps of `SL(2, ℤ)` are precisely the `SL(2, ℤ)` orbit of `∞`. -/
/-
**isCusp_SL2Z_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCusp_SL2Z_iff' {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ exists g : SL(2, Int)
, c = mapGL Real g • ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isCusp_SL2Z_iff`：isCusp_SL2Z_iff {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ c i
n Set.range (OnePoint.map Rat.cast)
· 使用引理 `OnePoint.exists_mem_SL2`：exists_mem_SL2 (A : Type*) [CommRing A] [IsDoma
in A] [Algebra A K] [IsFractionRing A K] [IsPrincipalIdealRing A] (c : OnePoint 
K) : exists g…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.coe_castHom`：∀ {α : Type u_3} [inst : DivisionRing α] [inst_1 : Char
Zero α], ⇑(Rat.castHom α) = Rat.cast
· 使用引理 `OnePoint.map_smul`：map_smul {L : Type*} [Field L] [DecidableEq L] (f : K
 ->+* L) (g : GL (Fin 2) K) (c : OnePoint K) : OnePoint.map f (g • c) = (g.map f
) • (c.…
· 使用定理 `OnePoint.map_infty`：∀ {X : Type u_1} {Y : Type u_2} (f : X → Y), OnePoin
t.map f OnePoint.infty = OnePoint.infty
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用引理 `Matrix.SpecialLinearGroup.map_mapGL`：map_mapGL {T : Type*} [CommRing T] 
[Algebra R T] [Algebra S T] [IsScalarTower R S T] (g : SpecialLinearGroup n R) :
 (mapGL S g).map (algebra…

--- 原说明 ---
The cusps of `SL(2, ℤ)` are precisely the `SL(2, ℤ)` orbit of `∞`.
-/
lemma isCusp_SL2Z_iff' {c : OnePoint ℝ} : IsCusp c 𝒮ℒ ↔ ∃ g : SL(2, ℤ), c = mapGL ℝ g • ∞ := by
  rw [isCusp_SL2Z_iff]
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨g, rfl⟩ := c.exists_mem_SL2 ℤ
    refine ⟨g, ?_⟩
    rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
      ← (Rat.castHom ℝ).algebraMap_toAlgebra, g.map_mapGL]
  · rintro ⟨g, rfl⟩
    refine ⟨mapGL ℚ g • ∞, ?_⟩
    rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
       ← (Rat.castHom ℝ).algebraMap_toAlgebra, g.map_mapGL]

/-- The cusps of any arithmetic subgroup are the same as those of `SL(2, ℤ)`. -/
/-
**Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (𝒢 : Subgroup (GL (Fin 2) Rea
l)) [𝒢.IsArithmetic] {c : OnePoint Real} : IsCusp c 𝒢 ↔ IsCusp c 𝒮ℒ
参数：𝒢 : Subgroup (GL (Fin 2) Real)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.Commensurable.isCusp_iff`：Subgroup.Commensurable.isCusp_iff {𝒢 
𝒢' : Subgroup (GL (Fin 2) Real)} (h𝒢 : Commensurable 𝒢 𝒢') {c : OnePoint Real} :
 IsCusp c 𝒢 ↔ IsCusp c …
· 使用定理 `Subgroup.IsArithmetic.is_commensurable`：∀ {𝒢 : Subgroup (GL (Fin 2) ℝ)} 
[self : 𝒢.IsArithmetic], 𝒢.Commensurable (Matrix.SpecialLinearGroup.mapGL ℝ).ran
ge

--- 原说明 ---
The cusps of any arithmetic subgroup are the same as those of `SL(2, ℤ)`.
-/
lemma Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic]
    {c : OnePoint ℝ} : IsCusp c 𝒢 ↔ IsCusp c 𝒮ℒ :=
  is_commensurable.isCusp_iff

end IsCusp

section CuspOrbits
/-!
## Cusp orbits

We consider the orbits for the action of `𝒢` on its own cusps. The main result is that if
`[𝒢.IsArithmetic]` holds, then this set is finite.
-/

/-- The action of `𝒢` on its own cusps. -/
/-
**cuspsSubMulAction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cuspsSubMulAction (𝒢 : Subgroup (GL (Fin 2) Real)) : SubMulAction 𝒢 (OnePo
int Real) where carrier
参数：𝒢 : Subgroup (GL (Fin 2) Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of `𝒢` on its own cusps.
-/
noncomputable def cuspsSubMulAction (𝒢 : Subgroup (GL (Fin 2) ℝ)) :
    SubMulAction 𝒢 (OnePoint ℝ) where
  carrier := {c | IsCusp c 𝒢}
  smul_mem' g _ hc := IsCusp.smul_of_mem hc g.property

/-- The type of cusp orbits of `𝒢`, i.e. orbits for the action of `𝒢` on its own cusps. -/
/-
**CuspOrbits** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CuspOrbits (𝒢 : Subgroup (GL (Fin 2) Real))
参数：𝒢 : Subgroup (GL (Fin 2) Real)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of cusp orbits of `𝒢`, i.e. orbits for the action of `𝒢` on its own cus
ps.
-/
abbrev CuspOrbits (𝒢 : Subgroup (GL (Fin 2) ℝ)) :=
  MulAction.orbitRel.Quotient 𝒢 (cuspsSubMulAction 𝒢)

set_option backward.isDefEq.respectTransparency false in
/-- Surjection from `SL(2, ℤ) / (𝒢 ⊓ SL(2, ℤ))` to cusp orbits of `𝒢`. Mostly useful for showing
that `CuspOrbits 𝒢` is finite for arithmetic subgroups. -/
/-
**cosetToCuspOrbit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cosetToCuspOrbit (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic] : SL(2,
 Int) ⧸ (𝒢.comap <| mapGL Real) -> CuspOrbits 𝒢
参数：𝒢 : Subgroup (GL (Fin 2) Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Surjection from `SL(2, ℤ) / (𝒢 ⊓ SL(2, ℤ))` to cusp orbits of `𝒢`. Mostly useful
 for showing
that `CuspOrbits 𝒢` is finite for arithmetic subgroups.
-/
noncomputable def cosetToCuspOrbit (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] :
    SL(2, ℤ) ⧸ (𝒢.comap <| mapGL ℝ) → CuspOrbits 𝒢 :=
  Quotient.lift
    (fun g ↦ ⟦⟨mapGL ℝ g⁻¹ • ∞,
      (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z 𝒢).mpr <| isCusp_SL2Z_iff.mpr
        ⟨mapGL ℚ g⁻¹ • ∞, by rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
          ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_mapGL]⟩⟩⟧)
    (fun a b hab ↦ by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hab
      refine Quotient.eq.mpr ⟨⟨_, hab⟩, ?_⟩
      simp [mul_smul])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**cosetToCuspOrbit_apply_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cosetToCuspOrbit_apply_mk {𝒢 : Subgroup (GL (Fin 2) Real)} [𝒢.IsArithmetic
] (g : SL(2, Int)) : cosetToCuspOrbit 𝒢 ⟦g⟧ = ⟦⟨mapGL Real g⁻¹ • ∞, (Subgroup.Is
Arithmetic.isCusp_iff_isCusp_SL2Z 𝒢).mpr isCusp_SL2Z_iff.mpr ⟨mapGL Rat g⁻¹ • ∞,
 by rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty, ← (Rat.castHom
 Real).algebraMap_toAlgebra, map_mapGL]⟩⟩⟧
参数：GL (Fin 2) Real；g : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cosetToCuspOrbit_apply_mk {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] (g : SL(2, ℤ)) :
    cosetToCuspOrbit 𝒢 ⟦g⟧ = ⟦⟨mapGL ℝ g⁻¹ • ∞,
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z 𝒢).mpr <| isCusp_SL2Z_iff.mpr
      ⟨mapGL ℚ g⁻¹ • ∞, by rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
        ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_mapGL]⟩⟩⟧ :=
  rfl
/-
**surjective_cosetToCuspOrbit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：surjective_cosetToCuspOrbit (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmet
ic] : (cosetToCuspOrbit 𝒢).Surjective
参数：𝒢 : Subgroup (GL (Fin 2) Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isCusp_SL2Z_iff'`：isCusp_SL2Z_iff' {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ e
xists g : SL(2, Int), c = mapGL Real g • ∞
· 使用引理 `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`：Subgroup.IsArithmetic.isCu
sp_iff_isCusp_SL2Z (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic] {c : OnePoi
nt Real} : IsCusp c 𝒢 ↔ IsCusp c 𝒮…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isCusp_SL2Z_iff`：isCusp_SL2Z_iff {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ c i
n Set.range (OnePoint.map Rat.cast)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma surjective_cosetToCuspOrbit (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] :
    (cosetToCuspOrbit 𝒢).Surjective := by
  rintro ⟨c, (hc : IsCusp c _)⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff'] at hc
  obtain ⟨g, rfl⟩ := hc
  use ⟦g⁻¹⟧
  aesop

/-- An arithmetic subgroup has finitely many cusp orbits. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arithmetic subgroup has finitely many cusp orbits.
-/
instance (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] : Finite (CuspOrbits 𝒢) :=
  .of_surjective _ (surjective_cosetToCuspOrbit 𝒢)

end CuspOrbits

section Width
/-!
## Width of a cusp

We define the *strict width* of `𝒢` at `∞` to be the smallest `h > 0` such that `[1, h; 0, 1] ∈ 𝒢`,
or `0` if no such `h` exists; and the *width* of `𝒢` to be the strict width of the subgroup
generated by `𝒢` and `-1`, or equivalently the smallest `h > 0` such that `±[1, h; 0, 1] ∈ 𝒢`
(again, if it exists). We show both widths exist when `𝒢` is discrete and has det `± 1`.
-/

namespace Subgroup

section Ring

variable {R : Type*} [Ring R] (𝒢 : Subgroup (GL (Fin 2) R))

/-- For a subgroup `𝒢` of `GL(2, R)`, this is the additive group of `x : R` such that
`[1, x; 0, 1] ∈ 𝒢`. -/
/-
**Subgroup.strictPeriods** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：strictPeriods : AddSubgroup R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a subgroup `𝒢` of `GL(2, R)`, this is the additive group of `x : R` such tha
t
`[1, x; 0, 1] ∈ 𝒢`.
-/
def strictPeriods : AddSubgroup R :=
  (toAddSubgroup 𝒢).comap upperRightHom.toAddMonoidHom

variable {𝒢} in
/-
**Subgroup.mem_strictPeriods_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {𝒢 : Subgroup (GL (Fin 2) R)} {x : R},   
x ∈ 𝒢.strictPeriods ↔ Matrix.GeneralLinearGroup.upperRightHom x ∈ 𝒢
参数：GL (Fin 2) R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.upperRightHom_apply`：∀ {R : Type u_1} [inst : 
Ring R] (x : R),   Matrix.GeneralLinearGroup.upperRightHom x =     { val := !![1
, x; 0, 1], inv := !![1, -x; 0, 1],…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_strictPeriods_iff {x : R} :
    x ∈ 𝒢.strictPeriods ↔ upperRightHom x ∈ 𝒢 := by
  simp [strictPeriods]

/-- For a subgroup `𝒢` of `GL(2, R)`, this is the additive group of `x : R` such that
`±[1, x; 0, 1] ∈ 𝒢`. -/
/-
**Subgroup.periods** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：{R : Type u_1} → [inst : Ring R] → Subgroup (GL (Fin 2) R) → AddSubgroup R
参数：GL (Fin 2) R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a subgroup `𝒢` of `GL(2, R)`, this is the additive group of `x : R` such tha
t
`±[1, x; 0, 1] ∈ 𝒢`.
-/
protected noncomputable def periods : AddSubgroup R :=
  𝒢.adjoinNegOne.strictPeriods
/-
**Subgroup.strictPeriods_le_periods** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：strictPeriods_le_periods : 𝒢.strictPeriods <= 𝒢.periods
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.le_adjoinNegOne`：Subgroup.le_adjoinNegOne (𝒢 : Subgroup (GL n R
)) : 𝒢 <= 𝒢.adjoinNegOne
-/
lemma strictPeriods_le_periods : 𝒢.strictPeriods ≤ 𝒢.periods := by
  intro k
  simp only [Subgroup.periods, strictPeriods]
  apply 𝒢.le_adjoinNegOne

/-- A subgroup is *regular at ∞* if its periods and strict periods coincide. -/
/-
**Subgroup.IsRegularAtInfty** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：IsRegularAtInfty : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup is *regular at ∞* if its periods and strict periods coincide.
-/
def IsRegularAtInfty : Prop :=
  𝒢.strictPeriods = 𝒢.periods
/-
**Subgroup.IsRegularAtInfty.eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsRegularAtIn
fty`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] (𝒢 : Subgroup (GL (Fin 2) R)), 𝒢.IsRegula
rAtInfty → 𝒢.strictPeriods = 𝒢.periods
参数：𝒢 : Subgroup (GL (Fin 2) R)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsRegularAtInfty.eq (h : 𝒢.IsRegularAtInfty) : 𝒢.strictPeriods = 𝒢.periods := h
/-
**Subgroup.relIndex_strictPeriods** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_strictPeriods : 𝒢.strictPeriods.relIndex 𝒢.periods = 1 ∨ 𝒢.strict
Periods.relIndex 𝒢.periods = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddSubgroup.relIndex_self`：∀ {G : Type u_1} [inst : AddGroup G] (H : Add
Subgroup G), H.relIndex H = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用引理 `Subgroup.strictPeriods_le_periods`：strictPeriods_le_periods : 𝒢.strictPe
riods <= 𝒢.periods
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.lt_iff_le_and_exists`：lt_iff_le_and_exists : p < q ↔ p <= q ∧ ex
ists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `AddSubgroup.relIndex_eq_two_iff_exists_notMem_and`：∀ {G : Type u_1} [ins
t : AddGroup G] {H K : AddSubgroup G},   H.relIndex K = 2 ↔ ∃ a ∈ K, a ∉ H ∧ ∀ b
 ∈ K, b + a ∈ H ∨ b ∈ H
· 使用引理 `AddChar.map_add_eq_mul`：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (
x + y) = ψ x * ψ y
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
-/
lemma relIndex_strictPeriods :
    𝒢.strictPeriods.relIndex 𝒢.periods = 1 ∨ 𝒢.strictPeriods.relIndex 𝒢.periods = 2 := by
  by_cases h : 𝒢.strictPeriods = 𝒢.periods
  · simp [h]
  · replace h := 𝒢.strictPeriods_le_periods.lt_of_ne h
    obtain ⟨u, hu_mem, hu_notMem⟩ := (SetLike.lt_iff_le_and_exists.mp h).2
    rw [AddSubgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine .inr ⟨u, hu_mem, hu_notMem, fun b hb ↦ ?_⟩
    simp only [Subgroup.periods, mem_strictPeriods_iff, mem_adjoinNegOne_iff,
      AddChar.map_add_eq_mul] at hu_mem hu_notMem hb ⊢
    rcases hb with h | h
    · exact Or.inr h
    · simpa only [neg_mul_neg] using Or.inl (mul_mem h <| hu_mem.resolve_left hu_notMem)
/-
**Subgroup.commensurable_strictPeriods_periods** 是 Mathlib 中的一个引理，位于命名空间 `Subgro
up`。
形式化陈述：commensurable_strictPeriods_periods : 𝒢.strictPeriods.Commensurable 𝒢.peri
ods
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.relIndex_strictPeriods`：relIndex_strictPeriods : 𝒢.strictPeriod
s.relIndex 𝒢.periods = 1 ∨ 𝒢.strictPeriods.relIndex 𝒢.periods = 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubgroup.relIndex_eq_one`：∀ {G : Type u_1} [inst : AddGroup G] {H K :
 AddSubgroup G}, H.relIndex K = 1 ↔ K ≤ H
· 使用引理 `Subgroup.strictPeriods_le_periods`：strictPeriods_le_periods : 𝒢.strictPe
riods <= 𝒢.periods
-/
lemma commensurable_strictPeriods_periods :
    𝒢.strictPeriods.Commensurable 𝒢.periods := by
  constructor
  · rcases 𝒢.relIndex_strictPeriods with h | h <;> simp [h]
  · simp [AddSubgroup.relIndex_eq_one.mpr 𝒢.strictPeriods_le_periods]

variable {𝒢}
/-
**Subgroup.strictPeriods_eq_periods_of_neg_one_mem** 是 Mathlib 中的一个引理，位于命名空间 `Su
bgroup`。
形式化陈述：strictPeriods_eq_periods_of_neg_one_mem (h𝒢 : -1 in 𝒢) : 𝒢.strictPeriods =
 𝒢.periods
参数：h𝒢 : -1 in 𝒢。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.adjoinNegOne_eq_self_iff`：∀ {n : Type u_1} [inst : Fintype n] [
inst_1 : DecidableEq n] {R : Type u_2} [inst_2 : Ring R] {𝒢 : Subgroup (GL n R)}
,   𝒢.adjoinNegOne = 𝒢 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma strictPeriods_eq_periods_of_neg_one_mem (h𝒢 : -1 ∈ 𝒢) :
    𝒢.strictPeriods = 𝒢.periods := by
  simp [Subgroup.periods, adjoinNegOne_eq_self_iff.mpr h𝒢]
/-
**Subgroup.isRegularAtInfty_of_neg_one_mem** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isRegularAtInfty_of_neg_one_mem (h𝒢 : -1 in 𝒢) : 𝒢.IsRegularAtInfty
参数：h𝒢 : -1 in 𝒢。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.strictPeriods_eq_periods_of_neg_one_mem`：strictPeriods_eq_perio
ds_of_neg_one_mem (h𝒢 : -1 in 𝒢) : 𝒢.strictPeriods = 𝒢.periods
-/
lemma isRegularAtInfty_of_neg_one_mem (h𝒢 : -1 ∈ 𝒢) : 𝒢.IsRegularAtInfty :=
  𝒢.strictPeriods_eq_periods_of_neg_one_mem h𝒢

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- If `𝒢` is discrete, so is its strict period subgroup. -/
/-
**Subgroup.instDiscreteTopStrictPeriods** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：instDiscreteTopStrictPeriods [hG : DiscreteTopology 𝒢] : DiscreteTopology 
𝒢.strictPeriods
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteTopology.of_subset`：DiscreteTopology.of_subset {X : Type*} [Topo
logicalSpace X] {s t : Set X} (_ : DiscreteTopology s) (ts : t subseteq s) : Dis
creteTopology t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `DiscreteTopology.of_continuous_injective`：DiscreteTopology.of_continuous
_injective {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [DiscreteTopolo
gy β] {f : α -> β} (hc : Conti…
· 使用定理 `Continuous.restrict`：Continuous.restrict {f : X -> Y} {s : Set X} {t : S
et Y} (h1 : MapsTo f s t) (h2 : Continuous f) : Continuous (h1.restrict f s t)
· 使用引理 `Matrix.GeneralLinearGroup.continuous_upperRightHom`：continuous_upperRigh
tHom {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] : Continuou
s (upperRightHom (R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.MapsTo.restrict_inj`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β} (h : Set.MapsTo f s t),   Function.Injective (Set.MapsTo.re
strict f s t …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用引理 `Matrix.GeneralLinearGroup.injective_upperRightHom`：injective_upperRightH
om : Function.Injective (upperRightHom (R

--- 原说明 ---
If `𝒢` is discrete, so is its strict period subgroup.
-/
instance instDiscreteTopStrictPeriods [hG : DiscreteTopology 𝒢] :
    DiscreteTopology 𝒢.strictPeriods := by
  let H : Set (GL (Fin 2) R) := 𝒢 ∩ Set.range upperRightHom
  have hH : DiscreteTopology H := hG.of_subset Set.inter_subset_left
  have : Set.MapsTo upperRightHom 𝒢.strictPeriods H := fun x hx ↦ by
    grind [SetLike.mem_coe, Subgroup.mem_strictPeriods_iff]
  exact .of_continuous_injective (continuous_upperRightHom.restrict this)
    (this.restrict_inj.mpr injective_upperRightHom.injOn)

/-- If `𝒢` is discrete, so is its period subgroup. -/
/-
**Subgroup.instDiscreteTopPeriods** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：instDiscreteTopPeriods [T2Space R] [hG : DiscreteTopology 𝒢] : DiscreteTop
ology 𝒢.periods
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `𝒢` is discrete, so is its period subgroup.
-/
instance instDiscreteTopPeriods [T2Space R] [hG : DiscreteTopology 𝒢] :
    DiscreteTopology 𝒢.periods :=
  inferInstanceAs (DiscreteTopology 𝒢.adjoinNegOne.strictPeriods)

end Ring

/-
**Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem** 是 Mathlib 中的一个引理，位于命名空间 `S
ubgroup`。
形式化陈述：strictPeriods_eq_zmultiples_one_of_T_mem {Γ : Subgroup SL(2, Int)} (hΓ : M
odularGroup.T in Γ) : strictPeriods (Γ : Subgroup (GL (Fin 2) Real)) = AddSubgro
up.zmultiples 1
参数：2, Int；hΓ : ModularGroup.T in Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.GeneralLinearGroup.upperRightHom_apply`：∀ {R : Type u_1} [inst : 
Ring R] (x : R),   Matrix.GeneralLinearGroup.upperRightHom x =     { val := !![1
, x; 0, 1], inv := !![1, -x; 0, 1],…
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congr_fun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sor
t u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b
…
· 使用定理 `zpow_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : DivInvMonoid M] [inst_
1 : SetLike S M] [hSM : SubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n : ℤ…
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `ModularGroup.coe_T_zpow`：coe_T_zpow (n : Int) : (T ^ n).1 = !![1, n; 0, 
1]
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
-/
lemma strictPeriods_eq_zmultiples_one_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hΓ : ModularGroup.T ∈ Γ) :
    strictPeriods (Γ : Subgroup (GL (Fin 2) ℝ)) = AddSubgroup.zmultiples 1 := by
  ext x
  simp only [mem_strictPeriods_iff, Subgroup.mem_map, Units.ext_iff, mapGL_coe_matrix,
    map_apply_coe]
  refine ⟨fun ⟨g, _, hg⟩ ↦ ⟨g 0 1, by simpa using congr_fun₂ hg 0 1⟩, ?_⟩
  rintro ⟨m, rfl⟩
  refine ⟨ModularGroup.T ^ m, zpow_mem hΓ m, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow]
/-
**Subgroup.strictPeriods_SL2Z** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：(Matrix.SpecialLinearGroup.mapGL ℝ).range.strictPeriods = AddSubgroup.zmul
tiples 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用引理 `Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem`：strictPeriods_eq_zmul
tiples_one_of_T_mem {Γ : Subgroup SL(2, Int)} (hΓ : ModularGroup.T in Γ) : stric
tPeriods (Γ : Subgroup (GL (Fin 2) Real…
· 使用定理 `Subgroup.mem_top`：mem_top (x : G) : x in (⊤ : Subgroup G)
-/
@[simp] lemma strictPeriods_SL2Z : strictPeriods 𝒮ℒ = AddSubgroup.zmultiples 1 := by
  simpa [MonoidHom.range_eq_map] using strictPeriods_eq_zmultiples_one_of_T_mem (mem_top _)

section Real

variable (𝒢 : Subgroup (GL (Fin 2) ℝ))

open scoped Classical in
/-- The strict width of the cusp `∞`, i.e. the `x` such that `𝒢.strictPeriods = zmultiples x`, or
0 if no such `x` exists. -/
/-
**Subgroup.strictWidthInfty** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：strictWidthInfty : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The strict width of the cusp `∞`, i.e. the `x` such that `𝒢.strictPeriods = zmul
tiples x`, or
0 if no such `x` exists.
-/
noncomputable def strictWidthInfty : ℝ :=
  if h : DiscreteTopology 𝒢.strictPeriods then
    |Exists.choose <| 𝒢.strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
      <| AddSubgroup.discrete_iff_addCyclic.mpr h|
  else 0
/-
**Subgroup.strictWidthInfty_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：strictWidthInfty_nonneg : 0 <= 𝒢.strictWidthInfty
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma strictWidthInfty_nonneg : 0 ≤ 𝒢.strictWidthInfty := by
  unfold strictWidthInfty; aesop

/-- The width of the cusp `∞`, i.e. the `x` such that `𝒢.periods = zmultiples x`, or 0 if no such
`x` exists. -/
/-
**Subgroup.widthInfty** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：widthInfty : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The width of the cusp `∞`, i.e. the `x` such that `𝒢.periods = zmultiples x`, or
 0 if no such
`x` exists.
-/
noncomputable def widthInfty : ℝ := 𝒢.adjoinNegOne.strictWidthInfty
/-
**Subgroup.widthInfty_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：widthInfty_nonneg : 0 <= 𝒢.widthInfty
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.strictWidthInfty_nonneg`：strictWidthInfty_nonneg : 0 <= 𝒢.stric
tWidthInfty
-/
lemma widthInfty_nonneg : 0 ≤ 𝒢.widthInfty := 𝒢.adjoinNegOne.strictWidthInfty_nonneg

variable {𝒢} in
/-
**Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty** 是 Mathlib 中的一个引理，位于命名空
间 `Subgroup`。
形式化陈述：strictPeriods_eq_zmultiples_strictWidthInfty [DiscreteTopology 𝒢.strictPer
iods] : 𝒢.strictPeriods = AddSubgroup.zmultiples 𝒢.strictWidthInfty
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `zmultiples_abs`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] (g : G),   AddSubgroup.zmultiples |g| = AddSubg
roup…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top`：∀ {α : Type u_1} [
inst : AddGroup α] (H : AddSubgroup α), IsAddCyclic ↥H ↔ ∃ g, AddSubgroup.zmulti
ples g = H
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubgroup.discrete_iff_addCyclic`：∀ {G : Type u_1} [inst : AddCommGrou
p G] [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [inst_3 : TopologicalSpace 
G]   [OrderTopology G] […
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma strictPeriods_eq_zmultiples_strictWidthInfty [DiscreteTopology 𝒢.strictPeriods] :
    𝒢.strictPeriods = AddSubgroup.zmultiples 𝒢.strictWidthInfty := by
  simp [Subgroup.strictWidthInfty, dif_pos,
    Exists.choose_spec <| 𝒢.strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
      <| AddSubgroup.discrete_iff_addCyclic.mpr inferInstance]
/-
**Subgroup.strictWidthInfty_eq_one_of_T_mem** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`
。
形式化陈述：strictWidthInfty_eq_one_of_T_mem {Γ : Subgroup SL(2, Int)} (hΓ : ModularGr
oup.T in Γ) : strictWidthInfty (Γ : Subgroup (GL (Fin 2) Real)) = 1
参数：2, Int；hΓ : ModularGroup.T in Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem`：strictPeriods_eq_zmul
tiples_one_of_T_mem {Γ : Subgroup SL(2, Int)} (hΓ : ModularGroup.T in Γ) : stric
tPeriods (Γ : Subgroup (GL (Fin 2) Real…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.instDiscreteTopologyZMultiples`：∀ {G : Type u_1} [inst : Add
CommGroup G] [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [inst_3 : Topologic
alSpace G]   [OrderTopology G] (…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `AddSubgroup.zmultiples_eq_zmultiples_iff`：∀ {G : Type u_1} [inst : AddGr
oup G] {x y : G},   ¬IsOfFinAddOrder x → (AddSubgroup.zmultiples x = AddSubgroup
.zmultiples y ↔ x = y ∨ -x = y…
· 使用定理 `not_isOfFinAddOrder_of_isAddTorsionFree`：∀ {G : Type u_1} [inst : AddMon
oid G] {a : G} [IsAddTorsionFree G], a ≠ 0 → ¬IsOfFinAddOrder a
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty`：strictPeriods_eq_
zmultiples_strictWidthInfty [DiscreteTopology 𝒢.strictPeriods] : 𝒢.strictPeriods
 = AddSubgroup.zmultiples 𝒢.strictWidthInft…
-/
lemma strictWidthInfty_eq_one_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hΓ : ModularGroup.T ∈ Γ) :
    strictWidthInfty (Γ : Subgroup (GL (Fin 2) ℝ)) = 1 := by
  have hsp := strictPeriods_eq_zmultiples_one_of_T_mem hΓ
  have : DiscreteTopology (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    -- In fact the image of `Γ` in `GL (Fin 2) ℝ` is itself discrete, but this is quicker:
    rw [hsp]
    infer_instance
  rw [strictPeriods_eq_zmultiples_strictWidthInfty, Eq.comm,
    AddSubgroup.zmultiples_eq_zmultiples_iff (not_isOfFinAddOrder_of_isAddTorsionFree one_ne_zero)]
    at hsp
  grind [strictWidthInfty_nonneg]
/-
**Subgroup.strictWidthInfty_SL2Z** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：strictWidthInfty_SL2Z : strictWidthInfty 𝒮ℒ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用引理 `Subgroup.strictWidthInfty_eq_one_of_T_mem`：strictWidthInfty_eq_one_of_T_
mem {Γ : Subgroup SL(2, Int)} (hΓ : ModularGroup.T in Γ) : strictWidthInfty (Γ :
 Subgroup (GL (Fin 2) Real)) = …
· 使用定理 `Subgroup.mem_top`：mem_top (x : G) : x in (⊤ : Subgroup G)
-/
lemma strictWidthInfty_SL2Z : strictWidthInfty 𝒮ℒ = 1 := by
  simpa [MonoidHom.range_eq_map] using strictWidthInfty_eq_one_of_T_mem (mem_top _)
/-
**Subgroup.strictWidthInfty_mem_strictPeriods** 是 Mathlib 中的一个引理，位于命名空间 `Subgrou
p`。
形式化陈述：strictWidthInfty_mem_strictPeriods : 𝒢.strictWidthInfty in 𝒢.strictPeriods
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty`：strictPeriods_eq_
zmultiples_strictWidthInfty [DiscreteTopology 𝒢.strictPeriods] : 𝒢.strictPeriods
 = AddSubgroup.zmultiples 𝒢.strictWidthInft…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
-/
lemma strictWidthInfty_mem_strictPeriods : 𝒢.strictWidthInfty ∈ 𝒢.strictPeriods := by
  by_cases h : DiscreteTopology 𝒢.strictPeriods
  · simp [strictPeriods_eq_zmultiples_strictWidthInfty]
  · simp [strictWidthInfty, dif_neg h]

variable {𝒢} in
/-
**Subgroup.periods_eq_zmultiples_widthInfty** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`
。
形式化陈述：periods_eq_zmultiples_widthInfty [DiscreteTopology 𝒢.periods] : 𝒢.periods 
= AddSubgroup.zmultiples 𝒢.widthInfty
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty`：strictPeriods_eq_
zmultiples_strictWidthInfty [DiscreteTopology 𝒢.strictPeriods] : 𝒢.strictPeriods
 = AddSubgroup.zmultiples 𝒢.strictWidthInft…
-/
lemma periods_eq_zmultiples_widthInfty [DiscreteTopology 𝒢.periods] :
    𝒢.periods = AddSubgroup.zmultiples 𝒢.widthInfty :=
  have : DiscreteTopology 𝒢.adjoinNegOne.strictPeriods := ‹_›
  𝒢.adjoinNegOne.strictPeriods_eq_zmultiples_strictWidthInfty
/-
**Subgroup.widthInfty_mem_periods** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：widthInfty_mem_periods : 𝒢.widthInfty in 𝒢.periods
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.strictWidthInfty_mem_strictPeriods`：strictWidthInfty_mem_strict
Periods : 𝒢.strictWidthInfty in 𝒢.strictPeriods
-/
lemma widthInfty_mem_periods : 𝒢.widthInfty ∈ 𝒢.periods :=
  𝒢.adjoinNegOne.strictWidthInfty_mem_strictPeriods
/-
**Subgroup.two_mul_widthInfty_mem_strictPeriods** 是 Mathlib 中的一个引理，位于命名空间 `Subgr
oup`。
形式化陈述：two_mul_widthInfty_mem_strictPeriods : 2 * 𝒢.widthInfty in 𝒢.strictPeriods
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.widthInfty_mem_periods`：widthInfty_mem_periods : 𝒢.widthInfty i
n 𝒢.periods
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Subgroup.pow_mem`：∀ {G : Type u_1} [inst : Group G] (K : Subgroup G) {x 
: G}, x ∈ K → ∀ (n : ℕ), x ^ n ∈ K
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma two_mul_widthInfty_mem_strictPeriods : 2 * 𝒢.widthInfty ∈ 𝒢.strictPeriods := by
  have := 𝒢.widthInfty_mem_periods
  simp only [Subgroup.periods, mem_strictPeriods_iff] at this
  rcases this with (h | h) <;>
    simpa [-upperRightHom_apply, ← AddChar.map_nsmul_eq_pow] using Subgroup.pow_mem _ h 2

variable {𝒢} in
/-
**Subgroup.strictWidthInfty_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：strictWidthInfty_pos_iff [DiscreteTopology 𝒢.strictPeriods] [𝒢.HasDetPlusM
inusOne] : 0 < 𝒢.strictWidthInfty ↔ IsCusp ∞ 𝒢
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.mem_strictPeriods_iff`：∀ {R : Type u_1} [inst : Ring R] {𝒢 : Su
bgroup (GL (Fin 2) R)} {x : R},   x ∈ 𝒢.strictPeriods ↔ Matrix.GeneralLinearGrou
p.upperRightHom x ∈ …
· 使用引理 `Subgroup.strictWidthInfty_mem_strictPeriods`：strictWidthInfty_mem_strict
Periods : 𝒢.strictWidthInfty in 𝒢.strictPeriods
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.GeneralLinearGroup.isParabolic_iff_of_upperTriangular`：isParaboli
c_iff_of_upperTriangular {g : GL (Fin 2) K} (hg : g 1 0 = 0) : g.IsParabolic ↔ g
 0 0 = g 1 1 ∧ g 0 1 != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.GeneralLinearGroup.upperRightHom_apply`：∀ {R : Type u_1} [inst : 
Ring R] (x : R),   Matrix.GeneralLinearGroup.upperRightHom x =     { val := !![1
, x; 0, 1], inv := !![1, -x; 0, 1],…
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用引理 `Subgroup.strictWidthInfty_nonneg`：strictWidthInfty_nonneg : 0 <= 𝒢.stric
tWidthInfty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.zmultiples_ne_bot`：∀ {G : Type u_1} [inst : AddGroup G] {g :
 G}, AddSubgroup.zmultiples g ≠ ⊥ ↔ g ≠ 0
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Subgroup.HasDetPlusMinusOne.isParabolic_iff_of_upperTriangular`：isParabo
lic_iff_of_upperTriangular {g} (hg : g in 𝒢) (hg10 : g 1 0 = 0) : g.IsParabolic 
↔ (exists x != 0, g = upperRightHom x) ∨ (exists x !…
· 使用引理 `OnePoint.smul_infty_eq_self_iff`：smul_infty_eq_self_iff {g : GL (Fin 2) 
K} : g • (∞ : OnePoint K) = ∞ ↔ g 1 0 = 0
· 使用引理 `AddChar.map_nsmul_eq_pow`：map_nsmul_eq_pow (ψ : AddChar A M) (n : Nat) (
x : A) : ψ (n • x) = ψ x ^ n
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
lemma strictWidthInfty_pos_iff [DiscreteTopology 𝒢.strictPeriods] [𝒢.HasDetPlusMinusOne] :
    0 < 𝒢.strictWidthInfty ↔ IsCusp ∞ 𝒢 := by
  constructor
  · refine fun h ↦ ⟨_, mem_strictPeriods_iff.mpr 𝒢.strictWidthInfty_mem_strictPeriods, ?_, ?_⟩
    · rw [GeneralLinearGroup.isParabolic_iff_of_upperTriangular (by simp)]
      simpa using h.ne'
    · simp [smul_infty_eq_self_iff]
  · -- Hard implication: if `∞` is a cusp, show the strict width is positive.
    rintro ⟨g, hgg, hgp, hgi⟩
    apply 𝒢.strictWidthInfty_nonneg.lt_of_ne'
    rw [← AddSubgroup.zmultiples_ne_bot]
    simp only [AddSubgroup.ne_bot_iff_exists_ne_zero, Subtype.exists, Ne, AddSubgroup.mk_eq_zero,
      exists_prop, and_comm, ← strictPeriods_eq_zmultiples_strictWidthInfty, mem_strictPeriods_iff]
    -- We have some `g ∈ 𝒢` which is parabolic and fixes `∞`. So `g = ±[1, x; 0, 1]` some `x ≠ 0`.
    rw [smul_infty_eq_self_iff] at hgi
    rw [Subgroup.HasDetPlusMinusOne.isParabolic_iff_of_upperTriangular hgg hgi] at hgp
    rcases hgp with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · -- If `g = [1, x; 0, 1]`, we're done
      exact ⟨x, hx, hgg⟩
    · -- If `g = -[1, x; 0, 1]` then `g ^ 2 = [1, 2 * x; 0, 1]`.
      exact ⟨2 • x, by grind,
        by simpa only [AddChar.map_nsmul_eq_pow, neg_sq] using pow_mem hgg 2⟩
/-
**Subgroup.strictWidthInfty_pos** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：strictWidthInfty_pos [𝒢.IsArithmetic] : 0 < 𝒢.strictWidthInfty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.strictWidthInfty_pos_iff`：strictWidthInfty_pos_iff [DiscreteTop
ology 𝒢.strictPeriods] [𝒢.HasDetPlusMinusOne] : 0 < 𝒢.strictWidthInfty ↔ IsCusp 
∞ 𝒢
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Subgroup.instHasDetPlusMinusOneFinOfNatNatRealOfIsArithmetic`：∀ {Γ : Sub
group (GL (Fin 2) ℝ)} [h : Γ.IsArithmetic], Γ.HasDetPlusMinusOne
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OnePoint.map_infty`：∀ {X : Type u_1} {Y : Type u_2} (f : X → Y), OnePoin
t.map f OnePoint.infty = OnePoint.infty
-/
lemma strictWidthInfty_pos [𝒢.IsArithmetic] : 0 < 𝒢.strictWidthInfty := by
  rw [strictWidthInfty_pos_iff]
  simpa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    using ⟨_, OnePoint.map_infty _⟩

variable {𝒢} in
/-
**Subgroup.isCusp_of_mem_strictPeriods** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isCusp_of_mem_strictPeriods {h : Real} (hh : 0 < h) (h𝒢 : h in 𝒢.strictPer
iods) : IsCusp OnePoint.infty 𝒢
参数：hh : 0 < h；h𝒢 : h in 𝒢.strictPeriods。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_strictPeriods_iff`：∀ {R : Type u_1} [inst : Ring R] {𝒢 : Su
bgroup (GL (Fin 2) R)} {x : R},   x ∈ 𝒢.strictPeriods ↔ Matrix.GeneralLinearGrou
p.upperRightHom x ∈ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Matrix.GeneralLinearGroup.isParabolic_iff_of_upperTriangular`：isParaboli
c_iff_of_upperTriangular {g : GL (Fin 2) K} (hg : g 1 0 = 0) : g.IsParabolic ↔ g
 0 0 = g 1 1 ∧ g 0 1 != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `OnePoint.smul_infty_eq_self_iff`：smul_infty_eq_self_iff {g : GL (Fin 2) 
K} : g • (∞ : OnePoint K) = ∞ ↔ g 1 0 = 0
-/
lemma isCusp_of_mem_strictPeriods {h : ℝ} (hh : 0 < h) (h𝒢 : h ∈ 𝒢.strictPeriods) :
    IsCusp OnePoint.infty 𝒢 := by
  refine ⟨upperRightHom h, 𝒢.mem_strictPeriods_iff.mp h𝒢, ?_, smul_infty_eq_self_iff.mpr rfl⟩
  exact (GeneralLinearGroup.isParabolic_iff_of_upperTriangular rfl).mpr ⟨rfl, hh.ne'⟩

variable {𝒢} in
/-
**Subgroup.widthInfty_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：widthInfty_pos_iff [DiscreteTopology 𝒢.periods] [𝒢.HasDetPlusMinusOne] : 0
 < 𝒢.widthInfty ↔ IsCusp ∞ 𝒢
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.widthInfty.eq_1`：∀ (𝒢 : Subgroup (GL (Fin 2) ℝ)), 𝒢.widthInfty 
= 𝒢.adjoinNegOne.strictWidthInfty
· 使用引理 `Subgroup.strictWidthInfty_pos_iff`：strictWidthInfty_pos_iff [DiscreteTop
ology 𝒢.strictPeriods] [𝒢.HasDetPlusMinusOne] : 0 < 𝒢.strictWidthInfty ↔ IsCusp 
∞ 𝒢
· 使用定理 `instHasDetPlusMinusOneAdjoinNegOne`：∀ {n : Type u_1} [inst : Fintype n] 
[inst_1 : DecidableEq n] {R : Type u_3} [inst_2 : CommRing R]   {𝒢 : Subgroup (G
L n R)} [𝒢.HasDetPlusMin…
· 使用引理 `Subgroup.Commensurable.isCusp_iff`：Subgroup.Commensurable.isCusp_iff {𝒢 
𝒢' : Subgroup (GL (Fin 2) Real)} (h𝒢 : Commensurable 𝒢 𝒢') {c : OnePoint Real} :
 IsCusp c 𝒢 ↔ IsCusp c …
· 使用引理 `Subgroup.commensurable_adjoinNegOne_self`：Subgroup.commensurable_adjoinN
egOne_self (𝒢 : Subgroup (GL n R)) : Commensurable 𝒢.adjoinNegOne 𝒢
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma widthInfty_pos_iff [DiscreteTopology 𝒢.periods] [𝒢.HasDetPlusMinusOne] :
    0 < 𝒢.widthInfty ↔ IsCusp ∞ 𝒢 := by
  have : DiscreteTopology 𝒢.adjoinNegOne.strictPeriods := ‹_›
  rw [widthInfty, strictWidthInfty_pos_iff, (commensurable_adjoinNegOne_self 𝒢).isCusp_iff]

variable {𝒢} in
/-
**Subgroup.isRegularAtInfty_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isRegularAtInfty_iff [DiscreteTopology 𝒢.periods] : 𝒢.IsRegularAtInfty ↔ 𝒢
.widthInfty in 𝒢.strictPeriods
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.widthInfty_mem_periods`：widthInfty_mem_periods : 𝒢.widthInfty i
n 𝒢.periods
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Subgroup.strictPeriods_le_periods`：strictPeriods_le_periods : 𝒢.strictPe
riods <= 𝒢.periods
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.periods_eq_zmultiples_widthInfty`：periods_eq_zmultiples_widthIn
fty [DiscreteTopology 𝒢.periods] : 𝒢.periods = AddSubgroup.zmultiples 𝒢.widthInf
ty
· 使用定理 `AddSubgroup.zmultiples_le`：∀ {G : Type u_1} [inst : AddGroup G] {g : G} 
{H : AddSubgroup G}, AddSubgroup.zmultiples g ≤ H ↔ g ∈ H
-/
lemma isRegularAtInfty_iff [DiscreteTopology 𝒢.periods] :
    𝒢.IsRegularAtInfty ↔ 𝒢.widthInfty ∈ 𝒢.strictPeriods := by
  refine ⟨fun h ↦ h ▸ widthInfty_mem_periods 𝒢, fun h ↦ ?_⟩
  apply 𝒢.strictPeriods_le_periods.antisymm
  rwa [periods_eq_zmultiples_widthInfty, AddSubgroup.zmultiples_le]
/-
**Subgroup.widthInfty_pos** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：widthInfty_pos [𝒢.IsArithmetic] : 0 < 𝒢.widthInfty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.strictWidthInfty_pos`：strictWidthInfty_pos [𝒢.IsArithmetic] : 0
 < 𝒢.strictWidthInfty
-/
lemma widthInfty_pos [𝒢.IsArithmetic] : 0 < 𝒢.widthInfty := by
  apply strictWidthInfty_pos

end Real

end Subgroup

open Subgroup

namespace CongruenceSubgroup

set_option backward.isDefEq.respectTransparency.types false in
/-
**CongruenceSubgroup.strictPeriods_Gamma0** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceS
ubgroup`。
形式化陈述：∀ (N : ℕ),   (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Congruence
Subgroup.Gamma0 N)).strictPeriods =     AddSubgroup.zmultiples 1
参数：N : ℕ；Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Ga
mma0 N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem`：strictPeriods_eq_zmul
tiples_one_of_T_mem {Γ : Subgroup SL(2, Int)} (hΓ : ModularGroup.T in Γ) : stric
tPeriods (Γ : Subgroup (GL (Fin 2) Real…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma strictPeriods_Gamma0 (N : ℕ) :
    strictPeriods (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) = AddSubgroup.zmultiples 1 :=
  strictPeriods_eq_zmultiples_one_of_T_mem <| by simp [ModularGroup.T]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CongruenceSubgroup.strictPeriods_Gamma1** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceS
ubgroup`。
形式化陈述：∀ (N : ℕ),   (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Congruence
Subgroup.Gamma1 N)).strictPeriods =     AddSubgroup.zmultiples 1
参数：N : ℕ；Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Ga
mma1 N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem`：strictPeriods_eq_zmul
tiples_one_of_T_mem {Γ : Subgroup SL(2, Int)} (hΓ : ModularGroup.T in Γ) : stric
tPeriods (Γ : Subgroup (GL (Fin 2) Real…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma strictPeriods_Gamma1 (N : ℕ) :
    strictPeriods (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) = AddSubgroup.zmultiples 1 :=
  strictPeriods_eq_zmultiples_one_of_T_mem <| by simp [ModularGroup.T]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CongruenceSubgroup.strictWidthInfty_Gamma0** 是 Mathlib 中的一个定理，位于命名空间 `Congruen
ceSubgroup`。
形式化陈述：∀ (N : ℕ), (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSu
bgroup.Gamma0 N)).strictWidthInfty = 1
参数：N : ℕ；Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Ga
mma0 N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.strictWidthInfty_eq_one_of_T_mem`：strictWidthInfty_eq_one_of_T_
mem {Γ : Subgroup SL(2, Int)} (hΓ : ModularGroup.T in Γ) : strictWidthInfty (Γ :
 Subgroup (GL (Fin 2) Real)) = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma strictWidthInfty_Gamma0 (N : ℕ) :
    strictWidthInfty (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) = 1 :=
  strictWidthInfty_eq_one_of_T_mem <| by simp [ModularGroup.T]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CongruenceSubgroup.strictWidthInfty_Gamma1** 是 Mathlib 中的一个定理，位于命名空间 `Congruen
ceSubgroup`。
形式化陈述：∀ (N : ℕ), (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSu
bgroup.Gamma1 N)).strictWidthInfty = 1
参数：N : ℕ；Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Ga
mma1 N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.strictWidthInfty_eq_one_of_T_mem`：strictWidthInfty_eq_one_of_T_
mem {Γ : Subgroup SL(2, Int)} (hΓ : ModularGroup.T in Γ) : strictWidthInfty (Γ :
 Subgroup (GL (Fin 2) Real)) = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma strictWidthInfty_Gamma1 (N : ℕ) :
    strictWidthInfty (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) = 1 :=
  strictWidthInfty_eq_one_of_T_mem <| by simp [ModularGroup.T]
/-
**CongruenceSubgroup.strictPeriods_Gamma** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSu
bgroup`。
形式化陈述：∀ (N : ℕ),   (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Congruence
Subgroup.Gamma N)).strictPeriods =     AddSubgroup.zmultiples ↑N
参数：N : ℕ；Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Ga
mma N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.map_zmultiples`：∀ {G : Type u_1} [inst : AddGroup G] {N : T
ype u_3} [inst_1 : AddGroup N] (f : G →+ N) (x : G),   AddSubgroup.map f (AddSub
group.zmultiples …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.GeneralLinearGroup.upperRightHom_apply`：∀ {R : Type u_1} [inst : 
Ring R] (x : R),   Matrix.GeneralLinearGroup.upperRightHom x =     { val := !![1
, x; 0, 1], inv := !![1, -x; 0, 1],…
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.mem_map_of_mem`：∀ {G : Type u_1} [inst : AddGroup G] {N : Ty
pe u_5} [inst_1 : AddGroup N] (f : G →+ N) {K : AddSubgroup G} {x : G},   x ∈ K 
→ f x ∈ AddSubgr…
· 使用定理 `Int.mem_zmultiples_iff`：Int.mem_zmultiples_iff {a b : Int} : b in AddSub
group.zmultiples a ↔ a ∣ b
· 使用定理 `ZMod.intCast_zmod_eq_zero_iff_dvd`：intCast_zmod_eq_zero_iff_dvd (a : Int
) (b : Nat) : (a : ZMod b) = 0 ↔ (b : Int) ∣ a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `ModularGroup.coe_T_zpow`：coe_T_zpow (n : Int) : (T ^ n).1 = !![1, n; 0, 
1]
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
（共 40 条，此处仅展示前 30 条）
-/
@[simp] lemma strictPeriods_Gamma (N : ℕ) :
    strictPeriods (Gamma N : Subgroup (GL (Fin 2) ℝ)) = AddSubgroup.zmultiples ↑N := by
  ext x
  have : AddSubgroup.zmultiples ↑N = .map (Int.castAddHom ℝ) (.zmultiples N) := by simp
  simp only [this, mem_strictPeriods_iff, Subgroup.mem_map, Gamma_mem]
  constructor
  · rintro ⟨g, ⟨-, hg, -, -⟩, hx⟩
    rw [show x = g 0 1 by simpa using congr_arg (· 0 1) hx.symm]
    apply AddSubgroup.mem_map_of_mem
    rwa [Int.mem_zmultiples_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  · simp only [AddSubgroup.mem_map, AddSubgroup.mem_zmultiples_iff, existsAndEq, true_and,
      Units.ext_iff, mapGL_coe_matrix, map_apply_coe, forall_exists_index]
    refine fun a ha ↦ ⟨ModularGroup.T ^ (a * N), by simp [ModularGroup.coe_T_zpow], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, ← ha]
/-
**CongruenceSubgroup.strictWidthInfty_Gamma** 是 Mathlib 中的一个定理，位于命名空间 `Congruenc
eSubgroup`。
形式化陈述：∀ (N : ℕ) [NeZero N],   (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) 
(CongruenceSubgroup.Gamma N)).strictWidthInfty = ↑N
参数：N : ℕ；Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Ga
mma N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CongruenceSubgroup.strictPeriods_Gamma`：∀ (N : ℕ),   (Subgroup.map (Matr
ix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma N)).strictPeriods =    
 AddSubgroup.zmultiples ↑N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.zmultiples_eq_zmultiples_iff`：∀ {G : Type u_1} [inst : AddGr
oup G] {x y : G},   ¬IsOfFinAddOrder x → (AddSubgroup.zmultiples x = AddSubgroup
.zmultiples y ↔ x = y ∨ -x = y…
· 使用定理 `not_isOfFinAddOrder_of_isAddTorsionFree`：∀ {G : Type u_1} [inst : AddMon
oid G] {a : G} [IsAddTorsionFree G], a ≠ 0 → ¬IsOfFinAddOrder a
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty`：strictPeriods_eq_
zmultiples_strictWidthInfty [DiscreteTopology 𝒢.strictPeriods] : 𝒢.strictPeriods
 = AddSubgroup.zmultiples 𝒢.strictWidthInft…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Subgroup.instIsArithmeticMapSpecialLinearGroupFinOfNatNatIntGeneralLinea
rGroupRealMapGLOfFiniteIndex`：∀ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2)
 ℤ)) [Γ.FiniteIndex],   (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ).IsA
rithmetic
-/
@[simp] lemma strictWidthInfty_Gamma (N : ℕ) [NeZero N] :
    strictWidthInfty (Gamma N : Subgroup (GL (Fin 2) ℝ)) = N := by
  have hsp := strictPeriods_Gamma N
  rw [strictPeriods_eq_zmultiples_strictWidthInfty, Eq.comm,
    AddSubgroup.zmultiples_eq_zmultiples_iff
      (not_isOfFinAddOrder_of_isAddTorsionFree (NeZero.ne _))] at hsp
  grind [strictWidthInfty_nonneg, Nat.cast_nonneg]

end CongruenceSubgroup

end Width

