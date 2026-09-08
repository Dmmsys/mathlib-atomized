/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.DedekindDomain.LinearDisjoint
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!

# (Absolute) Discriminant and Different Ideal

## Main results
- `NumberField.absNorm_differentIdeal`:
  The norm of `differentIdeal ℤ 𝒪` is the absolute discriminant.
- `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`:
  Formula for the absolute discriminant of `L` in terms of that of `K` in an extension `L/K`.
- `NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow`:
  Assume that `K₁` and `K₂` are two linear disjoint number fields with coprime different ideals.
  Then, the absolute value of the discriminant of their compositum is equal to
  `|discr K₁| ^ [K₂ : ℚ] * |discr K₂| ^ [K₁ : ℚ]`.

-/

public section

namespace NumberField

variable (K 𝒪 : Type*) [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]

open IntermediateField IsDedekindDomain

section

variable [IsFractionRing 𝒪 K] [IsDedekindDomain 𝒪] [CharZero 𝒪]
variable [Module.Finite ℤ 𝒪]

open nonZeroDivisors IntermediateField Module

/-
**NumberField.absNorm_differentIdeal** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：absNorm_differentIdeal : (differentIdeal Int 𝒪).absNorm = (discr K).natAbs
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.relIndex_top_right`：∀ {G : Type u_1} [inst : AddGroup G] (H 
: AddSubgroup G), H.relIndex ⊤ = H.index
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.comap_map_eq_of_injective`：comap_map_eq_of_injective (p : Subm
odule R M) : (p.map f).comap f = p
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `AddSubgroup.relIndex_comap`：∀ {G : Type u_1} {G' : Type u_2} [inst : Add
Group G] [inst_1 : AddGroup G'] (H : AddSubgroup G) (f : G' →+ G)   (K : AddSubg
roup G'), (AddSu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `Algebra.IsSeparable.of_integral`：∀ (F : Type u_1) [inst : Field F] (K : 
Type u_2) [inst_1 : Ring K] [inst_2 : Algebra F K] [IsDomain K]   [Algebra.IsInt
egral F K] [CharZero …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instFiniteDimensionalFractionRingOfFinite`：∀ {R : Type u_1} {S : Type u_
2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [inst_3 : Is
Domain R]   [inst_4 : IsDomain …
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FractionalIdeal.coeIdeal_le_one`：coeIdeal_le_one {I : Ideal R} : (I : Fr
actionalIdeal S P) <= 1
· 使用引理 `le_inv_of_le_inv₀`：le_inv_of_le_inv₀ (ha : 0 < a) (h : a <= b⁻¹) : b <= 
a⁻¹
（共 84 条，此处仅展示前 30 条）
-/
lemma absNorm_differentIdeal : (differentIdeal ℤ 𝒪).absNorm = (discr K).natAbs := by
  refine (differentIdeal ℤ 𝒪).toAddSubgroup.relIndex_top_right.symm.trans ?_
  rw [← Submodule.comap_map_eq_of_injective (f := Algebra.linearMap 𝒪 K)
    (FaithfulSMul.algebraMap_injective 𝒪 K) (differentIdeal ℤ 𝒪)]
  refine (AddSubgroup.relIndex_comap (IsLocalization.coeSubmodule K
    (differentIdeal ℤ 𝒪)).toAddSubgroup (algebraMap 𝒪 K).toAddMonoidHom ⊤).trans ?_
  have := FractionalIdeal.quotientEquiv (R := 𝒪) (K := K) 1 (differentIdeal ℤ 𝒪)
    (differentIdeal ℤ 𝒪)⁻¹ 1 (by simp [differentIdeal_ne_bot]) FractionalIdeal.coeIdeal_le_one
    (le_inv_of_le_inv₀ (by simp [pos_iff_ne_zero, differentIdeal_ne_bot])
      (by simpa using FractionalIdeal.coeIdeal_le_one)) one_ne_zero one_ne_zero
  have := Nat.card_congr this.toEquiv
  refine this.trans ?_
  rw [FractionalIdeal.coe_one, coeIdeal_differentIdeal (K := ℚ), inv_inv]
  let b := integralBasis K
  let b' := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) b
  have hb : Submodule.span ℤ (Set.range b) = (1 : Submodule 𝒪 K).restrictScalars ℤ := by
    ext
    let e := IsIntegralClosure.equiv ℤ (RingOfIntegers K) K 𝒪
    simpa [e.symm.exists_congr_left, e] using mem_span_integralBasis K
  qify
  refine (AddSubgroup.relIndex_eq_abs_det (1 : Submodule 𝒪 K).toAddSubgroup (FractionalIdeal.dual
    ℤ ℚ 1 : FractionalIdeal 𝒪⁰ K).coeToSubmodule.toAddSubgroup ?_ b b' ?_ ?_).trans ?_
  · rw [Submodule.toAddSubgroup_le, ← FractionalIdeal.coe_one]
    exact FractionalIdeal.one_le_dual_one ℤ ℚ (L := K) (B := 𝒪)
  · apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure, hb, Submodule.toIntSubmodule_toAddSubgroup]
  · apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure, ← LinearMap.BilinForm.dualSubmodule_span_of_basis, hb]
    simp
  · simp only [Module.Basis.det_apply, discr, Algebra.discr]
    rw [← eq_intCast (algebraMap ℤ ℚ), RingHom.map_det]
    congr! 2
    ext i j
    simp [b', Module.Basis.toMatrix_apply, mul_comm (RingOfIntegers.basis K i),
      b, integralBasis_apply, ← map_mul, Algebra.trace_localization ℤ ℤ⁰]
/-
**NumberField.discr_mem_differentIdeal** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：discr_mem_differentIdeal : ↑(discr K) in differentIdeal Int 𝒪
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Ideal.absNorm_mem`：absNorm_mem (I : Ideal S) : ↑(Ideal.absNorm I) in I
· 使用定理 `Int.natAbs_eq`：∀ (a : ℤ), a = ↑a.natAbs ∨ a = -↑a.natAbs
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `NumberField.absNorm_differentIdeal`：absNorm_differentIdeal : (differentI
deal Int 𝒪).absNorm = (discr K).natAbs
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.eq_neg_comm`：∀ {a b : ℤ}, a = -b ↔ b = -a
-/
lemma discr_mem_differentIdeal : ↑(discr K) ∈ differentIdeal ℤ 𝒪 := by
  have := (differentIdeal ℤ 𝒪).absNorm_mem
  cases (discr K).natAbs_eq with
  | inl h =>
    rwa [absNorm_differentIdeal K, ← Int.cast_natCast, ← h] at this
  | inr h =>
    rwa [absNorm_differentIdeal K, ← Int.cast_natCast, Int.eq_neg_comm.mp h,
      Int.cast_neg, neg_mem_iff] at this

attribute [local instance] FractionRing.liftAlgebra in
/-
**NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow** 是 Ma
thlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (L 𝒪' : Type*)
 [Field L] [NumberField L] [CommRing 𝒪'] [Algebra 𝒪' L] [IsFractionRing 𝒪' L] [I
sDedekindDomain 𝒪'] [CharZero 𝒪'] [Algebra K L] [Algebra 𝒪 𝒪'] [Algebra 𝒪 L] [Is
ScalarTower 𝒪 K L] [IsScalarTower 𝒪 𝒪' L] [IsTorsionFree 𝒪 𝒪'] [Free Int 𝒪'] [Mo
dule.Finite Int 𝒪'] [Module.Finite 𝒪 𝒪'] : (discr L).natAbs = Ideal.absNorm (dif
ferentIdeal 𝒪 𝒪') * (discr K).natAbs ^ Module.finrank K L
参数：L 𝒪' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `differentIdeal_eq_differentIdeal_mul_differentIdeal`：differentIdeal_eq_d
ifferentIdeal_mul_differentIdeal (C : Type*) [IsDomain B] [CommRing C] [Algebra 
B C] [Algebra A C] [IsDedekindDomain C] […
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `Algebra.IsSeparable.of_integral`：∀ (F : Type u_1) [inst : Field F] (K : 
Type u_2) [inst_1 : Ring K] [inst_2 : Algebra F K] [IsDomain K]   [Algebra.IsInt
egral F K] [CharZero …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instFiniteDimensionalFractionRingOfFinite`：∀ {R : Type u_1} {S : Type u_
2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [inst_3 : Is
Domain R]   [inst_4 : IsDomain …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsFractionRing.finrank_eq`：∀ (A : Type u_1) (K : Type u_2) (B : Type u_3
) (L : Type u_4) [inst : CommRing A] [inst_1 : CommRing K]   [inst_2 : CommRing 
B] [inst_3 : Co…
· 使用引理 `NumberField.absNorm_differentIdeal`：absNorm_differentIdeal : (differentI
deal Int 𝒪).absNorm = (discr K).natAbs
· 使用定理 `Ideal.absNorm_algebraMap`：absNorm_algebraMap (I : Ideal R) [Module.Finit
e Int R] : absNorm (I.map (algebraMap R S)) = absNorm I ^ finrank R S
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (L 𝒪' : Type*) [Field L]
    [NumberField L] [CommRing 𝒪'] [Algebra 𝒪' L] [IsFractionRing 𝒪' L]
    [IsDedekindDomain 𝒪'] [CharZero 𝒪'] [Algebra K L] [Algebra 𝒪 𝒪'] [Algebra 𝒪 L]
    [IsScalarTower 𝒪 K L] [IsScalarTower 𝒪 𝒪' L] [IsTorsionFree 𝒪 𝒪'] [Free ℤ 𝒪']
    [Module.Finite ℤ 𝒪'] [Module.Finite 𝒪 𝒪'] :
    (discr L).natAbs = Ideal.absNorm (differentIdeal 𝒪 𝒪') *
      (discr K).natAbs ^ Module.finrank K L := by
  have := congr_arg Ideal.absNorm
    (differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ 𝒪 𝒪')
  rwa [absNorm_differentIdeal L, map_mul, Ideal.absNorm_algebraMap,
    absNorm_differentIdeal K, ← IsFractionRing.finrank_eq 𝒪 K 𝒪' L] at this

variable (L : Type*) [Field L]
/-
**NumberField.isCoprime_differentIdeal_of_isCoprime_discr** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField`。
形式化陈述：isCoprime_differentIdeal_of_isCoprime_discr {K₁ K₂ : Type*} [Field K₁] [Nu
mberField K₁] [Field K₂] [NumberField K₂] [Algebra K₁ L] [Algebra K₂ L] (h : IsC
oprime (discr K₁) (discr K₂)) : IsCoprime ((differentIdeal Int (𝓞 K₁)).map (alge
braMap (𝓞 K₁) (𝓞 L))) ((differentIdeal Int (𝓞 K₂)).map (algebraMap (𝓞 K₂) (𝓞 L))
)
参数：h : IsCoprime (discr K₁) (discr K₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isCoprime_iff_exists`：isCoprime_iff_exists : IsCoprime I J ↔ exist
s i in I, exists j in J, i + j = 1
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用引理 `NumberField.discr_mem_differentIdeal`：discr_mem_differentIdeal : ↑(discr
 K) in differentIdeal Int 𝒪
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
-/
theorem isCoprime_differentIdeal_of_isCoprime_discr {K₁ K₂ : Type*} [Field K₁]
    [NumberField K₁] [Field K₂] [NumberField K₂] [Algebra K₁ L] [Algebra K₂ L]
    (h : IsCoprime (discr K₁) (discr K₂)) :
    IsCoprime ((differentIdeal ℤ (𝓞 K₁)).map (algebraMap (𝓞 K₁) (𝓞 L)))
      ((differentIdeal ℤ (𝓞 K₂)).map (algebraMap (𝓞 K₂) (𝓞 L))) := by
  obtain ⟨u, v, h⟩ := h
  refine Ideal.isCoprime_iff_exists.mpr ⟨u * discr K₁, ?_, v * discr K₂, ?_, ?_⟩
  · apply Ideal.mul_mem_left
    rw [← map_intCast (algebraMap (𝓞 K₁) (𝓞 L))]
    exact Ideal.mem_map_of_mem (algebraMap (𝓞 K₁) (𝓞 L)) <| discr_mem_differentIdeal _ _
  · apply Ideal.mul_mem_left
    rw [← map_intCast (algebraMap (𝓞 K₂) (𝓞 L))]
    exact Ideal.mem_map_of_mem (algebraMap (𝓞 K₂) (𝓞 L)) <| discr_mem_differentIdeal _ _
  rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add, h, Int.cast_one]

variable [NumberField L]
/-
**NumberField.discr_dvd_discr** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：discr_dvd_discr [Algebra K L] : discr K ∣ discr L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.dvd_natAbs`：∀ {a b : ℤ}, a ∣ ↑b.natAbs ↔ a ∣ b
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `NumberField.RingOfIntegers.instIsTorsionFree_1`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   Module.IsT
orsionFree (NumberField.RingOfIntege…
· 使用定理 `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`
：natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (L 𝒪' : Type*) [Fie
ld L] [NumberField L] [CommRing 𝒪'] [Algebra 𝒪' L] [IsFractio…
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsScalarTower`：∀ (K : Type u_1) [inst : F
ield K] {L : Type u_3} [inst_1 : Ring L] [inst_2 : Algebra K L],   IsScalarTower
 (NumberField.RingOfIntegers K) K …
· 使用定理 `NumberField.RingOfIntegers.instIsScalarTower_1`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   IsScalarTo
wer (NumberField.RingOfIntegers K) (…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Int.mul_sign_self`：∀ (i : ℤ), i * i.sign = ↑i.natAbs
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Int.dvd_mul_right`：∀ (a b : ℤ), a ∣ a * b
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
（共 39 条，此处仅展示前 30 条）
-/
theorem discr_dvd_discr [Algebra K L] :
    discr K ∣ discr L := by
  suffices discr K ^ Module.finrank K L ∣ discr L from
    dvd_trans (dvd_pow_self _ (Nat.ne_zero_of_lt Module.finrank_pos)) this
  rw [← Int.dvd_natAbs, natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L),
    Nat.cast_mul, Nat.cast_pow, ← Int.mul_sign_self, mul_pow, ← mul_assoc,
    mul_comm _ (discr K ^ _), mul_assoc]
  exact Int.dvd_mul_right _ _

set_option backward.isDefEq.respectTransparency false in
/--
Let `K₁` and `K₂` be two number fields and assume that `K₁/ℚ` is Galois. If `discr K₁` and
`discr K₂` are coprime, then they are linear disjoint over `ℚ`.
-/
/-
**NumberField.linearDisjoint_of_isGalois_isCoprime_discr** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField`。
形式化陈述：linearDisjoint_of_isGalois_isCoprime_discr (K₁ K₂ : IntermediateField Rat 
L) [IsGalois Rat K₁] (h : IsCoprime (discr K₁) (discr K₂)) : K₁.LinearDisjoint K
₂
参数：K₁ K₂ : IntermediateField Rat L；h : IsCoprime (discr K₁) (discr K₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `IntermediateField.LinearDisjoint.of_inf_eq_bot`：of_inf_eq_bot [IsGalois 
F A] [FiniteDimensional F A] [FiniteDimensional F B] (h : A ⊓ B = ⊥) : A.LinearD
isjoint B
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `IsCoprime.isUnit_of_dvd'`：IsCoprime.isUnit_of_dvd' {a b x : R} (h : IsCo
prime a b) (ha : x ∣ a) (hb : x ∣ b) : IsUnit x
· 使用定理 `NumberField.discr_dvd_discr`：discr_dvd_discr [Algebra K L] : discr K ∣ d
iscr L
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_iff_ne_zero_and_ne_one`：∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.finrank_eq_one_iff`：finrank_eq_one_iff : finrank F K =
 1 ↔ K = ⊥
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Int.isUnit_iff_abs_eq`：isUnit_iff_abs_eq {x : Int} : IsUnit x ↔ abs x = 
1
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
Let `K₁` and `K₂` be two number fields and assume that `K₁/ℚ` is Galois. If `dis
cr K₁` and
`discr K₂` are coprime, then they are linear disjoint over `ℚ`.
-/
theorem linearDisjoint_of_isGalois_isCoprime_discr (K₁ K₂ : IntermediateField ℚ L) [IsGalois ℚ K₁]
    (h : IsCoprime (discr K₁) (discr K₂)) :
    K₁.LinearDisjoint K₂ := by
  apply IntermediateField.LinearDisjoint.of_inf_eq_bot
  suffices IsUnit (discr ↥(K₁ ⊓ K₂)) by
    contrapose! this
    have : 1 < Module.finrank ℚ ↥(K₁ ⊓ K₂) := by
      refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Module.finrank_pos.ne', ?_⟩
      rwa [ne_eq, ← IntermediateField.finrank_eq_one_iff] at this
    exact Int.isUnit_iff_abs_eq.not.mpr <| by linarith [abs_discr_gt_two this]
  exact h.isUnit_of_dvd' (NumberField.discr_dvd_discr _ _) (NumberField.discr_dvd_discr _ _)

/--
Let `K₁` and `K₂` be two number fields and assume that their different ideals (over ℤ) are coprime.
Then, the absolute value of the discriminant of their compositum is equal to
`|discr K₁| ^ [K₂ : ℚ] * |discr K₂| ^ [K₁ : ℚ]`.
-/
/-
**NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow** 是 Mathlib 
中的一个定理，位于命名空间 `NumberField`。
形式化陈述：natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow (K₁ K₂ : Intermediat
eField Rat L) (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) (h₃ : IsCoprime ((d
ifferentIdeal Int (𝓞 K₁)).map (algebraMap (𝓞 K₁) (𝓞 L))) ((differentIdeal Int (𝓞
 K₂)).map (algebraMap (𝓞 K₂) (𝓞 L)))) : (discr L).natAbs = (discr K₁).natAbs ^ M
odule.finrank Rat K₂ * (discr K₂).natAbs ^ Module.finrank Rat K₁
参数：K₁ K₂ : IntermediateField Rat L；h₁ : K₁.LinearDisjoint K₂；h₂ : K₁ ⊔ K₂ = ⊤；h₃
 : IsCoprime ((differentIdeal Int (𝓞 K₁)).map (algebraMap (𝓞 K₁) (𝓞 L))) ((diffe
rentIdeal Int (𝓞 K₂)).map (algebraMap (𝓞 K₂) (𝓞 L)))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `NumberField.RingOfIntegers.instIsTorsionFree_1`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   Module.IsT
orsionFree (NumberField.RingOfIntege…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `NumberField.instNontrivialRingOfIntegers`：∀ (K : Type u_1) [inst : Field
 K], Nontrivial (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`
：natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (L 𝒪' : Type*) [Fie
ld L] [NumberField L] [CommRing 𝒪'] [Algebra 𝒪' L] [IsFractio…
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsScalarTower`：∀ (K : Type u_1) [inst : F
ield K] {L : Type u_3} [inst_1 : Ring L] [inst_2 : Algebra K L],   IsScalarTower
 (NumberField.RingOfIntegers K) K …
· 使用定理 `NumberField.RingOfIntegers.instIsScalarTower_1`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   IsScalarTo
wer (NumberField.RingOfIntegers K) (…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.LinearDisjoint.finrank_left_eq_finrank`：finrank_left_e
q_finrank [Module.Finite F A] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) : finra
nk A E = finrank F B
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsFractionRing.finrank_eq`：∀ (A : Type u_1) (K : Type u_2) (B : Type u_3
) (L : Type u_4) [inst : CommRing A] [inst_1 : CommRing K]   [inst_2 : CommRing 
B] [inst_3 : Co…
· 使用定理 `IntermediateField.LinearDisjoint.finrank_right_eq_finrank`：finrank_right
_eq_finrank [Module.Finite F B] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) : fin
rank B E = finrank F A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Let `K₁` and `K₂` be two number fields and assume that their different ideals (o
ver ℤ) are coprime.
Then, the absolute value of the discriminant of their compositum is equal to
`|discr K₁| ^ [K₂ : ℚ] * |discr K₂| ^ [K₁ : ℚ]`.
-/
theorem natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow (K₁ K₂ : IntermediateField ℚ L)
    (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal ℤ (𝓞 K₁)).map (algebraMap (𝓞 K₁) (𝓞 L)))
      ((differentIdeal ℤ (𝓞 K₂)).map (algebraMap (𝓞 K₂) (𝓞 L)))) :
    (discr L).natAbs =
      (discr K₁).natAbs ^ Module.finrank ℚ K₂ * (discr K₂).natAbs ^ Module.finrank ℚ K₁ := by
  let _ : Algebra (FractionRing (𝓞 K₁)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have h_main := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K₂ (𝓞 K₂) L (𝓞 L)
  rwa [differentIdeal_eq_map_differentIdeal ℤ (𝓞 L) (𝓞 K₂) (𝓞 K₁) (F₁ := K₂) (F₂ := K₁)
    (by rwa [linearDisjoint_comm]) (by rwa [sup_comm]) (by rwa [isCoprime_comm]),
    Ideal.absNorm_algebraMap, absNorm_differentIdeal K₁, h₁.finrank_right_eq_finrank h₂,
    ← IsFractionRing.finrank_eq (𝓞 K₁) K₁ (𝓞 L) L, h₁.finrank_left_eq_finrank h₂] at h_main

end

/-- Also see `not_dvd_discr_iff_forall_mem` for a slightly easier to use RHS. -/
/-
**NumberField.not_dvd_discr_iff_forall_liesOver** 是 Mathlib 中的一个引理，位于命名空间 `Numbe
rField`。
形式化陈述：not_dvd_discr_iff_forall_liesOver [IsIntegralClosure 𝒪 Int K] {p : Int} (h
p : Prime p) : ¬ p ∣ discr K ↔ forall (P : Ideal 𝒪) (_ : P.IsMaximal), P.LiesOve
r (.span {p}) -> Algebra.IsUnramifiedAt Int P
参数：hp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `IsIntegralClosure.isDedekindDomain`：IsIntegralClosure.isDedekindDomain [
IsDedekindDomain A] : IsDedekindDomain C
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `IsIntegralClosure.isFractionRing_of_finite_extension`：isFractionRing_of_
finite_extension [IsDomain A] [Algebra K L] [IsScalarTower A K L] [FiniteDimensi
onal K L] : IsFractionRing C L
· 使用定理 `IsIntegralClosure.finite`：IsIntegralClosure.finite [IsIntegrallyClosed A
] [IsNoetherianRing A] : Module.Finite A C
· 使用定理 `Ring.HasFiniteQuotients.instIsNoetherianRing`：∀ {R : Type u_1} [inst : C
ommRing R] [Ring.HasFiniteQuotients R], IsNoetherianRing R
· 使用定理 `Ring.HasFiniteQuotients.instInt`：Ring.HasFiniteQuotients ℤ
· 使用引理 `CharZero.of_module`：CharZero.of_module [Semiring R] [AddCommMonoidWithOn
e M] [CharZero M] [Module R M] : CharZero R
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `Algebra.IsSeparable.of_integral`：∀ (F : Type u_1) [inst : Field F] (K : 
Type u_2) [inst_1 : Ring K] [inst_2 : Algebra F K] [IsDomain K]   [Algebra.IsInt
egral F K] [CharZero …
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Also see `not_dvd_discr_iff_forall_mem` for a slightly easier to use RHS.
-/
lemma not_dvd_discr_iff_forall_liesOver [IsIntegralClosure 𝒪 ℤ K] {p : ℤ} (hp : Prime p) :
    ¬ p ∣ discr K ↔ ∀ (P : Ideal 𝒪) (_ : P.IsMaximal), P.LiesOver (.span {p}) →
      Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K 𝒪
  have := IsIntegralClosure.finite ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  simp_rw [← not_dvd_differentIdeal_iff]
  contrapose!
  constructor
  · intro h
    rw [← Int.dvd_natAbs, ← absNorm_differentIdeal K 𝒪] at h
    obtain ⟨P, hP, h₁, h₂⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm hp _ h
    exact ⟨P, hP, ⟨h₁.symm⟩, h₂⟩
  · rintro ⟨P, hP, hP', hP''⟩
    have := Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hP'')
    rw [absNorm_differentIdeal K, ← Ideal.natAbs_pow_inertiaDeg p,
      ← Int.natAbs_pow, Int.natAbs_dvd_natAbs] at this
    exact (dvd_pow_self _ (Ideal.inertiaDeg_pos ..).ne').trans this

/-- A prime `p` does not divide `discr K` if and only if `p` (as the ideal `span {p}`) is
unramified in the ring of integers `𝒪`.

Also see `not_dvd_discr_iff_forall_liesOver` and `not_dvd_discr_iff_forall_mem` for variants
whose RHS does not use `Algebra.IsUnramifiedIn`. -/
/-
**NumberField.not_dvd_discr_iff_isUnramifiedIn** 是 Mathlib 中的一个引理，位于命名空间 `Number
Field`。
形式化陈述：not_dvd_discr_iff_isUnramifiedIn [IsIntegralClosure 𝒪 Int K] {p : Int} (hp
 : Prime p) : ¬ p ∣ discr K ↔ Algebra.IsUnramifiedIn 𝒪 (Ideal.span {p})
参数：hp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `IsIntegralClosure.isDedekindDomain`：IsIntegralClosure.isDedekindDomain [
IsDedekindDomain A] : IsDedekindDomain C
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用引理 `CharZero.of_module`：CharZero.of_module [Semiring R] [AddCommMonoidWithOn
e M] [CharZero M] [Module R M] : CharZero R
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.not_dvd_discr_iff_forall_liesOver`：not_dvd_discr_iff_forall_
liesOver [IsIntegralClosure 𝒪 Int K] {p : Int} (hp : Prime p) : ¬ p ∣ discr K ↔ 
forall (P : Ideal 𝒪) (_ : P.IsMaxim…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain'`：isUnramifiedIn_i
ff_forall_of_isDedekindDomain' [IsDomain R] [IsDedekindDomain S] [Module.IsTorsi
onFree R S] {p : Ideal R} (hp : p != ⊥) : Is…
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0

--- 原说明 ---
A prime `p` does not divide `discr K` if and only if `p` (as the ideal `span {p}
`) is
unramified in the ring of integers `𝒪`.

Also see `not_dvd_discr_iff_forall_liesOver` and `not_dvd_discr_iff_forall_mem` 
for variants
whose RHS does not use `Algebra.IsUnramifiedIn`.
-/
lemma not_dvd_discr_iff_isUnramifiedIn [IsIntegralClosure 𝒪 ℤ K] {p : ℤ} (hp : Prime p) :
    ¬ p ∣ discr K ↔ Algebra.IsUnramifiedIn 𝒪 (Ideal.span {p}) := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  rw [not_dvd_discr_iff_forall_liesOver K 𝒪 hp]
  exact (Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain'
    (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)).symm

/-- Also see `not_dvd_discr_iff_forall_liesOver` for a slightly easier to prove RHS. -/
/-
**NumberField.not_dvd_discr_iff_forall_mem** 是 Mathlib 中的一个引理，位于命名空间 `NumberFiel
d`。
形式化陈述：not_dvd_discr_iff_forall_mem [IsIntegralClosure 𝒪 Int K] {p : Int} (hp : P
rime p) : ¬ p ∣ discr K ↔ forall (P : Ideal 𝒪) (_ : P.IsPrime), ↑p in P -> Algeb
ra.IsUnramifiedAt Int P
参数：hp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `IsIntegralClosure.isDedekindDomain`：IsIntegralClosure.isDedekindDomain [
IsDedekindDomain A] : IsDedekindDomain C
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用引理 `CharZero.of_module`：CharZero.of_module [Semiring R] [AddCommMonoidWithOn
e M] [CharZero M] [Module R M] : CharZero R
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.not_dvd_discr_iff_forall_liesOver`：not_dvd_discr_iff_forall_
liesOver [IsIntegralClosure 𝒪 Int K] {p : Int} (hp : Prime p) : ¬ p ∣ discr K ↔ 
forall (P : Ideal 𝒪) (_ : P.IsMaxim…
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Ideal.liesOver_span_iff`：Ideal.liesOver_span_iff [NoZeroDivisors R] [Rin
g.KrullDimLE 1 R] [Algebra R S] {P : Ideal S} {p : R} (hP : P != ⊤) (hp : Prime 
p) : P.LiesOv…
· 使用定理 `Ring.DimensionLEOne.instKrullDimLEOfNatNat`：∀ {R : Type u_4} [inst : Com
mRing R] [Ring.DimensionLEOne R], Ring.KrullDimLE 1 R
· 使用定理 `Ring.HasFiniteQuotients.instDimensionLEOne`：∀ {R : Type u_1} [inst : Com
mRing R] [Ring.HasFiniteQuotients R], Ring.DimensionLEOne R
· 使用定理 `Ring.HasFiniteQuotients.instInt`：Ring.HasFiniteQuotients ℤ
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `Ideal.mem_span_singleton_self`：mem_span_singleton_self (x : α) : x in sp
an ({x} : Set α)

--- 原说明 ---
Also see `not_dvd_discr_iff_forall_liesOver` for a slightly easier to prove RHS.
-/
lemma not_dvd_discr_iff_forall_mem [IsIntegralClosure 𝒪 ℤ K] {p : ℤ} (hp : Prime p) :
    ¬ p ∣ discr K ↔ ∀ (P : Ideal 𝒪) (_ : P.IsPrime), ↑p ∈ P →
      Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  rw [NumberField.not_dvd_discr_iff_forall_liesOver K 𝒪 hp]
  exact ⟨fun H P hP h ↦ H P (hP.isMaximal (by aesop))
    ((Ideal.liesOver_span_iff hP.ne_top hp).mpr h),
    fun H P _ h ↦ H P _ (h.1.le (Ideal.mem_span_singleton_self _))⟩

end NumberField

