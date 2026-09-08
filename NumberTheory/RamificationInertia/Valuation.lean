/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Order.Hom.Units
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.RingTheory.DedekindDomain.AdicValuation


/-!
# Ramification theory for valuations

- `A` is a Dedekind domain with field of fractions `K`.
- `B` is a Dedekind domain with field of fractions `L`.
- `L` is a field extension of `K`.
- `v` is a height one prime ideal of `A`.
- `w` is a height one prime ideal of `B` lying over `v`.

This file establishes the relationship between the adic valuation on `K` associated to `v` and the
adic valuation on `L` associated to `w`, in terms of the ramification index.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open WithZero Ideal.IsDedekindDomain Valuation.IsRankOneDiscrete

section AKLB

variable {A K : Type*} (L : Type*) {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_liesOver** 是 Mathlib 中的一个定理，位于
命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_liesOver (x : A) : v.intValuation x ^ (v.asIdeal.ramification
Idx' w.asIdeal) = w.intValuation (algebraMap A B x)
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver`：∀ {R : Type
 u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S
] [IsDedekindDomain S]   [IsDomain R] [Module.IsT…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity`
：intValuation_eq_exp_neg_multiplicity {r : R} (hr : r != 0) : v.intValuation r =
 exp (-multiplicity v.asIdeal (Ideal.span {r}) : Int)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `WithZero.exp_neg`：∀ {G : Type u_5} [inst : AddGroup G] (a : G), WithZero
.exp (-a) = (WithZero.exp a)⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `WithZero.exp_nsmul`：∀ {M : Type u_4} [inst : AddMonoid M] (n : ℕ) (a : M
), WithZero.exp (n • a) = WithZero.exp a ^ n
（共 44 条，此处仅展示前 30 条）
-/
theorem intValuation_liesOver (x : A) :
    v.intValuation x ^ (v.asIdeal.ramificationIdx' w.asIdeal) =
      w.intValuation (algebraMap A B x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot]
  rw [intValuation_eq_exp_neg_multiplicity v hx, intValuation_eq_exp_neg_multiplicity w (by simpa),
    ← Set.image_singleton, ← Ideal.map_span, exp_neg, exp_neg, inv_pow, ← exp_nsmul,
    Int.nsmul_eq_mul, inv_inj, exp_inj, ← Nat.cast_mul, Nat.cast_inj]
  refine multiplicity_eq_of_emultiplicity_eq_some ?_ |>.symm
  replace hx : Ideal.span {x} ≠ ⊥ := by simp [hx]
  rw [emultiplicity_map_eq_ramificationIdx'_mul hx v.irreducible w.irreducible w.ne_bot,
    Nat.cast_mul, (FiniteMultiplicity.of_prime_left v.prime hx).emultiplicity_eq_multiplicity]
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_liesOver** 是 Mathlib 中的一个定理，位于命名空
间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_liesOver (x : K) : v.valuation K x ^ v.asIdeal.ramificationIdx' 
w.asIdeal = w.valuation L (algebraMap K L x)
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_liesOver`：intValuation_l
iesOver (x : A) : v.intValuation x ^ (v.asIdeal.ramificationIdx' w.asIdeal) = w.
intValuation (algebraMap A B x)
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem valuation_liesOver (x : K) :
    v.valuation K x ^ v.asIdeal.ramificationIdx' w.asIdeal =
      w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation_of_algebraMap, div_pow, ← IsScalarTower.algebraMap_apply A K L,
    IsScalarTower.algebraMap_apply A B L, intValuation_liesOver v w]

variable (K)
/-
**IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver** 是 M
athlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：uniformContinuous_algebraMap_liesOver : UniformContinuous (algebraMap (Wit
hVal (v.valuation K)) (WithVal (w.valuation L)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_of_continuousAt_zero`：∀ {α : Type u_1} {β : Type u_2} 
[inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom : Type 
u_3}   [inst_3 : UniformSpac…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `IsValuativeTopology.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 0).HasBa
sis (fun _ => True) fun γ : (ValueGroupWithZero R)ˣ => { x | valuation R x < γ }
· 使用定理 `WithVal.instIsValuativeTopology`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst 
: LinearOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀),   I
sValuativeTopology (W…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.IsRankOneDiscrete.mk'`：∀ {Γ : Type u_1} [inst : LinearOrderedC
ommGroupWithZero Γ] {R : Type u_2} [inst_1 : Ring R] (v : Valuation R Γ)   [IsCy
clic ↥(MonoidWithZero…
· 使用定理 `instIsCyclicUnitsWithZero`：∀ (G : Type u_4) [inst : Group G] [IsCyclic G
], IsCyclic (WithZero G)ˣ
· 使用定理 `instIsAddCyclicInt`：IsAddCyclic ℤ
· 使用定理 `Valuation.instNontrivialSubtypeUnitsMemSubgroupValueGroupOfClassOfIsNont
rivial`：∀ {R : Type u_3} [inst : Ring R] {Γ₀ : Type u_7} [inst_1 : LinearOrdered
CommGroupWithZero Γ₀] {v : Valuation R Γ₀}   [hv : v.IsNontrivial], …
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.instIsNontrivialWithZeroMultiplicativ
eIntValuation`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R
] (K : Type u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
· 使用定理 `WithVal.instCompatibleValuation`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst 
: LinearOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀),   (
WithVal.valuation v).…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
· 使用定理 `EmbeddingLike.map_eq_zero_iff`：∀ {F : Type u_1} {M : Type u_4} {N : Type
 u_5} [inst : Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [EmbeddingLik
e F M N] [ZeroHomCl…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 60 条，此处仅展示前 30 条）
-/
theorem uniformContinuous_algebraMap_liesOver :
    UniformContinuous (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero _)]
  intro γL _
  /-
  `ValueGroup₀ (w.valuation L)` <-------->  `ℤᵐ⁰` <--------> `ValueGroup₀ (v.valuation K)`
            ^                                                         ^
            |                                                         |
            |                                                         |
            v                                                         v
  `ValueGroup₀ (WithVal.valuation _)`             `ValueGroup₀ (WithVal.valuation _)`
            ^                                                         ^
            |                                                         |
            |                                                         |
            v                                                         v
  `γL : ValuativeRel.ValueGroupWithZero Lʷ`       `γK: ValuativeRel.ValueGroupWithZero Kᵛ`
  -/
  let e := v.asIdeal.ramificationIdx' w.asIdeal
  -- push `γL` to `ℤᵐ⁰`
  let σL := WithVal.valueGroupOrderIso₀ (w.valuation L)
  let σw := valueGroup₀_equiv_withZeroMulInt (w.valuation L)
  let σwV := ValuativeRel.ValueGroupWithZero.orderMonoidIso (WithVal.valuation (w.valuation L))
  let m : ℤᵐ⁰ := σw (σL (σwV γL))
  -- `ℤᵐ⁰` values in `K` exponentiate by `e` in `L` so take the `e`th root and pull back to `γK`
  let σvV := ValuativeRel.ValueGroupWithZero.orderMonoidIso (WithVal.valuation (v.valuation K))
  let σv := valueGroup₀_equiv_withZeroMulInt (v.valuation K)
  let σK := WithVal.valueGroupOrderIso₀ (v.valuation K)
  let γK := σvV.symm (σK.symm (σv.symm (exp (m.log / e))))
  have hγK : γK ≠ 0 := by simp [γK, EmbeddingLike.map_eq_zero_iff (f := σK.symm)]
  use .mk0 _ hγK
  simp only [Units.val_mk0, Set.mem_ofPred_eq, true_and]
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx₀; · simp
  rw [σvV.lt_symm_apply, σK.lt_symm_apply, σv.lt_symm_apply,
    ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀,
    ← Valuation.restrict_def, WithVal.valueGroupOrderIso₀_restrict,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (v.valuation_surjective K),
    ← log_lt_log (by simp_all) (by simp)] at hx
  rw [← σwV.strictMono.lt_iff_lt, ← σL.strictMono.lt_iff_lt,
    ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀, ← Valuation.restrict_def,
    WithVal.valueGroupOrderIso₀_restrict, ← σw.strictMono.lt_iff_lt,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (w.valuation_surjective L),
    WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply, ← valuation_liesOver L v,
    ← log_lt_log (by simp_all) (by simp [EmbeddingLike.map_eq_zero_iff (f := σwV)]), log_pow,
    nsmul_eq_mul, mul_comm]
  exact Int.mul_lt_of_lt_ediv
    (mod_cast pos_of_ne_zero (ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)) hx

end AKLB

end IsDedekindDomain.HeightOneSpectrum

