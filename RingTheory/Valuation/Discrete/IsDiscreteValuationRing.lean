/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Valuations associated to discrete valuation rings

Given a discrete valuation ring `A` with field of fractions `K`, the maximal ideal of `A`
is a height-one prime, and the associated valuation `(maximalIdeal A).valuation K` is
a rank-one discrete valuation on `K`.

## Main Definitions

* `IsDiscreteValuationRing.maximalIdeal`: The maximal ideal of `A` (as an element of
  `HeightOneSpectrum A`).
* `IsDiscreteValuationRing.equivValuationSubring`: The ring isomorphism between a DVR and the
  unit ball in its field of fractions endowed with the adic valuation of the maximal ideal.

## Main Results

* `IsDiscreteValuationRing.isRankOneDiscrete`: Given a DVR `A` and a field `K` satisfying
  `IsFractionRing A K`, the valuation induced on `K` is discrete.
-/

@[expose] public section

namespace IsDiscreteValuationRing

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
  IsLocalRing MonoidWithZeroHom Multiplicative Subring Valuation

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- The maximal ideal of a discrete valuation ring. -/
/-
**IsDiscreteValuationRing.maximalIdeal** 是 Mathlib 中的一个定义，位于命名空间 `IsDiscreteValu
ationRing`。
形式化陈述：maximalIdeal : HeightOneSpectrum A where asIdeal
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R

--- 原说明 ---
The maximal ideal of a discrete valuation ring.
-/
def maximalIdeal : HeightOneSpectrum A where
  asIdeal := IsLocalRing.maximalIdeal A
  isPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)
  ne_bot := by simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using not_isField A
/-
**IsDiscreteValuationRing.isRankOneDiscrete** 是 Mathlib 中的一个实例，位于命名空间 `IsDiscret
eValuationRing`。
形式化陈述：isRankOneDiscrete : IsRankOneDiscrete ((maximalIdeal A).valuation K)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer`：valuati
on_exists_uniformizer : exists π : K, v.valuation K π = exp (-1 : Int)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.nontrivial_iff_exists_ne_one`：nontrivial_iff_exists_ne_one (H :
 Subgroup G) : Nontrivial H ↔ exists x in H, x != (1 : G)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `MonoidWithZeroHom.mem_valueGroup`：mem_valueGroup {b : Bˣ} (hb : b.1 in r
ange f) : b in valueGroup f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Units.mk0.congr_simp`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] (a a_1
 : G₀) (e_a : a = a_1) (ha : a ≠ 0), Units.mk0 a ha = Units.mk0 a_1 ⋯
· 使用定理 `not_eq_of_beq_eq_false`：∀ {α : Type u_1} [inst : BEq α] [ReflBEq α] {a b
 : α}, (a == b) = false → ¬a = b
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `Std.LawfulBEqOrd.equivBEq`：∀ {α : Type u} [inst : BEq α] [inst_1 : Ord α
] [Std.LawfulBEqOrd α] [Std.TransOrd α], EquivBEq α
· 使用定理 `Std.LawfulBCmp.toLawfulBEqCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : 
LT α} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   S
td.LawfulBEqCmp cmp
· 使用定理 `instLawfulBCmpCompare_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], 
Std.LawfulBCmp compare
· 使用定理 `Std.LawfulBCmp.toTransCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : LT α
} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   Std.T
ransCmp cmp
· 使用定理 `Valuation.IsRankOneDiscrete.mk'`：∀ {Γ : Type u_1} [inst : LinearOrderedC
ommGroupWithZero Γ] {R : Type u_2} [inst_1 : Ring R] (v : Valuation R Γ)   [IsCy
clic ↥(MonoidWithZero…
· 使用定理 `instIsCyclicUnitsWithZero`：∀ (G : Type u_4) [inst : Group G] [IsCyclic G
], IsCyclic (WithZero G)ˣ
· 使用定理 `instIsAddCyclicInt`：IsAddCyclic ℤ
-/
instance isRankOneDiscrete :
    IsRankOneDiscrete ((maximalIdeal A).valuation K) := by
  have : Nontrivial (valueGroup
      (.ofClass (valuation K (maximalIdeal A)))) := by
    let v := (maximalIdeal A).valuation K
    let π := valuation_exists_uniformizer K (maximalIdeal A) |>.choose
    have hπ : v π = ↑(ofAdd (-1 : ℤ)) :=
      valuation_exists_uniformizer K (maximalIdeal A) |>.choose_spec
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    use Units.mk0 (v π) (by simp [hπ])
    constructor
    · apply mem_valueGroup
      use π
      simp [v]
    · simpa [hπ] using not_eq_of_beq_eq_false rfl
  infer_instance

variable {A K}

open scoped WithZero
/-
**IsDiscreteValuationRing.exists_lift_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `IsDis
creteValuationRing`。
形式化陈述：exists_lift_of_le_one {x : K} (H : ((maximalIdeal A).valuation K) x <= (1 
: Intᵐ⁰)) : exists a : A, algebraMap A K a = x
参数：H : ((maximalIdeal A).valuation K) x <= (1 : Intᵐ⁰)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `IsDiscreteValuationRing.exists_irreducible`：exists_irreducible : exists 
ϖ : R, Irreducible ϖ
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`：eq_unit_mul_pow_irr
educible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ) : exists (n : Nat)
 (u : Rˣ), x = u * ϖ ^ n
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_mem_nonZeroDivisors`：mul_mem_nonZeroDivisors : a * b in M₀⁰ ↔ a in M
₀⁰ ∧ b in M₀⁰ where mp h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd`：intValua
tion_lt_one_iff_dvd (r : R) : v.intValuation r < 1 ↔ v.asIdeal ∣ Ideal.span {r}
· 使用定理 `dvd_of_eq`：dvd_of_eq (h : a = b) : a ∣ b
· 使用定理 `IsDiscreteValuationRing.irreducible_iff_uniformizer`：irreducible_iff_uni
formizer (ϖ : R) : Irreducible ϖ ↔ maximalIdeal R = Ideal.span {ϖ}
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero`：intValuation_ne
_zero (x : R) (hx : x != 0) : v.intValuation x != 0
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `zpow_le_one_iff_right_of_lt_one₀`：∀ {G₀ : Type u_3} [inst : GroupWithZer
o G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀} [ZeroLEOneClass G
₀]   {n : ℤ}, 0 < a → …
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 75 条，此处仅展示前 30 条）
-/
theorem exists_lift_of_le_one {x : K} (H : ((maximalIdeal A).valuation K) x ≤ (1 : ℤᵐ⁰)) :
    ∃ a : A, algebraMap A K a = x := by
  obtain ⟨π, hπ⟩ := exists_irreducible A
  obtain ⟨a, b, hb, h_frac⟩ := IsFractionRing.div_surjective A x
  by_cases ha : a = 0
  · rw [← h_frac]
    use 0
    rw [ha, map_zero, zero_div]
  · rw [← h_frac] at H
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
    obtain ⟨m, w, rfl⟩ := eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    replace hb := (mul_mem_nonZeroDivisors.mp hb).2
    rw [mul_comm (w : A) _, map_mul _ (u : A) _, map_mul _ _ (w : A), div_eq_mul_inv, mul_assoc,
      Valuation.map_mul, Integers.one_of_isUnit' u.isUnit (valuation_le_one _), one_mul,
      mul_inv, ← mul_assoc, Valuation.map_mul, map_mul, map_inv₀, map_inv₀,
      Integers.one_of_isUnit' w.isUnit (valuation_le_one _), inv_one, mul_one, ← div_eq_mul_inv,
      ← map_div₀, ← IsFractionRing.mk'_mk_eq_div hb,
      valuation_of_mk', map_pow, map_pow] at H
    have h_mn : m ≤ n := by
      have v_π_lt_one := (intValuation_lt_one_iff_dvd (maximalIdeal A) π).mpr
          (dvd_of_eq ((irreducible_iff_uniformizer _).mp hπ))
      have v_π_ne_zero : (maximalIdeal A).intValuation π ≠ 0 := intValuation_ne_zero _ _ hπ.ne_zero
      zify
      rw [← WithZero.coe_one, div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast, ← ofAdd_zero,
        ← zpow_neg, ← zpow_add₀ v_π_ne_zero, ← sub_eq_add_neg] at H
      rwa [← sub_nonneg, ← zpow_le_one_iff_right_of_lt_one₀ (zero_lt_iff.mpr v_π_ne_zero)
        v_π_lt_one]
    use u * π ^ (n - m) * w.2
    simp only [← h_frac, Units.inv_eq_val_inv, _root_.map_mul, _root_.map_pow, map_units_inv,
      mul_assoc, mul_div_assoc ((algebraMap A _) ↑u) _ _]
    congr 1
    rw [div_eq_mul_inv, mul_inv, mul_comm ((algebraMap A _) ↑w)⁻¹ _, ←
      mul_assoc _ _ ((algebraMap A _) ↑w)⁻¹]
    congr
    rw [pow_sub₀ _ _ h_mn]
    apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact hπ.ne_zero
/-
**IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid** 是 Mathlib 中的一个引理，位
于命名空间 `IsDiscreteValuationRing`。
形式化陈述：mker_valuation_eq_isUnitSubmonoid : MonoidHom.mker ((IsDiscreteValuationRi
ng.maximalIdeal A).valuation K) = (IsUnit.submonoid A).map (algebraMap A K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDiscreteValuationRing.exists_lift_of_le_one`：exists_lift_of_le_one {x 
: K} (H : ((maximalIdeal A).valuation K) x <= (1 : Intᵐ⁰)) : exists a : A, algeb
raMap A K a = x
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem`：valuatio
n_eq_one_iff_notMem {r : R} : v.valuation K (algebraMap R K r) = 1 ↔ r ∉ v.asIde
al
-/
lemma mker_valuation_eq_isUnitSubmonoid :
    MonoidHom.mker ((IsDiscreteValuationRing.maximalIdeal A).valuation K) =
    (IsUnit.submonoid A).map (algebraMap A K) := by
  ext a
  simp only [MonoidHom.mem_mker, Submonoid.mem_map]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨b, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
    rw [valuation_eq_one_iff_notMem] at h
    simp only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      not_not] at h
    use b, h
  · obtain ⟨x, h, rfl⟩ := h
    simpa [IsDiscreteValuationRing.maximalIdeal] using! h

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsDiscreteValuationRing.associated_of_valuation_eq** 是 Mathlib 中的一个定理，位于命名空间 `
IsDiscreteValuationRing`。
形式化陈述：associated_of_valuation_eq (x y : K) (h : ((maximalIdeal A).valuation K) x
 = ((maximalIdeal A).valuation K) y) : exists u : Aˣ, u • x = y
参数：x y : K；h : ((maximalIdeal A).valuation K) x = ((maximalIdeal A).valuation K)
 y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
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
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid`：mker_valuatio
n_eq_isUnitSubmonoid : MonoidHom.mker ((IsDiscreteValuationRing.maximalIdeal A).
valuation K) = (IsUnit.submonoid A).map (algebr…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
（共 50 条，此处仅展示前 30 条）
-/
theorem associated_of_valuation_eq (x y : K)
    (h : ((maximalIdeal A).valuation K) x =
    ((maximalIdeal A).valuation K) y) : ∃ u : Aˣ, u • x = y := by
  by_cases hx : x = 0
  · rw [eq_comm] at h
    simp_all
  by_cases hy : y = 0
  · simp_all
  have : (y / x) ∈ MonoidHom.mker (((maximalIdeal A).valuation K)) := by simp_all
  rw [mker_valuation_eq_isUnitSubmonoid] at this
  obtain ⟨u, h⟩ := this
  use IsUnit.unit h.1
  simp only [Units.smul_def, Algebra.smul_def, IsUnit.unit_spec, h.2]
  field_simp
/-
**IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring** 是 Mathlib 中的一个定理，
位于命名空间 `IsDiscreteValuationRing`。
形式化陈述：map_algebraMap_eq_valuationSubring : Subring.map (algebraMap A K) ⊤ = ((ma
ximalIdeal A).valuation K).valuationSubring.toSubring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.ext`：ext {S T : Subring R} (h : forall x, x in S ↔ x in T) : S =
 T
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subring.mem_map`：mem_map {f : R ->+* S} {s : Subring R} {y : S} : y in s
.map f ↔ exists x in s, f x = y
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_le_one`：valuation_le_one (r
 : R) : v.valuation K r <= 1
· 使用定理 `IsDiscreteValuationRing.exists_lift_of_le_one`：exists_lift_of_le_one {x 
: K} (H : ((maximalIdeal A).valuation K) x <= (1 : Intᵐ⁰)) : exists a : A, algeb
raMap A K a = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subring.mem_top`：mem_top (x : R) : x in (⊤ : Subring R)
-/
theorem map_algebraMap_eq_valuationSubring : Subring.map (algebraMap A K) ⊤ =
    ((maximalIdeal A).valuation K).valuationSubring.toSubring := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, _, rfl⟩ := Subring.mem_map.mp h
    apply valuation_le_one
  · obtain ⟨y, rfl⟩ := exists_lift_of_le_one h
    rw [Subring.mem_map]
    exact ⟨y, mem_top _, rfl⟩

/-- The ring isomorphism between a DVR `A` and the valuation subring of a field of fractions
  of `A` endowed with the adic valuation of the maximal ideal. -/
/-
**IsDiscreteValuationRing.equivValuationSubring** 是 Mathlib 中的一个定义，位于命名空间 `IsDis
creteValuationRing`。
形式化陈述：equivValuationSubring : A ≃+* ((maximalIdeal A).valuation K).valuationSubr
ing
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring`：map_algebraM
ap_eq_valuationSubring : Subring.map (algebraMap A K) ⊤ = ((maximalIdeal A).valu
ation K).valuationSubring.toSubring

--- 原说明 ---
The ring isomorphism between a DVR `A` and the valuation subring of a field of f
ractions
  of `A` endowed with the adic valuation of the maximal ideal.
-/
noncomputable def equivValuationSubring :
    A ≃+* ((maximalIdeal A).valuation K).valuationSubring :=
  (topEquiv.symm.trans (equivMapOfInjective ⊤ (algebraMap A K)
    (IsFractionRing.injective A _))).trans
      (RingEquiv.subringCongr map_algebraMap_eq_valuationSubring)
/-
**IsDiscreteValuationRing.intValuation_maximalIdeal** 是 Mathlib 中的一个引理，位于命名空间 `I
sDiscreteValuationRing`。
形式化陈述：intValuation_maximalIdeal (x : A) : (maximalIdeal A).intValuation x = (ENa
t.recTopCoe 0 (WithZero.coe <| Multiplicative.ofAdd <| Nat.cast · ) (addVal A x)
)⁻¹
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `AddValuation.map_zero`：AddValuation.map_zero : addValuationDef (0 : Rat_
[p]) = ⊤
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsDiscreteValuationRing.exists_irreducible`：exists_irreducible : exists 
ϖ : R, Irreducible ϖ
· 使用定理 `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`：eq_unit_mul_pow_irr
educible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ) : exists (n : Nat)
 (u : Rˣ), x = u * ϖ ^ n
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_singleton`：intValuation_
singleton {r : R} (hr : r != 0) (hv : v.asIdeal = Ideal.span {r}) : v.intValuati
on r = exp (-1 : Int)
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Irreducible.maximalIdeal_eq`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] [inst_2 : IsDiscreteValuationRing R] {ϖ : R},   Irreducible ϖ → Is
LocalRing.maximal…
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 37 条，此处仅展示前 30 条）
-/
lemma intValuation_maximalIdeal (x : A) :
    (maximalIdeal A).intValuation x =
      (ENat.recTopCoe 0 (WithZero.coe <| Multiplicative.ofAdd <| Nat.cast · ) (addVal A x))⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  have : (maximalIdeal A).intValuation ↑u = 1 := by simp [maximalIdeal]
  simp [(maximalIdeal A).intValuation_singleton hϖ.ne_zero
    hϖ.maximalIdeal_eq, hϖ, this, WithZero.exp_eq_coe_ofAdd (n : ℤ)]

end IsDiscreteValuationRing

end

