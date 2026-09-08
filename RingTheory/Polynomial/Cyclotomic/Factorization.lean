/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Factorization of cyclotomic polynomials over finite fields

We compute the degree of the irreducible factors of the `n`-th cyclotomic polynomial over a finite
field of characteristic `p`, where `p` and `n` are coprime.

## Main results

* `Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible` : Let `K` be a finite field of cardinality
  `p ^ f` and let `P` be an irreducible factor of the `n`-th cyclotomic polynomial over `K`, where
  `p` and `n` are coprime. Then the degree of `P` is the multiplicative order of `p ^ f` modulo `n`.

-/

public section

namespace Polynomial

variable {K : Type*} [Field K] [Fintype K] {p f n : ℕ} {P : K[X]}
  (hK : Fintype.card K = p ^ f) (hn : p.Coprime n)

open ZMod AdjoinRoot FiniteField Multiset

include hK

/-
**Polynomial.f_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma f_ne_zero : f ≠ 0 := fun h0 ↦ not_subsingleton K <|
    Fintype.card_le_one_iff_subsingleton.mp <| by simpa [h0] using hK.le

variable [hp : Fact p.Prime]

/-- The degree of an irreducible monic factor of the `n`-th cyclotomic polynomial over a finite
  field. This is a special case of `natDegree_of_dvd_cyclotomic_of_irreducible` below. -/
/-
**Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible_of_monic** 是 Mathlib 中的一
个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The degree of an irreducible monic factor of the `n`-th cyclotomic polynomial ov
er a finite
  field. This is a special case of `natDegree_of_dvd_cyclotomic_of_irreducible` 
below.
-/
private theorem natDegree_of_dvd_cyclotomic_of_irreducible_of_monic (hP : P ∣ cyclotomic n K)
    (hPirr : Irreducible P) (hPmo : P.Monic) :
    P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f)) := by
  have : Fact (Irreducible P) := ⟨hPirr⟩
  have := hPmo.finite_adjoinRoot
  have : Finite (AdjoinRoot P) := Module.finite_of_finite K
  have hζ : IsPrimitiveRoot (root P) n := by
    have : NeZero (n : AdjoinRoot P) := by
      suffices NeZero (n : K) by
        simpa using! NeZero.of_injective (algebraMap K (AdjoinRoot P)).injective
      have := charP_of_card_eq_prime_pow hK
      exact ⟨fun h0 ↦ Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp.out, dvd_pow_self p (f_ne_zero hK), (CharP.cast_eq_zero_iff K p n).mp h0⟩
          (hn.pow_left f)⟩
    simpa [← isRoot_cyclotomic_iff] using! (isRoot_root P).dvd
      (by simpa using! map_dvd (algebraMap K (AdjoinRoot P)) hP)
  let pB := powerBasis hPirr.ne_zero
  rw [← powerBasis_dim hPirr.ne_zero, ← pB.finrank, ← orderOf_frobeniusAlgEquivOfAlgebraic]
  have hζ' := isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, pos_of_ne_zero (fun h0 ↦ by simp [h0, hp.out.ne_one] at hn),
      hζ.pow_eq_one⟩
  refine dvd_antisymm
    (orderOf_dvd_iff_pow_eq_one.mpr <| AlgEquiv.coe_toAlgHom_injective <| pB.algHom_ext ?_)
    (orderOf_dvd_iff_pow_eq_one.mpr <| Units.ext ?_)
  · simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_pow, AlgEquiv.one_apply,
      coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK]
    nth_rewrite 2 [← pow_one pB.gen]
    rw [powerBasis_gen hPirr.ne_zero, hζ'.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf,
      ← natCast_eq_natCast_iff]
    simpa only [Nat.cast_pow, Nat.cast_one, coe_unitOfCoprime, Units.val_one,
      Units.val_pow_eq_pow_val] using! Units.val_inj.mpr <| pow_orderOf_eq_one
      (unitOfCoprime _ (hn.pow_left f))
  · let φ := frobeniusAlgEquivOfAlgebraic K (AdjoinRoot P)
    have : (φ ^ orderOf φ) (root P) = root P := by simp [pow_orderOf_eq_one φ]
    simp only [AlgEquiv.coe_pow, φ, coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK] at this
    rw [Units.val_one, ← Nat.cast_one, Units.val_pow_eq_pow_val, coe_unitOfCoprime,
      ← Nat.cast_pow, natCast_eq_natCast_iff, hζ.eq_orderOf, ← hζ'.pow_eq_pow_iff_modEq, this,
      pow_one]

/-- Let `K` be a finite field of cardinality `p ^ f` and let `P` be an irreducible factor of the
  `n`-th cyclotomic polynomial over `K`, where `p` and `n` are coprime. Then the degree of `P` is
  the multiplicative order of `p ^ f` modulo `n`. -/
/-
**Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
形式化陈述：natDegree_of_dvd_cyclotomic_of_irreducible (hP : P ∣ cyclotomic n K) (hPir
r : Irreducible P) : P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f))
参数：hP : P ∣ cyclotomic n K；hPirr : Irreducible P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.pow_left`：∀ {m k : ℕ} (n : ℕ), m.Coprime k → (m ^ n).Coprime
 k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Let `K` be a finite field of cardinality `p ^ f` and let `P` be an irreducible f
actor of the
  `n`-th cyclotomic polynomial over `K`, where `p` and `n` are coprime. Then the
 degree of `P` is
  the multiplicative order of `p ^ f` modulo `n`.
-/
theorem natDegree_of_dvd_cyclotomic_of_irreducible (hP : P ∣ cyclotomic n K)
    (hPirr : Irreducible P) : P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f)) := by
  obtain ⟨A, hA⟩ := hP
  have hQ : P * C P.leadingCoeff⁻¹ ∣ cyclotomic n K := by
    refine ⟨A * C P.leadingCoeff, ?_⟩
    calc
      _ = P * A := hA
      _ = P * (C P.leadingCoeff⁻¹ * C P.leadingCoeff) * A := by
        simp [← C_mul, leadingCoeff_ne_zero.mpr hPirr.ne_zero]
      _ = _ := by ring
  simpa [← natDegree_mul_leadingCoeff_self_inv P] using
    natDegree_of_dvd_cyclotomic_of_irreducible_of_monic hK hn hQ
    (irreducible_mul_leadingCoeff_inv.mpr hPirr) (monic_mul_leadingCoeff_inv hPirr.ne_zero)

open UniqueFactorizationMonoid in
/-- Let `K` be a finite field of cardinality `p ^ f` and let `P` be a factor of the `n`-th
  cyclotomic polynomial over `K`, where `p` and `n` are coprime. If the degree of `P` is
  the multiplicative order of `p ^ f` modulo `n` then `P` is irreducible. -/
/-
**Polynomial.irreducible_of_dvd_cyclotomic_of_natDegree** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
形式化陈述：irreducible_of_dvd_cyclotomic_of_natDegree (hP : P ∣ cyclotomic n K) (hPde
g : P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f))) : Irreducible P
参数：hP : P ∣ cyclotomic n K；hPdeg : P.natDegree = orderOf (unitOfCoprime _ (hn.po
w_left f))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.pow_left`：∀ {m k : ℕ} (n : ℕ), m.Coprime k → (m ^ n).Coprime
 k
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `Polynomial.cyclotomic_ne_zero`：cyclotomic_ne_zero (n : Nat) (R : Type*) 
[Ring R] [Nontrivial R] : cyclotomic n R != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `UniqueFactorizationMonoid.exists_mem_normalizedFactors`：exists_mem_norma
lizedFactors {x : α} (hx : x != 0) (h : ¬IsUnit x) : exists p, p in normalizedFa
ctors x
· 使用引理 `Polynomial.not_isUnit_of_natDegree_pos`：not_isUnit_of_natDegree_pos (p :
 R[X]) (hpl : 0 < p.natDegree) : ¬ IsUnit p
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orderOf_eq_zero_iff`：orderOf_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder
 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ
· 使用定理 `Associated.irreducible`：∀ {M : Type u_1} [inst : Monoid M] {p q : M}, As
sociated p q → Irreducible p → Irreducible q
· 使用引理 `Polynomial.associated_of_dvd_of_natDegree_le`：associated_of_dvd_of_natDe
gree_le {K} [Field K] {p q : K[X]} (hpq : p ∣ q) (hq : q != 0) (h₁ : q.natDegree
 <= p.natDegree) : Associated p q
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible`：natDegree_of_dvd_
cyclotomic_of_irreducible (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) : P.
natDegree = orderOf (unitOfCoprime _ (hn.po…
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
· 使用定理 `UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
`：dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x != 0) (hy : y
 != 0) : x ∣ y ↔ normalizedFactors x <= normalizedFactors y
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Let `K` be a finite field of cardinality `p ^ f` and let `P` be a factor of the 
`n`-th
  cyclotomic polynomial over `K`, where `p` and `n` are coprime. If the degree o
f `P` is
  the multiplicative order of `p ^ f` modulo `n` then `P` is irreducible.
-/
theorem irreducible_of_dvd_cyclotomic_of_natDegree (hP : P ∣ cyclotomic n K)
    (hPdeg : P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f))) : Irreducible P := by
  classical
  have hP0 : P ≠ 0 := ne_zero_of_dvd_ne_zero (cyclotomic_ne_zero n K) hP
  obtain ⟨Q, HQ⟩ := exists_mem_normalizedFactors hP0 <| not_isUnit_of_natDegree_pos _ <|
    pos_of_ne_zero <| fun h ↦ orderOf_eq_zero_iff.mp (h ▸ hPdeg.symm) <| isOfFinOrder_of_finite ..
  refine (associated_of_dvd_of_natDegree_le (dvd_of_mem_normalizedFactors HQ) hP0 ?_).irreducible
    (irreducible_of_normalized_factor Q HQ)
  rw [hPdeg, ← natDegree_of_dvd_cyclotomic_of_irreducible hK hn ?_
    (irreducible_of_normalized_factor Q HQ)]
  exact dvd_of_mem_normalizedFactors <| mem_of_le
    ((dvd_iff_normalizedFactors_le_normalizedFactors hP0 (cyclotomic_ne_zero n K)).mp hP) HQ

omit hK in
/-- Let `P` be a factor of the `n`-th cyclotomic polynomial over `ZMod p`, where `p` does not divide
  `n`. If the degree of `P` is the multiplicative order of `p` modulo `n` then `P` is
  irreducible. -/
/-
**Polynomial._root_.ZMod.irreducible_of_dvd_cyclotomic_of_natDegree** 是 Mathlib 
中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `P` be a factor of the `n`-th cyclotomic polynomial over `ZMod p`, where `p`
 does not divide
  `n`. If the degree of `P` is the multiplicative order of `p` modulo `n` then `
P` is
  irreducible.
-/
theorem _root_.ZMod.irreducible_of_dvd_cyclotomic_of_natDegree {P : (ZMod p)[X]} (hpn : ¬p ∣ n)
    (hP : P ∣ cyclotomic n (ZMod p))
    (hPdeg : P.natDegree = orderOf (unitOfCoprime _ (hp.1.coprime_iff_not_dvd.mpr hpn))) :
    Irreducible P :=
  Polynomial.irreducible_of_dvd_cyclotomic_of_natDegree (f := 1) (p := p) (by simp)
    (by simpa using hp.1.coprime_iff_not_dvd.mpr hpn) hP (by simpa)

open UniqueFactorizationMonoid Nat

variable [DecidableEq K]
/-
**Polynomial.natDegree_of_mem_normalizedFactors_cyclotomic** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
形式化陈述：natDegree_of_mem_normalizedFactors_cyclotomic (hP : P in normalizedFactors
 (cyclotomic n K)) : P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f))
参数：hP : P in normalizedFactors (cyclotomic n K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible`：natDegree_of_dvd_
cyclotomic_of_irreducible (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) : P.
natDegree = orderOf (unitOfCoprime _ (hn.po…
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
-/
theorem natDegree_of_mem_normalizedFactors_cyclotomic
    (hP : P ∈ normalizedFactors (cyclotomic n K)) :
    P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f)) :=
  natDegree_of_dvd_cyclotomic_of_irreducible hK hn (dvd_of_mem_normalizedFactors hP)
    (irreducible_of_normalized_factor P hP)

/-- Let `K` be a finite field of cardinality `p ^ f` and let `P` be an irreducible factor of the
  `n`-th cyclotomic polynomial over `K`, where `p` and `n` are coprime. This result computes the
  number of distinct irreducible factors of `cyclotomic n K`. -/
/-
**Polynomial.normalizedFactors_cyclotomic_card** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：normalizedFactors_cyclotomic_card : (normalizedFactors (cyclotomic n K)).t
oFinset.card = φ n / orderOf (unitOfCoprime _ (hn.pow_left f))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `Polynomial.cyclotomic_ne_zero`：cyclotomic_ne_zero (n : Nat) (R : Type*) 
[Ring R] [Nontrivial R] : cyclotomic n R != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Nat.Coprime.pow_left`：∀ {m k : ℕ} (n : ℕ), m.Coprime k → (m ^ n).Coprime
 k
· 使用定理 `Polynomial.natDegree_of_mem_normalizedFactors_cyclotomic`：natDegree_of_m
em_normalizedFactors_cyclotomic (hP : P in normalizedFactors (cyclotomic n K)) :
 P.natDegree = orderOf (unitOfCoprime _ (hn.po…
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `Polynomial.degree_eq_degree_of_associated`：degree_eq_degree_of_associate
d (h : Associated p q) : degree p = degree q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.natDegree_multiset_prod`：natDegree_multiset_prod (h : (0 : R[
X]) ∉ t) : natDegree t.prod = (t.map natDegree).sum
· 使用定理 `UniqueFactorizationMonoid.zero_notMem_normalizedFactors`：zero_notMem_nor
malizedFactors (x : α) : (0 : α) ∉ normalizedFactors x
· 使用定理 `Polynomial.natDegree_cyclotomic`：natDegree_cyclotomic (n : Nat) (R : Typ
e*) [Ring R] [Nontrivial R] : (cyclotomic n R).natDegree = Nat.totient n
· 使用定理 `Nat.mul_div_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用引理 `orderOf_pos`：orderOf_pos (x : G) : 0 < orderOf x
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ
· 使用定理 `Multiset.toFinset_card_of_nodup`：Multiset.toFinset_card_of_nodup {m : Mu
ltiset α} (h : m.Nodup) : #m.toFinset = Multiset.card m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
Let `K` be a finite field of cardinality `p ^ f` and let `P` be an irreducible f
actor of the
  `n`-th cyclotomic polynomial over `K`, where `p` and `n` are coprime. This res
ult computes the
  number of distinct irreducible factors of `cyclotomic n K`.
-/
theorem normalizedFactors_cyclotomic_card : (normalizedFactors (cyclotomic n K)).toFinset.card =
    φ n / orderOf (unitOfCoprime _ (hn.pow_left f)) := by
  have h := prod_normalizedFactors (cyclotomic_ne_zero n K)
  have : ∀ P ∈ normalizedFactors (cyclotomic n K),
      P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f)) := fun P hP ↦
    natDegree_of_mem_normalizedFactors_cyclotomic hK hn hP
  have H := natDegree_eq_of_degree_eq <| degree_eq_degree_of_associated h
  rw [natDegree_cyclotomic, natDegree_multiset_prod _ (zero_notMem_normalizedFactors _),
    map_congr rfl this] at H
  simp only [map_const', sum_replicate, smul_eq_mul] at H
  rw [← H, mul_div_left _ (orderOf_pos _), toFinset_card_of_nodup]
  refine nodup_iff_count_le_one.mpr (fun P ↦ ?_)
  by_contra! H
  have : NeZero (n : K) := by
    refine ⟨fun H ↦ ?_⟩
    have := charP_of_card_eq_prime_pow hK
    exact hp.out.coprime_iff_not_dvd.mp ((coprime_pow_left_iff
      (pos_of_ne_zero <| f_ne_zero hK) _ _).mp (hn.pow_left f))
        ((CharP.cast_eq_zero_iff K p _).mp H)
  have hP : P ∈ normalizedFactors (cyclotomic n K) := count_pos.mp (by lia)
  refine (prime_of_normalized_factor _ hP).not_isUnit (squarefree_cyclotomic n K P ?_)
  have : {P, P} ≤ normalizedFactors (cyclotomic n K) := by
    refine le_iff_count.mpr (fun Q ↦ ?_)
    by_cases hQ : Q = P
    · simp only [hQ, insert_eq_cons, count_cons_self, nodup_singleton, mem_singleton,
        count_eq_one_of_mem, reduceAdd]
      lia
    · simp [hQ]
  have := prod_dvd_prod_of_le this
  simp only [insert_eq_cons, prod_cons, prod_singleton] at this
  exact this.trans h.dvd

end Polynomial

