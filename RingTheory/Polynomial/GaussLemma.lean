/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.Content

/-!
# Gauss's Lemma

Gauss's Lemma is one of a few results pertaining to irreducibility of primitive polynomials.

## Main Results

- `IsIntegrallyClosed.eq_map_mul_C_of_dvd`: if `R` is integrally closed, `K = Frac(R)` and
  `g : K[X]` divides a monic polynomial with coefficients in `R`, then `g * (C g.leadingCoeff⁻¹)`
  has coefficients in `R`
- `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`:
  A monic polynomial over an integrally closed domain is irreducible iff it is irreducible in a
  fraction field
- `isIntegrallyClosed_iff'`:
  Integrally closed domains are precisely the domains for in which Gauss's lemma holds
  for monic polynomials
- `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`:
  A primitive polynomial over a GCD domain is irreducible iff it is irreducible in a fraction field
- `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`:
  A primitive polynomial over `ℤ` is irreducible iff it is irreducible over `ℚ`.
- `Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`:
  Two primitive polynomials over a GCD domain divide each other iff they do in a fraction field.
- `Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast`:
  Two primitive polynomials over `ℤ` divide each other if they do in `ℚ`.

-/

public section


open scoped nonZeroDivisors Polynomial

variable {R : Type*} [CommRing R]

section IsIntegrallyClosed

open Polynomial

open integralClosure

open IsIntegrallyClosed

variable (K : Type*) [Field K] [Algebra R K]

/-
**integralClosure.mem_lifts_of_monic_of_dvd_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integralClosure.mem_lifts_of_monic_of_dvd_map {f : R[X]} (hf : f.Monic) {g
 : K[X]} (hg : g.Monic) (hd : g ∣ f.map (algebraMap R K)) : g in lifts (algebraM
ap (integralClosure R K) K)
参数：hf : f.Monic；hg : g.Monic；hd : g ∣ f.map (algebraMap R K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.mem_lift_of_roots_mem_range`：∀ {R : Type u_1} [inst : 
CommRing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits →     f.Monic →
 ∀ {S : Type u_4} [inst_2 : Ring S]…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Subalgebra.range_algebraMap`：range_algebraMap {R A : Type*} [CommRing R]
 [CommRing A] [Algebra R A] (S : Subalgebra R A) : (algebraMap S A).range = S.to
Subring
· 使用定理 `roots_mem_integralClosure`：roots_mem_integralClosure {f : R[X]} (hf : f.
Monic) {a : S} (ha : a in f.aroots S) : a in integralClosure R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots_def`：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain 
S] [Algebra T S] : p.aroots S = (p.map (algebraMap T S)).roots
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Polynomial.SplittingField.instIsScalarTower`：∀ {K : Type u_2} [inst : Fi
eld K] (f : Polynomial K) {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Alg
ebra R K],   IsScalarTower R K f.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
· 使用定理 `Polynomial.roots.le_of_dvd`：∀ {R : Type u} [inst : CommRing R] [inst_1 :
 IsDomain R] {p q : Polynomial R}, q ≠ 0 → p ∣ q → p.roots ≤ q.roots
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.map_dvd`：map_dvd (f : R ->+* S) {x y : R[X]} : x ∣ y -> x.map
 f ∣ y.map f
· 使用定理 `Polynomial.lifts_iff_coeff_lifts`：lifts_iff_coeff_lifts (p : S[X]) : p i
n lifts f ↔ forall n : Nat, p.coeff n in Set.range f
· 使用定理 `RingHom.coe_range`：coe_range : (f.range : Set S) = Set.range f
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Polynomial.eval₂_at_apply`：eval₂_at_apply {S : Type*} [Semiring S] (f : 
R ->+* S) (r : R) : p.eval₂ f (f r) = f (p.eval r)
（共 32 条，此处仅展示前 30 条）
-/
theorem integralClosure.mem_lifts_of_monic_of_dvd_map {f : R[X]} (hf : f.Monic) {g : K[X]}
    (hg : g.Monic) (hd : g ∣ f.map (algebraMap R K)) :
    g ∈ lifts (algebraMap (integralClosure R K) K) := by
  have := (SplittingField.splits g).mem_lift_of_roots_mem_range (hg.map _)
    (algebraMap (integralClosure R g.SplittingField) g.SplittingField)
     fun a ha =>
      (SetLike.ext_iff.mp (integralClosure R g.SplittingField).range_algebraMap _).mpr <|
        roots_mem_integralClosure hf ?_
  · rw [lifts_iff_coeff_lifts, ← RingHom.coe_range, Subalgebra.range_algebraMap] at this
    refine (lifts_iff_coeff_lifts _).2 fun n => ?_
    rw [← RingHom.coe_range, Subalgebra.range_algebraMap]
    obtain ⟨p, hp, he⟩ := SetLike.mem_coe.mp (this n); use p, hp
    rw [IsScalarTower.algebraMap_eq R K, coeff_map, ← eval₂_map, eval₂_at_apply] at he
    rw [eval₂_eq_eval_map]; apply (injective_iff_map_eq_zero _).1 _ _ he
    apply RingHom.injective
  rw [aroots_def, IsScalarTower.algebraMap_eq R K _, ← map_map]
  refine Multiset.mem_of_le (roots.le_of_dvd ((hf.map _).map _).ne_zero ?_) ha
  exact map_dvd (algebraMap K g.SplittingField) hd

variable [IsFractionRing R K]

/-- If `K = Frac(R)` and `g : K[X]` divides a monic polynomial with coefficients in `R`, then
`g * (C g.leadingCoeff⁻¹)` has coefficients in `R` -/
/-
**IsIntegrallyClosed.eq_map_mul_C_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegrallyClosed.eq_map_mul_C_of_dvd [IsIntegrallyClosed R] {f : R[X]} (
hf : f.Monic) {g : K[X]} (hg : g ∣ f.map (algebraMap R K)) : exists g' : R[X], g
'.map (algebraMap R K) * (C <| leadingCoeff g) = g
参数：hf : f.Monic；hg : g ∣ f.map (algebraMap R K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associated.dvd_iff_dvd_left`：Associated.dvd_iff_dvd_left [Monoid M] {a b
 c : M} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c
· 使用定理 `associated_mul_isUnit_left_iff`：associated_mul_isUnit_left_iff {N : Type
*} [Monoid N] {a u b : N} (hu : IsUnit u) : Associated (a * u) b ↔ Associated a 
b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Associated.refl`：∀ {M : Type u_1} [inst : Monoid M] (x : M), Associated 
x x
· 使用定理 `IsIntegrallyClosed.integralClosure_eq_bot`：integralClosure_eq_bot [IsInt
egrallyClosed R] : integralClosure R K = ⊥
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_lifts`：mem_lifts (p : S[X]) : p in lifts f ↔ exists q : R
[X], map f q = p
· 使用定理 `integralClosure.mem_lifts_of_monic_of_dvd_map`：integralClosure.mem_lifts
_of_monic_of_dvd_map {f : R[X]} (hf : f.Monic) {g : K[X]} (hg : g.Monic) (hd : g
 ∣ f.map (algebraMap R K)) : g in l…
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `K = Frac(R)` and `g : K[X]` divides a monic polynomial with coefficients in 
`R`, then
`g * (C g.leadingCoeff⁻¹)` has coefficients in `R`
-/
theorem IsIntegrallyClosed.eq_map_mul_C_of_dvd [IsIntegrallyClosed R] {f : R[X]} (hf : f.Monic)
    {g : K[X]} (hg : g ∣ f.map (algebraMap R K)) :
    ∃ g' : R[X], g'.map (algebraMap R K) * (C <| leadingCoeff g) = g := by
  have g_ne_0 : g ≠ 0 := ne_zero_of_dvd_ne_zero (Monic.ne_zero <| hf.map (algebraMap R K)) hg
  suffices lem : ∃ g' : R[X], g'.map (algebraMap R K) = g * C g.leadingCoeff⁻¹ by
    obtain ⟨g', hg'⟩ := lem
    use g'
    rw [hg', mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr g_ne_0), C_1, mul_one]
  have g_mul_dvd : g * C g.leadingCoeff⁻¹ ∣ f.map (algebraMap R K) := by
    rwa [Associated.dvd_iff_dvd_left (show Associated (g * C g.leadingCoeff⁻¹) g from _)]
    rw [associated_mul_isUnit_left_iff]
    exact isUnit_C.mpr (inv_ne_zero <| leadingCoeff_ne_zero.mpr g_ne_0).isUnit
  let algeq :=
    (Subalgebra.equivOfEq _ _ <| integralClosure_eq_bot R _).trans
      (Algebra.botEquivOfInjective <| IsFractionRing.injective R <| K)
  have :
    (algebraMap R _).comp algeq.toAlgHom.toRingHom = (integralClosure R _).toSubring.subtype := by
    ext x; (conv_rhs => rw [← algeq.symm_apply_apply x]); rfl
  have H :=
    (mem_lifts _).1
      (integralClosure.mem_lifts_of_monic_of_dvd_map K hf (monic_mul_leadingCoeff_inv g_ne_0)
        g_mul_dvd)
  refine ⟨map algeq.toAlgHom.toRingHom ?_, ?_⟩
  · use! Classical.choose H
  · rw [map_map, this]
    exact Classical.choose_spec H

end IsIntegrallyClosed

namespace Polynomial

section

variable {S : Type*} [CommRing S] [IsDomain S]
variable {φ : R →+* S} (hinj : Function.Injective φ) {f : R[X]} (hf : f.IsPrimitive)
include hinj hf

/-
**Polynomial.IsPrimitive.isUnit_iff_isUnit_map_of_injective** 是 Mathlib 中的一个定理，位
于命名空间 `Polynomial.IsPrimitive`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
[IsDomain S] {φ : R →+* S},   Function.Injective ⇑φ → ∀ {f : Polynomial R}, f.Is
Primitive → (IsUnit f ↔ IsUnit (Polynomial.map φ f))
参数：IsUnit f ↔ IsUnit (Polynomial.map φ f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.isUnit_map`：isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUn
it (f a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Polynomial.isUnit_iff`：isUnit_iff : IsUnit p ↔ exists r : R, IsUnit r ∧ 
C r = p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_C_of_degree_eq_zero`：eq_C_of_degree_eq_zero (h : degree p 
= 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.degree_map_eq_of_injective`：degree_map_eq_of_injective {f : R
 ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).degree = p.d
egree
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `Polynomial.isPrimitive_iff_isUnit_of_C_dvd`：isPrimitive_iff_isUnit_of_C_
dvd {p : R[X]} : p.IsPrimitive ↔ forall r : R, C r ∣ p -> IsUnit r
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem IsPrimitive.isUnit_iff_isUnit_map_of_injective : IsUnit f ↔ IsUnit (map φ f) := by
  refine ⟨(mapRingHom φ).isUnit_map, fun h => ?_⟩
  rcases isUnit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  have hdeg := degree_C u.ne_zero
  rw [hu, degree_map_eq_of_injective hinj] at hdeg
  rw [eq_C_of_degree_eq_zero hdeg] at hf ⊢
  exact isUnit_C.mpr (isPrimitive_iff_isUnit_of_C_dvd.mp hf (f.coeff 0) dvd_rfl)
/-
**Polynomial.IsPrimitive.irreducible_of_irreducible_map_of_injective** 是 Mathlib
 中的一个定理，位于命名空间 `Polynomial.IsPrimitive`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
[IsDomain S] {φ : R →+* S},   Function.Injective ⇑φ → ∀ {f : Polynomial R}, f.Is
Primitive → Irreducible (Polynomial.map φ f) → Irreducible f
参数：Polynomial.map φ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.IsPrimitive.isUnit_iff_isUnit_map_of_injective`：∀ {R : Type u
_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] [IsDomain S] {φ : R
 →+* S},   Function.Injective ⇑φ → ∀ {f : Polyn…
· 使用定理 `Polynomial.isPrimitive_of_dvd`：isPrimitive_of_dvd {p q : R[X]} (hp : IsP
rimitive p) (hq : q ∣ p) : IsPrimitive q
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
-/
theorem IsPrimitive.irreducible_of_irreducible_map_of_injective (h_irr : Irreducible (map φ f)) :
    Irreducible f := by
  refine
    ⟨fun h => h_irr.not_isUnit (IsUnit.map (mapRingHom φ) h), fun a b h =>
      (h_irr.isUnit_or_isUnit <| by rw [h, Polynomial.map_mul]).imp ?_ ?_⟩
  all_goals apply ((isPrimitive_of_dvd hf _).isUnit_iff_isUnit_map_of_injective hinj).mpr
  exacts [Dvd.intro _ h.symm, Dvd.intro_left _ h.symm]

end

section FractionMap

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-
**Polynomial.IsPrimitive.isUnit_iff_isUnit_map** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial.IsPrimitive`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [in
st_2 : Algebra R K] [IsFractionRing R K]   {p : Polynomial R}, p.IsPrimitive → (
IsUnit p ↔ IsUnit (Polynomial.map (algebraMap R K) p))
参数：IsUnit p ↔ IsUnit (Polynomial.map (algebraMap R K) p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsPrimitive.isUnit_iff_isUnit_map_of_injective`：∀ {R : Type u
_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] [IsDomain S] {φ : R
 →+* S},   Function.Injective ⇑φ → ∀ {f : Polyn…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
-/
theorem IsPrimitive.isUnit_iff_isUnit_map {p : R[X]} (hp : p.IsPrimitive) :
    IsUnit p ↔ IsUnit (p.map (algebraMap R K)) :=
  hp.isUnit_iff_isUnit_map_of_injective (IsFractionRing.injective _ _)

section IsIntegrallyClosed

open IsIntegrallyClosed

/-- **Gauss's Lemma** for integrally closed domains states that a monic polynomial is irreducible
  iff it is irreducible in the fraction field. -/
/-
**Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map** 是 Mathlib 中的一个
定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [in
st_2 : Algebra R K] [IsFractionRing R K]   [IsIntegrallyClosed R] {p : Polynomia
l R}, p.Monic → (Irreducible p ↔ Irreducible (Polynomial.map (algebraMap R K) p)
)
参数：Irreducible p ↔ Irreducible (Polynomial.map (algebraMap R K) p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `irreducible_iff`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irreducible
 p ↔ ¬IsUnit p ∧ ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Not.imp`：∀ {a b : Prop}, ¬b → (a → b) → ¬a
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Polynomial.IsPrimitive.isUnit_iff_isUnit_map`：∀ {R : Type u_1} [inst : C
ommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra R K] [IsFractionR
ing R K]   {p : Polynomial R}, p.I…
· 使用定理 `Polynomial.Monic.isPrimitive`：∀ {R : Type u_1} [inst : CommSemiring R] {
p : Polynomial R}, p.Monic → p.IsPrimitive
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `IsIntegrallyClosed.eq_map_mul_C_of_dvd`：IsIntegrallyClosed.eq_map_mul_C_
of_dvd [IsIntegrallyClosed R] {f : R[X]} (hf : f.Monic) {g : K[X]} (hg : g ∣ f.m
ap (algebraMap R K)) : exist…
· 使用定理 `dvd_of_mul_right_eq`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α} (c 
: α), a * c = b → a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_of_mul_left_eq`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α} 
(c : α), c * a = b → a ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**Gauss's Lemma** for integrally closed domains states that a monic polynomial i
s irreducible
  iff it is irreducible in the fraction field.
-/
theorem Monic.irreducible_iff_irreducible_map_fraction_map [IsIntegrallyClosed R] {p : R[X]}
    (h : p.Monic) : Irreducible p ↔ Irreducible (p.map <| algebraMap R K) := by
  /- The ← direction follows from `IsPrimitive.irreducible_of_irreducible_map_of_injective`.
       For the → direction, it is enough to show that if `(p.map <| algebraMap R K) = a * b` and
       `a` is not a unit then `b` is a unit -/
  refine
    ⟨fun hp =>
      irreducible_iff.mpr
        ⟨hp.not_isUnit.imp h.isPrimitive.isUnit_iff_isUnit_map.mpr, fun a b H =>
          or_iff_not_imp_left.mpr fun hₐ => ?_⟩,
      fun hp =>
      h.isPrimitive.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective R K) hp⟩
  obtain ⟨a', ha⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_right_eq b H.symm)
  obtain ⟨b', hb⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_left_eq a H.symm)
  have : a.leadingCoeff * b.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← H, Monic.leadingCoeff (h.map <| algebraMap R K)]
  rw [← ha, ← hb, mul_comm _ (C b.leadingCoeff), mul_assoc, ← mul_assoc (C a.leadingCoeff), ←
    C_mul, this, C_1, one_mul, ← Polynomial.map_mul] at H
  rw [← hb, ← Polynomial.coe_mapRingHom]
  refine
    IsUnit.mul (IsUnit.map _ (Or.resolve_left (hp.isUnit_or_isUnit ?_) (show ¬IsUnit a' from ?_)))
      (isUnit_iff_exists_inv'.mpr
        (Exists.intro (C a.leadingCoeff) <| by rw [← C_mul, this, C_1]))
  · exact Polynomial.map_injective _ (IsFractionRing.injective R K) H
  · by_contra h_contra
    refine hₐ ?_
    rw [← ha, ← Polynomial.coe_mapRingHom]
    exact
      IsUnit.mul (IsUnit.map _ h_contra)
        (isUnit_iff_exists_inv.mpr
          (Exists.intro (C b.leadingCoeff) <| by rw [← C_mul, this, C_1]))

/-- Integrally closed domains are precisely the domains for in which Gauss's lemma holds
for monic polynomials -/
/-
**Polynomial.isIntegrallyClosed_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isIntegrallyClosed_iff' [IsDomain R] : IsIntegrallyClosed R ↔ forall p : R
[X], p.Monic -> (Irreducible p ↔ Irreducible (p.map <| algebraMap R K))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`：∀ {R : Ty
pe u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra 
R K] [IsFractionRing R K]   [IsIntegrallyClosed R] …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isIntegrallyClosed_iff`：isIntegrallyClosed_iff : IsIntegrallyClosed R ↔ 
forall {x : K}, IsIntegral R x -> exists y, algebraMap R K y = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.mem_range`：mem_range {f : R ->+* S} {y : S} : y in f.range ↔ exi
sts x, f x = y
· 使用定理 `minpoly.mem_range_of_degree_eq_one`：mem_range_of_degree_eq_one (hx : (mi
npoly A x).degree = 1) : x in (algebraMap A B).range
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.degree_map`：∀ {R : Type u} {S : Type v} [inst : Semirin
g R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (f :
 R →+* S), (Polyn…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用引理 `Polynomial.degree_eq_one_of_irreducible_of_root`：degree_eq_one_of_irredu
cible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) : degree p = 1
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0

--- 原说明 ---
Integrally closed domains are precisely the domains for in which Gauss's lemma h
olds
for monic polynomials
-/
theorem isIntegrallyClosed_iff' [IsDomain R] :
    IsIntegrallyClosed R ↔
      ∀ p : R[X], p.Monic → (Irreducible p ↔ Irreducible (p.map <| algebraMap R K)) := by
  constructor
  · intro hR p hp; exact Monic.irreducible_iff_irreducible_map_fraction_map hp
  · intro H
    refine
      (isIntegrallyClosed_iff K).mpr fun {x} hx =>
        RingHom.mem_range.mp <| minpoly.mem_range_of_degree_eq_one R x ?_
    rw [← Monic.degree_map (minpoly.monic hx) (algebraMap R K)]
    apply
      degree_eq_one_of_irreducible_of_root ((H _ <| minpoly.monic hx).mp (minpoly.irreducible hx))
    rw [IsRoot, eval_map_algebraMap, minpoly.aeval R x]
/-
**Polynomial.Monic.dvd_of_fraction_map_dvd_fraction_map** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [in
st_2 : Algebra R K] [IsFractionRing R K]   [IsIntegrallyClosed R] {p q : Polynom
ial R},   p.Monic → q.Monic → Polynomial.map (algebraMap R K) q ∣ Polynomial.map
 (algebraMap R K) p → q ∣ p
参数：algebraMap R K；algebraMap R K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegrallyClosed.eq_map_mul_C_of_dvd`：IsIntegrallyClosed.eq_map_mul_C_
of_dvd [IsIntegrallyClosed R] {f : R[X]} (hf : f.Monic) {g : K[X]} (hg : g ∣ f.m
ap (algebraMap R K)) : exist…
· 使用定理 `dvd_of_mul_left_eq`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α} 
(c : α), c * a = b → a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_of_mul_right_eq`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α} (c 
: α), a * c = b → a ∣ b
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.Monic.of_mul_monic_left`：∀ {R : Type u} [inst : Semiring R] {
p q : Polynomial R}, p.Monic → (p * q).Monic → q.Monic
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
-/
theorem Monic.dvd_of_fraction_map_dvd_fraction_map [IsIntegrallyClosed R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic)
    (h : q.map (algebraMap R K) ∣ p.map (algebraMap R K)) : q ∣ p := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨d', hr'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hp (dvd_of_mul_left_eq _ hr.symm)
  rw [Monic.leadingCoeff, C_1, mul_one] at hr'
  · rw [← hr', ← Polynomial.map_mul] at hr
    exact dvd_of_mul_right_eq _ (Polynomial.map_injective _ (IsFractionRing.injective R K) hr.symm)
  · exact Monic.of_mul_monic_left (hq.map (algebraMap R K)) (by simpa [← hr] using hp.map _)
/-
**Polynomial.Monic.dvd_iff_fraction_map_dvd_fraction_map** 是 Mathlib 中的一个定理，位于命名
空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [in
st_2 : Algebra R K] [IsFractionRing R K]   [IsIntegrallyClosed R] {p q : Polynom
ial R},   p.Monic → q.Monic → (Polynomial.map (algebraMap R K) q ∣ Polynomial.ma
p (algebraMap R K) p ↔ q ∣ p)
参数：Polynomial.map (algebraMap R K) q ∣ Polynomial.map (algebraMap R K) p ↔ q ∣ p
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.dvd_of_fraction_map_dvd_fraction_map`：∀ {R : Type u_1} 
[inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra R K] [Is
FractionRing R K]   [IsIntegrallyClosed R] …
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Monic.dvd_iff_fraction_map_dvd_fraction_map [IsIntegrallyClosed R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic) : q.map (algebraMap R K) ∣ p.map (algebraMap R K) ↔ q ∣ p :=
  ⟨fun h => hp.dvd_of_fraction_map_dvd_fraction_map hq h, fun ⟨a, b⟩ =>
    ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩⟩

end IsIntegrallyClosed

open IsLocalization

section GCDMonoid

variable [IsDomain R]

/-
**Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart** 是 Mathl
ib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart [NormalizedGCDMo
noid R] {p : K[X]} (h0 : p != 0) (h : IsUnit (integerNormalization R⁰ p).primPar
t) : IsUnit p
参数：h0 : p != 0；h : IsUnit (integerNormalization R⁰ p).primPart。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Polynomial.isUnit_iff`：isUnit_iff : IsUnit p ↔ exists r : R, IsUnit r ∧ 
C r = p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsLocalization.integerNormalization_spec`：integerNormalization_spec (p :
 S[X]) : exists b in M, (integerNormalization M p).map (algebraMap R S) = b • p
· 使用定理 `isUnit_of_mul_isUnit_right`：isUnit_of_mul_isUnit_right [Monoid M] [IsDed
ekindFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit y
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.algebraMap_apply`：algebraMap_apply (r : R) : algebraMap R A[X
] r = C (algebraMap R A r)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Polynomial.eq_C_content_mul_primPart`：eq_C_content_mul_primPart (p : R[X
]) : p = C p.content * p.primPart
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `IsFractionRing.integerNormalization_eq_zero_iff`：integerNormalization_eq
_zero_iff {p : K[X]} : integerNormalization (nonZeroDivisors A) p = 0 ↔ p = 0
· 使用定理 `Polynomial.content_eq_zero_iff`：content_eq_zero_iff {p : R[X]} : content
 p = 0 ↔ p = 0
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
（共 31 条，此处仅展示前 30 条）
-/
theorem isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart [NormalizedGCDMonoid R]
    {p : K[X]} (h0 : p ≠ 0) (h : IsUnit (integerNormalization R⁰ p).primPart) : IsUnit p := by
  rcases isUnit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  obtain ⟨c, c0, hc⟩ := integerNormalization_spec R⁰ p
  rw [Algebra.smul_def, algebraMap_apply] at hc
  apply isUnit_of_mul_isUnit_right
  rw [← hc, (integerNormalization R⁰ p).eq_C_content_mul_primPart, ← hu, ← map_mul, isUnit_iff]
  refine
    ⟨algebraMap R K ((integerNormalization R⁰ p).content * ↑u), isUnit_iff_ne_zero.2 fun con => ?_,
      by simp⟩
  replace con := (injective_iff_map_eq_zero (algebraMap R K)).1 (IsFractionRing.injective _ _) _ con
  rw [mul_eq_zero, content_eq_zero_iff, IsFractionRing.integerNormalization_eq_zero_iff] at con
  rcases con with (con | con)
  · apply h0 con
  · apply Units.ne_zero _ con

variable [IsGCDMonoid R]
/-
**Polynomial.IsPrimitive.mul_map_mem_lifts_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial.IsPrimitive`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [in
st_2 : Algebra R K] [IsFractionRing R K]   [IsDomain R] [IsGCDMonoid R] {f : Pol
ynomial R},   f.IsPrimitive →     ∀ {g : Polynomial K},       g * Polynomial.map
 (algebraMap R K) f ∈ Polynomial.lifts (algebraMap R K) ↔ g ∈ Polynomial.lifts (
algebraMap R K)
参数：algebraMap R K；algebraMap R K；algebraMap R K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyNormalizedGCDMonoidOfIsGCDMonoid`：∀ (α : Type u_2) [inst : C
ommMonoidWithZero α] [IsGCDMonoid α], Nonempty (NormalizedGCDMonoid α)
· 使用定理 `IsLocalization.integerNormalization_spec`：integerNormalization_spec (p :
 S[X]) : exists b in M, (integerNormalization M p).map (algebraMap R S) = b • p
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_smul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p 
: Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (r : R),   Polynomial.map f 
(r • p) =…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Associated.of_eq`：Associated.of_eq [Monoid M] {a b : M} (h : a = b) : a 
~ᵤ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.dvd_content_iff_C_dvd`：dvd_content_iff_C_dvd {p : R[X]} {r : 
R} : r ∣ p.content ↔ C r ∣ p
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Associated.dvd'`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associate
d a b → b ∣ a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.IsPrimitive.content_eq_one`：∀ {R : Type u_1} [inst : CommRing
 R] [inst_1 : NormalizedGCDMonoid R] {p : Polynomial R}, p.IsPrimitive → p.conte
nt = 1
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `Associated.instIsTrans`：∀ {M : Type u_1} [inst : Monoid M], IsTrans M As
sociated
· 使用定理 `Associated.refl`：∀ {M : Type u_1} [inst : Monoid M] (x : M), Associated 
x x
· 使用定理 `Polynomial.associated_content_C_mul`：associated_content_C_mul (r : R) (p
 : R[X]) : Associated (C r * p).content (r * p.content)
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Polynomial.associated_content_mul`：associated_content_mul (p q : R[X]) :
 Associated ((p * q).content) (p.content * q.content)
· 使用定理 `Polynomial.C_mul'`：C_mul' (a : R) (f : R[X]) : C a * f = a • f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 45 条，此处仅展示前 30 条）
-/
lemma IsPrimitive.mul_map_mem_lifts_iff {f : R[X]} (hf : IsPrimitive f) {g : K[X]} :
    g * f.map (algebraMap R K) ∈ lifts (algebraMap R K) ↔ g ∈ lifts (algebraMap R K) := by
  let : NormalizedGCDMonoid R := Nonempty.some inferInstance
  refine ⟨fun ⟨k, (hk : k.map _ = _)⟩ ↦ ?_, fun h ↦ mul_mem h ⟨_, rfl⟩⟩
  let g' := integerNormalization R⁰ g
  obtain ⟨b, hb₁, (hb₂ : g'.map _ = _)⟩ := integerNormalization_spec R⁰ g
  have g'_mul_f : g' * f = b • k := by
    apply map_injective (algebraMap R K) (FaithfulSMul.algebraMap_injective R K)
    rw [Polynomial.map_smul, algebraMap_smul, hk, ← smul_mul_assoc, ← hb₂, Polynomial.map_mul]
  apply_fun content at g'_mul_f
  have h := Associated.of_eq g'_mul_f
  grw [← C_mul', associated_content_mul, associated_content_C_mul, hf.content_eq_one, mul_one] at h
  obtain ⟨g'', hg⟩ : C b ∣ g' := dvd_content_iff_C_dvd.mp <| (dvd_mul_right ..).trans h.dvd'
  use g''
  simp [← smul_right_inj (nonZeroDivisors.ne_zero hb₁), ← hb₂, hg, C_mul']
/-
**Polynomial.IsPrimitive.map_mul_mem_lifts_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial.IsPrimitive`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [in
st_2 : Algebra R K] [IsFractionRing R K]   [IsDomain R] [IsGCDMonoid R] {f : Pol
ynomial R},   f.IsPrimitive →     ∀ {g : Polynomial K},       Polynomial.map (al
gebraMap R K) f * g ∈ Polynomial.lifts (algebraMap R K) ↔ g ∈ Polynomial.lifts (
algebraMap R K)
参数：algebraMap R K；algebraMap R K；algebraMap R K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.IsPrimitive.mul_map_mem_lifts_iff`：∀ {R : Type u_1} [inst : C
ommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra R K] [IsFractionR
ing R K]   [IsDomain R] [IsGCDMono…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsPrimitive.map_mul_mem_lifts_iff {f : R[X]} (hf : IsPrimitive f) {g : K[X]} :
    f.map (algebraMap R K) * g ∈ lifts (algebraMap R K) ↔ g ∈ lifts (algebraMap R K) := by
  rw [mul_comm, hf.mul_map_mem_lifts_iff]

/-- **Gauss's Lemma** for GCD domains states that a primitive polynomial is irreducible iff it is
  irreducible in the fraction field. -/
/-
**Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map** 是 Mathli
b 中的一个定理，位于命名空间 `Polynomial.IsPrimitive`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [in
st_2 : Algebra R K] [IsFractionRing R K]   [IsDomain R] [IsGCDMonoid R] {p : Pol
ynomial R},   p.IsPrimitive → (Irreducible p ↔ Irreducible (Polynomial.map (alge
braMap R K) p))
参数：Irreducible p ↔ Irreducible (Polynomial.map (algebraMap R K) p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.IsPrimitive.isUnit_iff_isUnit_map`：∀ {R : Type u_1} [inst : C
ommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra R K] [IsFractionR
ing R K]   {p : Polynomial R}, p.I…
· 使用定理 `IsLocalization.integerNormalization_spec`：integerNormalization_spec (p :
 S[X]) : exists b in M, (integerNormalization M p).map (algebraMap R S) = b • p
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.algebraMap_apply`：algebraMap_apply (r : R) : algebraMap R A[X
] r = C (algebraMap R A r)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
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
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `instNonemptyNormalizedGCDMonoidOfIsGCDMonoid`：∀ (α : Type u_2) [inst : C
ommMonoidWithZero α] [IsGCDMonoid α], Nonempty (NormalizedGCDMonoid α)
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
**Gauss's Lemma** for GCD domains states that a primitive polynomial is irreduci
ble iff it is
  irreducible in the fraction field.
-/
theorem IsPrimitive.irreducible_iff_irreducible_map_fraction_map {p : R[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (algebraMap R K)) := by
  refine
    ⟨fun hi => ⟨fun h => hi.not_isUnit (hp.isUnit_iff_isUnit_map.2 h), fun a b hab => ?_⟩,
      hp.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective _ _)⟩
  obtain ⟨c, c0, hc⟩ := integerNormalization_spec R⁰ a
  obtain ⟨d, d0, hd⟩ := integerNormalization_spec R⁰ b
  rw [Algebra.smul_def, algebraMap_apply] at hc hd
  rw [mem_nonZeroDivisors_iff_ne_zero] at c0 d0
  have hcd0 : c * d ≠ 0 := mul_ne_zero c0 d0
  rw [Ne, ← C_eq_zero] at hcd0
  have h1 : C c * C d * p = integerNormalization R⁰ a * integerNormalization R⁰ b := by
    apply map_injective (algebraMap R K) (IsFractionRing.injective _ _) _
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, hc, hd, map_C, map_C, hab]
    ring
  have := Classical.arbitrary (NormalizedGCDMonoid R)
  obtain ⟨u, hu⟩ :
    Associated (c * d)
      (content (integerNormalization R⁰ a) * content (integerNormalization R⁰ b)) := by
    grw [← associated_content_mul, ← h1, associated_content_mul, ← C_mul, content_C,
      hp.content_eq_one, mul_one]
    apply associated_normalize
  rw [← map_mul, eq_comm, (integerNormalization R⁰ a).eq_C_content_mul_primPart,
    (integerNormalization R⁰ b).eq_C_content_mul_primPart, mul_assoc, mul_comm _ (C _ * _), ←
    mul_assoc, ← mul_assoc, ← map_mul, ← hu, map_mul, mul_assoc, mul_assoc, ←
    mul_assoc (C (u : R))] at h1
  have h0 : a ≠ 0 ∧ b ≠ 0 := by
    rw [Ne, Ne, ← not_or, ← mul_eq_zero, ← hab]
    intro con
    apply hp.ne_zero (map_injective (algebraMap R K) (IsFractionRing.injective _ _) _)
    simp [con]
  rcases hi.isUnit_or_isUnit (mul_left_cancel₀ hcd0 h1).symm with (h | h)
  · right
    apply
      isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart h0.2
        (isUnit_of_mul_isUnit_right h)
  · left
    apply isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart h0.1 h
/-
**Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial.IsPrimitive`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [in
st_2 : Algebra R K] [IsFractionRing R K]   [IsDomain R] [IsGCDMonoid R] {p q : P
olynomial R},   p.IsPrimitive → Polynomial.map (algebraMap R K) p ∣ Polynomial.m
ap (algebraMap R K) q → p ∣ q
参数：algebraMap R K；algebraMap R K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.IsPrimitive.mul_map_mem_lifts_iff`：∀ {R : Type u_1} [inst : C
ommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra R K] [IsFractionR
ing R K]   [IsDomain R] [IsGCDMono…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
-/
theorem IsPrimitive.dvd_of_fraction_map_dvd_fraction_map {p q : R[X]} (hp : p.IsPrimitive)
    (h_dvd : p.map (algebraMap R K) ∣ q.map (algebraMap R K)) : p ∣ q := by
  rcases h_dvd with ⟨r, hr⟩
  obtain ⟨r, rfl⟩ := (mul_map_mem_lifts_iff hp).mp ⟨q, mul_comm _ r ▸ hr⟩
  use r
  simpa [← Polynomial.map_mul, (map_injective _ (FaithfulSMul.algebraMap_injective R K)).eq_iff]
    using hr

variable (K)
/-
**Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map** 是 Mathlib 中的一个定
理，位于命名空间 `Polynomial.IsPrimitive`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (K : Type u_2) [inst_1 : Field K] [in
st_2 : Algebra R K] [IsFractionRing R K]   [IsDomain R] [IsGCDMonoid R] {p q : P
olynomial R},   p.IsPrimitive → (p ∣ q ↔ Polynomial.map (algebraMap R K) p ∣ Pol
ynomial.map (algebraMap R K) q)
参数：K : Type u_2；p ∣ q ↔ Polynomial.map (algebraMap R K) p ∣ Polynomial.map (alge
braMap R K) q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map`：∀ {R : Type
 u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra R 
K] [IsFractionRing R K]   [IsDomain R] [IsGCDMono…
-/
theorem IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map {p q : R[X]} (hp : p.IsPrimitive) :
    p ∣ q ↔ p.map (algebraMap R K) ∣ q.map (algebraMap R K) :=
  ⟨fun ⟨a, b⟩ => ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩, fun h =>
    hp.dvd_of_fraction_map_dvd_fraction_map h⟩

end GCDMonoid

end FractionMap

/-- **Gauss's Lemma** for `ℤ` states that a primitive integer polynomial is irreducible iff it is
  irreducible over `ℚ`. -/
/-
**Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast** 是 Mathlib 中的
一个定理，位于命名空间 `Polynomial.IsPrimitive.Int`。
形式化陈述：∀ {p : Polynomial ℤ}, p.IsPrimitive → (Irreducible p ↔ Irreducible (Polyno
mial.map (Int.castRingHom ℚ) p))
参数：Irreducible p ↔ Irreducible (Polynomial.map (Int.castRingHom ℚ) p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`：∀ {
R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Al
gebra R K] [IsFractionRing R K]   [IsDomain R] [IsGCDMono…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsBezout.instIsGCDMonoidOfIsCancelMulZero`：∀ (R : Type u) [inst : CommRi
ng R] [IsBezout R] [IsCancelMulZero R], IsGCDMonoid R
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ

--- 原说明 ---
**Gauss's Lemma** for `ℤ` states that a primitive integer polynomial is irreduci
ble iff it is
  irreducible over `ℚ`.
-/
theorem IsPrimitive.Int.irreducible_iff_irreducible_map_cast {p : ℤ[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (Int.castRingHom ℚ)) :=
  hp.irreducible_iff_irreducible_map_fraction_map
/-
**Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial.IsPrimitive.Int`。
形式化陈述：∀ (p q : Polynomial ℤ),   p.IsPrimitive → (p ∣ q ↔ Polynomial.map (Int.cas
tRingHom ℚ) p ∣ Polynomial.map (Int.castRingHom ℚ) q)
参数：p q : Polynomial ℤ；p ∣ q ↔ Polynomial.map (Int.castRingHom ℚ) p ∣ Polynomial.
map (Int.castRingHom ℚ) q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`：∀ {R : Typ
e u_1} [inst : CommRing R] (K : Type u_2) [inst_1 : Field K] [inst_2 : Algebra R
 K] [IsFractionRing R K]   [IsDomain R] [IsGCDMono…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsBezout.instIsGCDMonoidOfIsCancelMulZero`：∀ (R : Type u) [inst : CommRi
ng R] [IsBezout R] [IsCancelMulZero R], IsGCDMonoid R
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
-/
theorem IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast (p q : ℤ[X]) (hp : p.IsPrimitive) :
    p ∣ q ↔ p.map (Int.castRingHom ℚ) ∣ q.map (Int.castRingHom ℚ) :=
  hp.dvd_iff_fraction_map_dvd_fraction_map ℚ

end Polynomial

