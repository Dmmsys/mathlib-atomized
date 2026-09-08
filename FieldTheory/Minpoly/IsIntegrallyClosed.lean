/-
Copyright (c) 2019 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Paul Lezeau, Junyan Xu
-/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Minimal polynomials over a GCD monoid

This file specializes the theory of minpoly to the case of an algebra over a GCD monoid.

## Main results

* `minpoly.isIntegrallyClosed_eq_field_fractions`: For integrally closed domains, the minimal
  polynomial over the ring is the same as the minimal polynomial over the fraction field.

* `minpoly.isIntegrallyClosed_dvd`: For integrally closed domains, the minimal polynomial divides
  any primitive polynomial that has the integral element as root.

* `IsIntegrallyClosed.Minpoly.unique`: The minimal polynomial of an element `x` is uniquely
  characterized by its defining property: if there is another monic polynomial of minimal degree
  that has `x` as a root, then this polynomial is equal to the minimal polynomial of `x`.

-/

@[expose] public section

open Polynomial Set Function minpoly Module

namespace minpoly

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]

section

variable (K L : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [CommRing L] [Nontrivial L]
  [Algebra R L] [Algebra S L] [Algebra K L] [IsScalarTower R K L] [IsScalarTower R S L]

variable [IsIntegrallyClosed R]

/-- For integrally closed domains, the minimal polynomial over the ring is the same as the minimal
polynomial over the fraction field. See `minpoly.isIntegrallyClosed_eq_field_fractions'` if
`S` is already a `K`-algebra. -/
/-
**minpoly.isIntegrallyClosed_eq_field_fractions** 是 Mathlib 中的一个定理，位于命名空间 `minpo
ly`。
形式化陈述：isIntegrallyClosed_eq_field_fractions [IsDomain S] {s : S} (hs : IsIntegra
l R s) : minpoly K (algebraMap S L s) = (minpoly R s).map (algebraMap R K)
参数：hs : IsIntegral R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.eq_of_irreducible_of_monic`：eq_of_irreducible_of_monic [Nontrivi
al B] {p : A[X]} (hp1 : Irreducible p) (hp2 : Polynomial.aeval x p = 0) (hp3 : p
.Monic) : p = minpoly A …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`：∀ {R : Ty
pe u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra 
R K] [IsFractionRing R K]   [IsIntegrallyClosed R] …
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…

--- 原说明 ---
For integrally closed domains, the minimal polynomial over the ring is the same 
as the minimal
polynomial over the fraction field. See `minpoly.isIntegrallyClosed_eq_field_fra
ctions'` if
`S` is already a `K`-algebra.
-/
theorem isIntegrallyClosed_eq_field_fractions [IsDomain S] {s : S} (hs : IsIntegral R s) :
    minpoly K (algebraMap S L s) = (minpoly R s).map (algebraMap R K) := by
  refine (eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · exact ((monic hs).irreducible_iff_irreducible_map_fraction_map).1 (irreducible hs)
  · rw [aeval_map_algebraMap, aeval_algebraMap_apply, aeval, map_zero]
  · exact (monic hs).map _

/-- For integrally closed domains, the minimal polynomial over the ring is the same as the minimal
polynomial over the fraction field. Compared to `minpoly.isIntegrallyClosed_eq_field_fractions`,
this version is useful if the element is in a ring that is already a `K`-algebra. -/
/-
**minpoly.isIntegrallyClosed_eq_field_fractions'** 是 Mathlib 中的一个定理，位于命名空间 `minp
oly`。
形式化陈述：isIntegrallyClosed_eq_field_fractions' [IsDomain S] [Algebra K S] [IsScala
rTower R K S] {s : S} (hs : IsIntegral R s) : minpoly K s = (minpoly R s).map (a
lgebraMap R K)
参数：hs : IsIntegral R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.isIntegrallyClosed_eq_field_fractions`：isIntegrallyClosed_eq_fie
ld_fractions [IsDomain S] {s : S} (hs : IsIntegral R s) : minpoly K (algebraMap 
S L s) = (minpoly R s).map (algebra…
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `minpoly.algebraMap_eq`：algebraMap_eq {B} [CommRing B] [Algebra A B] [Alg
ebra B B'] [IsScalarTower A B B'] (h : Function.Injective (algebraMap B B')) (x 
: B) : minp…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …

--- 原说明 ---
For integrally closed domains, the minimal polynomial over the ring is the same 
as the minimal
polynomial over the fraction field. Compared to `minpoly.isIntegrallyClosed_eq_f
ield_fractions`,
this version is useful if the element is in a ring that is already a `K`-algebra
.
-/
theorem isIntegrallyClosed_eq_field_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S]
    {s : S} (hs : IsIntegral R s) : minpoly K s = (minpoly R s).map (algebraMap R K) := by
  let L := FractionRing S
  rw [← isIntegrallyClosed_eq_field_fractions K L hs, algebraMap_eq (IsFractionRing.injective S L)]

end

variable [IsIntegrallyClosed R] [IsDomain S] [IsTorsionFree R S]

/-- For integrally closed rings, the minimal polynomial divides any polynomial that has the
  integral element as root. See also `minpoly.dvd` which relaxes the assumptions on `S`
  in exchange for stronger assumptions on `R`. -/
/-
**minpoly.isIntegrallyClosed_dvd** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：isIntegrallyClosed_dvd {s : S} (hs : IsIntegral R s) {p : R[X]} (hp : Poly
nomial.aeval s p = 0) : minpoly R s ∣ p
参数：hs : IsIntegral R s；hp : Polynomial.aeval s p = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_modByMonic`：map_modByMonic [Ring S] (f : R ->+* S) (hq : 
Monic q) : (p %ₘ q).map f = p.map f %ₘ q.map f
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Polynomial.modByMonic_eq_sub_mul_div`：modByMonic_eq_sub_mul_div : forall
 p q : R[X], p %ₘ q = p - q * (p /ₘ q) | p, q => letI
· 使用定理 `dvd_sub`：dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_aeval_eq_aeval_map`：map_aeval_eq_aeval_map {S T U : Type*
} [Semiring S] [CommSemiring T] [Semiring U] [Algebra R S] [Algebra T U] {φ : R 
->+* T} {ψ : S ->+* U} …
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
· 使用定理 `minpoly.isIntegrallyClosed_eq_field_fractions`：isIntegrallyClosed_eq_fie
ld_fractions [IsDomain S] {s : S} (hs : IsIntegral R s) : minpoly K (algebraMap 
S L s) = (minpoly R s).map (algebra…
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用引理 `Polynomial.eq_zero_of_dvd_of_degree_lt`：eq_zero_of_dvd_of_degree_lt (h₁ 
: p ∣ q) (h₂ : degree q < degree p) : q = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.map_dvd_map`：map_dvd_map [Ring S] (f : R ->+* S) (hf : Functi
on.Injective f) {x y : R[X]} (hx : x.Monic) : x.map f ∣ y.map f ↔ x ∣ y
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI

--- 原说明 ---
For integrally closed rings, the minimal polynomial divides any polynomial that 
has the
  integral element as root. See also `minpoly.dvd` which relaxes the assumptions
 on `S`
  in exchange for stronger assumptions on `R`.
-/
theorem isIntegrallyClosed_dvd {s : S} (hs : IsIntegral R s) {p : R[X]}
    (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p := by
  let K := FractionRing R
  let L := FractionRing S
  let _ : Algebra K L := FractionRing.liftAlgebra R L
  have : minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (p %ₘ minpoly R s) := by
    rw [map_modByMonic _ (minpoly.monic hs), modByMonic_eq_sub_mul_div]
    refine dvd_sub (minpoly.dvd K (algebraMap S L s) ?_) ?_
    · rw [← map_aeval_eq_aeval_map, hp, map_zero]
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    apply dvd_mul_of_dvd_left
    rw [isIntegrallyClosed_eq_field_fractions K L hs]
  rw [isIntegrallyClosed_eq_field_fractions _ _ hs,
    map_dvd_map (algebraMap R K) (IsFractionRing.injective R K) (minpoly.monic hs)] at this
  rw [← modByMonic_eq_zero_iff_dvd (minpoly.monic hs)]
  exact Polynomial.eq_zero_of_dvd_of_degree_lt this (degree_modByMonic_lt p <| minpoly.monic hs)
/-
**minpoly.isIntegrallyClosed_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：isIntegrallyClosed_dvd_iff {s : S} (hs : IsIntegral R s) (p : R[X]) : Poly
nomial.aeval s p = 0 ↔ minpoly R s ∣ p
参数：hs : IsIntegral R s；p : R[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.isIntegrallyClosed_dvd`：isIntegrallyClosed_dvd {s : S} (hs : IsI
ntegral R s) {p : R[X]} (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p
· 使用定理 `Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero`：aeval_eq_zero_of_dvd_aeva
l_eq_zero {x : B} (h₁ : p ∣ q) (h₂ : aeval x p = 0) : aeval x q = 0
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
-/
theorem isIntegrallyClosed_dvd_iff {s : S} (hs : IsIntegral R s) (p : R[X]) :
    Polynomial.aeval s p = 0 ↔ minpoly R s ∣ p :=
  ⟨fun hp => isIntegrallyClosed_dvd hs hp, fun hp => by
    simpa only [RingHom.mem_ker, RingHom.coe_comp, coe_evalRingHom, coe_mapRingHom,
      Function.comp_apply, eval_map_algebraMap] using
      aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval R s)⟩
/-
**minpoly.ker_eval** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：ker_eval {s : S} (hs : IsIntegral R s) : RingHom.ker ((Polynomial.aeval s)
.toRingHom : R[X] ->+* S) = Ideal.span ({minpoly R s} : Set R[X])
参数：hs : IsIntegral R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `minpoly.isIntegrallyClosed_dvd_iff`：isIntegrallyClosed_dvd_iff {s : S} (
hs : IsIntegral R s) (p : R[X]) : Polynomial.aeval s p = 0 ↔ minpoly R s ∣ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_eval {s : S} (hs : IsIntegral R s) :
    RingHom.ker ((Polynomial.aeval s).toRingHom : R[X] →+* S) =
    Ideal.span ({minpoly R s} : Set R[X]) := by
  ext p
  simp_rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    isIntegrallyClosed_dvd_iff hs, ← Ideal.mem_span_singleton]

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `minpoly.degree_le_of_ne_zero` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
/-
**minpoly.IsIntegrallyClosed.degree_le_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `min
poly.IsIntegrallyClosed`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[IsDomain R] [inst_3 : Algebra R S]   [IsIntegrallyClosed R] [IsDomain S] [Modul
e.IsTorsionFree R S] {s : S} {p : Polynomial R},   p ≠ 0 → (Polynomial.aeval s) 
p = 0 → (minpoly R s).degree ≤ p.degree
参数：Polynomial.aeval s；minpoly R s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Polynomial.natDegree_le_of_dvd`：natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q
 != 0) : p.natDegree <= q.natDegree
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `minpoly.isIntegrallyClosed_dvd_iff`：isIntegrallyClosed_dvd_iff {s : S} (
hs : IsIntegral R s) (p : R[X]) : Polynomial.aeval s p = 0 ↔ minpoly R s ∣ p

--- 原说明 ---
If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` 
is at least the
degree of the minimal polynomial of `x`. See also `minpoly.degree_le_of_ne_zero`
 which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`.
-/
theorem IsIntegrallyClosed.degree_le_of_ne_zero {s : S} {p : R[X]}
    (hp0 : p ≠ 0) (hp : Polynomial.aeval s p = 0) : degree (minpoly R s) ≤ degree p := by
  by_cases! hs : ¬IsIntegral R s
  · simp [minpoly, hs]
  rw [degree_eq_natDegree (minpoly.ne_zero hs), degree_eq_natDegree hp0]
  norm_cast
  exact natDegree_le_of_dvd ((isIntegrallyClosed_dvd_iff hs _).mp hp) hp0

/-- If `x` is a root of an irreducible polynomial `p`, then `x` is integral
iff the leading coefficient of `p` is a unit. -/
/-
**minpoly.IsIntegrallyClosed.isIntegral_iff_isUnit_leadingCoeff** 是 Mathlib 中的一个
定理，位于命名空间 `minpoly.IsIntegrallyClosed`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[IsDomain R] [inst_3 : Algebra R S]   [IsIntegrallyClosed R] [IsDomain S] [Modul
e.IsTorsionFree R S] {x : S} {p : Polynomial R},   Irreducible p → (Polynomial.a
eval x) p = 0 → (IsIntegral R x ↔ IsUnit p.leadingCoeff)
参数：Polynomial.aeval x；IsIntegral R x ↔ IsUnit p.leadingCoeff。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.isIntegrallyClosed_dvd`：isIntegrallyClosed_dvd {s : S} (hs : IsI
ntegral R s) {p : R[X]} (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `of_irreducible_mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Irredu
cible (a * b) → IsUnit a ∨ IsUnit b
· 使用定理 `minpoly.not_isUnit`：not_isUnit [Nontrivial B] : ¬IsUnit (minpoly A x)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `IsIntegral.smul`：IsIntegral.smul {R} [CommSemiring R] [Algebra R B] [Alg
ebra S B] [Algebra R S] [IsScalarTower R S B] {x : B} (r : R) (hx : IsIntegral S
 x) :…
· 使用定理 `isIntegral_leadingCoeff_smul`：isIntegral_leadingCoeff_smul [Algebra R S]
 (h : aeval x p = 0) : IsIntegral R (p.leadingCoeff • x)

--- 原说明 ---
If `x` is a root of an irreducible polynomial `p`, then `x` is integral
iff the leading coefficient of `p` is a unit.
-/
theorem IsIntegrallyClosed.isIntegral_iff_isUnit_leadingCoeff {x : S} {p : R[X]}
    (hirr : Irreducible p) (hp : p.aeval x = 0) :
    IsIntegral R x ↔ IsUnit p.leadingCoeff where
  mp int_x := by
    obtain ⟨p, rfl⟩ := isIntegrallyClosed_dvd int_x hp
    rw [leadingCoeff_mul, monic int_x, one_mul]
    exact ((of_irreducible_mul hirr).resolve_left (not_isUnit R x)).map leadingCoeffHom
  mpr isUnit := by
    simpa [smul_smul] using (isIntegral_leadingCoeff_smul _ _ hp).smul ((isUnit.unit⁻¹ : Rˣ) : R)

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root, then this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.unique` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
/-
**minpoly._root_.IsIntegrallyClosed.minpoly.unique** 是 Mathlib 中的一个定理，位于命名空间 `mi
npoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal polynomial of an element `x` is uniquely characterized by its defini
ng property:
if there is another monic polynomial of minimal degree that has `x` as a root, t
hen this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.unique` which relax
es the
assumptions on `S` in exchange for stronger assumptions on `R`.
-/
theorem _root_.IsIntegrallyClosed.minpoly.unique {s : S} {P : R[X]} (hmo : P.Monic)
    (hP : Polynomial.aeval s P = 0)
    (Pmin : ∀ Q : R[X], Q.Monic → Polynomial.aeval s Q = 0 → degree P ≤ degree Q) :
    P = minpoly R s := by
  have hs : IsIntegral R s := ⟨P, hmo, hP⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
  refine IsIntegrallyClosed.degree_le_of_ne_zero (s := s) hnz (by simp [hP]) |>.not_gt ?_
  refine degree_sub_lt_left ?_ (ne_zero hs) ?_
  · exact le_antisymm (min R s hmo hP) (Pmin (minpoly R s) (monic hs) (aeval R s))
  · rw [(monic hs).leadingCoeff, hmo.leadingCoeff]
/-
**minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly** 是 Mathlib 中的一个
定理，位于命名空间 `minpoly.IsIntegrallyClosed`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[IsDomain R] [inst_3 : Algebra R S]   [IsIntegrallyClosed R] [IsDomain S] [Modul
e.IsTorsionFree R S] {s : S} {p : Polynomial R},   p.Monic → (Polynomial.aeval s
) p = 0 → p.degree ≤ (minpoly R s).degree → p = minpoly R s
参数：Polynomial.aeval s；minpoly R s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegrallyClosed.minpoly.unique`：∀ {R : Type u_1} {S : Type u_2} [inst
 : CommRing R] [inst_1 : CommRing S] [IsDomain R] [inst_3 : Algebra R S]   [IsIn
tegrallyClosed R] [IsDo…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
-/
theorem IsIntegrallyClosed.unique_of_degree_le_degree_minpoly {s : S} {p : R[X]} (hmo : p.Monic)
    (hp : p.aeval s = 0) (pmin : p.degree ≤ (minpoly R s).degree) : p = minpoly R s :=
  IsIntegrallyClosed.minpoly.unique hmo hp fun _ qm hq ↦ pmin.trans <| min _ _ qm hq
/-
**minpoly.IsIntegrallyClosed.isIntegral_iff_leadingCoeff_dvd** 是 Mathlib 中的一个定理，
位于命名空间 `minpoly.IsIntegrallyClosed`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[IsDomain R] [inst_3 : Algebra R S]   [IsIntegrallyClosed R] [IsDomain S] [Modul
e.IsTorsionFree R S] {s : S} {p : Polynomial R},   (Polynomial.aeval s) p = 0 → 
    p ≠ 0 →       (∀ (q : Polynomial R), q.Monic → (Polynomial.aeval s) q = 0 → 
p.degree ≤ q.degree) →         (IsIntegral R s ↔ Polynomial.C p.leadingCoeff ∣ p
)
参数：Polynomial.aeval s；∀ (q : Polynomial R), q.Monic → (Polynomial.aeval s) q = 0
 → p.degree ≤ q.degree；IsIntegral R s ↔ Polynomial.C p.leadingCoeff ∣ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.isIntegrallyClosed_dvd`：isIntegrallyClosed_dvd {s : S} (hs : IsI
ntegral R s) {p : R[X]} (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p
· 使用定理 `WithBot.le_of_add_le_add_left`：∀ {α : Type u} [inst : Add α] {x y z : Wi
thBot α} [inst_1 : LE α] [AddLeftReflectLE α], x ≠ ⊥ → x + y ≤ x + z → y ≤ z
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.degree_ne_bot`：degree_ne_bot : degree p != ⊥ ↔ p != 0
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_le_zero_iff`：degree_le_zero_iff : degree p <= 0 ↔ p = 
C (coeff p 0)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 44 条，此处仅展示前 30 条）
-/
theorem IsIntegrallyClosed.isIntegral_iff_leadingCoeff_dvd {s : S} {p : R[X]} (hp : p.aeval s = 0)
    (h₀ : p ≠ 0) (pmin : ∀ q : R[X], q.Monic → q.aeval s = 0 → p.degree ≤ q.degree) :
    IsIntegral R s ↔ C p.leadingCoeff ∣ p := by
  refine ⟨fun hInt ↦ ?_, fun ⟨q, hMul⟩ ↦ minpoly.ne_zero_iff.mp ?_⟩
  · use minpoly R s
    have ⟨q, hMul⟩ := isIntegrallyClosed_dvd hInt hp
    suffices q.degree ≤ 0 by simp [degree_le_zero_iff.mp this ▸ hMul, minpoly.monic hInt, mul_comm]
    apply WithBot.le_of_add_le_add_left <| Polynomial.degree_ne_bot.mpr <| minpoly.ne_zero hInt
    convert! pmin _ (minpoly.monic hInt) (minpoly.aeval ..)
    · rw [hMul, degree_mul]
    · rw [add_zero]
  · convert! right_ne_zero_of_mul <| hMul ▸ h₀
    refine IsIntegrallyClosed.minpoly.unique ?_ ?_ ?_ |>.symm
    · have := hMul ▸ leadingCoeff_mul .. |>.symm
      simp only [leadingCoeff_C, ne_eq, leadingCoeff_eq_zero, h₀, not_false_eq_true, mul_eq_left₀]
        at this
      exact this
    · have := congrArg (Polynomial.aeval s) hMul
      simp only [hp, h₀, map_mul, aeval_C, zero_eq_mul, FaithfulSMul.algebraMap_eq_zero_iff,
        leadingCoeff_eq_zero, false_or] at this
      exact this
    · exact (hMul ▸ degree_C_mul <| by simp [h₀]) ▸ pmin
/-
**minpoly.prime_of_isIntegrallyClosed** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：prime_of_isIntegrallyClosed {x : S} (hx : IsIntegral R x) : Prime (minpoly
 R x)
参数：hx : IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `minpoly.degree_pos`：degree_pos [Nontrivial B] (hx : IsIntegral A x) : 0 
< degree (minpoly A x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.degree_eq_zero_of_isUnit`：degree_eq_zero_of_isUnit [Nontrivia
l R] (h : IsUnit p) : degree p = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.isIntegrallyClosed_dvd_iff`：isIntegrallyClosed_dvd_iff {s : S} (
hs : IsIntegral R s) (p : R[X]) : Polynomial.aeval s p = 0 ↔ minpoly R s ∣ p
· 使用定理 `eq_zero_of_ne_zero_of_mul_left_eq_zero`：eq_zero_of_ne_zero_of_mul_left_e
q_zero (hx : x != 0) (hxy : x * y = 0) : y = 0
· 使用定理 `Polynomial.aeval_mul`：aeval_mul : aeval x (p * q) = aeval x p * aeval x 
q
-/
theorem prime_of_isIntegrallyClosed {x : S} (hx : IsIntegral R x) : Prime (minpoly R x) := by
  refine
    ⟨(minpoly.monic hx).ne_zero,
      ⟨fun h_contra => (ne_of_lt (minpoly.degree_pos hx)) (degree_eq_zero_of_isUnit h_contra).symm,
        fun a b h => or_iff_not_imp_left.mpr fun h' => ?_⟩⟩
  rw [← minpoly.isIntegrallyClosed_dvd_iff hx] at h' h ⊢
  rw [aeval_mul] at h
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero h' h
/-
**minpoly._root_.IsIntegrallyClosed.minpoly_smul** 是 Mathlib 中的一个引理，位于命名空间 `minp
oly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsIntegrallyClosed.minpoly_smul {r : R} (hr : r ≠ 0) {s : S} (hs : IsIntegral R s) :
    minpoly R (r • s) = (minpoly R s).scaleRoots r := by
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra K L := FractionRing.liftAlgebra _ _
  apply map_injective _ (FaithfulSMul.algebraMap_injective R K)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L (hs.smul r),
    map_scaleRoots _ _ _ (by simpa [minpoly.ne_zero_iff]),
    ← minpoly.isIntegrallyClosed_eq_field_fractions K L hs]
  simp_rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R K L]
  refine eq_of_monic_of_associated (minpoly.monic ?_) ?_
    (associated_of_dvd_dvd (minpoly.dvd _ _ ?_) ?_)
  · refine isIntegral_algebraMap.mul (hs.map (IsScalarTower.toAlgHom R S L)).tower_top
  · simpa [monic_scaleRoots_iff] using minpoly.monic
      (hs.map (IsScalarTower.toAlgHom R S L)).tower_top
  · exact scaleRoots_aeval_eq_zero (minpoly.aeval _ _)
  · rw [← Polynomial.scaleRoots_dvd_iff _ _ (r := (algebraMap R K r)⁻¹) (IsUnit.mk0 _ (by simpa)),
      ← scaleRoots_mul, mul_inv_cancel₀ (by simpa), scaleRoots_one]
    refine minpoly.dvd _ _ ?_
    nth_rw 1 [← inv_mul_cancel_left₀ (b := algebraMap S L s)
      (a := algebraMap K L (algebraMap R K r)) (by simpa), ← map_inv₀]
    exact scaleRoots_aeval_eq_zero (minpoly.aeval _ _)

noncomputable section AdjoinRoot

open Algebra Polynomial AdjoinRoot

variable {x : S}
/-
**minpoly.ToAdjoin.injective** 是 Mathlib 中的一个定理，位于命名空间 `minpoly.ToAdjoin`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[IsDomain R] [inst_3 : Algebra R S]   [IsIntegrallyClosed R] [IsDomain S] [Modul
e.IsTorsionFree R S] {x : S},   IsIntegral R x → Function.Injective ⇑(AdjoinRoot
.Minpoly.toAdjoin R x)
参数：AdjoinRoot.Minpoly.toAdjoin R x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AdjoinRoot.mk_surjective`：mk_surjective : Function.Surjective (mk g)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.coe_aeval_mk_apply`：coe_aeval_mk_apply {S : Subalgebra R A} (
h : x in S) : (aeval (⟨x, h⟩ : S) p : A) = aeval x p
· 使用定理 `minpoly.isIntegrallyClosed_dvd_iff`：isIntegrallyClosed_dvd_iff {s : S} (
hs : IsIntegral R s) (p : R[X]) : Polynomial.aeval s p = 0 ↔ minpoly R s ∣ p
-/
theorem ToAdjoin.injective (hx : IsIntegral R x) : Function.Injective (Minpoly.toAdjoin R x) := by
  refine (injective_iff_map_eq_zero _).2 fun P₁ hP₁ => ?_
  obtain ⟨P, rfl⟩ := mk_surjective P₁
  simpa [← Subalgebra.coe_eq_zero, isIntegrallyClosed_dvd_iff hx, ← aeval_def] using hP₁

/-- The algebra isomorphism `AdjoinRoot (minpoly R x) ≃ₐ[R] adjoin R x` -/
/-
**minpoly.equivAdjoin** 是 Mathlib 中的一个定义，位于命名空间 `minpoly`。
形式化陈述：equivAdjoin (hx : IsIntegral R x) : AdjoinRoot (minpoly R x) ≃ₐ[R] adjoin 
R ({x} : Set S)
参数：hx : IsIntegral R x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra isomorphism `AdjoinRoot (minpoly R x) ≃ₐ[R] adjoin R x`
-/
def equivAdjoin (hx : IsIntegral R x) : AdjoinRoot (minpoly R x) ≃ₐ[R] adjoin R ({x} : Set S) :=
  AlgEquiv.ofBijective (Minpoly.toAdjoin R x)
    ⟨minpoly.ToAdjoin.injective hx, Minpoly.toAdjoin.surjective R x⟩

@[simp]
/-
**minpoly.equivAdjoin_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：equivAdjoin_toAlgHom (hx : IsIntegral R x) : equivAdjoin hx = Minpoly.toAd
join R x
参数：hx : IsIntegral R x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivAdjoin_toAlgHom (hx : IsIntegral R x) : equivAdjoin hx = Minpoly.toAdjoin R x := rfl

@[simp]
/-
**minpoly.coe_equivAdjoin** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：coe_equivAdjoin (hx : IsIntegral R x) : ⇑(equivAdjoin hx) = Minpoly.toAdjo
in R x
参数：hx : IsIntegral R x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_equivAdjoin (hx : IsIntegral R x) : ⇑(equivAdjoin hx) = Minpoly.toAdjoin R x := rfl

/-- The `PowerBasis` of `adjoin R {x}` given by `x`. See `Algebra.adjoin.powerBasis` for a version
over a field. -/
/-
**minpoly._root_.Algebra.adjoin.powerBasis'** 是 Mathlib 中的一个定义，位于命名空间 `minpoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `PowerBasis` of `adjoin R {x}` given by `x`. See `Algebra.adjoin.powerBasis`
 for a version
over a field.
-/
def _root_.Algebra.adjoin.powerBasis' (hx : IsIntegral R x) :
    PowerBasis R (Algebra.adjoin R ({x} : Set S)) :=
  PowerBasis.map (AdjoinRoot.powerBasis' (minpoly.monic hx)) (minpoly.equivAdjoin hx)

@[simp]
/-
**minpoly._root_.Algebra.adjoin.powerBasis'_dim** 是 Mathlib 中的一个定理，位于命名空间 `minpo
ly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Algebra.adjoin.powerBasis'_dim (hx : IsIntegral R x) :
    (Algebra.adjoin.powerBasis' hx).dim = (minpoly R x).natDegree := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**minpoly._root_.Algebra.adjoin.powerBasis'_gen** 是 Mathlib 中的一个定理，位于命名空间 `minpo
ly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Algebra.adjoin.powerBasis'_gen (hx : IsIntegral R x) :
    (adjoin.powerBasis' hx).gen = ⟨x, SetLike.mem_coe.1 <| subset_adjoin <| mem_singleton x⟩ := by
  rw [Algebra.adjoin.powerBasis', PowerBasis.map_gen, AdjoinRoot.powerBasis'_gen, equivAdjoin,
    AlgEquiv.ofBijective_apply, Minpoly.toAdjoin, liftAlgHom_root]

/--
If `x` generates `S` over `R` and is integral over `R`, then it defines a power basis.
See `PowerBasis.ofAdjoinEqTop` for a version over a field.
-/
/-
**minpoly._root_.PowerBasis.ofAdjoinEqTop'** 是 Mathlib 中的一个定义，位于命名空间 `minpoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x` generates `S` over `R` and is integral over `R`, then it defines a power 
basis.
See `PowerBasis.ofAdjoinEqTop` for a version over a field.
-/
noncomputable def _root_.PowerBasis.ofAdjoinEqTop' {x : S} (hx : IsIntegral R x)
    (hx' : adjoin R {x} = ⊤) :
    PowerBasis R S :=
  (adjoin.powerBasis' hx).map ((Subalgebra.equivOfEq _ _ hx').trans Subalgebra.topEquiv)

open Algebra in
/-
**minpoly.** 是 Mathlib 中的一个示例，位于命名空间 `minpoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {x : S} (B : PowerBasis R S)
    (hint : IsIntegral R x) (hx : B.gen ∈ R[x]) :
    PowerBasis R S := by
  apply PowerBasis.ofAdjoinEqTop' hint
  exact PowerBasis.adjoin_eq_top_of_gen_mem_adjoin hx

@[simp]
/-
**minpoly._root_.PowerBasis.ofAdjoinEqTop'_dim** 是 Mathlib 中的一个定理，位于命名空间 `minpol
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.PowerBasis.ofAdjoinEqTop'_dim {x : S} (hx : IsIntegral R x)
    (hx' : adjoin R {x} = ⊤) :
    (PowerBasis.ofAdjoinEqTop' hx hx').dim = (minpoly R x).natDegree := rfl

@[simp]
/-
**minpoly._root_.PowerBasis.ofAdjoinEqTop'_gen** 是 Mathlib 中的一个定理，位于命名空间 `minpol
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.PowerBasis.ofAdjoinEqTop'_gen {x : S} (hx : IsIntegral R x)
    (hx' : adjoin R {x} = ⊤) : (PowerBasis.ofAdjoinEqTop' hx hx').gen = x := by
  simp [PowerBasis.ofAdjoinEqTop']

end AdjoinRoot

section Subring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (A : Subring K) [IsIntegrallyClosed A] [IsFractionRing A K]

-- Implementation note: `inferInstance` does not work for these.
/-
**minpoly.** 是 Mathlib 中的一个实例，位于命名空间 `minpoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra A (integralClosure A L) := Subalgebra.algebra (integralClosure A L)
/-
**minpoly.** 是 Mathlib 中的一个实例，位于命名空间 `minpoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul A (integralClosure A L) := Algebra.toSMul
/-
**minpoly.** 是 Mathlib 中的一个实例，位于命名空间 `minpoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower A ((integralClosure A L)) L :=
  IsScalarTower.subalgebra' A L L (integralClosure A L)

/-- The minimal polynomial of `x : L` over `K` agrees with its minimal polynomial over the
integrally closed subring `A`. -/
/-
**minpoly.ofSubring** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：ofSubring (x : integralClosure A L) : Polynomial.map (algebraMap A K) (min
poly A x) = minpoly K (x : L)
参数：x : integralClosure A L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `minpoly.isIntegrallyClosed_eq_field_fractions`：isIntegrallyClosed_eq_fie
ld_fractions [IsDomain S] {s : S} (hs : IsIntegral R s) : minpoly K (algebraMap 
S L s) = (minpoly R s).map (algebra…
· 使用定理 `Subring.instIsDomainSubtypeMem`：∀ {R : Type u_1} [inst : Ring R] [IsDoma
in R] (s : Subring R), IsDomain ↥s
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Submonoid.instIsScalarTowerSubtypeMem`：∀ {M' : Type u_1} {α : Type u_2} 
{β : Type u_3} {S' : Type u_4} [inst : SetLike S' M'] (s : S') [inst_1 : SMul α 
β]   [inst_2 : SMul M' α] […
· 使用定理 `minpoly.instIsScalarTowerSubtypeMemSubringSubalgebraIntegralClosure`：∀ {
K : Type u_3} {L : Type u_4} [inst : Field K] [inst_1 : Field L] [inst_2 : Algeb
ra K L] (A : Subring K),   IsScalarTower (↥A) (↥(integral…
· 使用定理 `instIsDomainSubtypeMemSubalgebraIntegralClosure`：∀ {R : Type u_1} {S : T
ype u_2} [inst : CommRing R] [inst_1 : CommRing S] [IsDomain S] [inst_3 : Algebr
a R S],   IsDomain ↥(integralClosure …
· 使用定理 `IsIntegralClosure.isIntegral`：∀ (R : Type u_1) {A : Type u_2} (B : Type 
u_3) [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 :
 Algebra R B] [ins…

--- 原说明 ---
The minimal polynomial of `x : L` over `K` agrees with its minimal polynomial ov
er the
integrally closed subring `A`.
-/
theorem ofSubring (x : integralClosure A L) :
    Polynomial.map (algebraMap A K) (minpoly A x) = minpoly K (x : L) :=
  eq_comm.mpr (isIntegrallyClosed_eq_field_fractions K L (IsIntegralClosure.isIntegral A L x))

end Subring

end minpoly

