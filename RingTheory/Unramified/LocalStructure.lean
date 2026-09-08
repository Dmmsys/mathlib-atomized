/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.ZariskisMainTheorem

/-!

# Local structure of unramified algebras

In this file, we will prove that if `S` is a finite type `R`-algebra unramified at `Q`, then
there exists `f ∉ Q` and a standard etale algebra `A` over `R` that surjects onto `S[1/f]`.
Geometrically, this says that unramified morphisms locally are closed subsets of etale covers.

As a corollary, we also obtain results about the local structure of etale and smooth algebras.

## Main definition and results
- `HasStandardEtaleSurjectionOn`: The predicate
  "there exists a standard etale algebra `A` over `R` that surjects onto `S[1/f]`".
- `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`:
  If `S` is a finite type `R`-algebra that is unramified at a prime `p`, then
  there exists a standard etale algebra over `R` that surjects onto `S[1/f]` for some `f ∉ p`.
- `Algebra.IsEtaleAt.exists_isStandardEtale`:
  If `S` is a finitely presented `R`-algebra that is etale at a prime `p`, then
  `S[1/f]` is standard etale for some `f ∉ p`.
- `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`:
  If `S` is a finitely presented `R`-algebra that is smooth at a prime `p`, then
  there exists some `f ∉ p` such that `S[1/f]` is `R`-isomorphic to a standard etale algebra
  over `R[x₁,...,xₙ]`.

-/

@[expose] public section

open Polynomial TensorProduct Algebra

open scoped nonZeroDivisors

variable {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R S] [Algebra R A]

variable (R) in
/-- The predicate "there exists a standard etale algebra `A` over `R` that surjects onto `S[1/f]`".
We shall show if `S` is `R`-unramified at `Q` then there exists `f ∉ Q` satisfying it. -/
/-
**HasStandardEtaleSurjectionOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasStandardEtaleSurjectionOn (f : S) : Prop
参数：f : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate "there exists a standard etale algebra `A` over `R` that surjects 
onto `S[1/f]`".
We shall show if `S` is `R`-unramified at `Q` then there exists `f ∉ Q` satisfyi
ng it.
-/
def HasStandardEtaleSurjectionOn (f : S) : Prop :=
  ∃ (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] Localization.Away f), Function.Surjective φ
/-
**HasStandardEtaleSurjectionOn.mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasStandardEtaleSurjectionOn.mk [IsStandardEtale R A] {Sf : Type*} [CommRi
ng Sf] [Algebra R Sf] [Algebra S Sf] [IsScalarTower R S Sf] {f : S} [IsLocalizat
ion.Away f Sf] (φ : A ->ₐ[R] Sf) (H : Function.Surjective φ) : HasStandardEtaleS
urjectionOn R f
参数：φ : A ->ₐ[R] Sf；H : Function.Surjective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsStandardEtale.nonempty_standardEtalePresentation`：∀ {R : Type 
u_4} {S : Type u_5} {inst : CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra 
R S}   [self : Algebra.IsStandardEtale R S], Non…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma HasStandardEtaleSurjectionOn.mk [IsStandardEtale R A]
    {Sf : Type*} [CommRing Sf] [Algebra R Sf] [Algebra S Sf] [IsScalarTower R S Sf]
    {f : S} [IsLocalization.Away f Sf] (φ : A →ₐ[R] Sf) (H : Function.Surjective φ) :
    HasStandardEtaleSurjectionOn R f :=
  let P : StandardEtalePresentation R A := Nonempty.some inferInstance
  ⟨P.P, (((IsLocalization.algEquiv (.powers f) (Localization.Away f) Sf).restrictScalars R)
    |>.symm.toAlgHom).comp (φ.comp P.equivRing.symm.toAlgHom), by simpa⟩
/-
**HasStandardEtaleSurjectionOn.of_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasStandardEtaleSurjectionOn.of_dvd {f g : S} (H : HasStandardEtaleSurject
ionOn R f) (h : f ∣ g) : HasStandardEtaleSurjectionOn R g
参数：H : HasStandardEtaleSurjectionOn R f；h : f ∣ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.Away.mul'`：mul' (T : Type*) [CommSemiring T] [Algebra S T
] [Algebra R T] [IsScalarTower R S T] (x y : R) [IsLocalization.Away x S] [IsLoc
alization.Away…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.IsStandardEtale.of_isLocalizationAway`：∀ {R : Type u_1} {S : Typ
e u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algeb
ra.IsStandardEtale R S] {Sₛ : Type …
· 使用定理 `Algebra.instIsStandardEtaleRing`：∀ {R : Type u_1} [inst : CommRing R] (P
 : StandardEtalePair R), Algebra.IsStandardEtale R P.Ring
· 使用引理 `HasStandardEtaleSurjectionOn.mk`：HasStandardEtaleSurjectionOn.mk [IsStan
dardEtale R A] {Sf : Type*} [CommRing Sf] [Algebra R Sf] [Algebra S Sf] [IsScala
rTower R S Sf] {f : S…
· 使用引理 `IsLocalization.Away.mapₐ_surjective_of_surjective`：mapₐ_surjective_of_su
rjective {f : A ->ₐ[R] B} (a : A) [Away a Aₚ] [Away (f a) Bₚ] (hf : Function.Sur
jective f) : Function.Surjective (mapₐ …
-/
lemma HasStandardEtaleSurjectionOn.of_dvd
    {f g : S} (H : HasStandardEtaleSurjectionOn R f) (h : f ∣ g) :
    HasStandardEtaleSurjectionOn R g := by
  obtain ⟨P, φ, hsurj⟩ := H
  obtain ⟨g, rfl⟩ := h
  obtain ⟨a, ha⟩ := hsurj (algebraMap _ _ g)
  have : IsLocalization.Away (f * g) (Localization.Away (φ a)) :=
    ha ▸ .mul' (Localization.Away f) _ _ _
  have : IsStandardEtale R (Localization.Away a) := .of_isLocalizationAway a
  exact .mk _ (IsLocalization.Away.mapₐ_surjective_of_surjective
    (Aₚ := Localization.Away a) (Bₚ := Localization.Away (φ a)) a hsurj)
/-
**HasStandardEtaleSurjectionOn.isStandardEtale** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasStandardEtaleSurjectionOn.isStandardEtale {f : S} (H : HasStandardEtale
SurjectionOn R f) [Etale R (Localization.Away f)] : IsStandardEtale R (Localizat
ion.Away f)
参数：H : HasStandardEtaleSurjectionOn R f；Localization.Away f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsStandardEtale.of_surjective`：∀ {R : Type u_1} {S : Type u_2} {
T : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   
[inst_3 : Algebra R S] [ins…
· 使用定理 `Algebra.instIsStandardEtaleRing`：∀ {R : Type u_1} [inst : CommRing R] (P
 : StandardEtalePair R), Algebra.IsStandardEtale R P.Ring
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma HasStandardEtaleSurjectionOn.isStandardEtale
    {f : S} (H : HasStandardEtaleSurjectionOn R f) [Etale R (Localization.Away f)] :
    IsStandardEtale R (Localization.Away f) :=
  .of_surjective _ H.choose_spec.choose_spec

namespace Algebra.IsUnramifiedAt

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_si
ngleton_eq_top_aux** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsUnramifiedAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top_aux₁
    (P : Ideal R) [P.IsPrime] (x : S) (hx : R[x] = ⊤) :
    (RingHom.ker (aeval (R := R) x).toRingHom).map (mapRingHom (algebraMap R P.ResidueField)) =
      RingHom.ker (aeval (1 ⊗ₜ x : P.Fiber S)).toRingHom := by
  have hx' : Function.Surjective (aeval (R := R) x) :=
    (AlgHom.range_eq_top _).mp ((adjoin_singleton_eq_range_aeval R x).symm.trans hx)
  let I := RingHom.ker (aeval (R := R) x).toRingHom
  let e : P.Fiber S ≃ₐ[P.ResidueField]
      P.ResidueField[X] ⧸ I.map (mapRingHom (algebraMap _ P.ResidueField)) :=
    Polynomial.fiberEquivQuotient (aeval (R := R) x) hx' _
  rw [← RingHom.ker_comp_of_injective _ (f := e.toRingHom) e.injective]
  convert! Ideal.mk_ker.symm
  ext a
  · dsimp [-TensorProduct.algebraMap_apply]
    rw [aeval_C, AlgEquiv.commutes]
    simp [← Ideal.Quotient.mk_algebraMap, I]
  · simpa [e] using! Polynomial.fiberEquivQuotient_tmul _ hx' P 1 X

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-
**Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_si
ngleton_eq_top_aux** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsUnramifiedAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top_aux₂
    {P : Ideal R} [P.IsPrime] {Q : Ideal S} [Q.IsPrime]
    [Q.LiesOver P] [IsUnramifiedAt R Q] (x : S) (p : R[X])
    [Algebra (Localization.AtPrime P) (Localization.AtPrime Q)]
    [Localization.AtPrime.IsLiesOverAlgebra P Q]
    (hp₁ : Ideal.span {p.map (algebraMap R P.ResidueField)} =
      RingHom.ker (aeval ((1 : P.ResidueField) ⊗ₜ[R] x)).toRingHom)
    (hp₂ : R[x] = ⊤) :
    ¬ minpoly P.ResidueField (algebraMap S Q.ResidueField x) ^ 2 ∣
      p.map (algebraMap R P.ResidueField) := by
  let Q' : Ideal (P.Fiber S) :=
    (PrimeSpectrum.primesOverOrderIsoFiber R S P ⟨Q, ‹_›, ‹_›⟩).asIdeal
  have : Q'.LiesOver Q := ⟨congr($((PrimeSpectrum.primesOverOrderIsoFiber R S P).symm_apply_apply
    ⟨Q, ‹_›, ‹_›⟩).1).symm⟩
  have : Q'.LiesOver P := .trans _ Q _
  let := Localization.AtPrime.algebraOfLiesOver Q Q'
  let := Localization.AtPrime.algebraOfLiesOver P Q'
  have : IsUnramifiedAt P.ResidueField Q' := .residueField P Q _ (Q'.over_def Q)
  have : Function.Surjective (aeval (R := P.ResidueField) ((1 : P.ResidueField) ⊗ₜ[R] x)) := by
    rw [← AlgHom.range_eq_top, ← adjoin_singleton_eq_range_aeval]
    simpa using TensorProduct.adjoin_one_tmul_image_eq_top (A := P.ResidueField) _ hp₂
  convert! IsUnramifiedAt.not_minpoly_sq_dvd (A := P.Fiber S) Q' (1 ⊗ₜ x) _ hp₁ this
  rw [← minpoly.algHom_eq _
    (IsScalarTower.toAlgHom P.ResidueField Q.ResidueField Q'.ResidueField).injective]
  congr 1
  · apply algebra_ext; intros r; congr 1; ext x; simp [← IsScalarTower.algebraMap_apply]
  · simp [← TensorProduct.right_algebraMap_apply, ← IsScalarTower.algebraMap_apply]

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] aeval_algebraMap_apply in
-- Subsumed by `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`.
/-
**Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_si
ngleton_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsUnramifiedAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top
    [Module.Finite R S] (H : ∃ x : S, R[x] = ⊤)
    (Q : Ideal S) [Q.IsPrime] [IsUnramifiedAt R Q] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionOn R f := by
  cases subsingleton_or_nontrivial S
  · cases Ideal.IsPrime.ne_top' (Subsingleton.elim Q ⊤)
  have := (algebraMap R S).domain_nontrivial
  -- Suppose `S = R[X]/I` is finite (as an `R`-module), and `R`-unramified at a prime `Q`,
  -- which lies over the prime `P` of `R`.
  -- We shall show that `S[1/f]` has a surjection from a standard etale algebra for some `f ∉ Q`.
  let P := Q.under R
  let := Localization.AtPrime.algebraOfLiesOver P Q
  obtain ⟨x, hx⟩ := H
  have hRx : IsIntegral R x := IsIntegral.isIntegral _
  let I := RingHom.ker (aeval (R := R) x).toRingHom
  have hx' : Function.Surjective (aeval (R := R) x) :=
    (AlgHom.range_eq_top _).mp ((adjoin_singleton_eq_range_aeval R x).symm.trans hx)
  -- It suffices to find some monic `q : R[X]` such that `q(x) = 0` and `q'(x) ∉ Q`.
  suffices ∃ q : R[X], q.Monic ∧ aeval x q = 0 ∧ aeval x q.derivative ∉ Q by
    -- Since if we have such a `q`, then `(R[X]/q)[1/q'] → S[1/q'(x)]` is the desired surjection.
    obtain ⟨q, hq, hqx, hq'x⟩ := this
    let P : StandardEtalePair R := ⟨q, hq, q.derivative, 1, 0, 1, by simp⟩
    have hP : P.HasMap (algebraMap _ (Localization.Away (aeval x q.derivative)) x) :=
      ⟨by simp_all [P], by simpa using IsLocalization.Away.algebraMap_isUnit _⟩
    let f : AdjoinRoot P.f →ₐ[R] S := AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) x hqx
    have : IsLocalization.Away (aeval x (derivative q)) (Localization.Away (f (.mk P.f P.g))) := by
      simp only [AdjoinRoot.liftAlgHom_mk, toRingHom_ofId, f, ← aeval_def, P]; infer_instance
    refine ⟨_, hq'x, .mk ((Localization.awayMapₐ f _).comp P.equivAwayAdjoinRoot.toAlgHom) ?_⟩
    simpa using IsLocalization.Away.mapₐ_surjective_of_surjective _
      (Ideal.Quotient.lift_surjective_of_surjective _ _ hx')
  -- Using the fact that `κ(P)[X]` is a PID, the image of `I` in `κ(P)[X]`
  -- (i.e. the kernel of `κ(P)[X] → κ(P) ⊗[R] S`) is generated by a single polynomial `p ∈ I`.
  obtain ⟨p, hpI, hp⟩ := Ideal.exists_mem_span_singleton_map_residueField_eq P I
  have hI' : I.map (mapRingHom (algebraMap R P.ResidueField)) =
      RingHom.ker (aeval (1 ⊗ₜ x : P.Fiber S)).toRingHom :=
    exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top_aux₁ P x hx
  -- Let `x` denote the image of `X` in `S`,
  -- and let `m` be the minimal polynomial of `x` (viewed as an element of `κ(Q)`) over `κ(P)`.
  -- By unramified-ness we know that `m` divides `p` only once.
  -- (via `Algebra.IsUnramifiedAt.not_minpoly_sq_dvd`).
  let m := minpoly P.ResidueField (algebraMap S Q.ResidueField x)
  have hm : Prime m := minpoly.prime (IsIntegral.isIntegral _)
  have hmp₁ : m ∣ p.map (algebraMap _ _) := by simp_all [m, I, minpoly.dvd_iff]
  have hmp₂ : ¬ m ^ 2 ∣ p.map (algebraMap _ _) :=
    exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top_aux₂ x p (hp.trans hI') hx
  -- But the issue is that `p` is not necessarily monic.
  -- Let `q := M + p` for some monic `M ∈ I` with large enough degree (since `S` is `R`-finite).
  -- I claim that `q` satisfies the desired properties.
  let q := minpoly R x ^ (p.natDegree + 2) + p
  refine ⟨q, ?_, by simpa [q], ?_⟩
  · refine ((minpoly.monic hRx).pow _).add_of_left (degree_lt_degree ?_)
    grw [natDegree_pow' (by simp [minpoly.monic hRx]),
      ← Nat.le_mul_of_pos_right _ (minpoly.natDegree_pos hRx)]; lia
  -- To show that `q'(x) ∉ Q`, we first show that `m` still divides `q` only once in `κ(P)[X]`.
  have ⟨w, h₁, h₂⟩ : ∃ w, q.map (algebraMap R _) = p.map (algebraMap R _) * w ∧ ¬ m ∣ w := by
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp
      (hp.ge (Ideal.mem_map_of_mem _ (x := minpoly R x) (by simp [I])))
    refine ⟨1 + w * (minpoly R x).map (algebraMap R P.ResidueField) ^ (p.natDegree + 1), ?_, ?_⟩
    · simp_all [q]
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
      the new canonicalizer; a minimization would help. The original proof was:
      `simp_all [q]; grind` -/
      ring
    · rw [dvd_add_left (dvd_mul_of_dvd_right (dvd_pow (by simp [m, minpoly.dvd_iff]) (by simp)) _),
        ← isUnit_iff_dvd_one]
      exact hm.not_isUnit
  have hm' : derivative m ≠ 0 :=
    (separable_iff_derivative_ne_zero hm.irreducible).mp (IsSeparable.isSeparable ..)
  suffices ¬m ∣ derivative (q.map (algebraMap R _)) by
    rwa [← Ideal.ker_algebraMap_residueField Q, RingHom.mem_ker, ← aeval_algebraMap_apply,
      ← aeval_map_algebraMap P.ResidueField, ← derivative_map, ← minpoly.dvd_iff]
  obtain ⟨c, hc⟩ := hmp₁
  simp_all [hm.dvd_mul, dvd_add_left, pow_two, mul_dvd_mul_iff_left, hm.ne_zero]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.IsUnramifiedAt.exists_notMem_forall_ne_mem_and_adjoin_eq_top** 是 Mathl
ib 中的一个引理，位于命名空间 `Algebra.IsUnramifiedAt`。
形式化陈述：exists_notMem_forall_ne_mem_and_adjoin_eq_top (Q : Ideal S) [Q.IsPrime] [M
odule.Finite R S] [IsUnramifiedAt R Q] [Algebra (Localization.AtPrime (Q.under R
)) (Localization.AtPrime Q)] [Localization.AtPrime.IsLiesOverAlgebra (Q.under R)
 Q] : exists t ∉ Q, (forall Q' in (Q.under R).primesOver S, Q' != Q -> t in Q') 
∧ adjoin (Ideal.under R Q).ResidueField {algebraMap _ Q.ResidueField t} = ⊤
参数：Q : Ideal S；Localization.AtPrime (Q.under R)；Localization.AtPrime Q；Q.under R
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsArtinianRing.of_finite`：IsArtinianRing.of_finite (R S) [Ring R] [Ring 
S] [Module R S] [IsScalarTower R S S] [IsArtinianRing R] [Module.Finite R S] : I
sArtinianRing …
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Field.exists_primitive_element`：exists_primitive_element : exists α : E,
 F⟮α⟯ = ⊤
· 使用定理 `Algebra.instFiniteResidueFieldOfQuasiFiniteAt`：∀ {R : Type u_1} {S : Typ
e u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ide
al R)   [inst_3 : p.IsPrime] (P : I…
· 使用定理 `Algebra.QuasiFinite.instLocalization`：∀ {R : Type u_1} {S : Type u_2} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (M : Submonoid S)
   [Algebra.QuasiFinite R …
· 使用定理 `Algebra.QuasiFinite.instOfFinite`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Finite R S], 
  Algebra.QuasiFinite …
· 使用定理 `Algebra.instIsSeparableResidueFieldOfIsUnramifiedAt`：∀ (R : Type u_1) {S
 : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   
[Algebra.EssFiniteType R S] (p : Ideal R)…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.adjoin_singleton_one`：adjoin_singleton_one : R[1 : A]= ⊥
· 使用定理 `Algebra.adjoin_singleton_zero`：adjoin_singleton_zero : R[0 : A] = ⊥
· 使用定理 `IntermediateField.adjoin_eq_top_iff`：adjoin_eq_top_iff [Algebra.IsAlgebr
aic F E] {S : Set E} : adjoin F S = ⊤ ↔ Algebra.adjoin F S = ⊤
· 使用定理 `instIsAlgebraicResidueFieldOfIsIntegral`：∀ {A : Type u_2} {B : Type u_3}
 [inst : CommRing A] [inst_1 : CommRing B] [inst_2 : Algebra A B] (p : Ideal A) 
  (q : Ideal B) [inst_3 : q.L…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsLocalRing.ResidueField.instIsScalarTower`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst_3
 : IsLocalRing S] [inst_4 : Alge…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
（共 83 条，此处仅展示前 30 条）
-/
lemma exists_notMem_forall_ne_mem_and_adjoin_eq_top
    (Q : Ideal S) [Q.IsPrime] [Module.Finite R S] [IsUnramifiedAt R Q]
    [Algebra (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q)]
    [Localization.AtPrime.IsLiesOverAlgebra (Q.under R) Q] :
    ∃ t ∉ Q, (∀ Q' ∈ (Q.under R).primesOver S, Q' ≠ Q → t ∈ Q') ∧
      adjoin (Ideal.under R Q).ResidueField {algebraMap _ Q.ResidueField t} = ⊤ := by
  let p := Q.under R
  #adaptation_note /-- Needed after nightly-2023-02-23 -/
  have : p.IsPrime := Ideal.IsPrime.under R Q
  #adaptation_note /-- After nightly-2026-04-06, typeclass synthesis fails to find these
  instances; provide them explicitly. -/
  let : Module p.ResidueField (p.Fiber S) := TensorProduct.leftModule
  let : SMul p.ResidueField (p.Fiber S) := this.toSMul -- added for #13807 (2026-05-20)
  let : IsScalarTower p.ResidueField (p.Fiber S) (p.Fiber S) := IsScalarTower.right
  let : Module.Finite p.ResidueField (p.Fiber S) := Module.Finite.base_change R p.ResidueField S
  have : IsArtinianRing (p.Fiber S) := .of_finite p.ResidueField _
  let α := PrimeSpectrum.primesOverOrderIsoFiber R S p
  obtain ⟨x, hx0, hx⟩ : ∃ x : Q.ResidueField, x ≠ 0 ∧ p.ResidueField[x] = ⊤ := by
    obtain ⟨x, hx⟩ := Field.exists_primitive_element p.ResidueField Q.ResidueField
    rw [IntermediateField.adjoin_eq_top_iff] at hx
    by_cases hx0 : x = 0
    · exact ⟨1, by simp, by simpa [p, hx0] using hx⟩
    · exact ⟨x, hx0, hx⟩
  obtain ⟨x, rfl⟩ := Ideal.Fiber.lift_residueField_surjective p _ x
  set φ : p.Fiber S →ₐ[p.ResidueField] Q.ResidueField := TensorProduct.lift
      (Algebra.ofId _ _) (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
  obtain ⟨r, hrQ, hrid, hr⟩ :=
    IsArtinianRing.exists_not_mem_forall_mem_of_ne (α ⟨Q, ‹_›, ⟨rfl⟩⟩).asIdeal
  obtain ⟨s, hsQ, t, e⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ (r * x)
  have hrQ' : φ r ≠ 0 := by
    have : Ideal.ResidueField.mapₐ p Q (ofId R S) (Ideal.over_def Q p) =
      AlgHom.restrictScalars R (ofId p.ResidueField Q.ResidueField) := by ext
    rw [← AlgHom.restrictScalars_apply R, Algebra.TensorProduct.restrictScalars_lift]
    convert! hrQ
    rw [← SetLike.mem_coe, PrimeSpectrum.coe_primesOverOrderIsoFiber_apply_asIdeal]
    simp [this]
  have hsQ' : algebraMap R Q.ResidueField s ≠ 0 := by
    simpa [IsScalarTower.algebraMap_apply R S Q.ResidueField]
  replace hrQ' : φ r = 1 := by
    simpa [hrQ', sub_eq_zero, @eq_comm _ _ (φ r)] using (hrid.map φ).one_sub_mul_self
  have e' : algebraMap _ _ s * φ x = algebraMap _ _ t := by
    simpa [φ, smul_def, mul_assoc, hrQ'] using congr(φ $e)
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [← Ideal.algebraMap_residueField_eq_zero, ← e']
    simpa [hx0, IsScalarTower.algebraMap_apply R S Q.ResidueField]
  · rintro Q' ⟨_, _⟩ H
    let := Localization.AtPrime.algebraOfLiesOver p Q'
    have hsQ'' : algebraMap R Q'.ResidueField s ≠ 0 := by
      suffices s ∉ Q'.under _ by simpa [IsScalarTower.algebraMap_apply R S Q'.ResidueField]
      rwa [← Q'.over_def p]
    let φ' : p.Fiber S →ₐ[p.ResidueField] Q'.ResidueField := TensorProduct.lift
        (Algebra.ofId _ _) (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
    have H : φ' r = 0 := (hr (α ⟨Q', ⟨‹_›, ‹_›⟩⟩).asIdeal inferInstance (by
        rwa [ne_eq, ← PrimeSpectrum.ext_iff, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]) :)
    rw [← Ideal.algebraMap_residueField_eq_zero]
    trans φ' (1 ⊗ₜ t)
    · simp [φ']
    · simpa [smul_def, H] using congr(φ' $e).symm
  · have : φ x = (algebraMap _ p.ResidueField s)⁻¹ • algebraMap _ _ t := by
      simpa [smul_def, ← IsScalarTower.algebraMap_apply, eq_inv_mul_iff_mul_eq₀ hsQ']
    rw [← top_le_iff, ← hx, this]
    refine adjoin_singleton_le ?_
    exact Subalgebra.smul_mem _ (self_mem_adjoin_singleton _ _) _

attribute [-instance] Subalgebra.instSMulSubtypeMem
  Subalgebra.toAlgebra Subalgebra.isScalarTower_left in
/-- Let `S` be an finite `R`-algebra that is unramified at some prime `Q`. Then there exists some
`x : S` such that `Q` is the unique prime lying over `P := Q ∩ R⟨x⟩` and `κ(P) = κ(Q)`. -/
/-
**Algebra.IsUnramifiedAt.exists_primesOver_under_adjoin_eq_singleton_and_residue
Field_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsUnramifiedAt`。
形式化陈述：exists_primesOver_under_adjoin_eq_singleton_and_residueField_bijective (Q 
: Ideal S) [Q.IsPrime] [Module.Finite R S] [Algebra.IsUnramifiedAt R Q] : exists
 x : S, (Q.under (R[x])).primesOver S = {Q} ∧ letI
参数：Q : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用引理 `Algebra.IsUnramifiedAt.exists_notMem_forall_ne_mem_and_adjoin_eq_top`：ex
ists_notMem_forall_ne_mem_and_adjoin_eq_top (Q : Ideal S) [Q.IsPrime] [Module.Fi
nite R S] [IsUnramifiedAt R Q] [Algebra (Localization.AtPr…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ideal.LiesOver.trans`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type
 u_3} [inst_1 : CommSemiring B] {C : Type u_4} [inst_2 : Semiring C]   [inst_3 :
 Algebra A…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsLocalRing.ResidueField.instIsScalarTower_1`：∀ {R : Type u_1} {S : Type
 u_2} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst
_3 : IsLocalRing S] [inst_4 : Alge…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra_1`：∀ {A : Type
 u_4} {B : Type u_5} {C : Type u_6} [inst : CommSemiring A] [inst_1 : CommSemiri
ng B] [inst_2 : Algebra A B]   [inst_3 : CommSemi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.range_eq_top`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Co
mmSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring 
B] [inst_…
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Algebra.adjoin_singleton_le`：adjoin_singleton_le {S : Subalgebra R A} {a
 : A} (H : a in S) : R[a] <= S
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用定理 `IsScalarTower.coe_toAlgHom`：coe_toAlgHom : ↑(toAlgHom R S A) = algebraMa
p S A
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Let `S` be an finite `R`-algebra that is unramified at some prime `Q`. Then ther
e exists some
`x : S` such that `Q` is the unique prime lying over `P := Q ∩ R⟨x⟩` and `κ(P) =
 κ(Q)`.
-/
lemma exists_primesOver_under_adjoin_eq_singleton_and_residueField_bijective
    (Q : Ideal S) [Q.IsPrime] [Module.Finite R S] [Algebra.IsUnramifiedAt R Q] :
    ∃ x : S, (Q.under (R[x])).primesOver S = {Q} ∧
      letI := Localization.AtPrime.algebraOfLiesOver (Q.under R[x]) Q
      Function.Bijective (algebraMap (Q.under (R[x])).ResidueField
        Q.ResidueField) := by
  let := Localization.AtPrime.algebraOfLiesOver (Q.under R) Q
  obtain ⟨t, htQ, htQ', ht⟩ :=
    IsUnramifiedAt.exists_notMem_forall_ne_mem_and_adjoin_eq_top (R := R) Q
  let p := Q.under R
  let := Localization.AtPrime.algebraOfLiesOver p (Q.under R[t])
  let := Localization.AtPrime.algebraOfLiesOver (Q.under R[t]) Q
  refine ⟨t, ?_, RingHom.injective _, ?_⟩
  · refine Set.ext fun Q' ↦ ⟨fun ⟨_, _⟩ ↦ ?_, fun e ↦ by exact ⟨e ▸ inferInstance, ⟨e ▸ rfl⟩⟩⟩
    by_contra! H
    have : Q'.LiesOver p := .trans _ (Q.under (R[t])) _
    exact htQ (SetLike.le_def.mp (Q'.over_def (Q.under (R[t]))).ge
      (x := ⟨t, self_mem_adjoin_singleton _ _⟩) (htQ' Q' ⟨‹_›, ‹_›⟩ H))
  · change Function.Surjective (IsScalarTower.toAlgHom p.ResidueField _ _)
    rw [← AlgHom.range_eq_top, ← top_le_iff, ← ht]
    refine adjoin_singleton_le ?_
    use algebraMap (R[t]) _ ⟨t, self_mem_adjoin_singleton _ _⟩
    rw [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom, ← IsScalarTower.algebraMap_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
-- Subsumed by `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`.
/-
**Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn_of_finite** 是 Mathl
ib 中的一个引理，位于命名空间 `Algebra.IsUnramifiedAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_hasStandardEtaleSurjectionOn_of_finite
    (Q : Ideal S) [Q.IsPrime] [Module.Finite R S] [IsUnramifiedAt R Q] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionOn R f := by
  obtain ⟨x, hQ', hQ'Q⟩ :=
    exists_primesOver_under_adjoin_eq_singleton_and_residueField_bijective (R := R) Q
  let S' := R[x]
  let Q' := Q.under S'
  let := Localization.AtPrime.algebraOfLiesOver Q' Q
  have : Module.Finite S' S := .of_restrictScalars_finite R _ _
  have : IsUnramifiedAt S' Q := .of_restrictScalars R _
  have hφ : Function.Bijective (Localization.localRingHom Q' Q S'.val rfl) :=
    ⟨Localization.localRingHom_injective_of_primesOver_eq_singleton hQ',
      Localization.localRingHom_surjective_of_primesOver_eq_singleton hQ' hQ'Q.2⟩
  obtain ⟨r, hrQ', H⟩ := Localization.exists_awayMap_bijective_of_residueField_surjective hQ' hQ'Q.2
  have : Module.Finite R S' := finite_adjoin_simple_of_isIntegral (IsIntegral.isIntegral _)
  have : IsUnramifiedAt R Q' := .of_equiv <| .symm <| .ofBijective (IsScalarTower.toAlgHom _ _ _) hφ
  obtain ⟨f, hfQ', hf⟩ :=
    IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top
    (R := R) (S := S') ⟨⟨x, self_mem_adjoin_singleton _ _⟩, Subalgebra.map_injective
      (f := S'.val) Subtype.val_injective (by simp [Subalgebra.range_val, S'])⟩ Q'
  obtain ⟨P, φ, hP⟩ := hf.of_dvd (g := f * r) (by simp)
  exact ⟨_, (inferInstance : Q'.IsPrime).mul_notMem hfQ' hrQ', .mk
    (f := IsScalarTower.toAlgHom R S' S (f * r))
    ((Localization.awayMapₐ (IsScalarTower.toAlgHom _ _ S) (f * r)).comp φ)
    (by exact (H _ (by simp)).surjective.comp hP)⟩

attribute [local instance high] Module.Free.of_divisionRing in
/-
**Algebra.IsUnramifiedAt.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsUnramifiedAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low)
    [EssFiniteType R S] [FormallyUnramified R S] : QuasiFinite R S where
  finite_fiber _ _ := FormallyUnramified.finite_of_free _ _
/-
**Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn** 是 Mathlib 中的一个引理，
位于命名空间 `Algebra.IsUnramifiedAt`。
形式化陈述：exists_hasStandardEtaleSurjectionOn (Q : Ideal S) [Q.IsPrime] [FiniteType 
R S] [IsUnramifiedAt R Q] : exists f ∉ Q, HasStandardEtaleSurjectionOn R f
参数：Q : Ideal S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bij
ective`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S
] [inst_2 : Algebra R S]   [Algebra.FiniteType R S] (p : Ideal S),  …
· 使用定理 `Algebra.ZariskisMainProperty.of_finiteType`：∀ {R : Type u} {S : Type v} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Algebra.Finite
Type R S]   (p : Ideal S) [inst_…
· 使用定理 `Algebra.QuasiFinite.instLocalization`：∀ {R : Type u_1} {S : Type u_2} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (M : Submonoid S)
   [Algebra.QuasiFinite R …
· 使用定理 `Algebra.IsUnramifiedAt.instQuasiFiniteOfEssFiniteTypeOfFormallyUnramifie
d`：∀ {R : Type u_1} {S : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [in
st_2 : Algebra R S]   [Algebra.EssFiniteType R S] [Algebra.Form…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.fg_top`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (N : Submodule R M), ⊤.F
G ↔ N.…
· 使用定理 `Algebra.FormallyUnramified.of_equiv`：of_equiv [FormallyUnramified R A] (
e : A ≃ₐ[R] B) : FormallyUnramified R B
· 使用定理 `Algebra.FormallyUnramified.instLocalization`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra
.FormallyUnramified R S] (M : Sub…
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.basicOpen_subset_unramifiedLocus_iff`：basicOpen_subset_unramifie
dLocus_iff {f : A} : ↑(PrimeSpectrum.basicOpen f) subseteq unramifiedLocus R A ↔
 Algebra.FormallyUnramified R (Loc…
· 使用定理 `_private.Mathlib.RingTheory.Unramified.LocalStructure.0.Algebra.IsUnrami
fiedAt.exists_hasStandardEtaleSurjectionOn_of_finite`：∀ {R : Type u_1} {S : Type
 u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (Q : Idea
l S)   [inst_3 : Q.IsPrime] [Modul…
· 使用引理 `Localization.awayMap_bijective_of_dvd`：awayMap_bijective_of_dvd {R : Typ
e*} [CommRing R] (f : R ->+* S) {a b : R} (h : a ∣ b) (H : Function.Bijective (a
wayMap f a)) : Function.Bij…
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用引理 `HasStandardEtaleSurjectionOn.of_dvd`：HasStandardEtaleSurjectionOn.of_dvd
 {f g : S} (H : HasStandardEtaleSurjectionOn R f) (h : f ∣ g) : HasStandardEtale
SurjectionOn R g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.IsPrime.mul_notMem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x ∉ I → y ∉ I → x * y ∉ I
· 使用引理 `HasStandardEtaleSurjectionOn.mk`：HasStandardEtaleSurjectionOn.mk [IsStan
dardEtale R A] {Sf : Type*} [CommRing Sf] [Algebra R Sf] [Algebra S Sf] [IsScala
rTower R S Sf] {f : S…
· 使用定理 `Algebra.instIsStandardEtaleRing`：∀ {R : Type u_1} [inst : CommRing R] (P
 : StandardEtalePair R), Algebra.IsStandardEtale R P.Ring
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
（共 51 条，此处仅展示前 30 条）
-/
lemma exists_hasStandardEtaleSurjectionOn
    (Q : Ideal S) [Q.IsPrime] [FiniteType R S] [IsUnramifiedAt R Q] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionOn R f := by
  wlog H : Unramified R S
  · obtain ⟨s, hsQ, hs⟩ := exists_formallyUnramified_of_isUnramifiedAt (R := R) Q
    have hQ : (Ideal.map (algebraMap S (Localization.Away s)) Q).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (.powers s) _ _ ‹_› (by simp [Set.disjoint_iff,
        Set.ext_iff, Submonoid.mem_powers_iff, mt (‹Q.IsPrime›.mem_of_pow_mem _) hsQ])
    have inst : Unramified R (Localization.Away s) := {}
    obtain ⟨f, hf, H⟩ := this (R := R)
      (Q.map (algebraMap _ (Localization.Away s))) inferInstance
    obtain ⟨f, t, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) f
    refine ⟨s * f, ?_, ?_⟩
    · simpa [IsLocalization.mk'_mem_map_algebraMap_iff, Submonoid.mem_powers_iff,
        Ideal.IsPrime.mul_mem_left_iff, hsQ, (mt (‹Q.IsPrime›.mem_of_pow_mem _) hsQ)] using hf
    obtain ⟨P, φ, hφ⟩ : HasStandardEtaleSurjectionOn R (algebraMap S (Localization.Away s) f) :=
      H.of_dvd ⟨algebraMap _ _ t.1, by simp⟩
    exact .mk _ hφ
  obtain ⟨S', hS', r, hrQ, hr⟩ := ZariskisMainProperty.of_finiteType (R := R) Q
    |>.exists_fg_and_exists_notMem_and_awayMap_bijective
  have : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : FormallyUnramified R (Localization.Away r) :=
    .of_equiv (AlgEquiv.ofBijective (Localization.awayMapₐ S'.val r) hr :).symm
  have : IsUnramifiedAt R (Ideal.under (↥S') Q) := by
    rw [← basicOpen_subset_unramifiedLocus_iff] at this
    exact @this ⟨Q.under S', inferInstance⟩ hrQ
  obtain ⟨f, hfQ, hf⟩ :=
    IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn_of_finite (R := R) (Q.under S')
  let e : Localization.Away (r * f) ≃ₐ[R] Localization.Away (r.1 * f.1) :=
    .ofBijective (Localization.awayMapₐ S'.val (r * f))
      (Localization.awayMap_bijective_of_dvd _ (dvd_mul_right r f) hr)
  obtain ⟨P, φ, hφ⟩ := hf.of_dvd (g := r * f) (by simp)
  refine ⟨_, ‹Q.IsPrime›.mul_notMem hrQ hfQ,
    .mk (f := r.1 * f.1) (e.toAlgHom.comp φ) (e.surjective.comp hφ)⟩

end IsUnramifiedAt

@[stacks 00UE]
/-
**Algebra.IsEtaleAt.exists_isStandardEtale** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Is
EtaleAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (Q : Ideal S)   [inst_3 : Q.IsPrime] [Algebra.FinitePrese
ntation R S] [Algebra.IsEtaleAt R Q],   ∃ f ∉ Q, Algebra.IsStandardEtale R (Loca
lization.Away f)
参数：Q : Ideal S；Localization.Away f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.exists_etale_of_isEtaleAt`：exists_etale_of_isEtaleAt (P : Ideal 
A) [P.IsPrime] [IsEtaleAt R P] : exists f ∉ P, Algebra.Etale R (Localization.Awa
y f)
· 使用引理 `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`：exists_hasSt
andardEtaleSurjectionOn (Q : Ideal S) [Q.IsPrime] [FiniteType R S] [IsUnramified
At R Q] : exists f ∉ Q, HasStandardEtaleSurjecti…
· 使用定理 `Algebra.FormallyEtale.instFormallyUnramified`：∀ {R : Type u} {A : Type v
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Fo
rmallyEtale R A], Algebra.Formally…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.basicOpen_subset_etaleLocus_iff_etale`：basicOpen_subset_etaleLoc
us_iff_etale {f : A} : ↑(PrimeSpectrum.basicOpen f) subseteq etaleLocus R A ↔ Al
gebra.Etale R (Localization.Away f)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `PrimeSpectrum.basicOpen_mul_le_left`：basicOpen_mul_le_left (f g : R) : b
asicOpen (f * g) <= basicOpen f
· 使用定理 `Ideal.IsPrime.mul_notMem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x ∉ I → y ∉ I → x * y ∉ I
· 使用引理 `HasStandardEtaleSurjectionOn.isStandardEtale`：HasStandardEtaleSurjection
On.isStandardEtale {f : S} (H : HasStandardEtaleSurjectionOn R f) [Etale R (Loca
lization.Away f)] : IsStandardEtal…
· 使用引理 `HasStandardEtaleSurjectionOn.of_dvd`：HasStandardEtaleSurjectionOn.of_dvd
 {f g : S} (H : HasStandardEtaleSurjectionOn R f) (h : f ∣ g) : HasStandardEtale
SurjectionOn R g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma IsEtaleAt.exists_isStandardEtale
    (Q : Ideal S) [Q.IsPrime] [FinitePresentation R S] [IsEtaleAt R Q] :
    ∃ f, f ∉ Q ∧ IsStandardEtale R (Localization.Away f) := by
  obtain ⟨f, hfQ, h⟩ := exists_etale_of_isEtaleAt (R := R) Q
  obtain ⟨g, hgQ, hg⟩ := IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := R) Q
  have : Etale R (Localization.Away (f * g)) := by
    rw [← basicOpen_subset_etaleLocus_iff_etale] at h ⊢
    exact .trans (PrimeSpectrum.basicOpen_mul_le_left _ _) h
  exact ⟨f * g, ‹Q.IsPrime›.mul_notMem hfQ hgQ, (hg.of_dvd (by simp)).isStandardEtale⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `S` a finitely presented `R`-algebra, and `p` a prime of `S`. If `S` is smooth over `R`
at `p`, then there exists `f ∉ p` such that `R → S[1/f]` factors through some `R[X₁,...,Xₙ]`,
and that `S[1/f]` is standard etale over `R[X₁,...,Xₙ]`. -/
/-
**Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra.IsSmoothAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] {p : Ideal S}   [inst_3 : p.IsPrime] [Algebra.FinitePrese
ntation R S] [Algebra.IsSmoothAt R p],   ∃ f ∉ p,     ∃ n x,       IsScalarTower
 R (MvPolynomial (Fin n) R) (Localization.Away f) ∧         Algebra.IsStandardEt
ale (MvPolynomial (Fin n) R) (Localization.Away f)
参数：MvPolynomial (Fin n) R；Localization.Away f；MvPolynomial (Fin n) R；Localizatio
n.Away f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`：∀ (R : Type u_1) {S :
 Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [A
lgebra.FinitePresentation R S] (p : Ide…
· 使用定理 `RingHom.IsStandardSmooth.exists_etale_mvPolynomial`：∀ {R : Type u} {S : 
Type v} [inst : CommRing R] [inst_1 : CommRing S] {f : R →+* S},   f.IsStandardS
mooth → ∃ n g, g.comp MvPolynomial.C = f…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.isPrime_of_isPrime_disjoint`：isPrime_of_isPrime_disjoint 
(I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) : (Ideal.map (alge
braMap R S) I).IsPrime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.disjoint_powers_iff_notMem_of_isPrime`：disjoint_powers_iff_notMem_
of_isPrime [I.IsPrime] (y : R) : Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ 
I
· 使用定理 `Algebra.IsEtaleAt.exists_isStandardEtale`：∀ {R : Type u_1} {S : Type u_3
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (Q : Ideal S)
   [inst_3 : Q.IsPrime] [Algeb…
· 使用定理 `Algebra.Etale.finitePresentation`：∀ {R : Type u} {A : Type v} {inst : Co
mmRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A
],   Algebra.FinitePre…
· 使用定理 `RingHom.Etale.toAlgebra`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRin
g R] [inst_1 : CommRing S] {f : R →+* S}, f.Etale → Algebra.Etale R S
· 使用定理 `Algebra.FormallyEtale.instLocalization`：∀ {R : Type u_2} {S : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.Form
allyEtale R S] (M : Submonoi…
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Ideal.IsPrime.mem_of_pow_mem`：∀ {α : Type u} [inst : Semiring α] {I : Id
eal α}, I.IsPrime → ∀ {r : α} (n : ℕ), r ^ n ∈ I → r ∈ I
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `IsLocalization.Away.of_associated`：of_associated {r r' : R} (h : Associa
ted r r') [IsLocalization.Away r S] : IsLocalization.Away r' S
· 使用引理 `IsLocalization.Away.algebraMap_pow_isUnit`：algebraMap_pow_isUnit (n : Na
t) : IsUnit (algebraMap R S x ^ n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Given `S` a finitely presented `R`-algebra, and `p` a prime of `S`. If `S` is sm
ooth over `R`
at `p`, then there exists `f ∉ p` such that `R → S[1/f]` factors through some `R
[X₁,...,Xₙ]`,
and that `S[1/f]` is standard etale over `R[X₁,...,Xₙ]`.
-/
theorem IsSmoothAt.exists_isStandardEtale_mvPolynomial
    {p : Ideal S} [p.IsPrime] [FinitePresentation R S] [IsSmoothAt R p] :
    ∃ f ∉ p, ∃ (n : ℕ) (_ : Algebra (MvPolynomial (Fin n) R) (Localization.Away f)),
      IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away f) ∧
      IsStandardEtale (MvPolynomial (Fin n) R) (Localization.Away f) := by
  obtain ⟨f, hfp, H⟩ := IsSmoothAt.exists_notMem_isStandardSmooth R p
  obtain ⟨n, φ, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (f := algebraMap R (Localization.Away f)) (by simpa [RingHom.isStandardSmooth_algebraMap])
  algebraize [φ]
  have := IsScalarTower.of_algebraMap_eq' hgC.symm
  have : (Ideal.map (algebraMap S (Localization.Away f)) p).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_›
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hfp)
  obtain ⟨g₀, hg, H⟩ := IsEtaleAt.exists_isStandardEtale (R := (MvPolynomial (Fin n) R))
    (S := (Localization.Away f)) (p.map (algebraMap _ _))
  obtain ⟨g, ⟨_, m, rfl⟩, hg₀⟩ := IsLocalization.exists_mk'_eq (.powers f) g₀
  replace hg : g ∉ p := by simpa [Submonoid.mem_powers_iff, Ideal.IsPrime.mul_mem_iff_mem_or_mem,
    IsLocalization.mk'_mem_map_algebraMap_iff, mt (‹p.IsPrime›.mem_of_pow_mem _) hfp,
    ← hg₀] using hg
  have : IsLocalization.Away (f * g) (Localization.Away g₀) := by
    suffices IsLocalization.Away (algebraMap _ (Localization.Away f) g) (Localization.Away g₀) from
      .mul' (Localization.Away f) _ _ _
    refine IsLocalization.Away.of_associated (r := g₀)
      ⟨(IsLocalization.Away.algebraMap_pow_isUnit f m).unit, ?_⟩
    simp only [← hg₀, IsUnit.unit_spec, ← map_pow, mul_comm, IsLocalization.mk'_spec'_mk]
  let e : Localization.Away g₀ ≃ₐ[S] Localization.Away (f * g) :=
    IsLocalization.algEquiv (.powers (f * g)) _ _
  let : Algebra (MvPolynomial (Fin n) R) (Localization.Away (f * g)) :=
    (e.toRingHom.comp (algebraMap (MvPolynomial (Fin n) R) _)).toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away (f * g)) := by
    refine .of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    exact (e.toAlgHom.comp_algebraMap_of_tower (R := R)).symm
  let e' : Localization.Away g₀ ≃ₐ[MvPolynomial (Fin n) R] Localization.Away (f * g) :=
    { __ := e, commutes' r := rfl }
  exact ⟨f * g, ‹p.IsPrime›.mul_notMem ‹_› ‹_›, n, ‹_›, ‹_›, .of_equiv e'⟩

end Algebra

