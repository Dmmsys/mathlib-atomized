/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Ideal.MonicSpan
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!

# Polynomial over Regular Ring

In this file we prove that the polynomial ring over a regular ring is regular.

## Main results

* `Polynomial.isRegularRing_of_isRegularRing` : the polynomial ring over a regular ring is
  a regular ring.

* `MvPolynomial.isRegularRing_of_isRegularRing` : the multivariate polynomial ring with finite
  variates over a regular ring is a regular ring.

-/

@[expose] public section

variable (R : Type*) [CommRing R]

open IsLocalRing Polynomial Ideal

/-
**Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal** 
是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdea
l [IsRegularLocalRing R] (p : Ideal R[X]) [p.IsPrime] (max : p.comap C = maximal
Ideal R) : IsRegularLocalRing (Localization.AtPrime p)
参数：p : Ideal R[X]；max : p.comap C = maximalIdeal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegularLocalRing.toIsLocalRing`：∀ {R : Type u_1} {inst : CommRing R} [
self : IsRegularLocalRing R], IsLocalRing R
· 使用引理 `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`：of_spanFinrank_maxima
lIdeal_le [IsLocalRing R] [IsNoetherianRing R] (le : (maximalIdeal R).spanFinran
k <= ringKrullDim R) : IsRegularLocalRi…
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `IsLocalization.instIsNoetherianRingLocalization`：∀ {R : Type u_3} [inst 
: CommRing R] [IsNoetherianRing R] (S : Submonoid R), IsNoetherianRing (Localiza
tion S)
· 使用定理 `Polynomial.isNoetherianRing`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsNoetherianRing R], IsNoetherianRing (Polynomial R)
· 使用定理 `IsRegularLocalRing.toIsNoetherian`：∀ {R : Type u_1} {inst : CommRing R} 
[self : IsRegularLocalRing R], IsNoetherian R R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isRegularLocalRing_iff`：isRegularLocalRing_iff [IsLocalRing R] [IsNoethe
rianRing R] : IsRegularLocalRing R ↔ (maximalIdeal R).spanFinrank = ringKrullDim
 R
· 使用引理 `Ideal.fg_of_isNoetherianRing`：Ideal.fg_of_isNoetherianRing {R : Type*} [
Semiring R] [IsNoetherianRing R] (I : Ideal R) : I.FG
· 使用定理 `Submodule.FG.finite_generators`：∀ {R : Type u_1} {M : Type u} [inst : Se
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, p.FG → p.ge…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Polynomial.height_map_C`：height_map_C (p : Ideal R) [p.IsMaximal] : (p.m
ap C).height = p.height
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Submodule.span_generators`：span_generators (p : Submodule R M) : span R 
(generators p) = p
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLocalization.height_under`：IsLocalization.height_under (S : Submonoid 
R) {A : Type*} [CommRing A] [Algebra R A] [IsLocalization S A] (J : Ideal A) : (
J.under R).height…
· 使用定理 `IsLocalization.AtPrime.under_maximalIdeal`：under_maximalIdeal (h : IsLoc
alRing S
（共 72 条，此处仅展示前 30 条）
-/
lemma Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal
    [IsRegularLocalRing R] (p : Ideal R[X]) [p.IsPrime] (max : p.comap C = maximalIdeal R) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  let q := (maximalIdeal R).map C
  have qle : q ≤ p := by simpa [q, ← max] using map_comap_le
  have reg := (isRegularLocalRing_iff R).mp ‹_›
  have fg' := (maximalIdeal R).fg_of_isNoetherianRing
  have fg := Submodule.FG.finite_generators fg'
  have ht : (maximalIdeal R).height ≤ q.height := le_of_eq (height_map_C (maximalIdeal R)).symm
  by_cases eq : p = q
  · have ht1 : (maximalIdeal R).height ≤ p.height := by simpa [eq]
    have : Ideal.span ((algebraMap R (Localization.AtPrime p)) '' (maximalIdeal R).generators) =
      maximalIdeal (Localization.AtPrime p) := by
      rw [IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime p), RingHom.coe_comp,
        Set.image_comp, ← Ideal.map_span, ← Ideal.map_span]
      simp only [Ideal.span, (maximalIdeal R).span_generators, algebraMap_eq, q, ← eq,
        Localization.AtPrime.map_eq_maximalIdeal]
    simp only [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_under p.primeCompl,
      IsLocalization.AtPrime.under_maximalIdeal _ p, ge_iff_le]
    apply le_trans _ (WithBot.coe_le_coe.mpr ht1)
    simp only [maximalIdeal_height_eq_ringKrullDim, ← reg, Nat.cast_le, ← this,
      ← Submodule.FG.generators_ncard fg']
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (fg.image _)).trans (Set.ncard_image_le fg)
  · have lt : q < p := lt_of_le_of_ne qle (Ne.symm eq)
    have : (comap C p).IsMaximal := by simpa [max] using maximalIdeal.isMaximal R
    obtain ⟨y, _, hy⟩ := Polynomial.exists_monic_span_sup_map_eq R p this (by simpa [max])
    have peq : p = Ideal.span (((algebraMap R R[X]) '' (maximalIdeal R).generators) ∪ {y}) := by
      simp only [Set.union_comm, Ideal.span_union, ← Ideal.map_span, algebraMap_eq, sup_comm]
      nth_rw 1 [hy, max, ← (maximalIdeal R).span_generators]
    simp only [← Localization.AtPrime.map_eq_maximalIdeal, peq, Ideal.map_span]
    rw [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_under p.primeCompl,
      IsLocalization.AtPrime.under_maximalIdeal _ p]
    apply le_trans _ (WithBot.coe_le_coe.mpr (Ideal.height_add_one_le_of_lt_of_isPrime lt))
    apply le_trans _ (WithBot.coe_le_coe.mpr (add_le_add_left ht 1))
    rw [WithBot.coe_add, maximalIdeal_height_eq_ringKrullDim, WithBot.coe_one, ← reg,
      ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    have fin := (fg.image (algebraMap R R[X])).union (Set.finite_singleton y)
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (fin.image _))
    apply le_trans (Set.ncard_image_le fin) (le_trans (Set.ncard_union_le _ _) _)
    rw [Set.ncard_singleton, add_le_add_iff_right, ← Submodule.FG.generators_ncard fg']
    exact Set.ncard_image_le fg
/-
**Polynomial.isRegularRing_of_isRegularRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Polynomial.isRegularRing_of_isRegularRing [IsRegularRing R] : IsRegularRin
g R[X]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isRegularRing_iff`：isRegularRing_iff [IsNoetherianRing R] : IsRegularRin
g R ↔ forall (p : Ideal R) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime
 p)
· 使用定理 `Polynomial.isNoetherianRing`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsNoetherianRing R], IsNoetherianRing (Polynomial R)
· 使用定理 `IsRegularRing.toIsNoetherian`：∀ {R : Type u_2} {inst : CommRing R} [self
 : IsRegularRing R], IsNoetherian R R
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用引理 `Polynomial.isLocalization`：isLocalization {R} [CommSemiring R] (S : Subm
onoid R) (A) [CommSemiring A] [Algebra R A] [IsLocalization S A] : IsLocalizatio
n (S.map C) A[X…
· 使用定理 `Set.disjoint_image_left`：disjoint_image_left {f : α -> β} {s : Set α} {t
 : Set β} : Disjoint (f '' s) t ↔ Disjoint s (f ⁻¹' t)
· 使用引理 `Set.disjoint_compl_left_iff_subset`：disjoint_compl_left_iff_subset : Dis
joint sᶜ t ↔ t subseteq s
· 使用定理 `IsLocalization.isPrime_of_isPrime_disjoint`：isPrime_of_isPrime_disjoint 
(I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) : (Ideal.map (alge
braMap R S) I).IsPrime
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
· 使用定理 `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`：isL
ocalization_isLocalization_atPrime_isLocalization (p : Ideal S) [Hp : p.IsPrime]
 [IsLocalization.AtPrime T p] : IsLocalization.AtPrime T …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.map_under`：map_under (J : Ideal S) : Ideal.map (algebraMa
p R S) (J.under R) = J
· 使用定理 `Polynomial.algebraMap_eq`：algebraMap_eq : algebraMap R R[X] = C
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `instIsScalarTowerPolynomial`：∀ (R : Type u_1) (S : Type u_2) (A : Type u
_3) [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [i
nst_3 : Algebra R…
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalization.AtPrime.under_maximalIdeal`：under_maximalIdeal (h : IsLoc
alRing S
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 32 条，此处仅展示前 30 条）
-/
instance Polynomial.isRegularRing_of_isRegularRing [IsRegularRing R] : IsRegularRing R[X] := by
  apply isRegularRing_iff.mpr (fun p hp ↦ ?_)
  let q := p.comap C
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let : Algebra R[X] S := algebra R (Localization.AtPrime q)
  have : IsLocalization pc S := Polynomial.isLocalization _ _
  let pS := p.map (algebraMap R[X] S)
  have disj : Disjoint (pc : Set R[X]) (p : Set R[X]) := by
    simpa [pc, q] using! Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj).symm
  have := isRegularRing_iff.mp ‹_› q
  have eq : comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_under q.primeCompl _ (comap C pS),
      ← IsLocalization.map_under q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X], ← comap_comap,
      ← Ideal.under_def R[X], IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj]
    simp [q, IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
  have := isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal _ pS eq
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv
/-
**MvPolynomial.isRegularRing_of_isRegularRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MvPolynomial.isRegularRing_of_isRegularRing [IsRegularRing R] {ι : Type*} 
[Finite ι] : IsRegularRing (MvPolynomial ι R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用引理 `IsRegularRing.of_ringEquiv`：IsRegularRing.of_ringEquiv {R' : Type*} [Com
mRing R'] (e : R ≃+* R') [IsRegularRing R] : IsRegularRing R'
-/
instance MvPolynomial.isRegularRing_of_isRegularRing [IsRegularRing R] {ι : Type*} [Finite ι] :
    IsRegularRing (MvPolynomial ι R) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H => exact IsRegularRing.of_ringEquiv (renameEquiv _ e).toRingEquiv
  | h_empty => exact IsRegularRing.of_ringEquiv (isEmptyRingEquiv R _).symm
  | h_option IH =>
    exact IsRegularRing.of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv.symm
