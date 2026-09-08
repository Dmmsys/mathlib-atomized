/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Sihan Su, Yi Song, Christian Merten
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Krull dimension of polynomial ring

This file proves properties of the Krull dimension of the polynomial ring over a commutative ring

## Main results

* `Polynomial.ringKrullDim_le`: the Krull dimension of the polynomial ring over a commutative ring
  `R` is less than `2 * (ringKrullDim R) + 1`.

For noetherian rings:
* `Polynomial.ringKrullDim_of_isNoetherianRing`: the Krull dimension of `R[X]` is `dim R + 1`.
* `MvPolynomial.ringKrullDim_of_isNoetherianRing`: the Krull dimension of `R[X₁, ..., Xₙ]` is
  `dim R + n`.
-/

public section

/-
**Polynomial.ringKrullDim_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.ringKrullDim_le {R : Type*} [CommRing R] : ringKrullDim (Polyno
mial R) <= 2 * (ringKrullDim R) + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNoZeroDivisorsENat`：NoZeroDivisors ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ringKrullDim.eq_1`：∀ (R : Type u_1) [inst : CommSemiring R], ringKrullDi
m R = Order.krullDim (PrimeSpectrum R)
· 使用引理 `Order.krullDim_le_of_krullDim_preimage_le'`：krullDim_le_of_krullDim_prei
mage_le' (f : α -> β) (h_mono : Monotone f) (h : forall (x : β), Order.krullDim 
(f ⁻¹' {x}) <= m) : Order.krullD…
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `Order.krullDim_eq_of_orderIso`：krullDim_eq_of_orderIso (f : α ≃o β) : kr
ullDim α = krullDim β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ringKrullDim_eq_of_ringEquiv`：ringKrullDim_eq_of_ringEquiv (e : R ≃+* S)
 : ringKrullDim R = ringKrullDim S
· 使用引理 `Ring.krullDimLE_iff`：Ring.krullDimLE_iff {n : Nat} : KrullDimLE n R ↔ ri
ngKrullDim R <= n
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
-/
theorem Polynomial.ringKrullDim_le {R : Type*} [CommRing R] :
    ringKrullDim (Polynomial R) ≤ 2 * (ringKrullDim R) + 1 := by
  rw [ringKrullDim, ringKrullDim]
  apply Order.krullDim_le_of_krullDim_preimage_le' (PrimeSpectrum.comap C) ?_ (fun p ↦ ?_)
  · exact fun {a b} h ↦ Ideal.comap_mono h
  · rw [show C = (algebraMap R (Polynomial R)) from rfl, Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.preimageOrderIsoFiber R (Polynomial R) p), ← ringKrullDim,
      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,
      ← Ring.krullDimLE_iff]
    infer_instance

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

namespace Polynomial

open Ideal IsLocalization

/--
Let `p` be a maximal ideal of `A`. If `P` is a maximal ideal of `A[X]` lying above `p`,
then `ht(P) = ht(p) + 1`.
See `Polynomial.height_eq_height_add_one` for the more general version that does not assume `p` is
maximal.
-/
/-
**Polynomial.height_eq_height_add_one_of_isMaximal** 是 Mathlib 中的一个引理，位于命名空间 `Po
lynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `p` be a maximal ideal of `A`. If `P` is a maximal ideal of `A[X]` lying abo
ve `p`,
then `ht(P) = ht(p) + 1`.
See `Polynomial.height_eq_height_add_one` for the more general version that does
 not assume `p` is
maximal.
-/
private lemma height_eq_height_add_one_of_isMaximal (p : Ideal R) [p.IsMaximal] (P : Ideal R[X])
    [P.IsMaximal] [P.LiesOver p] : P.height = p.height + 1 := by
  let _ : Field (R ⧸ p) := Quotient.field p
  suffices h : (P.map (Ideal.Quotient.mk (Ideal.map (algebraMap R R[X]) p))).height = 1 by
    rw [height_eq_height_add_of_liesOver_of_hasGoingDown p, h]
  let e : (R[X] ⧸ (p.map (algebraMap R R[X]))) ≃+* (R ⧸ p)[X] :=
    (polynomialQuotientEquivQuotientPolynomial p).symm
  let P' : Ideal (R ⧸ p)[X] := Ideal.map e <| P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))
  have : (P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))).IsMaximal := by
    refine .map_of_surjective_of_ker_le Quotient.mk_surjective ?_
    rw [mk_ker, LiesOver.over (P := P) (p := p)]
    exact map_comap_le
  have : P'.IsMaximal := map_isMaximal_of_equiv e
  have : P'.height = 1 :=
    IsPrincipalIdealRing.height_eq_one_of_isMaximal P' (Polynomial.not_isField (R ⧸ p))
  rwa [← e.height_map <| P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))]

/-- Let `p` be a maximal ideal of `R`. Then the height of `p[X]` equals the height of `p`. -/
/-
**Polynomial.height_map_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：height_map_C (p : Ideal R) [p.IsMaximal] : (p.map C).height = p.height
参数：p : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`：Ideal.height_eq_
height_add_of_liesOver_of_hasGoingDown [IsNoetherianRing S] [Algebra.HasGoingDow
n R S] (p : Ideal R) [p.IsPrime] (P : Ideal …
· 使用定理 `Polynomial.isNoetherianRing`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsNoetherianRing R], IsNoetherianRing (Polynomial R)
· 使用定理 `Polynomial.instFree`：∀ {R : Type u_1} [inst : Semiring R], Module.Free R
 (Polynomial R)
· 使用定理 `Ideal.map_quotient_self`：map_quotient_self (I : Ideal R) [I.IsTwoSided] 
: map (Quotient.mk I) I = ⊥
· 使用引理 `Ideal.height_bot`：Ideal.height_bot [Nontrivial R] : (⊥ : Ideal R).height
 = 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Let `p` be a maximal ideal of `R`. Then the height of `p[X]` equals the height o
f `p`.
-/
lemma height_map_C (p : Ideal R) [p.IsMaximal] : (p.map C).height = p.height := by
  have : (p.map C).LiesOver p := ⟨IsMaximal.eq_of_le inferInstance IsPrime.ne_top' le_comap_map⟩
  simp [height_eq_height_add_of_liesOver_of_hasGoingDown p]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
/-- Let `p` be a prime ideal of `R`. If `P` is a maximal ideal of `R[X]` lying over `p`,
`ht(P) = ht(p) + 1`. -/
/-
**Polynomial.height_eq_height_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：height_eq_height_add_one (p : Ideal R) (P : Ideal R[X]) [P.IsMaximal] [P.L
iesOver p] : P.height = p.height + 1
参数：p : Ideal R；P : Ideal R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Polynomial.algebraMap_eq`：algebraMap_eq : algebraMap R R[X] = C
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
· 使用引理 `Polynomial.isLocalization`：isLocalization {R} [CommSemiring R] (S : Subm
onoid R) (A) [CommSemiring A] [Algebra R A] [IsLocalization S A] : IsLocalizatio
n (S.map C) A[X…
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.IsMaximal.of_isLocalization_of_disjoint`：Ideal.IsMaximal.of_isLoca
lization_of_disjoint [IsLocalization M S] {J : Ideal S} [(J.under R).IsMaximal] 
: J.IsMaximal
· 使用引理 `IsLocalization.liesOver_of_isPrime_of_disjoint`：IsLocalization.liesOver_
of_isPrime_of_disjoint {R' S' : Type*} (M : Submonoid R) (T : Submonoid S) [Comm
Semiring R'] [CommSemiring S'] [Alge…
· 使用定理 `instIsScalarTowerPolynomial`：∀ (R : Type u_1) (S : Type u_2) (A : Type u
_3) [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [i
nst_3 : Algebra R…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsLocalization.height_map_of_disjoint`：IsLocalization.height_map_of_disj
oint {S : Type*} [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M 
S] (p : Ideal R) [p.IsPrime…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `_private.Mathlib.RingTheory.KrullDimension.Polynomial.0.Polynomial.heigh
t_eq_height_add_one_of_isMaximal`：∀ {R : Type u_1} [inst : CommRing R] [IsNoethe
rianRing R] (p : Ideal R) [p.IsMaximal] (P : Ideal (Polynomial R))   [P.IsMaxima
l] [P.LiesOver…
· 使用定理 `IsLocalization.instIsNoetherianRingLocalization`：∀ {R : Type u_3} [inst 
: CommRing R] [IsNoetherianRing R] (S : Submonoid R), IsNoetherianRing (Localiza
tion S)

--- 原说明 ---
Let `p` be a prime ideal of `R`. If `P` is a maximal ideal of `R[X]` lying over 
`p`,
`ht(P) = ht(p) + 1`.
-/
lemma height_eq_height_add_one (p : Ideal R)
    (P : Ideal R[X]) [P.IsMaximal] [P.LiesOver p] :
    P.height = p.height + 1 := by
  have : p.IsPrime := by rw [P.over_def p]; infer_instance
  let Rₚ := Localization.AtPrime p
  set p' : Ideal Rₚ := p.map (algebraMap R Rₚ) with p'_def
  have : p'.IsMaximal := by
    rw [p'_def, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal.isMaximal Rₚ
  let P' : Ideal Rₚ[X] := P.map (algebraMap R[X] Rₚ[X])
  have disj : Disjoint (p.primeCompl.map C : Set R[X]) P := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha ↦ hb.1 ?_
    rwa [SetLike.mem_coe, LiesOver.over (P := P) (p := p), mem_comap, algebraMap_eq, hb.2]
  have eq := under_map_of_isPrime_disjoint _ Rₚ[X] ‹P.IsMaximal›.isPrime disj
  have : (P'.under R[X]).IsMaximal := eq.symm ▸ ‹P.IsMaximal›
  have : P'.IsMaximal := .of_isLocalization_of_disjoint (p.primeCompl.map C)
  have : P'.LiesOver p' := liesOver_of_isPrime_of_disjoint p.primeCompl _ _ disj
  have eq1 : p.height = p'.height := by
    rw [height_map_of_disjoint p.primeCompl]
    exact Disjoint.symm <| Set.disjoint_left.mpr fun _ a b ↦ b a
  have eq2 : P.height = P'.height := by
    rw [height_map_of_disjoint (Submonoid.map C <| p.primeCompl) _ disj]
  rw [eq1, eq2]
  apply height_eq_height_add_one_of_isMaximal p' P'

/-- If `R` is Noetherian, `dim R[X] = dim R + 1`. -/
@[simp]
/-
**Polynomial.ringKrullDim_of_isNoetherianRing** 是 Mathlib 中的一个引理，位于命名空间 `Polynom
ial`。
形式化陈述：ringKrullDim_of_isNoetherianRing : ringKrullDim R[X] = ringKrullDim R + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ringKrullDim_eq_bot_of_subsingleton`：ringKrullDim_eq_bot_of_subsingleton
 [Subsingleton R] : ringKrullDim R = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ringKrullDim_le_iff_isMaximal_height_le`：ringKrullDim_le_iff_isMaximal_h
eight_le {R : Type*} [CommRing R] (n : WithBot Nat∞) : ringKrullDim R <= n ↔ for
all ⦃m : Ideal R⦄, m.IsMaxima…
· 使用引理 `Polynomial.height_eq_height_add_one`：height_eq_height_add_one (p : Ideal
 R) (P : Ideal R[X]) [P.IsMaximal] [P.LiesOver p] : P.height = p.height + 1
· 使用定理 `WithBot.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用定理 `WithBot.coe_one`：∀ {α : Type u} [inst : One α], ↑1 = 1
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Ideal.height_le_ringKrullDim_of_ne_top`：Ideal.height_le_ringKrullDim_of_
ne_top {I : Ideal R} (h : I != ⊤) : I.height <= ringKrullDim R
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `ringKrullDim_succ_le_ringKrullDim_polynomial`：ringKrullDim_succ_le_ringK
rullDim_polynomial : ringKrullDim R + 1 <= ringKrullDim R[X]

--- 原说明 ---
If `R` is Noetherian, `dim R[X] = dim R + 1`.
-/
lemma ringKrullDim_of_isNoetherianRing : ringKrullDim R[X] = ringKrullDim R + 1 := by
  refine le_antisymm ?_ ?_
  · nontriviality R[X]
    refine (ringKrullDim_le_iff_isMaximal_height_le (ringKrullDim R + 1)).mpr fun M hM ↦ ?_
    rw [height_eq_height_add_one (M.under R) M, WithBot.coe_add, WithBot.coe_one]
    gcongr
    exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  · exact ringKrullDim_succ_le_ringKrullDim_polynomial

end Polynomial

/-- If `R` is Noetherian, `dim R[X₁, ..., Xₙ] = dim R + n`. -/
@[simp]
/-
**MvPolynomial.ringKrullDim_of_isNoetherianRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MvPolynomial.ringKrullDim_of_isNoetherianRing {ι : Type*} [Finite ι] : rin
gKrullDim (MvPolynomial ι R) = ringKrullDim R + Nat.card ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ringKrullDim_eq_of_ringEquiv`：ringKrullDim_eq_of_ringEquiv (e : R ≃+* S)
 : ringKrullDim R = ringKrullDim S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ringKrullDim_mvPolynomial_of_isEmpty`：ringKrullDim_mvPolynomial_of_isEmp
ty (σ : Type*) [IsEmpty σ] : ringKrullDim (MvPolynomial σ R) = ringKrullDim R
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fintype.card_option`：Fintype.card_option {α : Type*} [Fintype α] : Finty
pe.card (Option α) = Fintype.card α + 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Polynomial.ringKrullDim_of_isNoetherianRing`：ringKrullDim_of_isNoetheria
nRing : ringKrullDim R[X] = ringKrullDim R + 1
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `R` is Noetherian, `dim R[X₁, ..., Xₙ] = dim R + n`.
-/
lemma MvPolynomial.ringKrullDim_of_isNoetherianRing {ι : Type*} [Finite ι] :
    ringKrullDim (MvPolynomial ι R) = ringKrullDim R + Nat.card ι := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    convert! ← H using 1
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
    · rw [Nat.card_congr e]
  | h_empty => simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv,
      Polynomial.ringKrullDim_of_isNoetherianRing, IH]
