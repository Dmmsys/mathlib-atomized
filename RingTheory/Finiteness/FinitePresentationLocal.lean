/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Finiteness.FiniteTypeLocal
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!

# `Algebra.FinitePresentation` is local

In this file we show that being a finitely presented algebra is local.

## Main results

- `Algebra.FinitePresentation.of_span_eq_top_target`: finite presentation is local on the
  (algebraic) target

-/

public section

open scoped Pointwise TensorProduct

namespace Algebra.FinitePresentation

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/--
If `S` is an `R`-algebra with a surjection from a finitely-presented `R`-algebra `A`, such that
localized at a spanning set `{ r }` of elements of `A`, `Sᵣ` is finitely-presented, then
`S` is finitely presented.
This is almost `finitePresentation_ofLocalizationSpanTarget`. The difference is,
that here the set `t` generates the unit ideal of `A`, while in the general version,
it only generates a quotient of `A`.
-/
/-
**Algebra.FinitePresentation.of_span_eq_top_target_aux** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.FinitePresentation`。
形式化陈述：of_span_eq_top_target_aux {A : Type*} [CommRing A] [Algebra R A] [Algebra.
FinitePresentation R A] (f : A ->ₐ[R] S) (hf : Function.Surjective f) (t : Finse
t A) (ht : Ideal.span (t : Set A) = ⊤) (H : forall g : t, Algebra.FinitePresenta
tion R (Localization.Away (f g))) : Algebra.FinitePresentation R S
参数：f : A ->ₐ[R] S；hf : Function.Surjective f；t : Finset A；ht : Ideal.span (t : S
et A) = ⊤；H : forall g : t, Algebra.FinitePresentation R (Localization.Away (f g
))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.of_surjective`：of_surjective {f : A ->ₐ[R] B}
 (hf : Function.Surjective f) (hker : (RingHom.ker f.toRingHom).FG) [FinitePrese
ntation R A] : FinitePresentat…
· 使用引理 `RingHom.ker_fg_of_localizationSpan`：RingHom.ker_fg_of_localizationSpan (
t : Set R) (ht : Ideal.span t = ⊤) (H : forall g : t, (RingHom.ker (Localization
.awayMap f g.val)).FG) :…
· 使用定理 `Algebra.FinitePresentation.trans`：trans [Algebra A B] [IsScalarTower R A
 B] [FinitePresentation R A] [FinitePresentation A B] : FinitePresentation R B
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalization.Away.finitePresentation`：IsLocalization.Away.finitePresen
tation (r : R) {S} [CommRing S] [Algebra R S] [IsLocalization.Away r S] : Algebr
a.FinitePresentation R S
· 使用定理 `Algebra.FinitePresentation.ker_fG_of_surjective`：ker_fG_of_surjective (f
 : A ->ₐ[R] B) (hf : Function.Surjective f) [FinitePresentation R A] [FinitePres
entation R B] : (RingHom.ker f.toRing…
· 使用引理 `IsLocalization.Away.mapₐ_surjective_of_surjective`：mapₐ_surjective_of_su
rjective {f : A ->ₐ[R] B} (a : A) [Away a Aₚ] [Away (f a) Bₚ] (hf : Function.Sur
jective f) : Function.Surjective (mapₐ …

--- 原说明 ---
If `S` is an `R`-algebra with a surjection from a finitely-presented `R`-algebra
 `A`, such that
localized at a spanning set `{ r }` of elements of `A`, `Sᵣ` is finitely-present
ed, then
`S` is finitely presented.
This is almost `finitePresentation_ofLocalizationSpanTarget`. The difference is,
that here the set `t` generates the unit ideal of `A`, while in the general vers
ion,
it only generates a quotient of `A`.
-/
lemma of_span_eq_top_target_aux {A : Type*} [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (f : A →ₐ[R] S) (hf : Function.Surjective f)
    (t : Finset A) (ht : Ideal.span (t : Set A) = ⊤)
    (H : ∀ g : t, Algebra.FinitePresentation R (Localization.Away (f g))) :
    Algebra.FinitePresentation R S := by
  apply Algebra.FinitePresentation.of_surjective hf
  apply RingHom.ker_fg_of_localizationSpan t ht
  intro g
  let f' : Localization.Away g.val →ₐ[R] Localization.Away (f g) :=
    Localization.awayMapₐ f g.val
  have (g : t) : Algebra.FinitePresentation R (Localization.Away g.val) :=
    haveI : Algebra.FinitePresentation A (Localization.Away g.val) :=
      IsLocalization.Away.finitePresentation g.val
    Algebra.FinitePresentation.trans R A (Localization.Away g.val)
  apply Algebra.FinitePresentation.ker_fG_of_surjective f'
  exact IsLocalization.Away.mapₐ_surjective_of_surjective _ hf

universe u

set_option backward.isDefEq.respectTransparency.types false in
/-- Finite-presentation can be checked on a standard covering of the target. -/
/-
**Algebra.FinitePresentation.of_span_eq_top_target** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.FinitePresentation`。
形式化陈述：of_span_eq_top_target (s : Set S) (hs : Ideal.span (s : Set S) = ⊤) (h : f
orall i in s, Algebra.FinitePresentation R (Localization.Away i)) : Algebra.Fini
tePresentation R S
参数：s : Set S；hs : Ideal.span (s : Set S) = ⊤；h : forall i in s, Algebra.FinitePr
esentation R (Localization.Away i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_eq_top_iff_finite`：span_eq_top_iff_finite (s : Set α) : span 
s = ⊤ ↔ exists s' : Finset α, ↑s' subseteq s ∧ span (s' : Set α) = ⊤
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `Algebra.FiniteType.of_span_eq_top_target`：Algebra.FiniteType.of_span_eq_
top_target (s : Set S) (hs : Ideal.span (s : Set S) = ⊤) (h : forall x in s, Alg
ebra.FiniteType R (Localizatio…
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial''`：iff_quotient_mvPolynomia
l'' : FiniteType R S ↔ exists (n : Nat) (f : MvPolynomial (Fin n) R ->ₐ[R] S), S
urjective f
· 使用定理 `Finsupp.mem_span_iff_linearCombination`：mem_span_iff_linearCombination (
s : Set M) (x : M) : x in span R s ↔ exists l : s ->₀ R, linearCombination R (↑)
 l = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.linearCombination_apply_of_mem_supported`：linearCombination_appl
y_of_mem_supported {l : α ->₀ R} {s : Finset α} (hs : l in supported R R (↑s : S
et α)) : linearCombination R v l = s.s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.coe_attach`：coe_attach (s : Finset α) : (s.attach : Set s) = Set.
univ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
Finite-presentation can be checked on a standard covering of the target.
-/
lemma of_span_eq_top_target (s : Set S) (hs : Ideal.span (s : Set S) = ⊤)
    (h : ∀ i ∈ s, Algebra.FinitePresentation R (Localization.Away i)) :
    Algebra.FinitePresentation R S := by
  obtain ⟨s, h₁, hs⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  replace h (i : s) : Algebra.FinitePresentation R (Localization.Away i.val) := h i (h₁ i.property)
  classical
  /-
  We already know that `S` is of finite type over `R`, so we have a surjection
  `MvPolynomial (Fin n) R →ₐ[R] S`. To reason about the kernel, we want to check it on the stalks
  of preimages of `s`. But the preimages do not necessarily span `MvPolynomial (Fin n) R`, so
  we quotient out by an ideal and apply `finitePresentation_ofLocalizationSpanTarget_aux`.
  -/
  have hfintype : Algebra.FiniteType R S := by
    apply Algebra.FiniteType.of_span_eq_top_target s hs
    intro x hx
    have := h ⟨x, hx⟩
    infer_instance
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hfintype
  obtain ⟨l, hl⟩ := (Finsupp.mem_span_iff_linearCombination S (s : Set S) 1).mp
      (show (1 : S) ∈ Ideal.span (s : Set S) by rw [hs]; trivial)
  choose g' hg' using (fun g : s ↦ hf g)
  choose h' hh' using (fun g : s ↦ hf (l g))
  let I : Ideal (MvPolynomial (Fin n) R) := Ideal.span { ∑ g : s, g' g * h' g - 1 }
  let A := MvPolynomial (Fin n) R ⧸ I
  have hfI : ∀ a ∈ I, f a = 0 := by
    intro p hp
    simp only [Finset.univ_eq_attach, I, Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    simp only [map_mul, map_sub, map_sum, map_one, hg', hh']
    rw [Finsupp.linearCombination_apply_of_mem_supported (α := (s : Set S)) S (s := s.attach)] at hl
    · rw [← hl]
      simp only [Finset.coe_sort_coe, smul_eq_mul, mul_comm, sub_self, zero_mul]
    · rintro a -
      simp
  let f' : A →ₐ[R] S := Ideal.Quotient.liftₐ I f hfI
  have hf' : Function.Surjective f' :=
    Ideal.Quotient.lift_surjective_of_surjective I hfI hf
  let t : Finset A := Finset.image (fun g ↦ g' g) Finset.univ
  have ht : Ideal.span (t : Set A) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : ∑ g : { x // x ∈ s }, g' g * h' g = (1 : A) := by
      apply eq_of_sub_eq_zero
      rw [← map_one (Ideal.Quotient.mk I), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.subset_span
      simp
    simp_rw [← this, Finset.univ_eq_attach, map_sum, map_mul]
    refine Ideal.sum_mem _ (fun g _ ↦ Ideal.mul_mem_right _ _ <| Ideal.subset_span ?_)
    simp [t]
  have : Algebra.FinitePresentation R A := by
    apply Algebra.FinitePresentation.quotient
    simp only [Finset.univ_eq_attach, I]
    exact ⟨{∑ g ∈ s.attach, g' g * h' g - 1}, by simp⟩
  have Ht (g : t) : Algebra.FinitePresentation R (Localization.Away (f' g)) := by
    have : ∃ (a : S) (hb : a ∈ s), (Ideal.Quotient.mk I) (g' ⟨a, hb⟩) = g.val := by
      obtain ⟨g, hg⟩ := g
      convert! hg
      simp [A, t]
    obtain ⟨r, hr, hrr⟩ := this
    simp only [f']
    rw [← hrr, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    simp_rw +instances [RingHom.coe_coe]
    rw [hg']
    apply h
  exact of_span_eq_top_target_aux f' hf' t ht Ht

/-- Finite-presentation can be checked on a standard covering of the target. -/
/-
**Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway** 是 Mat
hlib 中的一个引理，位于命名空间 `Algebra.FinitePresentation`。
形式化陈述：of_span_eq_top_target_of_isLocalizationAway {ι : Type*} (s : ι -> S) (hs :
 Ideal.span (Set.range s) = ⊤) (T : ι -> Type*) [forall i, CommRing (T i)] [fora
ll i, Algebra R (T i)] [forall i, Algebra S (T i)] [forall i, IsScalarTower R S 
(T i)] [forall i, IsLocalization.Away (s i) (T i)] [forall i, Algebra.FinitePres
entation R (T i)] : Algebra.FinitePresentation R S
参数：s : ι -> S；hs : Ideal.span (Set.range s) = ⊤；T : ι -> Type*；T i；T i；T i；T i；s
 i；T i；T i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.FinitePresentation.of_span_eq_top_target`：of_span_eq_top_target 
(s : Set S) (hs : Ideal.span (s : Set S) = ⊤) (h : forall i in s, Algebra.Finite
Presentation R (Localization.Away i)) …
· 使用定理 `Algebra.FinitePresentation.equiv`：equiv [FinitePresentation R A] (e : A 
≃ₐ[R] B) : FinitePresentation R B
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Finite-presentation can be checked on a standard covering of the target.
-/
lemma of_span_eq_top_target_of_isLocalizationAway {ι : Type*} (s : ι → S)
    (hs : Ideal.span (Set.range s) = ⊤) (T : ι → Type*) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    [∀ i, Algebra S (T i)] [∀ i, IsScalarTower R S (T i)] [∀ i, IsLocalization.Away (s i) (T i)]
    [∀ i, Algebra.FinitePresentation R (T i)] :
    Algebra.FinitePresentation R S := by
  apply of_span_eq_top_target _ hs
  rintro - ⟨i, rfl⟩
  exact .equiv <| (IsLocalization.algEquiv (.powers <| s i) _ (T i)).symm |>.restrictScalars R
/-
**Algebra.FinitePresentation.pi** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FinitePresent
ation`。
形式化陈述：pi {ι : Type*} [Finite ι] (S : ι -> Type*) [forall i, CommRing (S i)] [for
all i, Algebra R (S i)] [forall i, Algebra.FinitePresentation R (S i)] : Algebra
.FinitePresentation R (forall a, S a)
参数：S : ι -> Type*；S i；S i；S i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.away_of_isIdempotentElem`：away_of_isIdempotentElem {R S} 
[CommRing R] [CommRing S] [Algebra R S] {e : R} (he : IsIdempotentElem e) (H : R
ingHom.ker (algebraMap R S) =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RingHom.ker_evalRingHom`：RingHom.ker_evalRingHom {ι : Type*} [DecidableE
q ι] (R : ι -> Type*) [forall i, CommRing (R i)] (i : ι) : RingHom.ker (Pi.evalR
ingHom R i) =…
· 使用定理 `RingHom.surjective`：RingHom.surjective (σ : R₁ ->+* R₂) [t : RingHomSurj
ective σ] : Function.Surjective σ
· 使用定理 `instRingHomSurjectiveForallEvalRingHom`：∀ {I : Type u} (f : I → Type u_1
) [inst : (i : I) → Semiring (f i)] (i : I), RingHomSurjective (Pi.evalRingHom f
 i)
· 使用引理 `Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway`：
of_span_eq_top_target_of_isLocalizationAway {ι : Type*} (s : ι -> S) (hs : Ideal
.span (Set.range s) = ⊤) (T : ι -> Type*) [forall i, CommRin…
· 使用引理 `Ideal.span_single_eq_top`：span_single_eq_top {ι : Type*} [DecidableEq ι]
 [Finite ι] (R : ι -> Type*) [forall i, Semiring (R i)] : Ideal.span (Set.range 
fun i => (Pi.s…
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
-/
instance pi {ι : Type*} [Finite ι] (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Algebra.FinitePresentation R (S i)] :
    Algebra.FinitePresentation R (∀ a, S a) := by
  classical
  let (i : ι) : Algebra (Π a, S a) (S i) := (Pi.evalAlgHom R S i).toAlgebra
  have (i : ι) : IsLocalization.Away (Pi.single i 1 : ∀ a, S a) (S i) := by
    refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom S i).surjective)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  exact Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway
    _ (Ideal.span_single_eq_top S) (fun i ↦ S i)

end Algebra.FinitePresentation

