/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Support

/-!
# Smooth locus of an algebra

Most results in this file are proved for algebras of finite presentations.
Some of them are true for arbitrary algebras but the proof is substantially harder.

## Main results
- `Algebra.smoothLocus` : The set of primes that are smooth over the base.
- `Algebra.basicOpen_subset_smoothLocus_iff` :
  `D(f)` is contained in the smooth locus if and only if `A_f` is smooth over `R`.
- `Algebra.smoothLocus_eq_univ_iff` :
  The smooth locus is the whole spectrum if and only if `A` is smooth over `R`.
- `Algebra.isOpen_smoothLocus` : The smooth locus is open.
-/

@[expose] public section

universe u

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

namespace Algebra

variable {A} in
/--
An `R`-algebra `A` is smooth at a prime `p` of `A` if `Aₚ` is formally smooth over `R`.

This does not imply `Aₚ` is smooth over `R` under the mathlib definition
even if `A` is finitely presented,
but it can be shown that this is equivalent to the stacks project definition that `A` is smooth
at `p` if and only if there exists `f ∉ p` such that `A_f` is smooth over `R`.
See `Algebra.basicOpen_subset_smoothLocus_iff_smooth` and `Algebra.isOpen_smoothLocus`.
-/
@[stacks 00TB]
/-
**Algebra.IsSmoothAt** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：IsSmoothAt (p : Ideal A) [p.IsPrime] : Prop
参数：p : Ideal A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-algebra `A` is smooth at a prime `p` of `A` if `Aₚ` is formally smooth ov
er `R`.

This does not imply `Aₚ` is smooth over `R` under the mathlib definition
even if `A` is finitely presented,
but it can be shown that this is equivalent to the stacks project definition tha
t `A` is smooth
at `p` if and only if there exists `f ∉ p` such that `A_f` is smooth over `R`.
See `Algebra.basicOpen_subset_smoothLocus_iff_smooth` and `Algebra.isOpen_smooth
Locus`.
-/
abbrev IsSmoothAt (p : Ideal A) [p.IsPrime] : Prop :=
  Algebra.FormallySmooth R (Localization.AtPrime p)

/-- `Algebra.smoothLocus R A` is the set of primes `p` of `A`
such that `Aₚ` is formally smooth over `R`. -/
/-
**Algebra.smoothLocus** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：smoothLocus : Set (PrimeSpectrum A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Algebra.smoothLocus R A` is the set of primes `p` of `A`
such that `Aₚ` is formally smooth over `R`.
-/
def smoothLocus : Set (PrimeSpectrum A) := { p | IsSmoothAt R p.asIdeal }

variable {R A}

attribute [local instance] Module.finitePresentation_of_projective in
/-
**Algebra.smoothLocus_eq_compl_support_inter** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`
。
形式化陈述：smoothLocus_eq_compl_support_inter [EssFiniteType R A] : smoothLocus R A =
 (Module.support A (H1Cotangent R A))ᶜ inter Module.freeLocus A Ω[A⁄R]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Algebra.formallySmooth_iff`：∀ (R : Type u) (A : Type v) [inst : CommRing
 R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.FormallySmooth R A ↔
 Module.Projecti…
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.H1Cotangent.isLocalizedModule`：∀ (R : Type u_1) {S : Type u_2} (
T : Type u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   
[inst_3 : Algebra R S] [ins…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `Algebra.EssFiniteType.of_isLocalization`：∀ {R : Type u_1} (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (M : Submonoid
 R)   [IsLocalization M S], A…
· 使用定理 `Algebra.EssFiniteType.comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type u_
3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 : A
lgebra R S] [ins…
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Module.Free.of_equiv'`：of_equiv' {P : Type v} [AddCommMonoid P] [Module 
R P] (_ : Module.Free R P) (e : P ≃ₗ[R] N) : Module.Free R N
-/
lemma smoothLocus_eq_compl_support_inter [EssFiniteType R A] :
    smoothLocus R A = (Module.support A (H1Cotangent R A))ᶜ ∩ Module.freeLocus A Ω[A⁄R] := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Module.notMem_support_iff,
    Module.mem_freeLocus]
  refine (Algebra.formallySmooth_iff _ _).trans (and_comm.trans ?_)
  congr! 1
  · have := IsLocalizedModule.iso p.asIdeal.primeCompl
      (H1Cotangent.map R R A (Localization.AtPrime p.asIdeal))
    exact this.subsingleton_congr.symm
  · trans Module.Free (Localization.AtPrime p.asIdeal) Ω[Localization.AtPrime p.asIdeal⁄R]
    · have : EssFiniteType A (Localization.AtPrime p.asIdeal) :=
        .of_isLocalization _ p.asIdeal.primeCompl
      have : EssFiniteType R (Localization.AtPrime p.asIdeal) := .comp _ A _
      exact ⟨fun _ ↦ Module.free_of_flat_of_isLocalRing, fun _ ↦ inferInstance⟩
    · have := IsLocalizedModule.iso p.asIdeal.primeCompl
        (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
      have := this.extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      exact ⟨fun H ↦ H.of_equiv' this.symm, fun H ↦ H.of_equiv' this⟩
/-
**Algebra.basicOpen_subset_smoothLocus_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：basicOpen_subset_smoothLocus_iff [FinitePresentation R A] {f : A} : ↑(Prim
eSpectrum.basicOpen f) subseteq smoothLocus R A ↔ Algebra.FormallySmooth R (Loca
lization.Away f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.smoothLocus_eq_compl_support_inter`：smoothLocus_eq_compl_support
_inter [EssFiniteType R A] : smoothLocus R A = (Module.support A (H1Cotangent R 
A))ᶜ inter Module.freeLocus A Ω[…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LocalizedModule.subsingleton_iff_support_subset`：LocalizedModule.subsing
leton_iff_support_subset {f : R} : Subsingleton (LocalizedModule.Away f M) ↔ Mod
ule.support R M subseteq PrimeSpectru…
· 使用定理 `Algebra.formallySmooth_iff`：∀ (R : Type u) (A : Type v) [inst : CommRing
 R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.FormallySmooth R A ↔
 Module.Projecti…
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.H1Cotangent.isLocalizedModule`：∀ (R : Type u_1) {S : Type u_2} (
T : Type u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   
[inst_3 : Algebra R S] [ins…
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `Module.basicOpen_subset_freeLocus_iff`：basicOpen_subset_freeLocus_iff [M
odule.FinitePresentation R M] {f : R} : (basicOpen f : Set (PrimeSpectrum R)) su
bseteq freeLocus R M ↔ Modu…
· 使用定理 `Algebra.instFinitePresentationKaehlerDifferentialOfFinitePresentation`：∀
 {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : A
lgebra R S]   [Algebra.FinitePresentation R S], Module.Fini…
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Module.Projective.of_equiv`：∀ {R : Type u_8} {S : Type u_9} [inst : Semi
ring R] [inst_1 : Semiring S] {M : Type u_10} {N : Type u_11}   [inst_2 : AddCom
mMonoid M] [inst…
-/
lemma basicOpen_subset_smoothLocus_iff [FinitePresentation R A] {f : A} :
    ↑(PrimeSpectrum.basicOpen f) ⊆ smoothLocus R A ↔
      Algebra.FormallySmooth R (Localization.Away f) := by
  rw [smoothLocus_eq_compl_support_inter, Set.subset_inter_iff, Set.subset_compl_comm,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl,
    ← LocalizedModule.subsingleton_iff_support_subset,
    Algebra.formallySmooth_iff, iff_comm, and_comm]
  congr! 1
  · have := IsLocalizedModule.iso (.powers f) (H1Cotangent.map R R A (Localization.Away f))
    rw [this.subsingleton_congr]
  · rw [← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Module.basicOpen_subset_freeLocus_iff]
    have := IsLocalizedModule.iso (.powers f)
        (KaehlerDifferential.map R R A (Localization.Away f))
    have := this.extendScalarsOfIsLocalization (.powers f) (Localization.Away f)
    exact ⟨fun _ ↦ .of_equiv this.symm, fun _ ↦ .of_equiv this⟩
/-
**Algebra.basicOpen_subset_smoothLocus_iff_smooth** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebra`。
形式化陈述：basicOpen_subset_smoothLocus_iff_smooth [FinitePresentation R A] {f : A} :
 ↑(PrimeSpectrum.basicOpen f) subseteq smoothLocus R A ↔ Algebra.Smooth R (Local
ization.Away f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.Away.finitePresentation`：IsLocalization.Away.finitePresen
tation (r : R) {S} [CommRing S] [Algebra R S] [IsLocalization.Away r S] : Algebr
a.FinitePresentation R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.basicOpen_subset_smoothLocus_iff`：basicOpen_subset_smoothLocus_i
ff [FinitePresentation R A] {f : A} : ↑(PrimeSpectrum.basicOpen f) subseteq smoo
thLocus R A ↔ Algebra.Formally…
· 使用定理 `Algebra.FinitePresentation.trans`：trans [Algebra A B] [IsScalarTower R A
 B] [FinitePresentation R A] [FinitePresentation A B] : FinitePresentation R B
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
-/
lemma basicOpen_subset_smoothLocus_iff_smooth [FinitePresentation R A] {f : A} :
    ↑(PrimeSpectrum.basicOpen f) ⊆ smoothLocus R A ↔
      Algebra.Smooth R (Localization.Away f) := by
  have : FinitePresentation A (Localization.Away f) := IsLocalization.Away.finitePresentation f
  rw [basicOpen_subset_smoothLocus_iff]
  exact ⟨fun H ↦ ⟨H, .trans _ A _⟩, fun H ↦ H.1⟩
/-
**Algebra.smoothLocus_eq_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：smoothLocus_eq_univ_iff [FinitePresentation R A] : smoothLocus R A = Set.u
niv ↔ Algebra.FormallySmooth R A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submonoid.powers_one`：powers_one : powers (1 : M) = ⊥
· 使用定理 `Algebra.FormallySmooth.iff_of_equiv`：∀ {R : Type u_4} [inst : CommRing R
] {A : Type u_5} {B : Type u_6} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [
inst_3 : CommRing B] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.basicOpen_subset_smoothLocus_iff`：basicOpen_subset_smoothLocus_i
ff [FinitePresentation R A] {f : A} : ↑(PrimeSpectrum.basicOpen f) subseteq smoo
thLocus R A ↔ Algebra.Formally…
· 使用定理 `PrimeSpectrum.basicOpen_one`：basicOpen_one : basicOpen (1 : R) = ⊤
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smoothLocus_eq_univ_iff [FinitePresentation R A] :
    smoothLocus R A = Set.univ ↔ Algebra.FormallySmooth R A := by
  have := IsLocalization.atUnits A (.powers 1) (S := Localization.Away (1 : A)) (by simp)
  rw [Algebra.FormallySmooth.iff_of_equiv (this.restrictScalars R),
    ← basicOpen_subset_smoothLocus_iff]
  simp
/-
**Algebra.smoothLocus_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：smoothLocus_eq_univ [Smooth R A] : smoothLocus R A = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.smoothLocus_eq_univ_iff`：smoothLocus_eq_univ_iff [FinitePresenta
tion R A] : smoothLocus R A = Set.univ ↔ Algebra.FormallySmooth R A
· 使用定理 `Algebra.Smooth.finitePresentation`：∀ {R : Type u_4} {inst : CommRing R} 
{A : Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smoo
th R A], Algebra.Finite…
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
-/
lemma smoothLocus_eq_univ [Smooth R A] : smoothLocus R A = Set.univ := by
  rw [smoothLocus_eq_univ_iff]
  infer_instance
/-
**Algebra.smoothLocus_comap_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
`。
形式化陈述：smoothLocus_comap_of_isLocalization {Af : Type*} [CommRing Af] [Algebra A 
Af] [Algebra R Af] [IsScalarTower R A Af] (f : A) [IsLocalization.Away f Af] : P
rimeSpectrum.comap (algebraMap A Af) ⁻¹' smoothLocus R A = smoothLocus R Af
参数：f : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`：isL
ocalization_isLocalization_atPrime_isLocalization (p : Ideal S) [Hp : p.IsPrime]
 [IsLocalization.AtPrime T p] : IsLocalization.AtPrime T …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.FormallySmooth.iff_of_equiv`：∀ {R : Type u_4} [inst : CommRing R
] {A : Type u_5} {B : Type u_6} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [
inst_3 : CommRing B] [ins…
-/
lemma smoothLocus_comap_of_isLocalization {Af : Type*} [CommRing Af] [Algebra A Af] [Algebra R Af]
    [IsScalarTower R A Af] (f : A) [IsLocalization.Away f Af] :
    PrimeSpectrum.comap (algebraMap A Af) ⁻¹' smoothLocus R A = smoothLocus R Af := by
  ext p
  let q := PrimeSpectrum.comap (algebraMap A Af) p
  have : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal) q.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f) _ p.asIdeal
  refine Algebra.FormallySmooth.iff_of_equiv ?_
  exact (IsLocalization.algEquiv q.asIdeal.primeCompl _ _).restrictScalars R

-- Note that this does not follow directly from `smoothLocus_eq_compl_support_inter` because
-- `H¹(L_{S/R})` is not necessarily finitely generated.
open PrimeSpectrum in
/-
**Algebra.isOpen_smoothLocus** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：isOpen_smoothLocus [FinitePresentation R A] : IsOpen (smoothLocus R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_forall_mem_open`：isOpen_iff_forall_mem_open : IsOpen s ↔ fora
ll x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Algebra.smoothLocus_eq_compl_support_inter`：smoothLocus_eq_compl_support
_inter [EssFiniteType R A] : smoothLocus R A = (Module.support A (H1Cotangent R 
A))ᶜ inter Module.freeLocus A Ω[…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用引理 `Module.isOpen_freeLocus`：isOpen_freeLocus [Module.FinitePresentation R M
] : IsOpen (freeLocus R M)
· 使用定理 `Algebra.instFinitePresentationKaehlerDifferentialOfFinitePresentation`：∀
 {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : A
lgebra R S]   [Algebra.FinitePresentation R S], Module.Fini…
· 使用定理 `IsLocalization.Away.finitePresentation`：IsLocalization.Away.finitePresen
tation (r : R) {S} [CommRing S] [Algebra R S] [IsLocalization.Away r S] : Algebr
a.FinitePresentation R S
· 使用定理 `Algebra.FinitePresentation.trans`：trans [Algebra A B] [IsScalarTower R A
 B] [FinitePresentation R A] [FinitePresentation A B] : FinitePresentation R B
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Module.Projective.of_equiv`：∀ {R : Type u_8} {S : Type u_9} [inst : Semi
ring R] [inst_1 : Semiring S] {M : Type u_10} {N : Type u_11}   [inst_2 : AddCom
mMonoid M] [inst…
· 使用引理 `Module.basicOpen_subset_freeLocus_iff`：basicOpen_subset_freeLocus_iff [M
odule.FinitePresentation R M] {f : R} : (basicOpen f : Set (PrimeSpectrum R)) su
bseteq freeLocus R M ↔ Modu…
· 使用定理 `Algebra.instEssFiniteTypeLocalization`：∀ (R : Type u_1) (S : Type u_2) [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.EssFi
niteType R S] (M : Submonoi…
· 使用引理 `Module.support_eq_zeroLocus`：Module.support_eq_zeroLocus : Module.suppor
t R M = zeroLocus (Module.annihilator R M)
· 使用定理 `Algebra.instFiniteH1CotangentOfFinitePresentationOfProjectiveKaehlerDiff
erential`：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.FinitePresentation R S] [Module.Proj…
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `PrimeSpectrum.localization_away_isOpenEmbedding`：localization_away_isOpe
nEmbedding (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.A
way r S] : IsOpenEmbedding (comap (al…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.smoothLocus_comap_of_isLocalization`：smoothLocus_comap_of_isLoca
lization {Af : Type*} [CommRing Af] [Algebra A Af] [Algebra R Af] [IsScalarTower
 R A Af] (f : A) [IsLocalization.…
（共 33 条，此处仅展示前 30 条）
-/
lemma isOpen_smoothLocus [FinitePresentation R A] : IsOpen (smoothLocus R A) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open
    (smoothLocus_eq_compl_support_inter.le hx).2 Module.isOpen_freeLocus
  rw [Module.basicOpen_subset_freeLocus_iff] at hf
  let Af := Localization.Away f
  have : Algebra.FinitePresentation A (Localization.Away f) :=
    IsLocalization.Away.finitePresentation f
  have : Algebra.FinitePresentation R (Localization.Away f) :=
    .trans _ A _
  have : IsOpen (smoothLocus R Af) := by
    have := IsLocalizedModule.iso (.powers f)
      (KaehlerDifferential.map R R A (Localization.Away f))
    have := this.extendScalarsOfIsLocalization (.powers f) (Localization.Away f)
    have := Module.Projective.of_equiv this
    rw [smoothLocus_eq_compl_support_inter, Module.support_eq_zeroLocus]
    exact (isClosed_zeroLocus _).isOpen_compl.inter Module.isOpen_freeLocus
  rw [← smoothLocus_comap_of_isLocalization f] at this
  replace this := (PrimeSpectrum.localization_away_isOpenEmbedding Af f).isOpenMap _ this
  rw [Set.image_preimage_eq_inter_range, localization_away_comap_range Af f] at this
  exact ⟨_, Set.inter_subset_left, this, hx, hxf⟩

variable (R) in
open PrimeSpectrum in
/-
**Algebra.IsSmoothAt.exists_notMem_smooth** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsS
moothAt`。
形式化陈述：∀ (R : Type u_1) {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A] 
[inst_2 : Algebra R A]   [Algebra.FinitePresentation R A] (p : Ideal A) [inst_4 
: p.IsPrime] [Algebra.IsSmoothAt R p],   ∃ f ∉ p, Algebra.Smooth R (Localization
.Away f)
参数：R : Type u_1；p : Ideal A；Localization.Away f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用引理 `Algebra.isOpen_smoothLocus`：isOpen_smoothLocus [FinitePresentation R A] 
: IsOpen (smoothLocus R A)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用引理 `Algebra.basicOpen_subset_smoothLocus_iff`：basicOpen_subset_smoothLocus_i
ff [FinitePresentation R A] {f : A} : ↑(PrimeSpectrum.basicOpen f) subseteq smoo
thLocus R A ↔ Algebra.Formally…
· 使用定理 `instFinitePresentationAway`：∀ {R : Type u_1} [inst : CommRing R] {S : Ty
pe u_2} [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FinitePresentati
on R S] (f : S),…
-/
lemma IsSmoothAt.exists_notMem_smooth [FinitePresentation R A] (p : Ideal A) [p.IsPrime]
    [IsSmoothAt R p] :
    ∃ f ∉ p, Smooth R (Localization.Away f) := by
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open ‹⟨p, ‹_›⟩ ∈ smoothLocus R A› isOpen_smoothLocus
  refine ⟨f, by simpa using hxf, ⟨?_, inferInstance⟩⟩
  rwa [basicOpen_subset_smoothLocus_iff] at hf

end Algebra

