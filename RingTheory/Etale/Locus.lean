/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Etale locus of an algebra

## Main results
Let `A` be a `R`-algebra.
- `Algebra.etaleLocus` : The set of primes of `A` where it is étale over `R`.
- `Algebra.basicOpen_subset_etaleLocus_iff` :
  `D(f)` is contained in the etale locus if and only if `A_f` is formally etale over `R`.
- `Algebra.etaleLocus_eq_univ_iff` :
  The etale locus is the whole spectrum if and only if `A` is formally etale over `R`.
- `Algebra.isOpen_etaleLocus` :
  If `A` is of finite type over `R`, then the etale locus is open.
-/

@[expose] public section

namespace Algebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]

variable (R) in
/-- We say that an `R`-algebra `A` is etale at a prime `q` of `A`
if `A_q` is formally etale over `R`. -/
/-
**Algebra.IsEtaleAt** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：IsEtaleAt (q : Ideal A) [q.IsPrime] : Prop
参数：q : Ideal A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that an `R`-algebra `A` is etale at a prime `q` of `A`
if `A_q` is formally etale over `R`.
-/
abbrev IsEtaleAt (q : Ideal A) [q.IsPrime] : Prop :=
  FormallyEtale R (Localization.AtPrime q)

variable (R A) in
/-- `Algebra.etaleLocus R A` is the set of primes `p` of `A` that are etale. -/
/-
**Algebra.etaleLocus** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：etaleLocus : Set (PrimeSpectrum A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Algebra.etaleLocus R A` is the set of primes `p` of `A` that are etale.
-/
def etaleLocus : Set (PrimeSpectrum A) :=
  { p | IsEtaleAt R p.asIdeal }

@[simp]
/-
**Algebra.mem_etaleLocus_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：mem_etaleLocus_iff {p : PrimeSpectrum A} : p in etaleLocus R A ↔ IsEtaleAt
 R p.asIdeal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_etaleLocus_iff {p : PrimeSpectrum A} : p ∈ etaleLocus R A ↔ IsEtaleAt R p.asIdeal := .rfl
/-
**Algebra.IsEtaleAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsEtaleAt`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : CommRing B]   [inst_3 : Algebra R A] [inst_4 : Algebra 
A B] [inst_5 : Algebra R B] [IsScalarTower R A B] (p : Ideal A) (P : Ideal B)   
[P.LiesOver p] [inst_8 : p.IsPrime] [inst_9 : P.IsPrime] [Algebra.IsEtaleAt R p]
 [Algebra.IsEtaleAt A P],   Algebra.IsEtaleAt R P
参数：p : Ideal A；P : Ideal B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyEtale.localization_base`：localization_base [FormallyEtal
e R Sₘ] : FormallyEtale Rₘ Sₘ
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `Algebra.FormallyEtale.comp`：comp [FormallyEtale R A] [FormallyEtale A B]
 : FormallyEtale R B
-/
lemma IsEtaleAt.comp
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsEtaleAt R p] [IsEtaleAt A P] : IsEtaleAt R P := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have : FormallyEtale (Localization.AtPrime p) (Localization.AtPrime P) :=
    .localization_base p.primeCompl
  exact FormallyEtale.comp R (Localization.AtPrime p) _
/-
**Algebra.etaleLocus_eq_unramfiedLocus_inter_smoothLocus** 是 Mathlib 中的一个引理，位于命名
空间 `Algebra`。
形式化陈述：etaleLocus_eq_unramfiedLocus_inter_smoothLocus : etaleLocus R A = unramifi
edLocus R A inter smoothLocus R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth`：iff_for
mallyUnramified_and_formallySmooth : FormallyEtale R A ↔ FormallyUnramified R A 
∧ FormallySmooth R A
-/
lemma etaleLocus_eq_unramfiedLocus_inter_smoothLocus :
    etaleLocus R A = unramifiedLocus R A ∩ smoothLocus R A :=
  Set.ext fun _ ↦ FormallyEtale.iff_formallyUnramified_and_formallySmooth
/-
**Algebra.etaleLocus_eq_compl_support** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：etaleLocus_eq_compl_support : etaleLocus R A = (Module.support A Ω[A⁄R])ᶜ 
inter (Module.support A (H1Cotangent R A))ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.H1Cotangent.isLocalizedModule`：∀ (R : Type u_1) {S : Type u_2} (
T : Type u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   
[inst_3 : Algebra R S] [ins…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Algebra.formallyEtale_iff`：∀ (R : Type u) (A : Type v) [inst : CommRing 
R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.FormallyEtale R A ↔ S
ubsingleton Ω[A…
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
-/
lemma etaleLocus_eq_compl_support :
    etaleLocus R A = (Module.support A Ω[A⁄R])ᶜ ∩ (Module.support A (H1Cotangent R A))ᶜ := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Module.notMem_support_iff]
  have h₁ := IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
  have h₂ := IsLocalizedModule.iso p.asIdeal.primeCompl
    (H1Cotangent.map R R A (Localization.AtPrime p.asIdeal))
  exact (Algebra.formallyEtale_iff _ _).trans
    (and_congr h₁.subsingleton_congr.symm h₂.subsingleton_congr.symm)
/-
**Algebra.basicOpen_subset_etaleLocus_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：basicOpen_subset_etaleLocus_iff {f : A} : ↑(PrimeSpectrum.basicOpen f) sub
seteq etaleLocus R A ↔ Algebra.FormallyEtale R (Localization.Away f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.etaleLocus_eq_compl_support`：etaleLocus_eq_compl_support : etale
Locus R A = (Module.support A Ω[A⁄R])ᶜ inter (Module.support A (H1Cotangent R A)
)ᶜ
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
· 使用定理 `Algebra.formallyEtale_iff`：∀ (R : Type u) (A : Type v) [inst : CommRing 
R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.FormallyEtale R A ↔ S
ubsingleton Ω[A…
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.H1Cotangent.isLocalizedModule`：∀ (R : Type u_1) {S : Type u_2} (
T : Type u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   
[inst_3 : Algebra R S] [ins…
-/
lemma basicOpen_subset_etaleLocus_iff {f : A} :
    ↑(PrimeSpectrum.basicOpen f) ⊆ etaleLocus R A ↔
      Algebra.FormallyEtale R (Localization.Away f) := by
  rw [etaleLocus_eq_compl_support, Set.subset_inter_iff, Set.subset_compl_comm,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl, Set.subset_compl_comm, compl_compl,
    ← LocalizedModule.subsingleton_iff_support_subset,
    ← LocalizedModule.subsingleton_iff_support_subset, formallyEtale_iff]
  exact and_congr (IsLocalizedModule.iso (.powers f)
    (KaehlerDifferential.map R R A (Localization.Away f))).subsingleton_congr
    (IsLocalizedModule.iso (.powers f)
      (H1Cotangent.map R R A (Localization.Away f))).subsingleton_congr
/-
**Algebra.etaleLocus_eq_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：etaleLocus_eq_univ_iff : etaleLocus R A = Set.univ ↔ Algebra.FormallyEtale
 R A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.etaleLocus_eq_compl_support`：etaleLocus_eq_compl_support : etale
Locus R A = (Module.support A Ω[A⁄R])ᶜ inter (Module.support A (H1Cotangent R A)
)ᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `compl_eq_comm`：compl_eq_comm : xᶜ = y ↔ yᶜ = x
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用引理 `Module.support_eq_empty_iff`：Module.support_eq_empty_iff : Module.suppor
t R M = ∅ ↔ Subsingleton M
· 使用定理 `Algebra.formallyEtale_iff`：∀ (R : Type u) (A : Type v) [inst : CommRing 
R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.FormallyEtale R A ↔ S
ubsingleton Ω[A…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma etaleLocus_eq_univ_iff :
    etaleLocus R A = Set.univ ↔ Algebra.FormallyEtale R A := by
  rw [etaleLocus_eq_compl_support, ← Set.compl_union, compl_eq_comm, Set.compl_univ, eq_comm,
    ← Set.subset_empty_iff, Set.union_subset_iff, Set.subset_empty_iff, Set.subset_empty_iff,
    Module.support_eq_empty_iff, Module.support_eq_empty_iff, Algebra.formallyEtale_iff]

variable [FinitePresentation R A]
/-
**Algebra.isOpen_etaleLocus** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：isOpen_etaleLocus : IsOpen (etaleLocus R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.etaleLocus_eq_unramfiedLocus_inter_smoothLocus`：etaleLocus_eq_un
ramfiedLocus_inter_smoothLocus : etaleLocus R A = unramifiedLocus R A inter smoo
thLocus R A
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用引理 `Algebra.isOpen_unramifiedLocus`：isOpen_unramifiedLocus [EssFiniteType R 
A] : IsOpen (unramifiedLocus R A)
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用引理 `Algebra.isOpen_smoothLocus`：isOpen_smoothLocus [FinitePresentation R A] 
: IsOpen (smoothLocus R A)
-/
lemma isOpen_etaleLocus : IsOpen (etaleLocus R A) := by
  rw [etaleLocus_eq_unramfiedLocus_inter_smoothLocus]
  exact isOpen_unramifiedLocus.inter isOpen_smoothLocus
/-
**Algebra.basicOpen_subset_etaleLocus_iff_etale** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
ra`。
形式化陈述：basicOpen_subset_etaleLocus_iff_etale {f : A} : ↑(PrimeSpectrum.basicOpen 
f) subseteq etaleLocus R A ↔ Algebra.Etale R (Localization.Away f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.basicOpen_subset_etaleLocus_iff`：basicOpen_subset_etaleLocus_iff
 {f : A} : ↑(PrimeSpectrum.basicOpen f) subseteq etaleLocus R A ↔ Algebra.Formal
lyEtale R (Localization.Away …
· 使用定理 `instFinitePresentationAway`：∀ {R : Type u_1} [inst : CommRing R] {S : Ty
pe u_2} [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FinitePresentati
on R S] (f : S),…
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
-/
lemma basicOpen_subset_etaleLocus_iff_etale {f : A} :
    ↑(PrimeSpectrum.basicOpen f) ⊆ etaleLocus R A ↔ Algebra.Etale R (Localization.Away f) := by
  rw [basicOpen_subset_etaleLocus_iff]
  refine ⟨fun H ↦ ⟨H, inferInstance⟩, fun _ ↦ inferInstance⟩
/-
**Algebra.etaleLocus_eq_univ_iff_etale** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：etaleLocus_eq_univ_iff_etale : etaleLocus R A = Set.univ ↔ Algebra.Etale R
 A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.etaleLocus_eq_univ_iff`：etaleLocus_eq_univ_iff : etaleLocus R A 
= Set.univ ↔ Algebra.FormallyEtale R A
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
-/
lemma etaleLocus_eq_univ_iff_etale :
    etaleLocus R A = Set.univ ↔ Algebra.Etale R A := by
  rw [etaleLocus_eq_univ_iff]
  refine ⟨fun H ↦ ⟨H, inferInstance⟩, fun _ ↦ inferInstance⟩
/-
**Algebra.exists_etale_of_isEtaleAt** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：exists_etale_of_isEtaleAt (P : Ideal A) [P.IsPrime] [IsEtaleAt R P] : exis
ts f ∉ P, Algebra.Etale R (Localization.Away f)
参数：P : Ideal A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用引理 `Algebra.isOpen_etaleLocus`：isOpen_etaleLocus : IsOpen (etaleLocus R A)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Algebra.basicOpen_subset_etaleLocus_iff`：basicOpen_subset_etaleLocus_iff
 {f : A} : ↑(PrimeSpectrum.basicOpen f) subseteq etaleLocus R A ↔ Algebra.Formal
lyEtale R (Localization.Away …
· 使用引理 `Algebra.FinitePresentation.of_isLocalizationAway`：Algebra.FinitePresenta
tion.of_isLocalizationAway {R S S' : Type*} [CommRing R] [CommRing S] [CommRing 
S'] [Algebra R S] [Algebra R S'] [Alge…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma exists_etale_of_isEtaleAt
    (P : Ideal A) [P.IsPrime] [IsEtaleAt R P] :
    ∃ f ∉ P, Algebra.Etale R (Localization.Away f) := by
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show ⟨P, ‹_›⟩ ∈ etaleLocus R A by assumption) isOpen_etaleLocus
  exact ⟨r, hpr, ⟨basicOpen_subset_etaleLocus_iff.mp hr, .of_isLocalizationAway r⟩⟩

end Algebra

