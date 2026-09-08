/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.LocalProperties.Basic

/-!

# The meta properties of unramified ring homomorphisms.

-/

@[expose] public section

namespace RingHom

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S]

/--
A ring homomorphism `R →+* A` is formally unramified if `Ω[A⁄R]` is trivial.
See `Algebra.FormallyUnramified`.
-/
@[algebraize Algebra.FormallyUnramified]
/-
**RingHom.FormallyUnramified** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：FormallyUnramified (f : R ->+* S) : Prop
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `R →+* A` is formally unramified if `Ω[A⁄R]` is trivial.
See `Algebra.FormallyUnramified`.
-/
def FormallyUnramified (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FormallyUnramified R S
/-
**RingHom.formallyUnramified_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：formallyUnramified_algebraMap [Algebra R S] : (algebraMap R S).FormallyUnr
amified ↔ Algebra.FormallyUnramified R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.FormallyUnramified.eq_1`：∀ {R : Type u_1} {S : Type u_2} [inst :
 CommRing R] [inst_1 : CommRing S] (f : R →+* S),   f.FormallyUnramified = Algeb
ra.FormallyUnramified…
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma formallyUnramified_algebraMap [Algebra R S] :
    (algebraMap R S).FormallyUnramified ↔ Algebra.FormallyUnramified R S := by
  rw [FormallyUnramified, toAlgebra_algebraMap]

namespace FormallyUnramified

/-
**RingHom.FormallyUnramified.of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Fo
rmallyUnramified`。
形式化陈述：of_surjective {f : R ->+* S} (hf : Function.Surjective f) : f.FormallyUnra
mified
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.of_surjective`：of_surjective [FormallyUnramif
ied R A] (f : A ->ₐ[R] B) (H : Function.Surjective f) : FormallyUnramified R B
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Etale.inst`：∀ {R : Type u} [inst : CommRing R], Algebra.Etale R 
R
-/
lemma of_surjective {f : R →+* S} (hf : Function.Surjective f) : f.FormallyUnramified := by
  algebraize [f]
  exact Algebra.FormallyUnramified.of_surjective (Algebra.ofId R S) hf
/-
**RingHom.FormallyUnramified.of_comp** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Formally
Unramified`。
形式化陈述：of_comp {T : Type*} [CommRing T] {f : R ->+* S} {g : S ->+* T} (h : (g.com
p f).FormallyUnramified) : g.FormallyUnramified
参数：h : (g.comp f).FormallyUnramified。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.FormallyUnramified.of_restrictScalars`：of_restrictScalars [Forma
llyUnramified R B] : FormallyUnramified A B
-/
lemma of_comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T}
    (h : (g.comp f).FormallyUnramified) :
    g.FormallyUnramified := by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyUnramified.of_restrictScalars R _ _
/-
**RingHom.FormallyUnramified.comp** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.FormallyUnr
amified`。
形式化陈述：comp {T : Type*} [CommRing T] {f : R ->+* S} {g : S ->+* T} (hf : f.Formal
lyUnramified) (hg : g.FormallyUnramified) : (g.comp f).FormallyUnramified
参数：hf : f.FormallyUnramified；hg : g.FormallyUnramified。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.FormallyUnramified.comp`：comp [FormallyUnramified R A] [Formally
Unramified A B] : FormallyUnramified R B
-/
lemma comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T} (hf : f.FormallyUnramified)
    (hg : g.FormallyUnramified) :
    (g.comp f).FormallyUnramified := by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyUnramified.comp R S T
/-
**RingHom.FormallyUnramified.stableUnderComposition** 是 Mathlib 中的一个引理，位于命名空间 `R
ingHom.FormallyUnramified`。
形式化陈述：stableUnderComposition : StableUnderComposition FormallyUnramified
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.FormallyUnramified.comp`：comp {T : Type*} [CommRing T] {f : R ->
+* S} {g : S ->+* T} (hf : f.FormallyUnramified) (hg : g.FormallyUnramified) : (
g.comp f).FormallyUnr…
-/
lemma stableUnderComposition : StableUnderComposition FormallyUnramified :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ .comp hf hg
/-
**RingHom.FormallyUnramified.respectsIso** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Form
allyUnramified`。
形式化陈述：respectsIso : RespectsIso FormallyUnramified
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.StableUnderComposition.respectsIso`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.StableUnd
erComposition P →     (∀ {R S : …
· 使用引理 `RingHom.FormallyUnramified.stableUnderComposition`：stableUnderCompositio
n : StableUnderComposition FormallyUnramified
· 使用引理 `RingHom.FormallyUnramified.of_surjective`：of_surjective {f : R ->+* S} (
hf : Function.Surjective f) : f.FormallyUnramified
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
-/
lemma respectsIso :
    RespectsIso FormallyUnramified := by
  refine stableUnderComposition.respectsIso ?_
  intro R S _ _ e
  exact .of_surjective e.surjective
/-
**RingHom.FormallyUnramified.isStableUnderBaseChange** 是 Mathlib 中的一个引理，位于命名空间 `
RingHom.FormallyUnramified`。
形式化陈述：isStableUnderBaseChange : IsStableUnderBaseChange FormallyUnramified
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用引理 `RingHom.FormallyUnramified.respectsIso`：respectsIso : RespectsIso Formal
lyUnramified
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.formallyUnramified_algebraMap`：formallyUnramified_algebraMap [Al
gebra R S] : (algebraMap R S).FormallyUnramified ↔ Algebra.FormallyUnramified R 
S
-/
lemma isStableUnderBaseChange :
    IsStableUnderBaseChange FormallyUnramified := by
  refine .mk respectsIso ?_
  introv H
  rw [formallyUnramified_algebraMap] at H ⊢
  infer_instance
/-
**RingHom.FormallyUnramified.holdsForLocalization** 是 Mathlib 中的一个引理，位于命名空间 `Rin
gHom.FormallyUnramified`。
形式化陈述：holdsForLocalization : HoldsForLocalization FormallyUnramified
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.formallyUnramified_algebraMap`：formallyUnramified_algebraMap [Al
gebra R S] : (algebraMap R S).FormallyUnramified ↔ Algebra.FormallyUnramified R 
S
· 使用定理 `Algebra.FormallyUnramified.of_isLocalization`：of_isLocalization [IsLocal
ization M Rₘ] : FormallyUnramified R Rₘ
-/
lemma holdsForLocalization :
    HoldsForLocalization FormallyUnramified := by
  intro R S _ _ _ M _
  rw [formallyUnramified_algebraMap]
  exact .of_isLocalization M
/-
**RingHom.FormallyUnramified.holdsForLocalizationAway** 是 Mathlib 中的一个引理，位于命名空间 
`RingHom.FormallyUnramified`。
形式化陈述：holdsForLocalizationAway : HoldsForLocalizationAway FormallyUnramified
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.HoldsForLocalization.holdsForLocalizationAway`：RingHom.HoldsForL
ocalization.holdsForLocalizationAway (hP : HoldsForLocalization P) : HoldsForLoc
alizationAway P
· 使用引理 `RingHom.FormallyUnramified.holdsForLocalization`：holdsForLocalization : 
HoldsForLocalization FormallyUnramified
-/
lemma holdsForLocalizationAway :
    HoldsForLocalizationAway FormallyUnramified :=
  holdsForLocalization.holdsForLocalizationAway
/-
**RingHom.FormallyUnramified.ofLocalizationPrime** 是 Mathlib 中的一个引理，位于命名空间 `Ring
Hom.FormallyUnramified`。
形式化陈述：ofLocalizationPrime : OfLocalizationPrime FormallyUnramified
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.FormallyUnramified.eq_1`：∀ {R : Type u_1} {S : Type u_2} [inst :
 CommRing R] [inst_1 : CommRing S] (f : R →+* S),   f.FormallyUnramified = Algeb
ra.FormallyUnramified…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Algebra.formallyUnramified_iff_forall`：formallyUnramified_iff_forall : F
ormallyUnramified R A ↔ forall q : PrimeSpectrum A, IsUnramifiedAt R q.1
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.localRingHom_to_map`：localRingHom_to_map (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) : localRingHom I J f hIJ (a
lgebraMap _ _ x) = alg…
· 使用定理 `Algebra.FormallyUnramified.comp`：comp [FormallyUnramified R A] [Formally
Unramified A B] : FormallyUnramified R B
· 使用定理 `Algebra.FormallyUnramified.instLocalization`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra
.FormallyUnramified R S] (M : Sub…
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Etale.inst`：∀ {R : Type u} [inst : CommRing R], Algebra.Etale R 
R
-/
lemma ofLocalizationPrime :
    OfLocalizationPrime FormallyUnramified := by
  intro R S _ _ f H
  algebraize [f]
  rw [FormallyUnramified, Algebra.formallyUnramified_iff_forall]
  intro x
  let Rₓ := Localization.AtPrime (x.asIdeal.comap f)
  let Sₓ := Localization.AtPrime x.asIdeal
  let : Algebra Rₓ Sₓ := (Localization.localRingHom _ _ _ rfl).toAlgebra
  have : IsScalarTower R Rₓ Sₓ := .of_algebraMap_eq
    fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  have : Algebra.FormallyUnramified Rₓ Sₓ := H _ _
  exact Algebra.FormallyUnramified.comp R Rₓ Sₓ
/-
**RingHom.FormallyUnramified.ofLocalizationSpanTarget** 是 Mathlib 中的一个引理，位于命名空间 
`RingHom.FormallyUnramified`。
形式化陈述：ofLocalizationSpanTarget : OfLocalizationSpanTarget FormallyUnramified
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.FormallyUnramified.eq_1`：∀ {R : Type u_1} {S : Type u_2} [inst :
 CommRing R] [inst_1 : CommRing S] (f : R →+* S),   f.FormallyUnramified = Algeb
ra.FormallyUnramified…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Algebra.formallyUnramified_iff_forall`：formallyUnramified_iff_forall : F
ormallyUnramified R A ↔ forall q : PrimeSpectrum A, IsUnramifiedAt R q.1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PrimeSpectrum.iSup_basicOpen_eq_top_iff'`：iSup_basicOpen_eq_top_iff' {s 
: Set R} : (⨆ i in s, PrimeSpectrum.basicOpen i) = ⊤ ↔ Ideal.span s = ⊤
· 使用引理 `TopologicalSpace.Opens.mem_top`：mem_top (x : α) : x in (⊤ : Opens α)
· 使用引理 `Algebra.basicOpen_subset_unramifiedLocus_iff`：basicOpen_subset_unramifie
dLocus_iff {f : A} : ↑(PrimeSpectrum.basicOpen f) subseteq unramifiedLocus R A ↔
 Algebra.FormallyUnramified R (Loc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `RingHom.formallyUnramified_algebraMap`：formallyUnramified_algebraMap [Al
gebra R S] : (algebraMap R S).FormallyUnramified ↔ Algebra.FormallyUnramified R 
S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofLocalizationSpanTarget :
    OfLocalizationSpanTarget FormallyUnramified := by
  intro R S _ _ f s hs H
  algebraize [f]
  rw [FormallyUnramified, Algebra.formallyUnramified_iff_forall]
  intro x
  obtain ⟨r, hr, hrx⟩ : ∃ r ∈ s, x ∈ PrimeSpectrum.basicOpen r := by
    simpa using (PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs).ge
      (TopologicalSpace.Opens.mem_top x)
  refine Algebra.basicOpen_subset_unramifiedLocus_iff.mpr ?_ hrx
  convert! H ⟨r, hr⟩
  dsimp
  rw [← algebraMap_toAlgebra f, ← IsScalarTower.algebraMap_eq,
    formallyUnramified_algebraMap]
/-
**RingHom.FormallyUnramified.propertyIsLocal** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.
FormallyUnramified`。
形式化陈述：propertyIsLocal : PropertyIsLocal FormallyUnramified
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.LocalizationPreserves.away`：RingHom.LocalizationPreserves.away (
H : RingHom.LocalizationPreserves @P) : RingHom.LocalizationAwayPreserves P
· 使用引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`：RingHom.IsStableU
nderBaseChange.localizationPreserves : LocalizationPreserves P
· 使用引理 `RingHom.FormallyUnramified.isStableUnderBaseChange`：isStableUnderBaseCha
nge : IsStableUnderBaseChange FormallyUnramified
· 使用引理 `RingHom.FormallyUnramified.ofLocalizationSpanTarget`：ofLocalizationSpanT
arget : OfLocalizationSpanTarget FormallyUnramified
· 使用定理 `RingHom.OfLocalizationSpanTarget.ofLocalizationSpan`：RingHom.OfLocalizat
ionSpanTarget.ofLocalizationSpan (hP : RingHom.OfLocalizationSpanTarget @P) (hP'
 : RingHom.StableUnderCompositionWithLoca…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAwa
y`：RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway (hP
c : RingHom.StableUnderComposition P) (hPl : HoldsForLocalizati…
· 使用引理 `RingHom.FormallyUnramified.stableUnderComposition`：stableUnderCompositio
n : StableUnderComposition FormallyUnramified
· 使用引理 `RingHom.FormallyUnramified.holdsForLocalizationAway`：holdsForLocalizatio
nAway : HoldsForLocalizationAway FormallyUnramified
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma propertyIsLocal :
    PropertyIsLocal FormallyUnramified := by
  constructor
  · exact isStableUnderBaseChange.localizationPreserves.away
  · exact ofLocalizationSpanTarget
  · exact ofLocalizationSpanTarget.ofLocalizationSpan
      (stableUnderComposition.stableUnderCompositionWithLocalizationAway
          holdsForLocalizationAway).1
  · exact (stableUnderComposition.stableUnderCompositionWithLocalizationAway
        holdsForLocalizationAway).2

end FormallyUnramified

/-
**RingHom.FormallyEtale.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.FormallyEtale
`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{T : Type u_3} [inst_2 : CommRing T]   {f : R →+* S} {g : S →+* T}, f.FormallyUn
ramified → (g.comp f).FormallyEtale → g.FormallyEtale
参数：g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用引理 `Algebra.FormallyEtale.of_restrictScalars`：of_restrictScalars [FormallyUn
ramified R A] [FormallyEtale R B] : FormallyEtale A B
-/
lemma FormallyEtale.of_comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.FormallyUnramified) (h : (g.comp f).FormallyEtale) :
    g.FormallyEtale := by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyEtale.of_restrictScalars (R := R)

end RingHom

