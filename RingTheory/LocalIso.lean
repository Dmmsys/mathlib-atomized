/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.OpenImmersion
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Local isomorphisms

A ring homomorphism is a local isomorphism if source locally (in the geometric sense)
it is a standard open immersion.

## Main declarations

- `Algebra.IsLocalIso`: The class of algebras that are locally standard open immersions.

We show that local isomorphisms are local, stable under composition and base change.

## Implementation note

Most results in this file follow purely formally from the corresponding property of
standard open immersion. We could use the `RingHom.Locally` API to obtain them, but
it would yield results with less universe generality and we would have to replace
`CommSemiring` by `CommRing`. In the future, we may consider refactoring the API
for `RingHom` properties to allow for also treating properties of `CommSemiring`s
and then simplify the proofs in this file.
-/

universe w v u

public section

open TensorProduct

/-- An `R`-algebra `S` is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
@[stacks 096E "(1) in the algebra formulation", mk_iff]
/-
**Algebra.IsLocalIso** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_1) → (S : Type u_2) → [inst : CommSemiring R] → [inst_1 : Comm
Semiring S] → [Algebra R S] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-algebra `S` is a local isomorphism if source locally (in the geometric se
nse),
it is a standard open immersion.
-/
class Algebra.IsLocalIso (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] : Prop where
  exists_notMem_isStandardOpenImmersion (q : Ideal S) [q.IsPrime] :
    ∃ g ∉ q, IsStandardOpenImmersion R (Localization.Away g)

namespace Algebra.IsLocalIso

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (R S) in
/-
**Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top** 是 Mathlib 中的一个引理，位于命名
空间 `Algebra.IsLocalIso`。
形式化陈述：span_isStandardOpenImmersion_eq_top [Algebra.IsLocalIso R S] : Ideal.span 
{g : S | Algebra.IsStandardOpenImmersion R (Localization.Away g)} = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion`：∀ {R : Type u_
1} {S : Type u_2} {inst : CommSemiring R} {inst_1 : CommSemiring S} {inst_2 : Al
gebra R S}   [self : Algebra.IsLocalIso R S] (…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
-/
lemma span_isStandardOpenImmersion_eq_top [Algebra.IsLocalIso R S] :
    Ideal.span {g : S | Algebra.IsStandardOpenImmersion R (Localization.Away g)} = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hms⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨g, hgm, hstd⟩ :=
    Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := R) m
  exact hgm (hms (Ideal.subset_span hstd))
/-
**Algebra.IsLocalIso.iff_span_isStandardOpenImmersion_eq_top** 是 Mathlib 中的一个引理，
位于命名空间 `Algebra.IsLocalIso`。
形式化陈述：iff_span_isStandardOpenImmersion_eq_top : IsLocalIso R S ↔ Ideal.span {g :
 S | IsStandardOpenImmersion R (Localization.Away g)} = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top`：span_isStandardO
penImmersion_eq_top [Algebra.IsLocalIso R S] : Ideal.span {g : S | Algebra.IsSta
ndardOpenImmersion R (Localization.Away g)} …
-/
lemma iff_span_isStandardOpenImmersion_eq_top :
    IsLocalIso R S ↔
      Ideal.span {g : S | IsStandardOpenImmersion R (Localization.Away g)} = ⊤ := by
  refine ⟨fun _ ↦ span_isStandardOpenImmersion_eq_top R S, fun h ↦ ⟨fun q hq ↦ ?_⟩⟩
  grind [Ideal.IsPrime.ne_top, Ideal.span_le, SetLike.mem_coe]
/-
**Algebra.IsLocalIso.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsLocalIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [IsStandardOpenImmersion R S] : IsLocalIso R S where
  exists_notMem_isStandardOpenImmersion q hq := by
    use 1, hq.one_notMem
    exact IsStandardOpenImmersion.trans _ S _
/-
**Algebra.IsLocalIso.of_span_range_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsL
ocalIso`。
形式化陈述：of_span_range_eq_top {ι : Type*} (f : ι -> S) (h : Ideal.span (Set.range f
) = ⊤) (T : ι -> Type*) [forall i, CommSemiring (T i)] [forall i, Algebra R (T i
)] [forall i, Algebra S (T i)] [forall i, IsScalarTower R S (T i)] [forall i, Is
Localization.Away (f i) (T i)] [forall i, IsLocalIso R (T i)] : IsLocalIso R S
参数：f : ι -> S；h : Ideal.span (Set.range f) = ⊤；T : ι -> Type*；T i；T i；T i；T i；f 
i；T i；T i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PrimeSpectrum.iSup_basicOpen_eq_top_iff`：iSup_basicOpen_eq_top_iff {ι : 
Type*} {f : ι -> R} : (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) = ⊤ ↔ Ideal.span 
(Set.range f) = ⊤
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion`：∀ {R : Type u_
1} {S : Type u_2} {inst : CommSemiring R} {inst_1 : CommSemiring S} {inst_2 : Al
gebra R S}   [self : Algebra.IsLocalIso R S] (…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `IsLocalization.Away.surj`：surj (z : S) : exists (n : Nat) (a : R), z * a
lgebraMap R S x ^ n = algebraMap R S a
· 使用定理 `Ideal.IsPrime.mul_notMem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x ∉ I → y ∉ I → x * y ∉ I
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.mul_unit_mem_iff_mem`：mul_unit_mem_iff_mem {x y : α} (hy : IsUnit 
y) : x * y in I ↔ x in I
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用引理 `IsLocalization.Away.algebraMap_isUnit`：algebraMap_isUnit : IsUnit (algeb
raMap R S x)
· 使用引理 `IsLocalization.Away.of_associated`：of_associated {r r' : R} (h : Associa
ted r r') [IsLocalization.Away r S] : IsLocalization.Away r' S
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `associated_mul_unit_right`：associated_mul_unit_right {N : Type*} [Monoid
 N] (a u : N) (hu : IsUnit u) : Associated a (a * u)
· 使用定理 `IsLocalization.Away.instHMulAwayCoeRingHomAlgebraMap`：∀ {R : Type u_1} [
inst : CommSemiring R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebr
a R S] (x y : R)   [IsLocalization.Away x …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Algebra.IsStandardOpenImmersion.of_algEquiv`：of_algEquiv {T : Type*} [Co
mmSemiring T] [Algebra R T] (e : S ≃ₐ[R] T) [h : IsStandardOpenImmersion R S] : 
IsStandardOpenImmersion R T
-/
lemma of_span_range_eq_top {ι : Type*} (f : ι → S) (h : Ideal.span (Set.range f) = ⊤)
    (T : ι → Type*) [∀ i, CommSemiring (T i)] [∀ i, Algebra R (T i)] [∀ i, Algebra S (T i)]
    [∀ i, IsScalarTower R S (T i)] [∀ i, IsLocalization.Away (f i) (T i)]
    [∀ i, IsLocalIso R (T i)] : IsLocalIso R S := by
  refine ⟨fun q hq ↦ ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, f i ∉ q := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff] at h
    have : ⟨q, hq⟩ ∈ ⨆ i, PrimeSpectrum.basicOpen (f i) := by simp [h]
    simpa using this
  have : ⟨q, hq⟩ ∈ PrimeSpectrum.basicOpen (f i) := hi
  rw [← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range (T i)] at this
  obtain ⟨q', hq'⟩ := this
  obtain ⟨g', hg', h⟩ := exists_notMem_isStandardOpenImmersion (R := R) q'.1
  obtain ⟨n, g, hg⟩ := IsLocalization.Away.surj (f i) g'
  refine ⟨g * (f i), ?_, ?_⟩
  · refine Ideal.IsPrime.mul_notMem hq ?_ hi
    simp only [PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal] at hq'
    rwa [← hq', Ideal.mem_comap, ← hg, Ideal.mul_unit_mem_iff_mem]
    exact (IsLocalization.Away.algebraMap_isUnit (f i)).pow n
  · have : IsLocalization.Away g' (Localization.Away (algebraMap S (T i) g)) := by
      rw [← hg]
      exact .of_associated
        (associated_mul_unit_right _ _ ((IsLocalization.Away.algebraMap_isUnit (f i)).pow n)).symm
    let e₁ : Localization.Away (algebraMap S (T i) g) ≃ₐ[S] Localization.Away (g * f i) :=
      IsLocalization.algEquiv (.powers (g * f i)) _ _
    let e₂ : Localization.Away g' ≃ₐ[R] Localization.Away (g * f i) :=
      ((IsLocalization.algEquiv (.powers g') _ _).restrictScalars R).trans (e₁.restrictScalars R)
    exact .of_algEquiv e₂
/-
**Algebra.IsLocalIso.of_span_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsLocalIs
o`。
形式化陈述：of_span_eq_top {s : Set S} (h : Ideal.span s = ⊤) (h : forall x in s, IsLo
calIso R (Localization.Away x)) : IsLocalIso R S
参数：h : Ideal.span s = ⊤；h : forall x in s, IsLocalIso R (Localization.Away x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `Algebra.IsLocalIso.of_span_range_eq_top`：of_span_range_eq_top {ι : Type*
} (f : ι -> S) (h : Ideal.span (Set.range f) = ⊤) (T : ι -> Type*) [forall i, Co
mmSemiring (T i)] [forall i, …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma of_span_eq_top {s : Set S} (h : Ideal.span s = ⊤)
    (h : ∀ x ∈ s, IsLocalIso R (Localization.Away x)) : IsLocalIso R S := by
  have heq : Ideal.span (Set.range fun i : s ↦ i.1) = ⊤ := by simpa
  have (i : s) : IsLocalIso R (Localization.Away i.1) := h _ i.property
  exact .of_span_range_eq_top _ heq fun i ↦ Localization.Away i.1
/-
**Algebra.IsLocalIso.pi_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsLocalIso`
。
形式化陈述：pi_of_finite {ι : Type*} (R : Type*) (S : ι -> Type*) [CommSemiring R] [fo
rall i, CommRing (S i)] [forall i, Algebra R (S i)] [Finite ι] [forall i, IsLoca
lIso R (S i)] : IsLocalIso R (forall i, S i)
参数：R : Type*；S : ι -> Type*；S i；S i；S i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用引理 `Algebra.IsLocalIso.of_span_range_eq_top`：of_span_range_eq_top {ι : Type*
} (f : ι -> S) (h : Ideal.span (Set.range f) = ⊤) (T : ι -> Type*) [forall i, Co
mmSemiring (T i)] [forall i, …
· 使用引理 `Ideal.span_single_eq_top`：span_single_eq_top {ι : Type*} [DecidableEq ι]
 [Finite ι] (R : ι -> Type*) [forall i, Semiring (R i)] : Ideal.span (Set.range 
fun i => (Pi.s…
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
-/
lemma pi_of_finite {ι : Type*} (R : Type*) (S : ι → Type*) [CommSemiring R]
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] [Finite ι] [∀ i, IsLocalIso R (S i)] :
    IsLocalIso R (∀ i, S i)  := by
  classical
  let (i : ι) : Algebra (∀ i, S i) (S i) := (Pi.evalAlgHom R S i).toAlgebra
  have (i : ι) : IsLocalization.Away (Pi.single i (1 : S i)) (S i) := by
    apply IsLocalization.away_of_isIdempotentElem
    · simp [IsIdempotentElem, ← Pi.single_mul_left]
    · apply RingHom.ker_evalRingHom
    · apply (Pi.evalRingHom S i).surjective
  apply of_span_range_eq_top (fun i ↦ Pi.single i (1 : S i)) _ fun i ↦ S i
  exact Ideal.span_single_eq_top _

variable (T : Type*) [CommSemiring T]

attribute [local instance] isScalarTower_localizationAlgebra in
variable (R S) in
/-- Local isomorphisms are stable under composition. -/
/-
**Algebra.IsLocalIso.trans** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsLocalIso`。
形式化陈述：trans [Algebra S T] [Algebra R T] [IsScalarTower R S T] [IsLocalIso R S] [
IsLocalIso S T] : IsLocalIso R T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.Away.instAlgebraMapSubmonoidPowersOfCoeRingHomAlgebraMap`
：∀ {R : Type u_1} [inst : CommSemiring R] {A : Type u_5} [inst_1 : CommSemiring 
A] [inst_2 : Algebra R A] (Aₚ : Type u_7)   [inst_3 : CommSem…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top`：span_isStandardO
penImmersion_eq_top [Algebra.IsLocalIso R S] : Ideal.span {g : S | Algebra.IsSta
ndardOpenImmersion R (Localization.Away g)} …
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.top_mul`：top_mul : ⊤ * I = I
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `Ideal.span_mul_span`：span_mul_span (S T : Set R) [(span S).IsTwoSided] :
 span S * span T = span (S * T)
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.mul_subset_iff`：mul_subset_iff : s * t subseteq u ↔ forall x in s, f
orall y in t, x * y in u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to₁₃₄`：∀ (M : Type u_9) (N : Type u_10) (P : Type u_11) (Q
 : Type u_12) [inst : SMul M N] [inst_1 : SMul M P]   [inst_2 : SMul M Q] [inst_
3 : SMul …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用引理 `isScalarTower_localizationAlgebra`：isScalarTower_localizationAlgebra [Al
gebra R Sₘ] [IsScalarTower R S Sₘ] : letI : Algebra Rₘ Sₘ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Algebra.algebraMapSubmonoid_powers`：algebraMapSubmonoid_powers (r : R) :
 Algebra.algebraMapSubmonoid S (.powers r) = Submonoid.powers (algebraMap R S r)
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsLocalization.commutes`：commutes (S₁ S₂ T : Type*) [CommSemiring S₁] [C
ommSemiring S₂] [CommSemiring T] [Algebra R S₁] [Algebra R S₂] [Algebra R T] [Al
gebra S₁ T] […
· 使用引理 `Algebra.isPushout_of_isLocalization`：Algebra.isPushout_of_isLocalization
 [IsLocalization (Algebra.algebraMapSubmonoid T S) B] : Algebra.IsPushout R T A 
B
· 使用引理 `Algebra.IsStandardOpenImmersion.of_isPushout`：of_isPushout (R' S' : Type
*) [CommSemiring R'] [CommSemiring S'] [Algebra R R'] [Algebra S S'] [Algebra R'
 S'] [Algebra R S'] [IsScalarTower…
· 使用定理 `Algebra.IsStandardOpenImmersion.trans`：∀ (R : Type u_1) (S : Type u_2) (
T : Type u_3) [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Comm
Semiring T] [inst_3 : Algeb…
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Local isomorphisms are stable under composition.
-/
lemma trans [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalIso R S] [IsLocalIso S T] : IsLocalIso R T := by
  -- The proof is purely formal given that open immersions are stable under composition.
  let s : Set S := {g : S | IsStandardOpenImmersion R (Localization.Away g)}
  let T' (g : S) := Localization.Away (algebraMap S T g)
  let (g : S) : Algebra (Localization.Away g) (T' g) := localizationAlgebra (.powers g) T
  let T'' (g : S) (x : T) := Localization.Away (algebraMap _ (T' g) x)
  let t (g : S) : Set T := {x : T | IsStandardOpenImmersion (Localization.Away g) (T'' g x)}
  let ι : Type _ := Σ i : s, t i.1
  have (i : ι) : IsStandardOpenImmersion (Localization.Away i.1.1) (T'' i.1 i.2) := i.2.2
  suffices h : Ideal.span (Set.range fun i : ι ↦ algebraMap S T i.1 * i.2) = ⊤ by
    have (i : ι) : IsStandardOpenImmersion R (T'' i.1 i.2) :=
      have : IsScalarTower R (Localization.Away i.1.1) (T' i.1.1) :=
        IsScalarTower.to₁₃₄ _ S _ _
      have : IsStandardOpenImmersion (Localization.Away i.1.1) (T'' i.1.1 i.2.1) := i.2.2
      have : IsStandardOpenImmersion R (Localization.Away i.1.1) := i.1.2
      .trans _ (Localization.Away i.1.1) _
    exact .of_span_range_eq_top _ h fun i : ι ↦ T'' i.1 i.2
  have h1 := congr(Ideal.map (algebraMap S T) $(span_isStandardOpenImmersion_eq_top R S))
  rw [Ideal.map_top, Ideal.map_span] at h1
  nth_rw 1 [_root_.eq_top_iff, ← Ideal.top_mul ⊤, ← h1, ← span_isStandardOpenImmersion_eq_top S T,
    Ideal.span_mul_span, Ideal.span_le, Set.mul_subset_iff]
  simp only [Set.mem_image, Set.mem_ofPred_eq, SetLike.mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro g hg x hx
  refine Ideal.subset_span ⟨⟨⟨g, hg⟩, ⟨x, ?_⟩⟩, rfl⟩
  simp only [Set.mem_ofPred_eq, t]
  let : Algebra (Localization.Away x) (T'' g x) :=
    localizationAlgebra (.powers x) (T' g)
  have : IsScalarTower S (Localization.Away x) (T'' g x) :=
    IsScalarTower.to₁₃₄ _ T _ _
  have : IsLocalization (algebraMapSubmonoid (Localization.Away x) (.powers g)) (T'' g x) := by
    have : algebraMapSubmonoid (Localization.Away x) (.powers g) =
      algebraMapSubmonoid (Localization.Away x) (.powers (algebraMap S T g)) := by
        simp [IsScalarTower.algebraMap_apply S T (Localization.Away x)]
    rw [this]
    exact .commutes _ (T' g) _ (.powers x) (.powers (algebraMap S T g))
  have : IsPushout S (Localization.Away x) (Localization.Away g) (T'' g x) :=
    Algebra.isPushout_of_isLocalization (.powers g) _ _ _
  exact .of_isPushout S (Localization.Away x) _ _

variable {T} in
/-
**Algebra.IsLocalIso.of_algEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsLocalIso`。
形式化陈述：of_algEquiv [Algebra R T] (e : S ≃ₐ[R] T) [IsLocalIso R S] : IsLocalIso R 
T
参数：e : S ≃ₐ[R] T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.IsStandardOpenImmersion.of_bijective`：of_bijective (h : Function
.Bijective (algebraMap R S)) : IsStandardOpenImmersion R S
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用引理 `Algebra.IsLocalIso.trans`：trans [Algebra S T] [Algebra R T] [IsScalarTow
er R S T] [IsLocalIso R S] [IsLocalIso S T] : IsLocalIso R T
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `Algebra.IsLocalIso.instOfIsStandardOpenImmersion`：∀ {R : Type u_1} {S : 
Type u_2} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R 
S]   [Algebra.IsStandardOpenImmersion …
-/
lemma of_algEquiv [Algebra R T] (e : S ≃ₐ[R] T) [IsLocalIso R S] : IsLocalIso R T := by
  algebraize [e.toAlgHom.toRingHom]
  have : IsStandardOpenImmersion S T := .of_bijective e.bijective
  exact .trans _ S _

variable {T} in
/-
**Algebra.IsLocalIso.iff_of_algEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsLocalI
so`。
形式化陈述：iff_of_algEquiv [Algebra R T] (e : S ≃ₐ[R] T) : IsLocalIso R S ↔ IsLocalIs
o R T
参数：e : S ≃ₐ[R] T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.IsLocalIso.of_algEquiv`：of_algEquiv [Algebra R T] (e : S ≃ₐ[R] T
) [IsLocalIso R S] : IsLocalIso R T
-/
lemma iff_of_algEquiv [Algebra R T] (e : S ≃ₐ[R] T) : IsLocalIso R S ↔ IsLocalIso R T :=
  ⟨fun _ ↦ .of_algEquiv e, fun _ ↦ .of_algEquiv e.symm⟩
/-
**Algebra.IsLocalIso.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsLocalIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra R T] [IsLocalIso R S] : IsLocalIso T (T ⊗[R] S) := by
  rw [iff_span_isStandardOpenImmersion_eq_top, _root_.eq_top_iff,
    ← Ideal.map_top Algebra.TensorProduct.includeRight, ← span_isStandardOpenImmersion_eq_top R S,
    Ideal.map_le_iff_le_comap, Ideal.span_le]
  intro g hg
  apply Ideal.subset_span
  simp only [Set.mem_ofPred_eq] at hg ⊢
  exact .of_algEquiv <| IsLocalization.Away.tensorProductEquivTMulRight R T g (Localization.Away g)

end Algebra.IsLocalIso

