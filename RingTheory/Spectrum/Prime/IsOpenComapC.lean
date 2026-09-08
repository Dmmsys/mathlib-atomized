/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
The morphism `Spec R[x] --> Spec R` induced by the natural inclusion `R --> R[x]` is an open map.

The main result is the first part of the statement of Lemma 00FB in the Stacks Project.

https://stacks.math.columbia.edu/tag/00FB
-/

@[expose] public section


open Ideal Polynomial PrimeSpectrum Set

namespace AlgebraicGeometry

namespace Polynomial

variable {R : Type*} [CommRing R] {f : R[X]}


/-- Given a polynomial `f ∈ R[x]`, `imageOfDf` is the subset of `Spec R` where at least one
of the coefficients of `f` does not vanish.  Lemma `imageOfDf_eq_comap_C_compl_zeroLocus`
proves that `imageOfDf` is the image of `(zeroLocus {f})ᶜ` under the morphism
`comap C : Spec R[x] → Spec R`. -/
/-
**AlgebraicGeometry.Polynomial.imageOfDf** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Polynomial`。
形式化陈述：imageOfDf (f : R[X]) : Set (PrimeSpectrum R)
参数：f : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a polynomial `f ∈ R[x]`, `imageOfDf` is the subset of `Spec R` where at le
ast one
of the coefficients of `f` does not vanish.  Lemma `imageOfDf_eq_comap_C_compl_z
eroLocus`
proves that `imageOfDf` is the image of `(zeroLocus {f})ᶜ` under the morphism
`comap C : Spec R[x] → Spec R`.
-/
def imageOfDf (f : R[X]) : Set (PrimeSpectrum R) :=
  { p : PrimeSpectrum R | ∃ i : ℕ, coeff f i ∉ p.asIdeal }
/-
**AlgebraicGeometry.Polynomial.isOpen_imageOfDf** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Polynomial`。
形式化陈述：isOpen_imageOfDf : IsOpen (imageOfDf f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Polynomial.imageOfDf.eq_1`：∀ {R : Type u_1} [inst : Co
mmRing R] (f : Polynomial R),   AlgebraicGeometry.Polynomial.imageOfDf f = {p | 
∃ i, f.coeff i ∉ p.asIdeal}
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `PrimeSpectrum.isOpen_basicOpen`：isOpen_basicOpen {a : R} : IsOpen (basic
Open a : Set (PrimeSpectrum R))
-/
theorem isOpen_imageOfDf : IsOpen (imageOfDf f) := by
  rw [imageOfDf, ofPred_exists fun i (x : PrimeSpectrum R) => coeff f i ∉ x.asIdeal]
  exact isOpen_iUnion fun i => isOpen_basicOpen

/-- If a point of `Spec R[x]` is not contained in the vanishing set of `f`, then its image in
`Spec R` is contained in the open set where at least one of the coefficients of `f` is non-zero.
This lemma is a reformulation of `exists_C_coeff_notMem`. -/
/-
**AlgebraicGeometry.Polynomial.comap_C_mem_imageOfDf** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Polynomial`。
形式化陈述：comap_C_mem_imageOfDf {I : PrimeSpectrum R[X]} (H : I in (zeroLocus {f} : 
Set (PrimeSpectrum R[X]))ᶜ) : PrimeSpectrum.comap (Polynomial.C : R ->+* R[X]) I
 in imageOfDf f
参数：H : I in (zeroLocus {f} : Set (PrimeSpectrum R[X]))ᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_C_coeff_notMem`：exists_C_coeff_notMem : f ∉ I -> exists i : Nat, 
C (coeff f i) ∉ I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.mem_compl_zeroLocus_iff_notMem`：mem_compl_zeroLocus_iff_no
tMem {f : R} {I : PrimeSpectrum R} : I in (zeroLocus {f} : Set (PrimeSpectrum R)
)ᶜ ↔ f ∉ I.asIdeal

--- 原说明 ---
If a point of `Spec R[x]` is not contained in the vanishing set of `f`, then its
 image in
`Spec R` is contained in the open set where at least one of the coefficients of 
`f` is non-zero.
This lemma is a reformulation of `exists_C_coeff_notMem`.
-/
theorem comap_C_mem_imageOfDf {I : PrimeSpectrum R[X]}
    (H : I ∈ (zeroLocus {f} : Set (PrimeSpectrum R[X]))ᶜ) :
    PrimeSpectrum.comap (Polynomial.C : R →+* R[X]) I ∈ imageOfDf f :=
  exists_C_coeff_notMem (mem_compl_zeroLocus_iff_notMem.mp H)

/-- The open set `imageOfDf f` coincides with the image of `basicOpen f` under the
morphism `C⁺ : Spec R[x] → Spec R`. -/
/-
**AlgebraicGeometry.Polynomial.imageOfDf_eq_comap_C_compl_zeroLocus** 是 Mathlib 
中的一个定理，位于命名空间 `AlgebraicGeometry.Polynomial`。
形式化陈述：imageOfDf_eq_comap_C_compl_zeroLocus : imageOfDf f = PrimeSpectrum.comap (
C : R ->+* R[X]) '' (zeroLocus {f})ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `PrimeSpectrum.mem_zeroLocus`：mem_zeroLocus (x : PrimeSpectrum R) (s : Se
t R) : x in zeroLocus s ↔ s subseteq x.asIdeal
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_map_C_iff`：mem_map_C_iff {I : Ideal R} {f : R[X]} : f in (Idea
l.map (C : R ->+* R[X]) I : Ideal R[X]) ↔ forall n : Nat, f.coeff n in I
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `AlgebraicGeometry.Polynomial.comap_C_mem_imageOfDf`：comap_C_mem_imageOfD
f {I : PrimeSpectrum R[X]} (H : I in (zeroLocus {f} : Set (PrimeSpectrum R[X]))ᶜ
) : PrimeSpectrum.comap (Polynomial.C : …

--- 原说明 ---
The open set `imageOfDf f` coincides with the image of `basicOpen f` under the
morphism `C⁺ : Spec R[x] → Spec R`.
-/
theorem imageOfDf_eq_comap_C_compl_zeroLocus :
    imageOfDf f = PrimeSpectrum.comap (C : R →+* R[X]) '' (zeroLocus {f})ᶜ := by
  ext x
  refine ⟨fun hx => ⟨⟨map C x.asIdeal, isPrime_map_C_of_isPrime⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rw [mem_compl_iff, mem_zeroLocus, singleton_subset_iff]
    obtain ⟨i, hi⟩ := hx
    exact fun a => hi (mem_map_C_iff.mp a i)
  · ext x
    refine ⟨fun h => ?_, fun h => subset_span (mem_image_of_mem C.1 h)⟩
    rw [← @coeff_C_zero R x _]
    exact mem_map_C_iff.mp h 0
  · rintro ⟨xli, complement, rfl⟩
    exact comap_C_mem_imageOfDf complement

/-- The morphism `C⁺ : Spec R[x] → Spec R` is open. -/
@[stacks 00FB "First part"]
/-
**AlgebraicGeometry.Polynomial.isOpenMap_comap_C** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Polynomial`。
形式化陈述：isOpenMap_comap_C : IsOpenMap (PrimeSpectrum.comap (C : R ->+* R[X]))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.iUnion_of_singleton_coe`：iUnion_of_singleton_coe (s : Set α) : ⋃ i :
 s, ({(i : α)} : Set α) = s
· 使用定理 `PrimeSpectrum.zeroLocus_iUnion`：zeroLocus_iUnion {ι : Sort*} (s : ι -> S
et R) : zeroLocus (⋃ i, s i) = ⋂ i, zeroLocus (s i)
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `AlgebraicGeometry.Polynomial.isOpen_imageOfDf`：isOpen_imageOfDf : IsOpen
 (imageOfDf f)

--- 原说明 ---
The morphism `C⁺ : Spec R[x] → Spec R` is open.
-/
theorem isOpenMap_comap_C : IsOpenMap (PrimeSpectrum.comap (C : R →+* R[X])) := by
  rintro U ⟨s, z⟩
  rw [← compl_compl U, ← z, ← iUnion_of_singleton_coe s, zeroLocus_iUnion, compl_iInter,
    image_iUnion]
  simp_rw [← imageOfDf_eq_comap_C_compl_zeroLocus]
  exact isOpen_iUnion fun f => isOpen_imageOfDf

end Polynomial

end AlgebraicGeometry

