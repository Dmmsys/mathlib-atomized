/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!

# Prime spectrum of (multivariate) polynomials

Also see `AlgebraicGeometry/AffineSpace` for the affine space over arbitrary schemes.

## Main results
- `isNilpotent_tensor_residueField_iff`:
  If `A` is a finite free `R`-algebra, then `f : A` is nilpotent on `κ(𝔭) ⊗ A` for some
  prime `𝔭 ◃ R` if and only if every non-leading coefficient of `charpoly(f)` is in `𝔭`.
- `Polynomial.exists_image_comap_of_monic`:
  If `g : R[X]` is monic, the image of `Z(g) ∩ D(f) : Spec R[X]` in `Spec R` is compact open.
- `Polynomial.isOpenMap_comap_C`: The structure map `Spec R[X] → Spec R` is an open map.
- `MvPolynomial.isOpenMap_comap_C`:
  The structure map `Spec (MvPolynomial σ R) → Spec R` is an open map.

-/

public section

open Polynomial TensorProduct PrimeSpectrum

variable {R M A} [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]

/-- If `A` is a finite free `R`-algebra, then `f : A` is nilpotent on `κ(𝔭) ⊗ A` for some
prime `𝔭 ◃ R` if and only if every non-leading coefficient of `charpoly(f)` is in `𝔭`. -/
/-
**isNilpotent_tensor_residueField_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isNilpotent_tensor_residueField_iff [Module.Free R A] [Module.Finite R A] 
(f : A) (I : Ideal R) [I.IsPrime] : IsNilpotent (algebraMap A (A otimes[R] I.Res
idueField) f) ↔ forall i < Module.finrank R A, (Algebra.lmul R A f).charpoly.coe
ff i in I
参数：f : A；I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RingHom.codomain_trivial`：codomain_trivial (f : α ->+* β) [h : Subsingle
ton α] : Subsingleton β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Module.finrank_subsingleton`：∀ {R : Type u} {M : Type v} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsingleton R],
 Module.finrank R…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Module.finrank_tensorProduct`：Module.finrank_tensorProduct : finrank R (
M otimes[S] M') = finrank R M * finrank S M'
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsNilpotent.map_iff`：IsNilpotent.map_iff [MonoidWithZero R] [MonoidWithZ
ero S] {r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] {f : F
} (hf : F…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
If `A` is a finite free `R`-algebra, then `f : A` is nilpotent on `κ(𝔭) ⊗ A` for
 some
prime `𝔭 ◃ R` if and only if every non-leading coefficient of `charpoly(f)` is i
n `𝔭`.
-/
lemma isNilpotent_tensor_residueField_iff
    [Module.Free R A] [Module.Finite R A] (f : A) (I : Ideal R) [I.IsPrime] :
    IsNilpotent (algebraMap A (A ⊗[R] I.ResidueField) f) ↔
      ∀ i < Module.finrank R A, (Algebra.lmul R A f).charpoly.coeff i ∈ I := by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R (A ⊗[R] I.ResidueField)).codomain_trivial
    simp [Subsingleton.elim I ⊤, Subsingleton.elim (f ⊗ₜ[R] (1 : I.ResidueField)) 0]
  have : Module.finrank I.ResidueField (I.ResidueField ⊗[R] A) = Module.finrank R A := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
  rw [← IsNilpotent.map_iff (Algebra.TensorProduct.comm R A I.ResidueField).injective]
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.coe_lmul_eq_mul, Algebra.TensorProduct.comm_tmul]
  rw [← IsNilpotent.map_iff (Algebra.lmul_injective (R := I.ResidueField)),
    LinearMap.isNilpotent_iff_charpoly, ← Algebra.baseChange_lmul, LinearMap.charpoly_baseChange,
    this]
  simp_rw [← ((LinearMap.mul R A) f).charpoly_natDegree]
  constructor
  · intro e i hi
    replace e := congr(($e).coeff i)
    simpa only [Algebra.coe_lmul_eq_mul, coeff_map, coeff_X_pow, hi.ne, ↓reduceIte,
      ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField] using e
  · intro H
    ext i
    obtain (hi | hi) := eq_or_ne i ((LinearMap.mul R A) f).charpoly.natDegree
    · simp only [Algebra.coe_lmul_eq_mul, hi, coeff_map, coeff_X_pow, ↓reduceIte]
      rw [← Polynomial.leadingCoeff, ((LinearMap.mul R A) f).charpoly_monic, map_one]
    obtain (hi | hi) := lt_or_gt_of_ne hi
    · simpa [hi.ne, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField] using H i hi
    · simp [hi.ne', coeff_eq_zero_of_natDegree_lt hi]

namespace PrimeSpectrum

set_option backward.isDefEq.respectTransparency false in
/-- Let `A` be an `R`-algebra.
`𝔭 : Spec R` is in the image of `Z(I) ∩ D(f) ⊆ Spec S`
if and only if `f` is not nilpotent on `κ(𝔭) ⊗ A ⧸ I`. -/
/-
**PrimeSpectrum.mem_image_comap_zeroLocus_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Prime
Spectrum`。
形式化陈述：mem_image_comap_zeroLocus_sdiff (f : A) (s : Set A) (x) : x in comap (alge
braMap R A) '' (zeroLocus s \ zeroLocus {f}) ↔ ¬ IsNilpotent (algebraMap A ((A ⧸
 Ideal.span s) otimes[R] x.asIdeal.ResidueField) f)
参数：f : A；s : Set A；x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用引理 `Ideal.ker_algebraMap_residueField`：Ideal.ker_algebraMap_residueField : R
ingHom.ker (algebraMap R I.ResidueField) = I
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `IsNilpotent.map`：IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {
r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpot
ent r…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `isNilpotent_iff_eq_zero`：isNilpotent_iff_eq_zero [MonoidWithZero R] [IsR
educed R] : IsNilpotent x ↔ x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `nilradical_eq_sInf`：nilradical_eq_sInf (R : Type*) [CommSemiring R] : ni
lradical R = sInf { J : Ideal R | J.IsPrime }
· 使用定理 `mem_nilradical`：mem_nilradical : x in nilradical R ↔ IsNilpotent x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Let `A` be an `R`-algebra.
`𝔭 : Spec R` is in the image of `Z(I) ∩ D(f) ⊆ Spec S`
if and only if `f` is not nilpotent on `κ(𝔭) ⊗ A ⧸ I`.
-/
lemma mem_image_comap_zeroLocus_sdiff (f : A) (s : Set A) (x) :
    x ∈ comap (algebraMap R A) '' (zeroLocus s \ zeroLocus {f}) ↔
      ¬ IsNilpotent (algebraMap A ((A ⧸ Ideal.span s) ⊗[R] x.asIdeal.ResidueField) f) := by
  constructor
  · rintro ⟨q, ⟨hqg, hqf⟩, rfl⟩ H
    simp only [mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] at hqg hqf
    have hs : Ideal.span s ≤ RingHom.ker (algebraMap A q.asIdeal.ResidueField) := by
      rwa [Ideal.span_le, Ideal.ker_algebraMap_residueField]
    let F : (A ⧸ Ideal.span s) ⊗[R] (q.asIdeal.comap (algebraMap R A)).ResidueField →ₐ[A]
        q.asIdeal.ResidueField :=
      Algebra.TensorProduct.lift
        (Ideal.Quotient.liftₐ (Ideal.span s) (Algebra.ofId A _) hs)
        (Ideal.ResidueField.mapₐ _ _ (Algebra.ofId _ _) rfl)
        fun _ _ ↦ .all _ _
    have := H.map F
    rw [AlgHom.commutes, isNilpotent_iff_eq_zero, ← RingHom.mem_ker,
      Ideal.ker_algebraMap_residueField] at this
    exact hqf this
  · intro H
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf] at H
    simp only [Set.mem_ofPred_eq, Algebra.TensorProduct.algebraMap_apply,
      Ideal.Quotient.algebraMap_eq, not_forall] at H
    obtain ⟨q, hq, hfq⟩ := H
    have : ∀ a ∈ s, Ideal.Quotient.mk (Ideal.span s) a ⊗ₜ[R] 1 ∈ q := fun a ha ↦ by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ha)]
    refine ⟨comap (algebraMap A _) ⟨q, hq⟩, ⟨by simpa [Set.subset_def], by simpa⟩, ?_⟩
    rw [← comap_comp_apply, ← IsScalarTower.algebraMap_eq,
      ← Algebra.TensorProduct.includeRight.comp_algebraMap, comap_comp_apply,
      Subsingleton.elim (α := PrimeSpectrum x.asIdeal.ResidueField) (comap _ _) ⊥]
    ext a
    exact congr(a ∈ $(Ideal.ker_algebraMap_residueField _))

/-- Let `A` be an `R`-algebra.
`𝔭 : Spec R` is in the image of `D(f) ⊆ Spec S`
if and only if `f` is not nilpotent on `κ(𝔭) ⊗ A`. -/
/-
**PrimeSpectrum.mem_image_comap_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectr
um`。
形式化陈述：mem_image_comap_basicOpen (f : A) (x) : x in comap (algebraMap R A) '' bas
icOpen f ↔ ¬ IsNilpotent (algebraMap A (A otimes[R] x.asIdeal.ResidueField) f)
参数：f : A；x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_empty`：span_empty : span (∅ : Set α) = ⊥
· 使用定理 `Ideal.instIsTwoSidedBot`：∀ {α : Type u} [inst : Semiring α], ⊥.IsTwoSide
d
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsNilpotent.map_iff`：IsNilpotent.map_iff [MonoidWithZero R] [MonoidWithZ
ero S] {r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] {f : F
} (hf : F…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用引理 `PrimeSpectrum.mem_image_comap_zeroLocus_sdiff`：mem_image_comap_zeroLocus
_sdiff (f : A) (s : Set A) (x) : x in comap (algebraMap R A) '' (zeroLocus s \ z
eroLocus {f}) ↔ ¬ IsNilpotent (alge…
· 使用定理 `PrimeSpectrum.zeroLocus_empty`：zeroLocus_empty : zeroLocus (∅ : Set R) =
 Set.univ
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Let `A` be an `R`-algebra.
`𝔭 : Spec R` is in the image of `D(f) ⊆ Spec S`
if and only if `f` is not nilpotent on `κ(𝔭) ⊗ A`.
-/
lemma mem_image_comap_basicOpen (f : A) (x) :
    x ∈ comap (algebraMap R A) '' basicOpen f ↔
      ¬ IsNilpotent (algebraMap A (A ⊗[R] x.asIdeal.ResidueField) f) := by
  have e : A ⊗[R] x.asIdeal.ResidueField ≃ₐ[A]
      (A ⧸ (Ideal.span ∅ : Ideal A)) ⊗[R] x.asIdeal.ResidueField := by
    refine Algebra.TensorProduct.congr ?f AlgEquiv.refl
    rw [Ideal.span_empty]
    exact { __ := (RingEquiv.quotientBot A).symm, __ := Algebra.ofId _ _ }
  rw [← IsNilpotent.map_iff e.injective, AlgEquiv.commutes,
    ← mem_image_comap_zeroLocus_sdiff f ∅ x, zeroLocus_empty, ← Set.compl_eq_univ_sdiff,
    basicOpen_eq_zeroLocus_compl]

/-- Let `A` be an `R`-algebra. If `A ⧸ I` is finite free over `R`,
then the image of `Z(I) ∩ D(f) ⊆ Spec S` in `Spec R` is compact open. -/
/-
**PrimeSpectrum.exists_image_comap_of_finite_of_free** 是 Mathlib 中的一个引理，位于命名空间 `
PrimeSpectrum`。
形式化陈述：exists_image_comap_of_finite_of_free (f : A) (s : Set A) [Module.Finite R 
(A ⧸ Ideal.span s)] [Module.Free R (A ⧸ Ideal.span s)] : exists t : Finset R, co
map (algebraMap R A) '' (zeroLocus s \ zeroLocus {f}) = (zeroLocus t)ᶜ
参数：f : A；s : Set A；A ⧸ Ideal.span s；A ⧸ Ideal.span s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.mem_image_comap_zeroLocus_sdiff`：mem_image_comap_zeroLocus
_sdiff (f : A) (s : Set A) (x) : x in comap (algebraMap R A) '' (zeroLocus s \ z
eroLocus {f}) ↔ ¬ IsNilpotent (alge…
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用引理 `isNilpotent_tensor_residueField_iff`：isNilpotent_tensor_residueField_iff
 [Module.Free R A] [Module.Finite R A] (f : A) (I : Ideal R) [I.IsPrime] : IsNil
potent (algebraMap A (A o…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Let `A` be an `R`-algebra. If `A ⧸ I` is finite free over `R`,
then the image of `Z(I) ∩ D(f) ⊆ Spec S` in `Spec R` is compact open.
-/
lemma exists_image_comap_of_finite_of_free (f : A) (s : Set A)
    [Module.Finite R (A ⧸ Ideal.span s)] [Module.Free R (A ⧸ Ideal.span s)] :
    ∃ t : Finset R, comap (algebraMap R A) '' (zeroLocus s \ zeroLocus {f}) = (zeroLocus t)ᶜ := by
  classical
  use (Finset.range (Module.finrank R (A ⧸ Ideal.span s))).image
    (Algebra.lmul R (A ⧸ Ideal.span s) (Ideal.Quotient.mk _ f)).charpoly.coeff
  ext x
  rw [mem_image_comap_zeroLocus_sdiff, IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span s),
    isNilpotent_tensor_residueField_iff]
  simp [Set.subset_def]

end PrimeSpectrum

namespace Polynomial

/-
**Polynomial.mem_image_comap_C_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mem_image_comap_C_basicOpen (f : R[X]) (x : PrimeSpectrum R) : x in comap 
C '' basicOpen f ↔ exists i, f.coeff i ∉ x.asIdeal
参数：f : R[X]；x : PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `PrimeSpectrum.mem_image_comap_basicOpen`：mem_image_comap_basicOpen (f : 
A) (x) : x in comap (algebraMap R A) '' basicOpen f ↔ ¬ IsNilpotent (algebraMap 
A (A otimes[R] x.asIdeal.Resi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsNilpotent.map_iff`：IsNilpotent.map_iff [MonoidWithZero R] [MonoidWithZ
ero S] {r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] {f : F
} (hf : F…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `isNilpotent_iff_eq_zero`：isNilpotent_iff_eq_zero [MonoidWithZero R] [IsR
educed R] : IsNilpotent x ↔ x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
-/
lemma mem_image_comap_C_basicOpen (f : R[X]) (x : PrimeSpectrum R) :
    x ∈ comap C '' basicOpen f ↔ ∃ i, f.coeff i ∉ x.asIdeal := by
  trans f.map (algebraMap R x.asIdeal.ResidueField) ≠ 0
  · refine (mem_image_comap_basicOpen _ _).trans (not_iff_not.mpr ?_)
    let e : R[X] ⊗[R] x.asIdeal.ResidueField ≃ₐ[R] x.asIdeal.ResidueField[X] :=
      (Algebra.TensorProduct.comm R _ _).trans (polyEquivTensor R x.asIdeal.ResidueField).symm
    rw [← IsNilpotent.map_iff e.injective, isNilpotent_iff_eq_zero]
    simp [e]
  · simp [Polynomial.ext_iff]
/-
**Polynomial.image_comap_C_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：image_comap_C_basicOpen (f : R[X]) : comap C '' basicOpen f = (zeroLocus (
Set.range f.coeff))ᶜ
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.mem_image_comap_C_basicOpen`：mem_image_comap_C_basicOpen (f :
 R[X]) (x : PrimeSpectrum R) : x in comap C '' basicOpen f ↔ exists i, f.coeff i
 ∉ x.asIdeal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_comap_C_basicOpen (f : R[X]) :
    comap C '' basicOpen f = (zeroLocus (Set.range f.coeff))ᶜ := by
  ext p
  rw [mem_image_comap_C_basicOpen]
  simp [Set.range_subset_iff]
/-
**Polynomial.isOpenMap_comap_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isOpenMap_comap_C : IsOpenMap (comap (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion`：∀ {α : Type u} [t : 
TopologicalSpace α] {B : Set (Set α)},   TopologicalSpace.IsTopologicalBasis B →
 ∀ {u : Set α}, IsOpen u → ∃ S ⊆ B, u = …
· 使用定理 `PrimeSpectrum.isTopologicalBasis_basic_opens`：isTopologicalBasis_basic_o
pens : TopologicalSpace.IsTopologicalBasis (Set.range fun r : R => (basicOpen r 
: Set (PrimeSpectrum R)))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_sUnion`：image_sUnion {f : α -> β} {s : Set (Set α)} : (f '' ⋃₀
 s) = ⋃₀ (image f '' s)
· 使用定理 `isOpen_sUnion`：isOpen_sUnion {s : Set (Set X)} (h : forall t in s, IsOpe
n t) : IsOpen (⋃₀ s)
· 使用引理 `Polynomial.image_comap_C_basicOpen`：image_comap_C_basicOpen (f : R[X]) :
 comap C '' basicOpen f = (zeroLocus (Set.range f.coeff))ᶜ
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isOpenMap_comap_C : IsOpenMap (comap (R := R) C) := by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := isTopologicalBasis_basic_opens.open_eq_sUnion hU
  rw [Set.image_sUnion]
  apply isOpen_sUnion
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, rfl⟩ := hS ht
  simp only [image_comap_C_basicOpen]
  exact (isClosed_zeroLocus _).isOpen_compl
/-
**Polynomial.comap_C_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：comap_C_surjective : Function.Surjective (comap (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.comap_comp_apply`：comap_comp_apply (f : R ->+* S) (g : S -
>+* S') (x : PrimeSpectrum S') : comap (g.comp f) x = comap f (comap g x)
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PrimeSpectrum.comap_id`：comap_id : comap (RingHom.id R) = fun x => x
-/
lemma comap_C_surjective : Function.Surjective (comap (R := R) C) := by
  intro x
  refine ⟨comap (evalRingHom 0) x, ?_⟩
  rw [← comap_comp_apply, (show (evalRingHom 0).comp C = .id R by ext; simp),
    comap_id]
/-
**Polynomial.exists_image_comap_of_monic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：exists_image_comap_of_monic (f g : R[X]) (hg : g.Monic) : exists t : Finse
t R, comap C '' (zeroLocus {g} \ zeroLocus {f}) = (zeroLocus t)ᶜ
参数：f g : R[X]；hg : g.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.exists_image_comap_of_finite_of_free`：exists_image_comap_o
f_finite_of_free (f : A) (s : Set A) [Module.Finite R (A ⧸ Ideal.span s)] [Modul
e.Free R (A ⧸ Ideal.span s)] : exists t …
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
-/
lemma exists_image_comap_of_monic (f g : R[X]) (hg : g.Monic) :
    ∃ t : Finset R, comap C '' (zeroLocus {g} \ zeroLocus {f}) = (zeroLocus t)ᶜ := by
  apply +allowSynthFailures exists_image_comap_of_finite_of_free
  · exact .of_basis (AdjoinRoot.powerBasis' hg).basis
  · exact .of_basis (AdjoinRoot.powerBasis' hg).basis
/-
**Polynomial.isCompact_image_comap_of_monic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l`。
形式化陈述：isCompact_image_comap_of_monic (f g : R[X]) (hg : g.Monic) : IsCompact (co
map C '' (zeroLocus {g} \ zeroLocus {f}))
参数：f g : R[X]；hg : g.Monic。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.exists_image_comap_of_monic`：exists_image_comap_of_monic (f g
 : R[X]) (hg : g.Monic) : exists t : Finset R, comap C '' (zeroLocus {g} \ zeroL
ocus {f}) = (zeroLocus t)ᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_of_singleton_coe`：iUnion_of_singleton_coe (s : Set α) : ⋃ i :
 s, ({(i : α)} : Set α) = s
· 使用定理 `PrimeSpectrum.zeroLocus_iUnion`：zeroLocus_iUnion {ι : Sort*} (s : ι -> S
et R) : zeroLocus (⋃ i, s i) = ⋂ i, zeroLocus (s i)
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `isCompact_iUnion`：isCompact_iUnion {ι : Sort*} {f : ι -> Set X} [Finite 
ι] (h : forall i, IsCompact (f i)) : IsCompact (⋃ i, f i)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `PrimeSpectrum.isCompact_basicOpen`：isCompact_basicOpen (f : R) : IsCompa
ct (basicOpen f : Set (PrimeSpectrum R))
-/
lemma isCompact_image_comap_of_monic (f g : R[X]) (hg : g.Monic) :
    IsCompact (comap C '' (zeroLocus {g} \ zeroLocus {f})) := by
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g hg
  rw [ht, ← (t : Set R).iUnion_of_singleton_coe, zeroLocus_iUnion, Set.compl_iInter]
  apply isCompact_iUnion
  exact fun _ ↦ by simpa using isCompact_basicOpen _
/-
**Polynomial.isOpen_image_comap_of_monic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isOpen_image_comap_of_monic (f g : R[X]) (hg : g.Monic) : IsOpen (comap C 
'' (zeroLocus {g} \ zeroLocus {f}))
参数：f g : R[X]；hg : g.Monic。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.exists_image_comap_of_monic`：exists_image_comap_of_monic (f g
 : R[X]) (hg : g.Monic) : exists t : Finset R, comap C '' (zeroLocus {g} \ zeroL
ocus {f}) = (zeroLocus t)ᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
-/
lemma isOpen_image_comap_of_monic (f g : R[X]) (hg : g.Monic) :
    IsOpen (comap C '' (zeroLocus {g} \ zeroLocus {f})) := by
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g hg
  rw [ht]
  exact (isClosed_zeroLocus (R := R) t).isOpen_compl

end Polynomial

namespace MvPolynomial

variable {σ : Type*}

/-
**MvPolynomial.mem_image_comap_C_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomi
al`。
形式化陈述：mem_image_comap_C_basicOpen (f : MvPolynomial σ R) (x : PrimeSpectrum R) :
 x in comap (C (σ
参数：f : MvPolynomial σ R；x : PrimeSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `PrimeSpectrum.mem_image_comap_basicOpen`：mem_image_comap_basicOpen (f : 
A) (x) : x in comap (algebraMap R A) '' basicOpen f ↔ ¬ IsNilpotent (algebraMap 
A (A otimes[R] x.asIdeal.Resi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsNilpotent.map_iff`：IsNilpotent.map_iff [MonoidWithZero R] [MonoidWithZ
ero S] {r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] {f : F
} (hf : F…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `isNilpotent_iff_eq_zero`：isNilpotent_iff_eq_zero [MonoidWithZero R] [IsR
educed R] : IsNilpotent x ↔ x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MvPolynomial.ringHom_ext'`：ringHom_ext' {A : Type*} [Semiring A] {f g : 
MvPolynomial σ R ->+* A} (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g 
(X i)) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.scalarRTensorAlgEquiv.eq_1`：∀ {R : Type u} {N : Type v} [in
st : CommSemiring R] {σ : Type u_1} [inst_1 : CommSemiring N] [inst_2 : Algebra 
R N],   MvPolynomial.scalarRT…
（共 46 条，此处仅展示前 30 条）
-/
lemma mem_image_comap_C_basicOpen (f : MvPolynomial σ R) (x : PrimeSpectrum R) :
    x ∈ comap (C (σ := σ)) '' basicOpen f ↔ ∃ i, f.coeff i ∉ x.asIdeal := by
  trans f.map (algebraMap R x.asIdeal.ResidueField) ≠ 0
  · refine (mem_image_comap_basicOpen _ _).trans (not_iff_not.mpr ?_)
    let e : x.asIdeal.ResidueField ⊗[R] MvPolynomial σ R ≃ₐ[x.asIdeal.ResidueField]
        MvPolynomial σ x.asIdeal.ResidueField := scalarRTensorAlgEquiv
    rw [← IsNilpotent.map_iff (Algebra.TensorProduct.comm ..).injective,
      ← IsNilpotent.map_iff e.injective, isNilpotent_iff_eq_zero]
    change (e.toAlgHom.toRingHom.comp (Algebra.TensorProduct.comm ..).toRingHom).comp
      (algebraMap _ _) f = 0 ↔ MvPolynomial.map _ f = 0
    congr!
    ext
    · simp [scalarRTensorAlgEquiv, e, Algebra.smul_def]
    · simp [e, scalarRTensorAlgEquiv, coeff, map, X, monomial]
  · simp [MvPolynomial.ext_iff, coeff_map]
/-
**MvPolynomial.image_comap_C_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：image_comap_C_basicOpen (f : MvPolynomial σ R) : comap (C (σ
参数：f : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.mem_image_comap_C_basicOpen`：mem_image_comap_C_basicOpen (f
 : MvPolynomial σ R) (x : PrimeSpectrum R) : x in comap (C (σ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_comap_C_basicOpen (f : MvPolynomial σ R) :
    comap (C (σ := σ)) '' basicOpen f = (zeroLocus (Set.range f.coeff))ᶜ := by
  ext p
  rw [mem_image_comap_C_basicOpen]
  simp [Set.range_subset_iff]
/-
**MvPolynomial.isOpenMap_comap_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：isOpenMap_comap_C : IsOpenMap (comap (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion`：∀ {α : Type u} [t : 
TopologicalSpace α] {B : Set (Set α)},   TopologicalSpace.IsTopologicalBasis B →
 ∀ {u : Set α}, IsOpen u → ∃ S ⊆ B, u = …
· 使用定理 `PrimeSpectrum.isTopologicalBasis_basic_opens`：isTopologicalBasis_basic_o
pens : TopologicalSpace.IsTopologicalBasis (Set.range fun r : R => (basicOpen r 
: Set (PrimeSpectrum R)))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_sUnion`：image_sUnion {f : α -> β} {s : Set (Set α)} : (f '' ⋃₀
 s) = ⋃₀ (image f '' s)
· 使用定理 `isOpen_sUnion`：isOpen_sUnion {s : Set (Set X)} (h : forall t in s, IsOpe
n t) : IsOpen (⋃₀ s)
· 使用引理 `MvPolynomial.image_comap_C_basicOpen`：image_comap_C_basicOpen (f : MvPol
ynomial σ R) : comap (C (σ
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isOpenMap_comap_C : IsOpenMap (comap (R := R) (C (σ := σ))) := by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := isTopologicalBasis_basic_opens.open_eq_sUnion hU
  rw [Set.image_sUnion]
  apply isOpen_sUnion
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, rfl⟩ := hS ht
  simp only [image_comap_C_basicOpen]
  exact (isClosed_zeroLocus _).isOpen_compl
/-
**MvPolynomial.comap_C_surjective** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：comap_C_surjective : Function.Surjective (comap (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.comap_comp_apply`：comap_comp_apply (f : R ->+* S) (g : S -
>+* S') (x : PrimeSpectrum S') : comap (g.comp f) x = comap f (comap g x)
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.eval₂Hom_zero`：eval₂Hom_zero (f : R ->+* S₂) : eval₂Hom f (
0 : σ -> S₂) = f.comp constantCoeff
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `MvPolynomial.constantCoeff_comp_C`：constantCoeff_comp_C : constantCoeff.
comp (C : R ->+* MvPolynomial σ R) = RingHom.id R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PrimeSpectrum.comap_id`：comap_id : comap (RingHom.id R) = fun x => x
-/
lemma comap_C_surjective : Function.Surjective (comap (R := R) (C (σ := σ))) := by
  intro x
  refine ⟨comap (eval₂Hom (.id _) 0) x, ?_⟩
  rw [← comap_comp_apply, (show (eval₂Hom (.id _) 0).comp C = .id R by ext; simp),
    comap_id]

end MvPolynomial

