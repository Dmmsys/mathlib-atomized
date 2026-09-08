/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.Extension
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.GroupTheory.Solvable

/-!
# Normal field extensions

In this file we prove that for a finite extension, being normal
is the same as being a splitting field (`Normal.of_isSplittingField` and
`Normal.exists_isSplittingField`).

## Additional Results

* `Algebra.IsQuadraticExtension.normal`: the instance that a quadratic extension, given as a class
  `Algebra.IsQuadraticExtension`, is normal.

-/

@[expose] public section


noncomputable section

open Polynomial IsScalarTower

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-
**Normal.exists_isSplittingField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Normal.exists_isSplittingField [h : Normal F K] [FiniteDimensional F K] : 
exists p : F[X], IsSplittingField F K p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Polynomial.Splits.prod`：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Ty
pe u_2} {f : ι → Polynomial R} {s : Finset ι},   (∀ i ∈ s, (f i).Splits) → (∏ i 
∈ s, f i).Sp…
· 使用定理 `Normal.splits`：Normal.splits (_ : Normal F K) (x : K) : Splits ((minpoly
 F x).map (algebraMap F K))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_prod`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R]
 [inst_1 : CommSemiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R)
 (s : Fin…
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.top_toSubmodule`：top_toSubmodule : Subalgebra.toSubmodule (⊤ : S
ubalgebra R A) = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.map_eq_zero`：∀ {R : Type u} {S : Type v} [inst : Ring R] [IsS
impleRing R] [inst_2 : Semiring S] [Nontrivial S] {p : Polynomial R}   (f : R →+
* S), Polyno…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `Normal.isIntegral`：Normal.isIntegral (_ : Normal F K) (x : K) : IsIntegr
al F x
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
（共 38 条，此处仅展示前 30 条）
-/
theorem Normal.exists_isSplittingField [h : Normal F K] [FiniteDimensional F K] :
    ∃ p : F[X], IsSplittingField F K p := by
  classical
  let s := Module.Basis.ofVectorSpace F K
  refine
    ⟨∏ x, minpoly F (s x), Polynomial.map_prod (algebraMap F K) _ _ ▸
      Splits.prod fun x _ => h.splits (s x), Subalgebra.toSubmodule.injective ?_⟩
  rw [Algebra.top_toSubmodule, eq_top_iff, ← s.span_eq, Submodule.span_le, Set.range_subset_iff]
  refine fun x =>
    Algebra.subset_adjoin
      (Multiset.mem_toFinset.mpr <|
        (mem_roots <|
              mt (Polynomial.map_eq_zero <| algebraMap F K).1 <|
                Finset.prod_ne_zero_iff.2 fun x _ => ?_).2 ?_)
  · exact minpoly.ne_zero (h.isIntegral (s x))
  rw [IsRoot.def, eval_map_algebraMap, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ _) (minpoly.aeval _ _)

section NormalTower

variable (E : Type*) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

variable {E F}

open IntermediateField

@[stacks 09HU "Normal part"]
/-
**Normal.of_isSplittingField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Normal.of_isSplittingField (p : F[X]) [hFEp : IsSplittingField F E p] : No
rmal F E
参数：p : F[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.IsSplittingField.adjoin_rootSet`：adjoin_rootSet (f : K[X]) [I
sSplittingField K L f] : Algebra.adjoin K (f.rootSet L : Set L) = ⊤
· 使用定理 `Normal.of_algEquiv`：Normal.of_algEquiv [h : Normal F E] (f : E ≃ₐ[F] E')
 : Normal F E'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.bijective_algebraMap_iff`：bijective_algebraMap_iff {R A : Type*}
 [Field R] [Semiring A] [Nontrivial A] [Algebra R A] : Function.Bijective (algeb
raMap R A) ↔ (⊤ : Suba…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_empty`：adjoin_empty : adjoin R (∅ : Set A) = ⊥
· 使用定理 `Polynomial.rootSet_zero`：rootSet_zero (S) [CommRing S] [IsDomain S] [Alg
ebra T S] : (0 : T[X]).rootSet S = ∅
· 使用定理 `normal_iff`：normal_iff : Normal F K ↔ forall x : K, IsIntegral F x ∧ Spl
its ((minpoly F x).map (algebraMap F K))
· 使用定理 `Polynomial.IsSplittingField.finiteDimensional`：finiteDimensional (f : K[
X]) [IsSplittingField K L f] : FiniteDimensional K L
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `Polynomial.splits_mul`：splits_mul (hf₀ : f != 0) (hg₀ : g != 0) : Splits
 (f * g) ↔ Splits f ∧ Splits g
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.Splits.of_splits_map`：∀ {R : Type u_1} {S : Type u_2} [inst :
 Field R] [inst_1 : CommRing S] [inst_2 : IsDomain S] {f : Polynomial R}   (i : 
R →+* S), (Polynomial…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
（共 35 条，此处仅展示前 30 条）
-/
theorem Normal.of_isSplittingField (p : F[X]) [hFEp : IsSplittingField F E p] : Normal F E := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · have := hFEp.adjoin_rootSet
    rw [rootSet_zero, Algebra.adjoin_empty] at this
    exact Normal.of_algEquiv
      (AlgEquiv.ofBijective (Algebra.ofId F E) (Algebra.bijective_algebraMap_iff.2 this.symm))
  refine normal_iff.mpr fun x ↦ ?_
  have : FiniteDimensional F E := IsSplittingField.finiteDimensional E p
  have hx := IsIntegral.of_finite F x
  let L := (p * minpoly F x).SplittingField
  have hL := SplittingField.splits (p * minpoly F x)
  rw [Polynomial.map_mul, splits_mul _ (map_ne_zero (minpoly.ne_zero hx))] at hL
  · obtain ⟨hL1, hL2⟩ := hL
    let j : E →ₐ[F] L := IsSplittingField.lift E p hL1
    rw [← j.comp_algebraMap, ← Polynomial.map_map] at hL2
    refine ⟨hx, Splits.of_splits_map (j : E →+* L) hL2 fun a ha ↦ ?_⟩
    rw [Polynomial.map_map, j.comp_algebraMap] at ha
    let : Algebra F⟮x⟯ L := ((algHomAdjoinIntegralEquiv F hx).symm ⟨a, ha⟩).toRingHom.toAlgebra
    let j' : E →ₐ[F⟮x⟯] L := IsSplittingField.lift E (p.map (algebraMap F F⟮x⟯)) ?_
    · change a ∈ j.range
      rw [← IsSplittingField.adjoin_rootSet_eq_range E p j,
            IsSplittingField.adjoin_rootSet_eq_range E p (j'.restrictScalars F)]
      exact ⟨x, (j'.commutes _).trans (algHomAdjoinIntegralEquiv_symm_apply_gen F hx _)⟩
    · rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  · exact Polynomial.map_ne_zero hp
/-
**Polynomial.SplittingField.instNormal** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Polynomial.SplittingField.instNormal (p : F[X]) : Normal F p.SplittingFiel
d
参数：p : F[X]。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Normal.of_isSplittingField`：Normal.of_isSplittingField (p : F[X]) [hFEp 
: IsSplittingField F E p] : Normal F E
· 使用定理 `Polynomial.IsSplittingField.splittingField`：∀ {K : Type v} [inst : Field
 K] (f : Polynomial K), Polynomial.IsSplittingField K f.SplittingField f
-/
instance Polynomial.SplittingField.instNormal (p : F[X]) : Normal F p.SplittingField :=
  Normal.of_isSplittingField p

end NormalTower

namespace IntermediateField

/-- A compositum of normal extensions is normal. -/
/-
**IntermediateField.normal_iSup** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：normal_iSup {ι : Type*} (t : ι -> IntermediateField F K) [h : forall i, No
rmal F (t i)] : Normal F (⨆ i, t i : IntermediateField F K)
参数：t : ι -> IntermediateField F K；t i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.isAlgebraic_iSup`：isAlgebraic_iSup {ι : Type*} {t : ι 
-> IntermediateField K L} (h : forall i, Algebra.IsAlgebraic K (t i)) : Algebra.
IsAlgebraic K (⨆ i, t i …
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.exists_finset_of_mem_supr''`：exists_finset_of_mem_supr
'' {ι : Type*} {f : ι -> IntermediateField F E} (h : forall i, Algebra.IsAlgebra
ic F (f i)) {x : E} (hx : x in ⨆ i,…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IntermediateField.isSplittingField_iSup`：isSplittingField_iSup {p : ι ->
 K[X]} {s : Finset ι} (h0 : ∏ i in s, p i != 0) (h : forall i in s, (p i).IsSpli
ttingField K (t i)) : (∏ i in…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `Normal.isIntegral`：Normal.isIntegral (_ : Normal F K) (x : K) : IsIntegr
al F x
· 使用定理 `IntermediateField.adjoin_rootSet_isSplittingField`：IntermediateField.adj
oin_rootSet_isSplittingField (hp : (p.map (algebraMap K L)).Splits) : p.IsSplitt
ingField K (adjoin K (p.rootSet L))
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `Normal.splits`：Normal.splits (_ : Normal F K) (x : K) : Splits ((minpoly
 F x).map (algebraMap F K))
· 使用定理 `Normal.of_isSplittingField`：Normal.of_isSplittingField (p : F[X]) [hFEp 
: IsSplittingField F E p] : Normal F E
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Splits.image_rootSet`：∀ {R : Type u_1} {A : Type u_2} {B : Ty
pe u_3} [inst : CommRing R] [inst_1 : Field A] [inst_2 : Algebra R A]   [inst_3 
: CommRing B] [inst_4…
· 使用定理 `IntermediateField.minpoly_eq`：minpoly_eq (x : S) : minpoly K x = minpoly
 K (x : L)
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a

--- 原说明 ---
A compositum of normal extensions is normal.
-/
instance normal_iSup {ι : Type*} (t : ι → IntermediateField F K) [h : ∀ i, Normal F (t i)] :
    Normal F (⨆ i, t i : IntermediateField F K) := by
  refine { toIsAlgebraic := isAlgebraic_iSup fun i => (h i).1, splits' := fun x => ?_ }
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr'' (fun i => (h i).1) x.2
  let E : IntermediateField F K := ⨆ i ∈ s, adjoin F ((minpoly F (i.2 :)).rootSet K)
  have hF : Normal F E := by
    have : IsSplittingField F E (∏ i ∈ s, minpoly F i.snd) := by
      refine isSplittingField_iSup ?_ fun i _ => adjoin_rootSet_isSplittingField ?_
      · exact Finset.prod_ne_zero_iff.mpr fun i _ => minpoly.ne_zero ((h i.1).isIntegral i.2)
      · simpa [Polynomial.map_map] using! ((h i.1).splits i.2).map (algebraMap (t i.1) K)
    apply Normal.of_isSplittingField (∏ i ∈ s, minpoly F i.2)
  have hE : E ≤ ⨆ i, t i := by
    refine iSup_le fun i => iSup_le fun _ => le_iSup_of_le i.1 ?_
    rw [adjoin_le_iff, ← ((h i.1).splits i.2).image_rootSet (t i.1).val]
    exact fun _ ⟨a, _, h⟩ => h ▸ a.2
  have := hF.splits ⟨x, hx⟩
  rw [minpoly_eq, Subtype.coe_mk, ← minpoly_eq] at this
  have := this.map (inclusion hE).toRingHom -- necessary for performance reasons
  rwa [Polynomial.map_map] at this

/-- If a set of algebraic elements in a field extension `K/F` have minimal polynomials that
  split in another extension `L/F`, then all minimal polynomials in the intermediate field
  generated by the set also split in `L/F`. -/
@[stacks 0BR3 "first part"]
/-
**IntermediateField.splits_of_mem_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：splits_of_mem_adjoin {L} [Field L] [Algebra F L] {S : Set K} (splits : for
all x in S, IsIntegral F x ∧ ((minpoly F x).map (algebraMap F L)).Splits) {x : K
} (hx : x in adjoin F S) : ((minpoly F x).map (algebraMap F L)).Splits
参数：splits : forall x in S, IsIntegral F x ∧ ((minpoly F x).map (algebraMap F L))
.Splits；hx : x in adjoin F S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Normal.of_isSplittingField`：Normal.of_isSplittingField (p : F[X]) [hFEp 
: IsSplittingField F E p] : Normal F E
· 使用定理 `IntermediateField.adjoin_rootSet_isSplittingField`：IntermediateField.adj
oin_rootSet_isSplittingField (hp : (p.map (algebraMap K L)).Splits) : p.IsSplitt
ingField K (adjoin K (p.rootSet L))
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IntermediateField.splits_of_splits`：IntermediateField.splits_of_splits (
h : (p.map (algebraMap K L)).Splits) (hF : forall x in p.rootSet L, x in F) : (p
.map (algebraMap K F)).S…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `IntermediateField.nonempty_algHom_adjoin_of_splits`：nonempty_algHom_adjo
in_of_splits : Nonempty (adjoin F S ->ₐ[F] K)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `minpoly.algHom_eq`：algHom_eq (f : B ->ₐ[A] B') (hf : Function.Injective 
f) (x : B) : minpoly A (f x) = minpoly A x
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `Normal.splits`：Normal.splits (_ : Normal F K) (x : K) : Splits ((minpoly
 F x).map (algebraMap F K))

--- 原说明 ---
If a set of algebraic elements in a field extension `K/F` have minimal polynomia
ls that
  split in another extension `L/F`, then all minimal polynomials in the intermed
iate field
  generated by the set also split in `L/F`.
-/
theorem splits_of_mem_adjoin {L} [Field L] [Algebra F L] {S : Set K}
    (splits : ∀ x ∈ S, IsIntegral F x ∧ ((minpoly F x).map (algebraMap F L)).Splits) {x : K}
    (hx : x ∈ adjoin F S) : ((minpoly F x).map (algebraMap F L)).Splits := by
  let E : IntermediateField F L := ⨆ x : S, adjoin F ((minpoly F x.val).rootSet L)
  have normal : Normal F E := normal_iSup (h := fun x ↦
    Normal.of_isSplittingField (hFEp := adjoin_rootSet_isSplittingField (splits x x.2).2))
  have : ∀ x ∈ S, ((minpoly F x).map (algebraMap F E)).Splits := fun x hx ↦ splits_of_splits
    (splits x hx).2 fun y hy ↦ (le_iSup _ ⟨x, hx⟩ : _ ≤ E) (subset_adjoin F _ <| by exact hy)
  obtain ⟨φ⟩ := nonempty_algHom_adjoin_of_splits fun x hx ↦ ⟨(splits x hx).1, this x hx⟩
  convert! (normal.splits <| φ ⟨x, hx⟩).map E.val.toRingHom
  simp [minpoly.algHom_eq _ φ.injective, ← minpoly.algHom_eq _ (adjoin F S).val.injective,
    Polynomial.map_map]
/-
**IntermediateField.normal_sup** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：normal_sup (E E' : IntermediateField F K) [Normal F E] [Normal F E'] : Nor
mal F (E ⊔ E' : IntermediateField F K)
参数：E E' : IntermediateField F K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_bool_eq`：iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ 
f false
-/
instance normal_sup
    (E E' : IntermediateField F K) [Normal F E] [Normal F E'] :
    Normal F (E ⊔ E' : IntermediateField F K) :=
  iSup_bool_eq (f := Bool.rec E' E) ▸ normal_iSup (h := by rintro (_ | _) <;> infer_instance)

/-- An intersection of normal extensions is normal. -/
@[stacks 09HP]
/-
**IntermediateField.normal_iInf** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：normal_iInf {ι : Type*} [hι : Nonempty ι] (t : ι -> IntermediateField F K)
 [h : forall i, Normal F (t i)] : Normal F (⨅ i, t i : IntermediateField F K)
参数：t : ι -> IntermediateField F K；t i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `Algebra.IsAlgebraic.of_injective`：Algebra.IsAlgebraic.of_injective (f : 
A ->ₐ[R] B) (hf : Function.Injective f) [Algebra.IsAlgebraic R B] : Algebra.IsAl
gebraic R A
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.algHom_eq`：algHom_eq (f : B ->ₐ[A] B') (hf : Function.Injective 
f) (x : B) : minpoly A (f x) = minpoly A x
· 使用定理 `Normal.splits'`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {inst_1
 : Field K} {inst_2 : Algebra F K} [self : Normal F K] (x : K),   (Polynomial.ma
p (a…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.splits_iff_mem`：IntermediateField.splits_iff_mem (h : 
(p.map (algebraMap K L)).Splits) : (p.map (algebraMap K F)).Splits ↔ forall x in
 p.rootSet L, x in F
· 使用定理 `Polynomial.Splits.of_isScalarTower`：∀ {R : Type u_1} [inst : CommSemirin
g R] {f : Polynomial R} {A : Type u_2} (B : Type u_3) [inst_1 : CommSemiring A] 
  [inst_2 : Semiring B] …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
An intersection of normal extensions is normal.
-/
instance normal_iInf {ι : Type*} [hι : Nonempty ι]
    (t : ι → IntermediateField F K) [h : ∀ i, Normal F (t i)] :
    Normal F (⨅ i, t i : IntermediateField F K) := by
  refine { toIsAlgebraic := ?_, splits' := fun x => ?_ }
  · let f := inclusion (iInf_le t hι.some)
    exact Algebra.IsAlgebraic.of_injective f f.injective
  · have hx : ∀ i, Splits ((minpoly F x).map (algebraMap F (t i))) := by
      intro i
      rw [← minpoly.algHom_eq (inclusion (iInf_le t i)) (inclusion (iInf_le t i)).injective]
      exact (h i).splits' (inclusion (iInf_le t i) x)
    simp only [splits_iff_mem (Splits.of_isScalarTower K (hx hι.some))] at hx ⊢
    rintro y hy - ⟨-, ⟨i, rfl⟩, rfl⟩
    exact hx i y hy

@[stacks 09HP]
/-
**IntermediateField.normal_inf** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：normal_inf (E E' : IntermediateField F K) [Normal F E] [Normal F E'] : Nor
mal F (E ⊓ E' : IntermediateField F K)
参数：E E' : IntermediateField F K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iInf_bool_eq`：∀ {α : Type u_1} [inst : CompleteLattice α] {f : Bool → α}
, ⨅ b, f b = f true ⊓ f false
-/
instance normal_inf
    (E E' : IntermediateField F K) [Normal F E] [Normal F E'] :
    Normal F (E ⊓ E' : IntermediateField F K) :=
  iInf_bool_eq (f := Bool.rec E' E) ▸ normal_iInf (h := by rintro (_ | _) <;> infer_instance)

end IntermediateField

variable {F} {K}
variable {K₁ K₂ K₃ : Type*} [Field K₁] [Field K₂] [Field K₃] [Algebra F K₁]
  [Algebra F K₂] [Algebra F K₃] (ϕ : K₁ →ₐ[F] K₂) (χ : K₁ ≃ₐ[F] K₂) (ψ : K₂ →ₐ[F] K₃)
  (ω : K₂ ≃ₐ[F] K₃)

section Restrict

variable (E : Type*) [Field E] [Algebra F E] [Algebra E K₁] [Algebra E K₂] [Algebra E K₃]
  [IsScalarTower F E K₁] [IsScalarTower F E K₂] [IsScalarTower F E K₃]

/-
**AlgHom.fieldRange_of_normal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.fieldRange_of_normal {E : IntermediateField F K} [Normal F E] (f : 
E ->ₐ[F] K) : f.fieldRange = E
参数：f : E ->ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `AlgHom.restrictNormal_commutes`：AlgHom.restrictNormal_commutes [Normal F
 E] (x : E) : algebraMap E K₂ (ϕ.restrictNormal E x) = ϕ (algebraMap E K₁ x)
· 使用定理 `AlgHom.map_fieldRange`：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} 
[inst_1 : Field E] [inst_2 : Algebra F E] {K : Type u_3}   [inst_3 : Field K] [i
nst_4 : Alg…
· 使用定理 `AlgEquiv.fieldRange_eq_top`：∀ {F : Type u_1} [inst : Field F] {E : Type 
u_2} [inst_1 : Field E] [inst_2 : Algebra F E] {K : Type u_3}   [inst_3 : Field 
K] [inst_4 : Alg…
· 使用定理 `AlgHom.fieldRange_eq_map`：∀ {F : Type u_1} [inst : Field F] {E : Type u_
2} [inst_1 : Field E] [inst_2 : Algebra F E] {K : Type u_3}   [inst_3 : Field K]
 [inst_4 : Alg…
· 使用定理 `IntermediateField.fieldRange_val`：fieldRange_val : S.val.fieldRange = S
-/
theorem AlgHom.fieldRange_of_normal {E : IntermediateField F K} [Normal F E]
    (f : E →ₐ[F] K) : f.fieldRange = E := by
  let g := f.restrictNormal' E
  rw [← show E.val.comp ↑g = f from DFunLike.ext_iff.mpr (f.restrictNormal_commutes E),
    ← AlgHom.map_fieldRange, AlgEquiv.fieldRange_eq_top g, ← AlgHom.fieldRange_eq_map,
    IntermediateField.fieldRange_val]

end Restrict

section lift

variable (E : Type*) [Field E] [Algebra F E] [Algebra K₁ E] [Algebra K₂ E] [IsScalarTower F K₁ E]
  [IsScalarTower F K₂ E]

/-- If `E/Kᵢ/F` are towers of fields with `E/F` normal then we can lift
  an algebra homomorphism `ϕ : K₁ →ₐ[F] K₂` to `ϕ.liftNormal E : E →ₐ[F] E`. -/
@[stacks 0BME "Part 2"]
/-
**AlgHom.liftNormal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.liftNormal [h : Normal F E] : E ->ₐ[F] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E/Kᵢ/F` are towers of fields with `E/F` normal then we can lift
  an algebra homomorphism `ϕ : K₁ →ₐ[F] K₂` to `ϕ.liftNormal E : E →ₐ[F] E`.
-/
noncomputable def AlgHom.liftNormal [h : Normal F E] : E →ₐ[F] E :=
  @AlgHom.restrictScalars F K₁ E E _ _ _ _ _ _
      ((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _ _ _ _ <|
    Nonempty.some <|
      @IntermediateField.nonempty_algHom_of_adjoin_splits _ _ _ _ _ _ _
        ((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _
        (fun x _ ↦ ⟨(h.out x).1.tower_top,
          @IsIntegral.minpoly_splits_tower_top F K₁ E E _ _ _ _ _ _ _ _ x
            (RingHom.toAlgebra _) _ _ (h.out x).1 (h.out x).2⟩)
        (IntermediateField.adjoin_univ _ _)

@[simp]
/-
**AlgHom.liftNormal_commutes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.liftNormal_commutes [Normal F E] (x : K₁) : ϕ.liftNormal E (algebra
Map K₁ E x) = algebraMap K₂ E (ϕ x)
参数：x : K₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
theorem AlgHom.liftNormal_commutes [Normal F E] (x : K₁) :
    ϕ.liftNormal E (algebraMap K₁ E x) = algebraMap K₂ E (ϕ x) :=
  -- We have to specify one `Algebra` instance by unification, not synthesis.
  @AlgHom.commutes K₁ E E _ _ _ _ (_) _ _

@[simp]
/-
**AlgHom.restrict_liftNormal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.restrict_liftNormal (ϕ : K₁ ->ₐ[F] K₁) [Normal F K₁] [Normal F E] :
 (ϕ.liftNormal E).restrictNormal K₁ = ϕ
参数：ϕ : K₁ ->ₐ[F] K₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.restrictNormal_commutes`：AlgHom.restrictNormal_commutes [Normal F
 E] (x : E) : algebraMap E K₂ (ϕ.restrictNormal E x) = ϕ (algebraMap E K₁ x)
· 使用定理 `AlgHom.liftNormal_commutes`：AlgHom.liftNormal_commutes [Normal F E] (x :
 K₁) : ϕ.liftNormal E (algebraMap K₁ E x) = algebraMap K₂ E (ϕ x)
-/
theorem AlgHom.restrict_liftNormal (ϕ : K₁ →ₐ[F] K₁) [Normal F K₁] [Normal F E] :
    (ϕ.liftNormal E).restrictNormal K₁ = ϕ :=
  AlgHom.ext fun x =>
    (algebraMap K₁ E).injective
      (Eq.trans (AlgHom.restrictNormal_commutes _ K₁ x) (ϕ.liftNormal_commutes E x))

/-- If `E/Kᵢ/F` are towers of fields with `E/F` normal then we can lift
  an algebra isomorphism `ϕ : K₁ ≃ₐ[F] K₂` to `ϕ.liftNormal E : Gal(E/F)`. -/
/-
**AlgEquiv.liftNormal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgEquiv.liftNormal [Normal F E] : Gal(E/F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E/Kᵢ/F` are towers of fields with `E/F` normal then we can lift
  an algebra isomorphism `ϕ : K₁ ≃ₐ[F] K₂` to `ϕ.liftNormal E : Gal(E/F)`.
-/
noncomputable def AlgEquiv.liftNormal [Normal F E] : Gal(E/F) :=
  AlgEquiv.ofBijective (χ.toAlgHom.liftNormal E) (AlgHom.normal_bijective F E E _)

@[simp]
/-
**AlgEquiv.liftNormal_commutes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.liftNormal_commutes [Normal F E] (x : K₁) : χ.liftNormal E (algeb
raMap K₁ E x) = algebraMap K₂ E (χ x)
参数：x : K₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.liftNormal_commutes`：AlgHom.liftNormal_commutes [Normal F E] (x :
 K₁) : ϕ.liftNormal E (algebraMap K₁ E x) = algebraMap K₂ E (ϕ x)
-/
theorem AlgEquiv.liftNormal_commutes [Normal F E] (x : K₁) :
    χ.liftNormal E (algebraMap K₁ E x) = algebraMap K₂ E (χ x) :=
  χ.toAlgHom.liftNormal_commutes E x

@[simp]
/-
**AlgEquiv.restrict_liftNormal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.restrict_liftNormal (χ : K₁ ≃ₐ[F] K₁) [Normal F K₁] [Normal F E] 
: (χ.liftNormal E).restrictNormal K₁ = χ
参数：χ : K₁ ≃ₐ[F] K₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgEquiv.restrictNormal_commutes`：AlgEquiv.restrictNormal_commutes [Norm
al F E] (x : E) : algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x)
· 使用定理 `AlgEquiv.liftNormal_commutes`：AlgEquiv.liftNormal_commutes [Normal F E] 
(x : K₁) : χ.liftNormal E (algebraMap K₁ E x) = algebraMap K₂ E (χ x)
-/
theorem AlgEquiv.restrict_liftNormal (χ : K₁ ≃ₐ[F] K₁) [Normal F K₁] [Normal F E] :
    (χ.liftNormal E).restrictNormal K₁ = χ :=
  AlgEquiv.ext fun x =>
    (algebraMap K₁ E).injective
      (Eq.trans (AlgEquiv.restrictNormal_commutes _ K₁ x) (χ.liftNormal_commutes E x))

/-- The group homomorphism given by restricting an algebra isomorphism to a normal subfield
is surjective. -/
/-
**AlgEquiv.restrictNormalHom_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.restrictNormalHom_surjective [Normal F K₁] [Normal F E] : Functio
n.Surjective (AlgEquiv.restrictNormalHom K₁ : Gal(E/F) -> K₁ ≃ₐ[F] K₁)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.restrict_liftNormal`：AlgEquiv.restrict_liftNormal (χ : K₁ ≃ₐ[F]
 K₁) [Normal F K₁] [Normal F E] : (χ.liftNormal E).restrictNormal K₁ = χ

--- 原说明 ---
The group homomorphism given by restricting an algebra isomorphism to a normal s
ubfield
is surjective.
-/
theorem AlgEquiv.restrictNormalHom_surjective [Normal F K₁] [Normal F E] :
    Function.Surjective (AlgEquiv.restrictNormalHom K₁ : Gal(E/F) → K₁ ≃ₐ[F] K₁) := fun χ =>
  ⟨χ.liftNormal E, χ.restrict_liftNormal E⟩

open IntermediateField in
/-
**Normal.minpoly_eq_iff_mem_orbit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Normal.minpoly_eq_iff_mem_orbit [h : Normal F E] {x y : E} : minpoly F x =
 minpoly F y ↔ x in MulAction.orbit Gal(E/F) y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.exists_algHom_of_splits_of_aeval`：exists_algHom_of_spl
its_of_aeval (hy : aeval y (minpoly F x) = 0) : exists φ : E ->ₐ[F] K, φ x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `normal_iff`：normal_iff : Normal F K ↔ forall x : K, IsIntegral F x ∧ Spl
its ((minpoly F x).map (algebraMap F K))
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `AlgHom.normal_bijective`：AlgHom.normal_bijective [h : Normal F E] (ϕ : E
 ->ₐ[F] K) : Function.Bijective ϕ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `minpoly.algEquiv_eq`：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f
 x) = minpoly A x
-/
theorem Normal.minpoly_eq_iff_mem_orbit [h : Normal F E] {x y : E} :
    minpoly F x = minpoly F y ↔ x ∈ MulAction.orbit Gal(E/F) y := by
  refine ⟨fun he ↦ ?_, fun ⟨f, he⟩ ↦ he ▸ minpoly.algEquiv_eq f y⟩
  obtain ⟨φ, hφ⟩ := exists_algHom_of_splits_of_aeval (normal_iff.mp h) (he ▸ minpoly.aeval F x)
  exact ⟨AlgEquiv.ofBijective φ (φ.normal_bijective F E E), hφ⟩

variable (F K₁)
/-
**isSolvable_of_isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSolvable_of_isScalarTower [Normal F K₁] [h1 : Group.IsSolvable (K₁ ≃ₐ[F]
 K₁)] [h2 : Group.IsSolvable (E ≃ₐ[K₁] E)] : Group.IsSolvable Gal(E/F)
参数：K₁ ≃ₐ[F] K₁；E ≃ₐ[K₁] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Group.isSolvable_of_ker_le_range`：isSolvable_of_ker_le_range {G' G'' : T
ype*} [Group G'] [Group G''] (f : G' ->* G) (g : G ->* G'') (hfg : g.ker <= f.ra
nge) [hG' : IsSolvable…
· 使用定理 `AlgEquiv.map_mul'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `AlgEquiv.map_add'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.restrictNormal_commutes`：AlgEquiv.restrictNormal_commutes [Norm
al F E] (x : E) : algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgEquiv.ext_iff`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst 
: CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Alge
bra R …
-/
theorem isSolvable_of_isScalarTower [Normal F K₁] [h1 : Group.IsSolvable (K₁ ≃ₐ[F] K₁)]
    [h2 : Group.IsSolvable (E ≃ₐ[K₁] E)] : Group.IsSolvable Gal(E/F) := by
  let f : (E ≃ₐ[K₁] E) →* Gal(E/F) :=
    { toFun := fun ϕ =>
        AlgEquiv.ofAlgHom (ϕ.toAlgHom.restrictScalars F) (ϕ.symm.toAlgHom.restrictScalars F)
          (AlgHom.ext fun x => ϕ.apply_symm_apply x) (AlgHom.ext fun x => ϕ.symm_apply_apply x)
      map_one' := AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  refine
    Group.isSolvable_of_ker_le_range f (AlgEquiv.restrictNormalHom K₁) fun ϕ hϕ =>
      ⟨{ ϕ with commutes' := fun x => ?_ }, AlgEquiv.ext fun _ => rfl⟩
  exact Eq.trans (ϕ.restrictNormal_commutes K₁ x).symm (congr_arg _ (AlgEquiv.ext_iff.mp hϕ x))

end lift

namespace minpoly

variable {K L : Type _} [Field K] [Field L] [Algebra K L]

open AlgEquiv IntermediateField

/-- If `x : L` is a root of `minpoly K y`, then we can find `(σ : Gal(L/K))` with `σ x = y`.
  That is, `x` and `y` are Galois conjugates. -/
/-
**minpoly.exists_algEquiv_of_root** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：exists_algEquiv_of_root [Normal K L] {x y : L} (hy : IsAlgebraic K y) (h_e
v : (Polynomial.aeval x) (minpoly K y) = 0) : exists σ : Gal(L/K), σ x = y
参数：hy : IsAlgebraic K y；h_ev : (Polynomial.aeval x) (minpoly K y) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `minpoly.eq_of_root`：eq_of_root {x y : L} (hx : IsAlgebraic K x) (h_ev : 
Polynomial.aeval y (minpoly K x) = 0) : minpoly K y = minpoly K x
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.liftNormal_commutes`：AlgEquiv.liftNormal_commutes [Normal F E] 
(x : K₁) : χ.liftNormal E (algebraMap K₁ E x) = algebraMap K₂ E (χ x)
· 使用定理 `minpoly.algEquiv_apply`：algEquiv_apply {x y : L} (hx : IsAlgebraic K x) 
(h_mp : minpoly K x = minpoly K y) : algEquiv hx h_mp (AdjoinSimple.gen K x) = A
djoinSimple.…
· 使用定理 `IntermediateField.AdjoinSimple.algebraMap_gen`：∀ (F : Type u_1) [inst : 
Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (α : E),   (al
gebraMap (↥F⟮α⟯) E) (IntermediateFi…

--- 原说明 ---
If `x : L` is a root of `minpoly K y`, then we can find `(σ : Gal(L/K))` with `σ
 x = y`.
  That is, `x` and `y` are Galois conjugates.
-/
theorem exists_algEquiv_of_root [Normal K L] {x y : L} (hy : IsAlgebraic K y)
    (h_ev : (Polynomial.aeval x) (minpoly K y) = 0) : ∃ σ : Gal(L/K), σ x = y := by
  have hx : IsAlgebraic K x := ⟨minpoly K y, ne_zero hy.isIntegral, h_ev⟩
  set f : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := algEquiv hx (eq_of_root hy h_ev)
  have hxy : (liftNormal f L) ((algebraMap (↥K⟮x⟯) L) (AdjoinSimple.gen K x)) = y := by
    rw [liftNormal_commutes f L, algEquiv_apply, AdjoinSimple.algebraMap_gen K y]
  exact ⟨(liftNormal f L), hxy⟩

/-- If `x : L` is a root of `minpoly K y`, then we can find `(σ : Gal(L/K))` with `σ y = x`.
  That is, `x` and `y` are Galois conjugates. -/
/-
**minpoly.exists_algEquiv_of_root'** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：exists_algEquiv_of_root' [Normal K L] {x y : L} (hy : IsAlgebraic K y) (h_
ev : (Polynomial.aeval x) (minpoly K y) = 0) : exists σ : Gal(L/K), σ y = x
参数：hy : IsAlgebraic K y；h_ev : (Polynomial.aeval x) (minpoly K y) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.exists_algEquiv_of_root`：exists_algEquiv_of_root [Normal K L] {x
 y : L} (hy : IsAlgebraic K y) (h_ev : (Polynomial.aeval x) (minpoly K y) = 0) :
 exists σ : Gal(L/K),…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x

--- 原说明 ---
If `x : L` is a root of `minpoly K y`, then we can find `(σ : Gal(L/K))` with `σ
 y = x`.
  That is, `x` and `y` are Galois conjugates.
-/
theorem exists_algEquiv_of_root' [Normal K L] {x y : L} (hy : IsAlgebraic K y)
    (h_ev : (Polynomial.aeval x) (minpoly K y) = 0) : ∃ σ : Gal(L/K), σ y = x := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_of_root hy h_ev
  use σ.symm
  rw [← hσ, symm_apply_apply]

end minpoly

/--
A quadratic extension is normal.
-/
/-
**Algebra.IsQuadraticExtension.normal** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.IsQuadraticExtension.normal (F K : Type*) [Field F] [Field K] [Alg
ebra F K] [IsQuadraticExtension F K] : Normal F K where splits'
参数：F K : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.instFiniteOfIsQuadraticExtension`：∀ (R : Type u_2) (S : Type u_3
) [inst : CommSemiring R] [inst_1 : StrongRankCondition R] [inst_2 : Semiring S]
   [inst_3 : Algebra R S] [Alg…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `minpoly.natDegree_le`：natDegree_le [Module.Free A B] : (minpoly A x).nat
Degree <= Module.finrank A B
· 使用定理 `Algebra.IsQuadraticExtension.toFree`：∀ {R : Type u_2} {S : Type u_3} {in
st : CommSemiring R} {inst_1 : StrongRankCondition R} {inst_2 : Semiring S}   {i
nst_3 : Algebra R S} [sel…
· 使用定理 `Algebra.IsQuadraticExtension.finrank_eq_two`：∀ (R : Type u_2) (S : Type 
u_3) [inst : CommSemiring R] [inst_1 : StrongRankCondition R] [inst_2 : Semiring
 S]   [inst_3 : Algebra R S] [Alg…
· 使用定理 `Polynomial.Splits.of_natDegree_le_one`：∀ {R : Type u_1} [inst : Division
Semiring R] {f : Polynomial R}, f.natDegree ≤ 1 → f.Splits
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Polynomial.natDegree_map_le`：natDegree_map_le : natDegree (p.map f) <= n
atDegree p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_iff_lt_add_one`：∀ {x y : ℕ}, x ≤ y ↔ x < y + 1
· 使用定理 `Polynomial.Splits.of_natDegree_eq_two`：∀ {R : Type u_1} [inst : Field R]
 {f : Polynomial R} {x : R}, f.natDegree = 2 → Polynomial.eval x f = 0 → f.Split
s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0

--- 原说明 ---
A quadratic extension is normal.
-/
instance Algebra.IsQuadraticExtension.normal (F K : Type*) [Field F] [Field K] [Algebra F K]
    [IsQuadraticExtension F K] :
    Normal F K where
  splits' := by
    intro x
    obtain h | h := le_iff_lt_or_eq.mp (finrank_eq_two F K ▸ minpoly.natDegree_le x)
    · exact Splits.of_natDegree_le_one <| natDegree_map_le.trans (by rwa [Nat.le_iff_lt_add_one])
    · exact Splits.of_natDegree_eq_two ((natDegree_map _).trans h)
        ((eval_map_algebraMap _ _).trans (minpoly.aeval F x))
