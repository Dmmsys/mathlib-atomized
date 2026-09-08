/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.Fuglede
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.ContinuousMap.Ideals
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Gelfand Duality

The `gelfandTransform` is an algebra homomorphism from a topological `𝕜`-algebra `A` to
`C(characterSpace 𝕜 A, 𝕜)`. In the case where `A` is a commutative complex Banach algebra, then
the Gelfand transform is actually spectrum-preserving (`spectrum.gelfandTransform_eq`). Moreover,
when `A` is a commutative C⋆-algebra over `ℂ`, then the Gelfand transform is a surjective isometry,
and even an equivalence between C⋆-algebras.

Consider the contravariant functors between compact Hausdorff spaces and commutative unital
C⋆algebras `F : Cpct → CommCStarAlg := X ↦ C(X, ℂ)` and
`G : CommCStarAlg → Cpct := A → characterSpace ℂ A` whose actions on morphisms are given by
`WeakDual.CharacterSpace.compContinuousMap` and `ContinuousMap.compStarAlgHom'`, respectively.

Then `η₁ : id → F ∘ G := gelfandStarTransform` and
`η₂ : id → G ∘ F := WeakDual.CharacterSpace.homeoEval` are the natural isomorphisms implementing
**Gelfand Duality**, i.e., the (contravariant) equivalence of these categories.

## Main definitions

* `Ideal.toCharacterSpace` : constructs an element of the character space from a maximal ideal in
  a commutative complex Banach algebra
* `WeakDual.CharacterSpace.compContinuousMap`: The functorial map taking `ψ : A →⋆ₐ[𝕜] B` to a
  continuous function `characterSpace 𝕜 B → characterSpace 𝕜 A` given by pre-composition with `ψ`.

## Main statements

* `spectrum.gelfandTransform_eq` : the Gelfand transform is spectrum-preserving when the algebra is
  a commutative complex Banach algebra.
* `gelfandTransform_isometry` : the Gelfand transform is an isometry when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.
* `gelfandTransform_bijective` : the Gelfand transform is bijective when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.
* `gelfandStarTransform_naturality`: The `gelfandStarTransform` is a natural isomorphism
* `WeakDual.CharacterSpace.homeoEval_naturality`: This map implements a natural isomorphism

## TODO

* After defining the category of commutative unital C⋆-algebras, bundle the existing unbundled
  **Gelfand duality** into an actual equivalence (duality) of categories associated to the
  functors `C(·, ℂ)` and `characterSpace ℂ ·` and the natural isomorphisms `gelfandStarTransform`
  and `WeakDual.CharacterSpace.homeoEval`.

## Tags

Gelfand transform, character space, C⋆-algebra
-/

@[expose] public section


open WeakDual

open scoped NNReal

section ComplexBanachAlgebra

open Ideal

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (I : Ideal A)
  [Ideal.IsMaximal I]

/-- Every maximal ideal in a commutative complex Banach algebra gives rise to a character on that
algebra. In particular, the character, which may be identified as an algebra homomorphism due to
`WeakDual.CharacterSpace.equivAlgHom`, is given by the composition of the quotient map and
the Gelfand-Mazur isomorphism `NormedRing.algEquivComplexOfComplete`. -/
/-
**Ideal.toCharacterSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.toCharacterSpace : characterSpace Complex A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Every maximal ideal in a commutative complex Banach algebra gives rise to a char
acter on that
algebra. In particular, the character, which may be identified as an algebra hom
omorphism due to
`WeakDual.CharacterSpace.equivAlgHom`, is given by the composition of the quotie
nt map and
the Gelfand-Mazur isomorphism `NormedRing.algEquivComplexOfComplete`.
-/
noncomputable def Ideal.toCharacterSpace : characterSpace ℂ A :=
  CharacterSpace.equivAlgHom.symm <|
    ((NormedRing.algEquivComplexOfComplete
      (letI := Quotient.field I; isUnit_iff_ne_zero (G₀ := A ⧸ I))).symm : A ⧸ I →ₐ[ℂ] ℂ).comp <|
    Quotient.mkₐ ℂ I
/-
**Ideal.toCharacterSpace_apply_eq_zero_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.toCharacterSpace_apply_eq_zero_of_mem {a : A} (ha : a in I) : I.toCh
aracterSpace a = 0
参数：ha : a in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `spectrum.nonempty`：∀ {A : Type u_2} [inst : NormedRing A] [inst_1 : Norm
edAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A),   (spectrum ℂ a).Nonemp
ty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedRing.algEquivComplexOfComplete_symm_apply`：∀ {A : Type u_2} [inst 
: NormedRing A] [inst_1 : NormedAlgebra ℂ A] [inst_2 : CompleteSpace A]   (hA : 
∀ {a : A}, IsUnit a ↔ a ≠ 0) (a : A),…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Set.Nonempty.some.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s = 
s_1) (h : s.Nonempty), h.some = ⋯.some
· 使用定理 `spectrum.zero_eq`：zero_eq [Nontrivial A] : σ (0 : A) = {0}
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
-/
theorem Ideal.toCharacterSpace_apply_eq_zero_of_mem {a : A} (ha : a ∈ I) :
    I.toCharacterSpace a = 0 := by
  unfold Ideal.toCharacterSpace
  simp only [CharacterSpace.equivAlgHom_symm_coe, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    Quotient.mkₐ_eq_mk, Function.comp_apply, NormedRing.algEquivComplexOfComplete_symm_apply]
  simp_rw [Quotient.eq_zero_iff_mem.mpr ha, spectrum.zero_eq]
  exact Set.eq_of_mem_singleton (Set.singleton_nonempty (0 : ℂ)).some_mem

/-- If `a : A` is not a unit, then some character takes the value zero at `a`. This is equivalent
to `gelfandTransform ℂ A a` takes the value zero at some character. -/
/-
**WeakDual.CharacterSpace.exists_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WeakDual.CharacterSpace.exists_apply_eq_zero {a : A} (ha : ¬IsUnit a) : ex
ists f : characterSpace Complex A, f a = 0
参数：ha : ¬IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.span_singleton_ne_top`：span_singleton_ne_top {α : Type*} [CommSemi
ring α] {x : α} (hx : ¬IsUnit x) : Ideal.span ({x} : Set α) != ⊤
· 使用定理 `Ideal.toCharacterSpace_apply_eq_zero_of_mem`：Ideal.toCharacterSpace_appl
y_eq_zero_of_mem {a : A} (ha : a in I) : I.toCharacterSpace a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
If `a : A` is not a unit, then some character takes the value zero at `a`. This 
is equivalent
to `gelfandTransform ℂ A a` takes the value zero at some character.
-/
theorem WeakDual.CharacterSpace.exists_apply_eq_zero {a : A} (ha : ¬IsUnit a) :
    ∃ f : characterSpace ℂ A, f a = 0 := by
  obtain ⟨M, hM, haM⟩ := (span {a}).exists_le_maximal (span_singleton_ne_top ha)
  exact
    ⟨M.toCharacterSpace,
      M.toCharacterSpace_apply_eq_zero_of_mem
        (haM (mem_span_singleton.mpr ⟨1, (mul_one a).symm⟩))⟩
/-
**WeakDual.CharacterSpace.mem_spectrum_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WeakDual.CharacterSpace.mem_spectrum_iff_exists {a : A} {z : Complex} : z 
in spectrum Complex a ↔ exists f : characterSpace Complex A, f a = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `WeakDual.CharacterSpace.exists_apply_eq_zero`：WeakDual.CharacterSpace.ex
ists_apply_eq_zero {a : A} (ha : ¬IsUnit a) : exists f : characterSpace Complex 
A, f a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `AlgHom.apply_mem_spectrum`：apply_mem_spectrum [Nontrivial R] (φ : F) (a 
: A) : φ a in σ a
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
-/
theorem WeakDual.CharacterSpace.mem_spectrum_iff_exists {a : A} {z : ℂ} :
    z ∈ spectrum ℂ a ↔ ∃ f : characterSpace ℂ A, f a = z := by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨f, hf⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hz
    simp only [map_sub, sub_eq_zero, AlgHomClass.commutes] at hf
    exact ⟨_, hf.symm⟩
  · rintro ⟨f, rfl⟩
    exact AlgHom.apply_mem_spectrum f a

/-- The Gelfand transform is spectrum-preserving. -/
/-
**spectrum.gelfandTransform_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectrum.gelfandTransform_eq (a : A) : spectrum Complex (gelfandTransform 
Complex A a) = spectrum Complex a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.spectrum_eq_range`：spectrum_eq_range [CompleteSpace 𝕜] (f 
: C(X, 𝕜)) : spectrum 𝕜 f = Set.range f
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `WeakDual.CharacterSpace.mem_spectrum_iff_exists`：WeakDual.CharacterSpace
.mem_spectrum_iff_exists {a : A} {z : Complex} : z in spectrum Complex a ↔ exist
s f : characterSpace Complex A, f a =…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The Gelfand transform is spectrum-preserving.
-/
theorem spectrum.gelfandTransform_eq (a : A) :
    spectrum ℂ (gelfandTransform ℂ A a) = spectrum ℂ a := by
  ext z
  rw [ContinuousMap.spectrum_eq_range, WeakDual.CharacterSpace.mem_spectrum_iff_exists]
  exact Iff.rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial A] : Nonempty (characterSpace ℂ A) :=
  ⟨Classical.choose <|
      WeakDual.CharacterSpace.exists_apply_eq_zero <| zero_mem_nonunits.2 zero_ne_one⟩

end ComplexBanachAlgebra

section ComplexCStarAlgebra

section Commutative

variable {A : Type*} [CommCStarAlgebra A]

/-
**gelfandTransform_map_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gelfandTransform_map_star (a : A) : gelfandTransform Complex A (star a) = 
star (gelfandTransform Complex A a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
-/
theorem gelfandTransform_map_star (a : A) :
    gelfandTransform ℂ A (star a) = star (gelfandTransform ℂ A a) :=
  ContinuousMap.ext fun φ => map_star φ a

variable (A)

/-- The Gelfand transform is an isometry when the algebra is a C⋆-algebra over `ℂ`. -/
/-
**gelfandTransform_isometry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gelfandTransform_isometry : Isometry (gelfandTransform Complex A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `WeakDual.CharacterSpace.instCompactSpaceElemCharacterSpaceOfProperSpace`
：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1 : No
rmedRing A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] …
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.gelfandTransform_eq`：spectrum.gelfandTransform_eq (a : A) : spe
ctrum Complex (gelfandTransform Complex A a) = spectrum Complex a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNReal.sqrt_sq`：∀ (x : NNReal), NNReal.sqrt (x ^ 2) = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CStarRing.nnnorm_star_mul_self`：nnnorm_star_mul_self {x : E} : ‖x⋆ * x‖₊
 = ‖x‖₊ * ‖x‖₊
· 使用定理 `ContinuousMap.instCStarRing`：∀ {α : Type u_1} {β : Type u_2} [inst : Top
ologicalSpace α] [inst_1 : CompactSpace α] [inst_2 : NonUnitalNormedRing β]   [i
nst_3 : StarRing …
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `IsSelfAdjoint.spectralRadius_eq_nnnorm`：IsSelfAdjoint.spectralRadius_eq_
nnnorm {a : A} (ha : IsSelfAdjoint a) : spectralRadius Complex a = ‖a‖₊
· 使用定理 `IsSelfAdjoint.star_mul_self`：star_mul_self [Mul R] [StarMul R] (x : R) :
 IsSelfAdjoint (star x * x)
· 使用定理 `gelfandTransform_map_star`：gelfandTransform_map_star (a : A) : gelfandTr
ansform Complex A (star a) = star (gelfandTransform Complex A a)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The Gelfand transform is an isometry when the algebra is a C⋆-algebra over `ℂ`.
-/
theorem gelfandTransform_isometry : Isometry (gelfandTransform ℂ A) := by
  refine AddMonoidHomClass.isometry_of_norm (gelfandTransform ℂ A) fun a => ?_
  /- By `spectrum.gelfandTransform_eq`, the spectra of `star a * a` and its
    `gelfandTransform` coincide. Therefore, so do their spectral radii, and since they are
    self-adjoint, so also do their norms. Applying the C⋆-property of the norm and taking square
    roots shows that the norm is preserved. -/
  have : spectralRadius ℂ (gelfandTransform ℂ A (star a * a)) = spectralRadius ℂ (star a * a) := by
    unfold spectralRadius; rw [spectrum.gelfandTransform_eq]
  rw [map_mul, (IsSelfAdjoint.star_mul_self a).spectralRadius_eq_nnnorm, gelfandTransform_map_star,
    (IsSelfAdjoint.star_mul_self (gelfandTransform ℂ A a)).spectralRadius_eq_nnnorm] at this
  simp only [ENNReal.coe_inj, CStarRing.nnnorm_star_mul_self, ← sq] at this
  simpa only [Function.comp_apply, NNReal.sqrt_sq] using!
    congr_arg (((↑) : ℝ≥0 → ℝ) ∘ ⇑NNReal.sqrt) this

set_option backward.defeqAttrib.useBackward true in
/-- The Gelfand transform is bijective when the algebra is a C⋆-algebra over `ℂ`. -/
/-
**gelfandTransform_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gelfandTransform_bijective : Function.Bijective (gelfandTransform Complex 
A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Isometry.injective`：∀ {α : Type u} {β : Type v} [inst : EMetricSpace α] 
[inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Function.Injective f
· 使用定理 `WeakDual.CharacterSpace.instCompactSpaceElemCharacterSpaceOfProperSpace`
：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1 : No
rmedRing A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] …
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `gelfandTransform_isometry`：gelfandTransform_isometry : Isometry (gelfand
Transform Complex A)
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousMap.instIsTopologicalRingOfLocallyCompactSpace`：∀ {α : Type u_
1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Loc
allyCompactSpace α]   [inst_3 : NonUnitalRing …
· 使用定理 `WeaklyLocallyCompactSpace.locallyCompactSpace`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X], LocallyCompactSpa
ce X
· 使用定理 `instR1SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Spac
e X] (p : X → Prop), R1Space (Subtype p)
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
The Gelfand transform is bijective when the algebra is a C⋆-algebra over `ℂ`.
-/
theorem gelfandTransform_bijective : Function.Bijective (gelfandTransform ℂ A) := by
  refine ⟨(gelfandTransform_isometry A).injective, ?_⟩
  /- The range of `gelfandTransform ℂ A` is actually a `StarSubalgebra`. The key lemma below may be
    hard to spot; it's `map_star` coming from `WeakDual.Complex.instStarHomClass`, which is a
    nontrivial result. -/
  let rng : StarSubalgebra ℂ C(characterSpace ℂ A, ℂ) :=
    { toSubalgebra := (gelfandTransform ℂ A).range
      star_mem' := by
        rintro - ⟨a, rfl⟩
        use star a
        ext1 φ
        dsimp
        simp only [map_star, RCLike.star_def] }
  suffices rng = ⊤ from
    fun x => show x ∈ rng from this.symm ▸ StarSubalgebra.mem_top
  /- Because the `gelfandTransform ℂ A` is an isometry, it has closed range, and so by the
    Stone-Weierstrass theorem, it suffices to show that the image of the Gelfand transform separates
    points in `C(characterSpace ℂ A, ℂ)` and is closed under `star`. -/
  have h : rng.topologicalClosure = rng := le_antisymm
    (StarSubalgebra.topologicalClosure_minimal le_rfl
      (gelfandTransform_isometry A).isClosedEmbedding.isClosed_range)
    (StarSubalgebra.le_topologicalClosure _)
  refine h ▸ ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    _ (fun _ _ => ?_)
  /- Separating points just means that elements of the `characterSpace` which agree at all points
    of `A` are the same functional, which is just extensionality. -/
  contrapose!
  exact fun h => Subtype.ext (ContinuousLinearMap.ext fun a =>
    h (gelfandTransform ℂ A a) ⟨gelfandTransform ℂ A a, ⟨a, rfl⟩, rfl⟩)

/-- The Gelfand transform as a `StarAlgEquiv` between a commutative unital C⋆-algebra over `ℂ`
and the continuous functions on its `characterSpace`. -/
@[simps!]
/-
**gelfandStarTransform** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：gelfandStarTransform : A ≃⋆ₐ[Complex] C(characterSpace Complex A, Complex)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `gelfandTransform_map_star`：gelfandTransform_map_star (a : A) : gelfandTr
ansform Complex A (star a) = star (gelfandTransform Complex A a)
· 使用定理 `gelfandTransform_bijective`：gelfandTransform_bijective : Function.Biject
ive (gelfandTransform Complex A)

--- 原说明 ---
The Gelfand transform as a `StarAlgEquiv` between a commutative unital C⋆-algebr
a over `ℂ`
and the continuous functions on its `characterSpace`.
-/
noncomputable def gelfandStarTransform : A ≃⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) :=
  StarAlgEquiv.ofBijective
    (show A →⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) from
      { gelfandTransform ℂ A with map_star' := fun x => gelfandTransform_map_star x })
    (gelfandTransform_bijective A)

end Commutative

namespace CommCStarAlgebra

variable {A : Type*} [NonUnitalCommCStarAlgebra A] {a b : A}

open scoped CStarAlgebra in
open Unitization in
/-
**CommCStarAlgebra.norm_add_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `CommCStarAlgebra`。
形式化陈述：norm_add_eq_max (h : a * b = 0) : ‖a + b‖ = max ‖a‖ ‖b‖
参数：h : a * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `WeakDual.CharacterSpace.instCompactSpaceElemCharacterSpaceOfProperSpace`
：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1 : No
rmedRing A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] …
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `NonUnitalCStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], CompleteSpace A
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `gelfandTransform_isometry`：gelfandTransform_isometry : Isometry (gelfand
Transform Complex A)
· 使用引理 `Unitization.isometry_inr`：isometry_inr : Isometry ((↑) : A -> Unitizatio
n 𝕜 A)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Isometry.norm_map_of_map_zero`：∀ {E : Type u_2} {F : Type u_3} [inst : S
eminormedAddGroup E] [inst_1 : SeminormedAddGroup F] {f : E → F},   Isometry f →
 f 0 = 0 → ∀ (x : E…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Unitization.inrNonUnitalAlgHom_toFun`：∀ (R : Type u_1) (A : Type u_2) [i
nst : CommSemiring R] [inst_1 : NonUnitalSemiring A] [inst_2 : _root_.Module R A
]   (a : A), (Unitization.…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
（共 55 条，此处仅展示前 30 条）
-/
lemma norm_add_eq_max (h : a * b = 0) : ‖a + b‖ = max ‖a‖ ‖b‖ := by
  let f := gelfandStarTransform A⁺¹ ∘ inrNonUnitalAlgHom ℂ A
  have hf : Isometry f := gelfandTransform_isometry _ |>.comp isometry_inr
  simp_rw [← hf.norm_map_of_map_zero (by simp [f]), show f (a + b) = f a + f b by simp [f]]
  exact ContinuousMap.norm_add_eq_max <| by simpa [f] using congr(f $h)
/-
**CommCStarAlgebra.nnnorm_add_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `CommCStarAlgebra
`。
形式化陈述：nnnorm_add_eq_max (h : a * b = 0) : ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊
参数：h : a * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `CommCStarAlgebra.norm_add_eq_max`：norm_add_eq_max (h : a * b = 0) : ‖a +
 b‖ = max ‖a‖ ‖b‖
-/
lemma nnnorm_add_eq_max (h : a * b = 0) : ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊ :=
  NNReal.eq <| norm_add_eq_max h
/-
**CommCStarAlgebra.norm_sub_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `CommCStarAlgebra`。
形式化陈述：norm_sub_eq_max (h : a * b = 0) : ‖a - b‖ = max ‖a‖ ‖b‖
参数：h : a * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `CommCStarAlgebra.norm_add_eq_max`：norm_add_eq_max (h : a * b = 0) : ‖a +
 b‖ = max ‖a‖ ‖b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
lemma norm_sub_eq_max (h : a * b = 0) : ‖a - b‖ = max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using norm_add_eq_max (a := a) (b := -b) (by simpa)
/-
**CommCStarAlgebra.nnnorm_sub_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `CommCStarAlgebra
`。
形式化陈述：nnnorm_sub_eq_max (h : a * b = 0) : ‖a - b‖₊ = max ‖a‖₊ ‖b‖₊
参数：h : a * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `CommCStarAlgebra.norm_sub_eq_max`：norm_sub_eq_max (h : a * b = 0) : ‖a -
 b‖ = max ‖a‖ ‖b‖
-/
lemma nnnorm_sub_eq_max (h : a * b = 0) : ‖a - b‖₊ = max ‖a‖₊ ‖b‖₊ :=
  NNReal.eq <| norm_sub_eq_max h

open scoped Function in
/-
**CommCStarAlgebra.nnnorm_sum_eq_sup** 是 Mathlib 中的一个引理，位于命名空间 `CommCStarAlgebra
`。
形式化陈述：nnnorm_sum_eq_sup {ι : Type*} {f : ι -> A} (s : Finset ι) (h0 : Pairwise (
(· * · = 0) on f)) : ‖∑ i in s, f i‖₊ = s.sup (‖f ·‖₊)
参数：s : Finset ι；h0 : Pairwise ((· * · = 0) on f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `CommCStarAlgebra.nnnorm_add_eq_max`：nnnorm_add_eq_max (h : a * b = 0) : 
‖a + b‖₊ = max ‖a‖₊ ‖b‖₊
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
-/
lemma nnnorm_sum_eq_sup {ι : Type*} {f : ι → A} (s : Finset ι) (h0 : Pairwise ((· * · = 0) on f)) :
    ‖∑ i ∈ s, f i‖₊ = s.sup (‖f ·‖₊) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i ∈ s, f i = 0 by simp_all [nnnorm_add_eq_max this]
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi ↦ h0 (by grind)

end CommCStarAlgebra

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] {a b : A}

namespace IsStarNormal

open scoped IsMulCommutative in
open NonUnitalStarAlgebra NonUnitalStarSubalgebra in
/-
**IsStarNormal.norm_add_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `IsStarNormal`。
形式化陈述：norm_add_eq_max (ha : IsStarNormal a) (hb : IsStarNormal b) (hcomm : Commu
te a b) (hab : a * b = 0) : ‖a + b‖ = max ‖a‖ ‖b‖
参数：ha : IsStarNormal a；hb : IsStarNormal b；hcomm : Commute a b；hab : a * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `NonUnitalStarSubalgebra.isClosed_topologicalClosure`：isClosed_topologica
lClosure (s : NonUnitalStarSubalgebra R A) : IsClosed (s.topologicalClosure : Se
t A)
· 使用定理 `IsStarNormal.commute_star_left`：∀ {A : Type u_2} [inst : NonUnitalCStarA
lgebra A] {a x : A}, IsStarNormal a → Commute a x → Commute (star a) x
· 使用定理 `IsStarNormal.commute_star_right`：∀ {A : Type u_2} [inst : NonUnitalCStar
Algebra A] {a x : A}, IsStarNormal a → Commute x a → Commute x (star a)
· 使用定理 `NonUnitalStarAlgebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s
 : Set A} (hcomm : forall x in s, forall y in s, x * y = y * x) (hcomm_star : fo
rall a in s, forall b in s, a * st…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `NonUnitalCommRing.mul_comm`：∀ {α : Type u} [self : NonUnitalCommRing α] 
(a b : α), a * b = b * a
· 使用定理 `NonUnitalCStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], CompleteSpace A
· 使用引理 `CommCStarAlgebra.norm_add_eq_max`：norm_add_eq_max (h : a * b = 0) : ‖a +
 b‖ = max ‖a‖ ‖b‖
· 使用定理 `NonUnitalStarSubalgebra.le_topologicalClosure`：le_topologicalClosure (s 
: NonUnitalStarSubalgebra R A) : s <= s.topologicalClosure
· 使用定理 `NonUnitalStarAlgebra.mem_adjoin_of_mem`：mem_adjoin_of_mem {s : Set A} {x
 : A} (hx : x in s) : x in adjoin R s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
（共 31 条，此处仅展示前 30 条）
-/
lemma norm_add_eq_max (ha : IsStarNormal a) (hb : IsStarNormal b)
    (hcomm : Commute a b) (hab : a * b = 0) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  /- Since `a` and `b` are normal, commute, and commute with the `star` of the other,
  the C⋆-subalgebra generated by `a` and `b` is commutative, and the conclusion follows from the
  corresponding result for commutative C⋆-algebras. -/
  -- TODO: once #36418 is merged, it should be possible to remove the `let _`s below entirely.
  let S : NonUnitalStarSubalgebra ℂ A := (adjoin ℂ {a, b}).topologicalClosure
  have hS : IsClosed (S : Set A) := (adjoin ℂ {a, b}).isClosed_topologicalClosure
  have hcomm₁ := ha.commute_star_left hcomm
  have hcomm₂ := hb.commute_star_right hcomm
  have : IsMulCommutative (adjoin ℂ {a, b}) :=
    isMulCommutative_adjoin ℂ (by grind) (by grind [commute_star_comm])
  let _ : NonUnitalCommRing S := (adjoin ℂ {a, b}).nonUnitalCommRingTopologicalClosure mul_comm
  let _ : NonUnitalCommCStarAlgebra S := { }
  refine CommCStarAlgebra.norm_add_eq_max (A := S) (a := ⟨a, ?_⟩) (b := ⟨b, ?_⟩) (by ext; simpa)
  all_goals apply le_topologicalClosure; aesop
/-
**IsStarNormal.nnnorm_add_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `IsStarNormal`。
形式化陈述：nnnorm_add_eq_max (ha : IsStarNormal a) (hb : IsStarNormal b) (hcomm : Com
mute a b) (hab : a * b = 0) : ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊
参数：ha : IsStarNormal a；hb : IsStarNormal b；hcomm : Commute a b；hab : a * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `IsStarNormal.norm_add_eq_max`：norm_add_eq_max (ha : IsStarNormal a) (hb 
: IsStarNormal b) (hcomm : Commute a b) (hab : a * b = 0) : ‖a + b‖ = max ‖a‖ ‖b
‖
-/
lemma nnnorm_add_eq_max (ha : IsStarNormal a) (hb : IsStarNormal b)
    (hcomm : Commute a b) (hab : a * b = 0) :
    ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊ :=
  NNReal.eq <| ha.norm_add_eq_max hb hcomm hab
/-
**IsStarNormal.norm_sub_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `IsStarNormal`。
形式化陈述：norm_sub_eq_max (ha : IsStarNormal a) (hb : IsStarNormal b) (hcomm : Commu
te a b) (hab : a * b = 0) : ‖a - b‖ = max ‖a‖ ‖b‖
参数：ha : IsStarNormal a；hb : IsStarNormal b；hcomm : Commute a b；hab : a * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `IsStarNormal.norm_add_eq_max`：norm_add_eq_max (ha : IsStarNormal a) (hb 
: IsStarNormal b) (hcomm : Commute a b) (hab : a * b = 0) : ‖a + b‖ = max ‖a‖ ‖b
‖
· 使用定理 `IsStarNormal.neg`：∀ {R : Type u_1} [inst : NonUnitalNonAssocRing R] [ins
t_1 : StarAddMonoid R] {x : R} [IsStarNormal x], IsStarNormal (-x)
· 使用定理 `Commute.neg_right`：neg_right : Commute a b -> Commute a (-b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
lemma norm_sub_eq_max (ha : IsStarNormal a) (hb : IsStarNormal b)
    (hcomm : Commute a b) (hab : a * b = 0) :
    ‖a - b‖ = max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using
    ha.norm_add_eq_max hb.neg hcomm.neg_right (by simpa)
/-
**IsStarNormal.nnnorm_sub_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `IsStarNormal`。
形式化陈述：nnnorm_sub_eq_max (ha : IsStarNormal a) (hb : IsStarNormal b) (hcomm : Com
mute a b) (hab : a * b = 0) : ‖a - b‖₊ = max ‖a‖₊ ‖b‖₊
参数：ha : IsStarNormal a；hb : IsStarNormal b；hcomm : Commute a b；hab : a * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `IsStarNormal.norm_sub_eq_max`：norm_sub_eq_max (ha : IsStarNormal a) (hb 
: IsStarNormal b) (hcomm : Commute a b) (hab : a * b = 0) : ‖a - b‖ = max ‖a‖ ‖b
‖
-/
lemma nnnorm_sub_eq_max (ha : IsStarNormal a) (hb : IsStarNormal b)
    (hcomm : Commute a b) (hab : a * b = 0) :
    ‖a - b‖₊ = max ‖a‖₊ ‖b‖₊ :=
  NNReal.eq <| ha.norm_sub_eq_max hb hcomm hab

end IsStarNormal

namespace IsSelfAdjoint

open NonUnitalStarAlgebra in
/-
**IsSelfAdjoint.norm_add_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：norm_add_eq_max (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b
 = 0) : ‖a + b‖ = max ‖a‖ ‖b‖
参数：ha : IsSelfAdjoint a；hb : IsSelfAdjoint b；hab : a * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsStarNormal.norm_add_eq_max`：norm_add_eq_max (ha : IsStarNormal a) (hb 
: IsStarNormal b) (hcomm : Commute a b) (hab : a * b = 0) : ‖a + b‖ = max ‖a‖ ‖b
‖
· 使用定理 `IsSelfAdjoint.isStarNormal`：isStarNormal {R : Type*} [Mul R] [Star R] {x
 : R} (hx : IsSelfAdjoint x) : IsStarNormal x
-/
lemma norm_add_eq_max (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0) :
    ‖a + b‖ = max ‖a‖ ‖b‖ :=
  ha.isStarNormal.norm_add_eq_max hb.isStarNormal (by grind [commute_of_mul_eq_zero]) hab
/-
**IsSelfAdjoint.nnnorm_add_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：nnnorm_add_eq_max (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a *
 b = 0) : ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊
参数：ha : IsSelfAdjoint a；hb : IsSelfAdjoint b；hab : a * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `IsSelfAdjoint.norm_add_eq_max`：norm_add_eq_max (ha : IsSelfAdjoint a) (h
b : IsSelfAdjoint b) (hab : a * b = 0) : ‖a + b‖ = max ‖a‖ ‖b‖
-/
lemma nnnorm_add_eq_max (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0) :
    ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊ :=
  NNReal.eq <| ha.norm_add_eq_max hb hab
/-
**IsSelfAdjoint.norm_sub_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：norm_sub_eq_max (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b
 = 0) : ‖a - b‖ = max ‖a‖ ‖b‖
参数：ha : IsSelfAdjoint a；hb : IsSelfAdjoint b；hab : a * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `IsSelfAdjoint.norm_add_eq_max`：norm_add_eq_max (ha : IsSelfAdjoint a) (h
b : IsSelfAdjoint b) (hab : a * b = 0) : ‖a + b‖ = max ‖a‖ ‖b‖
· 使用定理 `IsSelfAdjoint.neg`：neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-
x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
lemma norm_sub_eq_max (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0) :
    ‖a - b‖ = max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using ha.norm_add_eq_max hb.neg (by simpa)
/-
**IsSelfAdjoint.nnnorm_sub_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：nnnorm_sub_eq_max (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a *
 b = 0) : ‖a - b‖₊ = max ‖a‖₊ ‖b‖₊
参数：ha : IsSelfAdjoint a；hb : IsSelfAdjoint b；hab : a * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `IsSelfAdjoint.norm_sub_eq_max`：norm_sub_eq_max (ha : IsSelfAdjoint a) (h
b : IsSelfAdjoint b) (hab : a * b = 0) : ‖a - b‖ = max ‖a‖ ‖b‖
-/
lemma nnnorm_sub_eq_max (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0) :
    ‖a - b‖₊ = max ‖a‖₊ ‖b‖₊ :=
  NNReal.eq <| ha.norm_sub_eq_max hb hab

open scoped Function in
/-
**IsSelfAdjoint.nnnorm_sum_eq_sup** 是 Mathlib 中的一个引理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：nnnorm_sum_eq_sup {ι : Type*} {f : ι -> A} (s : Finset ι) (h : forall i in
 s, IsSelfAdjoint (f i)) (h0 : Pairwise ((· * · = 0) on f)) : ‖∑ i in s, f i‖₊ =
 s.sup (‖f ·‖₊)
参数：s : Finset ι；h : forall i in s, IsSelfAdjoint (f i)；h0 : Pairwise ((· * · = 0
) on f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `IsSelfAdjoint.nnnorm_add_eq_max`：nnnorm_add_eq_max (ha : IsSelfAdjoint a
) (hb : IsSelfAdjoint b) (hab : a * b = 0) : ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `isSelfAdjoint_sum`：isSelfAdjoint_sum {ι : Type*} [AddCommMonoid R] [Star
AddMonoid R] (s : Finset ι) {x : ι -> R} (h : forall i in s, IsSelfAdjoint (x i)
) : IsS…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
-/
lemma nnnorm_sum_eq_sup {ι : Type*} {f : ι → A} (s : Finset ι)
    (h : ∀ i ∈ s, IsSelfAdjoint (f i)) (h0 : Pairwise ((· * · = 0) on f)) :
    ‖∑ i ∈ s, f i‖₊ = s.sup (‖f ·‖₊) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i ∈ s, f i = 0 by
      simp_all [(h j (by simp)).nnnorm_add_eq_max (by cfc_tac) this]
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi ↦ h0 (by grind)

end IsSelfAdjoint

end NonUnital

end ComplexCStarAlgebra

section Functoriality

namespace WeakDual

namespace CharacterSpace

variable {A B C 𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [StarRing A]
variable [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B] [StarRing B]
variable [NormedRing C] [NormedAlgebra 𝕜 C] [CompleteSpace C] [StarRing C]

/-- The functorial map taking `ψ : A →⋆ₐ[ℂ] B` to a continuous function
`characterSpace ℂ B → characterSpace ℂ A` obtained by pre-composition with `ψ`. -/
@[simps]
/-
**WeakDual.CharacterSpace.compContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual.
CharacterSpace`。
形式化陈述：compContinuousMap (ψ : A ->⋆ₐ[𝕜] B) : C(characterSpace 𝕜 B, characterSpace
 𝕜 A) where toFun φ
参数：ψ : A ->⋆ₐ[𝕜] B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The functorial map taking `ψ : A →⋆ₐ[ℂ] B` to a continuous function
`characterSpace ℂ B → characterSpace ℂ A` obtained by pre-composition with `ψ`.
-/
noncomputable def compContinuousMap (ψ : A →⋆ₐ[𝕜] B) :
    C(characterSpace 𝕜 B, characterSpace 𝕜 A) where
  toFun φ := equivAlgHom.symm ((equivAlgHom φ).comp ψ.toAlgHom)
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_of_continuous_eval fun a => map_continuous <| gelfandTransform 𝕜 B (ψ a)) _

variable (A) in
/-- `WeakDual.CharacterSpace.compContinuousMap` sends the identity to the identity. -/
@[simp]
/-
**WeakDual.CharacterSpace.compContinuousMap_id** 是 Mathlib 中的一个定理，位于命名空间 `WeakDu
al.CharacterSpace`。
形式化陈述：compContinuousMap_id : compContinuousMap (StarAlgHom.id 𝕜 A) = ContinuousM
ap.id (characterSpace 𝕜 A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `WeakDual.CharacterSpace.ext`：ext {φ ψ : characterSpace 𝕜 A} (h : forall 
x, φ x = ψ x) : φ = ψ

--- 原说明 ---
`WeakDual.CharacterSpace.compContinuousMap` sends the identity to the identity.
-/
theorem compContinuousMap_id :
    compContinuousMap (StarAlgHom.id 𝕜 A) = ContinuousMap.id (characterSpace 𝕜 A) :=
  ContinuousMap.ext fun _a => ext fun _x => rfl

/-- `WeakDual.CharacterSpace.compContinuousMap` is functorial. -/
@[simp]
/-
**WeakDual.CharacterSpace.compContinuousMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Weak
Dual.CharacterSpace`。
形式化陈述：compContinuousMap_comp (ψ₂ : B ->⋆ₐ[𝕜] C) (ψ₁ : A ->⋆ₐ[𝕜] B) : compContinu
ousMap (ψ₂.comp ψ₁) = (compContinuousMap ψ₁).comp (compContinuousMap ψ₂)
参数：ψ₂ : B ->⋆ₐ[𝕜] C；ψ₁ : A ->⋆ₐ[𝕜] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `WeakDual.CharacterSpace.ext`：ext {φ ψ : characterSpace 𝕜 A} (h : forall 
x, φ x = ψ x) : φ = ψ

--- 原说明 ---
`WeakDual.CharacterSpace.compContinuousMap` is functorial.
-/
theorem compContinuousMap_comp (ψ₂ : B →⋆ₐ[𝕜] C) (ψ₁ : A →⋆ₐ[𝕜] B) :
    compContinuousMap (ψ₂.comp ψ₁) = (compContinuousMap ψ₁).comp (compContinuousMap ψ₂) :=
  ContinuousMap.ext fun _a => ext fun _x => rfl

end CharacterSpace

end WeakDual

end Functoriality

open CharacterSpace in
/--
Consider the contravariant functors between compact Hausdorff spaces and commutative unital
C⋆algebras `F : Cpct → CommCStarAlg := X ↦ C(X, ℂ)` and
`G : CommCStarAlg → Cpct := A → characterSpace ℂ A` whose actions on morphisms are given by
`WeakDual.CharacterSpace.compContinuousMap` and `ContinuousMap.compStarAlgHom'`, respectively.

Then `η : id → F ∘ G := gelfandStarTransform` is a natural isomorphism implementing (half of)
the duality between these categories. That is, for commutative unital C⋆-algebras `A` and `B` and
`φ : A →⋆ₐ[ℂ] B` the following diagram commutes:

```
A  --- η A ---> C(characterSpace ℂ A, ℂ)

|                     |

φ                  (F ∘ G) φ

|                     |
V                     V

B  --- η B ---> C(characterSpace ℂ B, ℂ)
```
-/
/-
**gelfandStarTransform_naturality** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gelfandStarTransform_naturality {A B : Type*} [CommCStarAlgebra A] [CommCS
tarAlgebra B] (φ : A ->⋆ₐ[Complex] B) : (gelfandStarTransform B : _ ->⋆ₐ[Complex
] _).comp φ = (compContinuousMap φ |>.compStarAlgHom' Complex Complex).comp (gel
fandStarTransform A : _ ->⋆ₐ[Complex] _)
参数：φ : A ->⋆ₐ[Complex] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `instAlgEquivClassOfNonUnitalAlgEquivClass`：∀ (F : Type u_1) (R : Type u_
2) (A : Type u_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]  
 [inst_2 : Algebra R A] [inst_3…
· 使用定理 `StarAlgEquiv.instNonUnitalAlgEquivClass`：∀ {R : Type u_2} {A : Type u_3}
 {B : Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B
]   [inst_4 : SMul R A] [inst…
· 使用定理 `NonUnitalStarRingHomClass.toStarHomClass`：∀ {F : Type u_1} {A : outParam
 (Type u_2)} {B : outParam (Type u_3)} {inst : NonUnitalNonAssocSemiring A}   {i
nst_1 : Star A} {inst_2 : NonU…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `StarRingEquivClass.toRingEquivClass`：∀ {F : Type u_1} {A : outParam (Typ
e u_2)} {B : outParam (Type u_3)} {inst : Add A} {inst_1 : Mul A} {inst_2 : Star
 A}   {inst_3 : Add B} {i…
· 使用定理 `StarAlgEquiv.instStarRingEquivClass`：∀ {R : Type u_2} {A : Type u_3} {B 
: Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B]   
[inst_4 : SMul R A] [inst…
· 使用定理 `StarRingEquivClass.instNonUnitalStarRingHomClass`：∀ {F : Type u_1} {A : 
Type u_2} {B : Type u_3} [inst : NonUnitalNonAssocSemiring A] [inst_1 : Star A] 
  [inst_2 : NonUnitalNonAssocSemiring …

--- 原说明 ---
Consider the contravariant functors between compact Hausdorff spaces and commuta
tive unital
C⋆algebras `F : Cpct → CommCStarAlg := X ↦ C(X, ℂ)` and
`G : CommCStarAlg → Cpct := A → characterSpace ℂ A` whose actions on morphisms a
re given by
`WeakDual.CharacterSpace.compContinuousMap` and `ContinuousMap.compStarAlgHom'`,
 respectively.

Then `η : id → F ∘ G := gelfandStarTransform` is a natural isomorphism implement
ing (half of)
the duality between these categories. That is, for commutative unital C⋆-algebra
s `A` and `B` and
`φ : A →⋆ₐ[ℂ] B` the following diagram commutes:

```
A  --- η A ---> C(characterSpace ℂ A, ℂ)

|                     |

φ                  (F ∘ G) φ

|                     |
V                     V

B  --- η B ---> C(characterSpace ℂ B, ℂ)
```
-/
theorem gelfandStarTransform_naturality {A B : Type*} [CommCStarAlgebra A] [CommCStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) :
    (gelfandStarTransform B : _ →⋆ₐ[ℂ] _).comp φ =
      (compContinuousMap φ |>.compStarAlgHom' ℂ ℂ).comp (gelfandStarTransform A : _ →⋆ₐ[ℂ] _) := by
  rfl

/--
Consider the contravariant functors between compact Hausdorff spaces and commutative unital
C⋆algebras `F : Cpct → CommCStarAlg := X ↦ C(X, ℂ)` and
`G : CommCStarAlg → Cpct := A → characterSpace ℂ A` whose actions on morphisms are given by
`WeakDual.CharacterSpace.compContinuousMap` and `ContinuousMap.compStarAlgHom'`, respectively.

Then `η : id → G ∘ F := WeakDual.CharacterSpace.homeoEval` is a natural isomorphism implementing
(half of) the duality between these categories. That is, for compact Hausdorff spaces `X` and `Y`,
`f : C(X, Y)` the following diagram commutes:

```
X  --- η X ---> characterSpace ℂ C(X, ℂ)

|                     |

f                  (G ∘ F) f

|                     |
V                     V

Y  --- η Y ---> characterSpace ℂ C(Y, ℂ)
```
-/
/-
**WeakDual.CharacterSpace.homeoEval_naturality** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WeakDual.CharacterSpace.homeoEval_naturality {X Y 𝕜 : Type*} [RCLike 𝕜] [T
opologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpa
ce Y] [T2Space Y] (f : C(X, Y)) : (homeoEval Y 𝕜 : C(_, _)).comp f = (f.compStar
AlgHom' 𝕜 𝕜 |> compContinuousMap).comp (homeoEval X 𝕜 : C(_, _))
参数：f : C(X, Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R

--- 原说明 ---
Consider the contravariant functors between compact Hausdorff spaces and commuta
tive unital
C⋆algebras `F : Cpct → CommCStarAlg := X ↦ C(X, ℂ)` and
`G : CommCStarAlg → Cpct := A → characterSpace ℂ A` whose actions on morphisms a
re given by
`WeakDual.CharacterSpace.compContinuousMap` and `ContinuousMap.compStarAlgHom'`,
 respectively.

Then `η : id → G ∘ F := WeakDual.CharacterSpace.homeoEval` is a natural isomorph
ism implementing
(half of) the duality between these categories. That is, for compact Hausdorff s
paces `X` and `Y`,
`f : C(X, Y)` the following diagram commutes:

```
X  --- η X ---> characterSpace ℂ C(X, ℂ)

|                     |

f                  (G ∘ F) f

|                     |
V                     V

Y  --- η Y ---> characterSpace ℂ C(Y, ℂ)
```
-/
lemma WeakDual.CharacterSpace.homeoEval_naturality {X Y 𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (f : C(X, Y)) :
    (homeoEval Y 𝕜 : C(_, _)).comp f =
      (f.compStarAlgHom' 𝕜 𝕜 |> compContinuousMap).comp (homeoEval X 𝕜 : C(_, _)) :=
  rfl
