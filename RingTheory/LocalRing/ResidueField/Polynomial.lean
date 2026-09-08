/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Residue field of primes in polynomial algebras

## Main results
- `Polynomial.residueFieldMapCAlgEquiv`: `κ(I[X]) ≃ₐ[κ(I)] κ(I)(X)`
- `Polynomial.fiberEquivQuotient`: `κ(p) ⊗[R] (R[X] ⧸ I) = κ(p)[X] / I`

-/

@[expose] public section

namespace Polynomial

open scoped nonZeroDivisors TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R) [I.IsPrime] (J : Ideal R[X]) [J.IsPrime] [J.LiesOver I]
  [Algebra (Localization.AtPrime I) (Localization.AtPrime J)]
  [Localization.AtPrime.IsLiesOverAlgebra I J]


set_option backward.isDefEq.respectTransparency.types false in
/-- `κ(I[X]) ≃ₐ[κ(I)] κ(I)(X)`. -/
noncomputable
/-
**Polynomial.residueFieldMapCAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：residueFieldMapCAlgEquiv (hJ : J = I.map C) : J.ResidueField ≃ₐ[I.ResidueF
ield] RatFunc I.ResidueField
参数：hJ : J = I.map C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def residueFieldMapCAlgEquiv (hJ : J = I.map C) :
    J.ResidueField ≃ₐ[I.ResidueField] RatFunc I.ResidueField := by
  letI f : J.ResidueField →+* RatFunc I.ResidueField := by
    refine Ideal.ResidueField.lift _
        ((algebraMap I.ResidueField[X] _).comp (mapRingHom (algebraMap _ _))) ?_ ?_
    · simp [hJ, Ideal.map_le_iff_le_comap, RingHom.comap_ker _ C, mapRingHom_comp_C,
        RingHom.ker_comp_of_injective, C_injective,
        FaithfulSMul.algebraMap_injective I.ResidueField[X] (RatFunc I.ResidueField)]
    · rintro x (hx : x ∉ J)
      suffices ∃ i, x.coeff i ∉ I by simpa [IsUnit.mem_submonoid_iff, Polynomial.ext_iff]
      contrapose! hx
      rwa [hJ, Ideal.mem_map_C_iff]
  haveI hf : f.comp (algebraMap I.ResidueField _) = algebraMap _ _ := by
    ext
    simp [f, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  refine .ofAlgHom ⟨f, fun r ↦ congr($hf r)⟩
      (RatFunc.liftAlgHom (aeval (algebraMap R[X] _ X)) fun x ↦ ?_) ?_ ?_
  · suffices Function.Injective (aeval (R := I.ResidueField) (algebraMap R[X] J.ResidueField X)) by
      simp [← this.eq_iff]
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, hr⟩ := map_surjective _ Ideal.Quotient.mk_surjective
      (IsLocalization.integerNormalization (R ⧸ I)⁰ x)
    obtain ⟨s, hs, hr⟩ : ∃ s ∉ I, r.map (algebraMap _ _) = s • x := by
      obtain ⟨b, hb0, hb⟩ := IsLocalization.integerNormalization_spec (R ⧸ I)⁰ x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨s, by simpa [Ideal.Quotient.eq_zero_iff_mem] using! hb0, ?_⟩
      simpa [← hr, map_map, ← Ideal.Quotient.algebraMap_eq] using! hb
    replace hx : r ∈ J := by
      apply_fun aeval (algebraMap R[X] J.ResidueField X) at hr
      simpa [hx, aeval_map_algebraMap, aeval_algebraMap_apply, Algebra.smul_def] using! hr
    refine ((IsUnit.mk0 (algebraMap R I.ResidueField s) (by simpa)).map C).mul_right_injective ?_
    simp only [← algebraMap_eq, ← Algebra.smul_def]
    rw [algebraMap_smul]
    simp only [← hr]
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using! hJ.le hx
  · apply AlgHom.coe_ringHom_injective
    apply IsFractionRing.injective_comp_algebraMap (A := I.ResidueField[X])
    dsimp [RatFunc.liftAlgHom]
    simp only [AlgHom.comp_toRingHom, AlgHom.coe_ringHom_mk, RingHom.comp_assoc,
      RatFunc.liftRingHom_comp_algebraMap, RingHomCompTriple.comp_eq, f]
    ext <;> simp [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  · apply AlgHom.coe_ringHom_injective
    ext
    · simp [f, RatFunc.liftAlgHom, ← IsScalarTower.algebraMap_apply]; rfl
    · simp [f, RatFunc.liftAlgHom]

@[simp]
/-
**Polynomial.residueFieldMapCAlgEquiv_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `Poly
nomial`。
形式化陈述：residueFieldMapCAlgEquiv_algebraMap (hJ : J = I.map C) (p : R[X]) : residu
eFieldMapCAlgEquiv I J hJ (algebraMap _ _ p) = algebraMap _ _ (p.map (algebraMap
 R I.ResidueField))
参数：hJ : J = I.map C；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂}
 [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3
 : Algebra R …
· 使用定理 `Ideal.ResidueField.lift_algebraMap`：∀ {R : Type u_1} {S : Type u_2} [ins
t : CommRing R] [inst_1 : CommRing S] (I : Ideal R) [inst_2 : I.IsPrime]   (f : 
R →+* S) (hf₁ : I ≤ Ring…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma residueFieldMapCAlgEquiv_algebraMap (hJ : J = I.map C) (p : R[X]) :
    residueFieldMapCAlgEquiv I J hJ (algebraMap _ _ p) =
      algebraMap _ _ (p.map (algebraMap R I.ResidueField)) := by
  simp [residueFieldMapCAlgEquiv]

@[simp]
/-
**Polynomial.residueFieldMapCAlgEquiv_symm_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al`。
形式化陈述：residueFieldMapCAlgEquiv_symm_C (hJ : J = I.map C) (r) : (residueFieldMapC
AlgEquiv I J hJ).symm (.C r) = algebraMap _ _ r
参数：hJ : J = I.map C；r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
-/
lemma residueFieldMapCAlgEquiv_symm_C (hJ : J = I.map C) (r) :
    (residueFieldMapCAlgEquiv I J hJ).symm (.C r) = algebraMap _ _ r :=
  (residueFieldMapCAlgEquiv I J hJ).symm.commutes r

@[simp]
/-
**Polynomial.residueFieldMapCAlgEquiv_symm_X** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al`。
形式化陈述：residueFieldMapCAlgEquiv_symm_X (hJ : J = I.map C) : (residueFieldMapCAlgE
quiv I J hJ).symm .X = algebraMap R[X] _ .X
参数：hJ : J = I.map C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用引理 `Polynomial.residueFieldMapCAlgEquiv_algebraMap`：residueFieldMapCAlgEquiv
_algebraMap (hJ : J = I.map C) (p : R[X]) : residueFieldMapCAlgEquiv I J hJ (alg
ebraMap _ _ p) = algebraMap _ _ (p.m…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma residueFieldMapCAlgEquiv_symm_X (hJ : J = I.map C) :
    (residueFieldMapCAlgEquiv I J hJ).symm .X = algebraMap R[X] _ .X :=
  (residueFieldMapCAlgEquiv I J hJ).injective (by simp)

set_option backward.isDefEq.respectTransparency.types false in
/-- `κ(p) ⊗[R] (R[X] ⧸ I) = κ(p)[X] / I` -/
noncomputable
/-
**Polynomial.fiberEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：fiberEquivQuotient (f : R[X] ->ₐ[R] S) (hf : Function.Surjective f) (p : I
deal R) [p.IsPrime] : p.Fiber S ≃ₐ[p.ResidueField] p.ResidueField[X] ⧸ ((RingHom
.ker (f : R[X] ->+* S)).map (mapRingHom (algebraMap R p.ResidueField)))
参数：f : R[X] ->ₐ[R] S；hf : Function.Surjective f；p : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fiberEquivQuotient (f : R[X] →ₐ[R] S) (hf : Function.Surjective f) (p : Ideal R) [p.IsPrime] :
    p.Fiber S ≃ₐ[p.ResidueField] p.ResidueField[X] ⧸
      ((RingHom.ker (f : R[X] →+* S)).map (mapRingHom (algebraMap R p.ResidueField))) := by
  refine .ofAlgHom (Algebra.TensorProduct.lift (Algebra.ofId _ _) (AlgHom.liftOfSurjective _ hf
    ((Ideal.Quotient.mkₐ _ _).comp (mapAlgHom (Algebra.ofId _ _))) ?_) fun _ _ ↦ .all _ _)
    (Ideal.Quotient.liftₐ _ (aeval (1 ⊗ₜ f .X)) ?_) ?_ ?_
  · simp [AlgHom.comp_toRingHom, ← RingHom.comap_ker, ← Ideal.map_le_iff_le_comap]
  · change Ideal.map _ _ ≤ RingHom.ker (aeval _).toRingHom
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
    have : ((aeval (1 ⊗ₜ[R] f X : p.Fiber S)).restrictScalars R).comp
        (mapAlgHom (Algebra.ofId R p.ResidueField)) =
        Algebra.TensorProduct.includeRight.comp f := by ext; simp
    exact .trans_eq (by intro; aesop) congr(RingHom.ker $this).symm
  · apply Ideal.Quotient.algHom_ext
    ext
    simp
  · ext x
    obtain ⟨x, rfl⟩ := hf x
    simpa using aeval_algHom_apply
      ((Algebra.TensorProduct.includeRight : S →ₐ[_] p.Fiber S).comp f) X x

set_option backward.isDefEq.respectTransparency.types false in
/-
**Polynomial.fiberEquivQuotient_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：fiberEquivQuotient_tmul (f : R[X] ->ₐ[R] S) (hf : Function.Surjective f) (
p : Ideal R) [p.IsPrime] (a b) : fiberEquivQuotient f hf p (a otimesₜ f b) = Ide
al.Quotient.mk _ (C a * b.map (algebraMap _ _))
参数：f : R[X] ->ₐ[R] S；hf : Function.Surjective f；p : Ideal R；a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂}
 [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3
 : Algebra R …
· 使用定理 `AlgHom.liftOfSurjective_apply`：∀ {R : Type u_5} {A : Type u_6} {B : Type
 u_7} {C : Type u_8} [inst : CommRing R] [inst_1 : CommRing A]   [inst_2 : CommR
ing B] [inst_3 : Co…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fiberEquivQuotient_tmul
    (f : R[X] →ₐ[R] S) (hf : Function.Surjective f) (p : Ideal R) [p.IsPrime] (a b) :
    fiberEquivQuotient f hf p (a ⊗ₜ f b) = Ideal.Quotient.mk _ (C a * b.map (algebraMap _ _)) := by
  simp [fiberEquivQuotient, ← Ideal.Quotient.mk_algebraMap]

/-- Given a prime `P` of `R` and an ideal `I` of `R[X]`, the image of `I` in `κ(P)[X]`
is generated by some `p ∈ I` (basically because `κ(P)[X]` is a PID). -/
/-
**Polynomial._root_.Ideal.exists_mem_span_singleton_map_residueField_eq** 是 Math
lib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a prime `P` of `R` and an ideal `I` of `R[X]`, the image of `I` in `κ(P)[X
]`
is generated by some `p ∈ I` (basically because `κ(P)[X]` is a PID).
-/
theorem _root_.Ideal.exists_mem_span_singleton_map_residueField_eq
    (P : Ideal R) [P.IsPrime] (I : Ideal R[X]) :
    ∃ p ∈ I, Ideal.span {p.map (algebraMap R P.ResidueField)} =
      I.map (mapRingHom (algebraMap R P.ResidueField)) := by
  obtain ⟨p, hp : _ = Ideal.span _⟩ := (inferInstance :
    (I.map (mapRingHom (algebraMap R P.ResidueField))).IsPrincipal)
  let := (mapRingHom (algebraMap (R ⧸ P) P.ResidueField)).toAlgebra
  have := Polynomial.isLocalization (R ⧸ P)⁰ P.ResidueField
  have : p ∈ (I.map (mapRingHom (algebraMap R (R ⧸ P)))).map (algebraMap _ _) := by
    rw [Ideal.map_map, RingHom.algebraMap_toAlgebra, mapRingHom_comp,
      ← IsScalarTower.algebraMap_eq, hp]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨⟨⟨r, hr⟩, s⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff ((R ⧸ P)⁰.map C) _).mp this
  obtain ⟨r, hr', rfl⟩ := (Ideal.mem_map_iff_of_surjective _
    (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)).mp hr
  simp only [algebraMap_def, coe_mapRingHom,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at e
  refine ⟨r, hr', le_antisymm ?_ ?_⟩
  · simpa [-le_of_subsingleton, Ideal.span_le] using! Ideal.mem_map_of_mem _ hr'
  · simp only [hp, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    rw [(IsLocalization.map_units P.ResidueField[X] s).unit.eq_mul_inv_iff_mul_eq.mpr e]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Polynomial

