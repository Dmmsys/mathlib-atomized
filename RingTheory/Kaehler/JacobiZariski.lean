/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.RingTheory.Flat.Basic

/-!

# The Jacobi-Zariski exact sequence

Given algebras $R \to S \to T$, the Jacobi-Zariski exact sequence is a long exact sequence
relating the first homology of the naive cotangent complexes and the Kähler differentials of
the respective algebras. It takes the form:
$$
H_1(L_{T/R}) \to H_1(L_{T/S}) \to T \otimes_S \Omega_{S/R} \to \Omega_{T/R} \to \Omega_{T/S} \to 0
$$
The maps in the sequence are
- `Algebra.H1Cotangent.map`
- `Algebra.H1Cotangent.δ`
- `KaehlerDifferential.mapBaseChange`
- `KaehlerDifferential.map`

The exactness lemmas are
- `Algebra.H1Cotangent.exact_map_δ`
- `Algebra.H1Cotangent.exact_δ_mapBaseChange`
- `KaehlerDifferential.exact_mapBaseChange_map`
- `KaehlerDifferential.map_surjective`

When $T$ is flat over $S$, the left bottom part of the snake lemma diagram used in
the construction of the connecting homomorphism `Algebra.Generators.H1Cotangent.δ`
naturally extends via a base change map. The exactness lemma is
`Algebra.Generators.H1Cotangent.exact_liftBaseChange_map_of_flat`. Globally, this extends
the Jacobi-Zariski exact sequence to the left via a natural base change map, taking the form
$$
T \otimes_S H_1(L_{S/R}) \to H_1(L_{T/R}) \to H_1(L_{T/S})
$$
The exactness lemma is `Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat`.

# TODO

The flatness assumption in `Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat`
is stronger than the `Tor`-vanishing conditions required in the full statement of
[Stacks Project, 00S2], this should be refactored and generalized once more API
for `Tor` modules is available.

-/

@[expose] public section

open KaehlerDifferential Module MvPolynomial TensorProduct

namespace Algebra

-- `Generators.{w, u₁, u₂}` depends on three universe variables and
-- to improve performance of universe unification, it should hold that
-- `w > u₁` and `w > u₂` in the lexicographic order. For more details
-- see https://github.com/leanprover-community/mathlib4/issues/26018
-- TODO: this remains an unsolved problem, ideally the lexicographic
-- order does not affect performance
universe w₁ w₂ w₃ w₄ w₅ u₁ u₂ u₃

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] [Algebra R S]
variable {T : Type u₃} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {ι : Type w₁} {ι' : Type w₃} {σ : Type w₂} {σ' : Type w₄} {τ : Type w₅}
variable (Q : Generators S T ι) (P : Generators R S σ)
variable (Q' : Generators S T ι') (P' : Generators R S σ') (W : Generators R T τ)

attribute [local instance] SMulCommClass.of_commMonoid

namespace Generators

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.Cotangent.surjective_map_ofComp** 是 Mathlib 中的一个定理，位于命名空间 `
Algebra.Generators.Cotangent`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] {T : Type u₃}   [inst_3 : CommRing T] [inst_4 : Algebra R T
] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T] {ι : Type w₁}   {σ : Typ
e w₂} (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ),   Function.
Surjective ⇑(Algebra.Extension.Cotangent.map (Q.ofComp P).toExtensionHom)
参数：Q : Algebra.Generators S T ι；P : Algebra.Generators R S σ；Algebra.Extension.C
otangent.map (Q.ofComp P).toExtensionHom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `Algebra.Generators.toAlgHom_ofComp_surjective`：toAlgHom_ofComp_surjectiv
e (Q : Generators S T ι') (P : Generators R S ι) : Function.Surjective (Q.ofComp
 P).toAlgHom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.Generators.map_ofComp_ker`：map_ofComp_ker (Q : Generators S T ι'
) (P : Generators R S ι) : Ideal.map (Q.ofComp P).toAlgHom (Q.comp P).ker = Q.ke
r
· 使用定理 `Algebra.Extension.Cotangent.map_mk`：∀ {R : Type u} {S : Type v} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension 
R S}   {R' : Type u_1} {…
-/
lemma Cotangent.surjective_map_ofComp :
    Function.Surjective (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) := by
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  have : x ∈ Q.ker := hx
  rw [← map_ofComp_ker Q P, Ideal.mem_map_iff_of_surjective
    _ (toAlgHom_ofComp_surjective Q P)] at this
  obtain ⟨x, hx', rfl⟩ := this
  exact ⟨.mk ⟨x, hx'⟩, Extension.Cotangent.map_mk _ _⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open Extension.Cotangent in
/--
Given representations `0 → I → R[X] → S → 0` and `0 → K → S[Y] → T → 0`,
we may consider the induced representation `0 → J → R[X, Y] → T → 0`, and the sequence
`T ⊗[S] (I/I²) → J/J² → K/K²` is exact.
-/
/-
**Algebra.Generators.Cotangent.exact** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Generato
rs.Cotangent`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] {T : Type u₃}   [inst_3 : CommRing T] [inst_4 : Algebra R T
] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T] {ι : Type w₁}   {σ : Typ
e w₂} (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ),   Function.
Exact ⇑(LinearMap.liftBaseChange T (Algebra.Extension.Cotangent.map (Q.toComp P)
.toExtensionHom))     ⇑(Algebra.Extension.Cotangent.map (Q.ofComp P).toExtension
Hom)
参数：Q : Algebra.Generators S T ι；P : Algebra.Generators R S σ；LinearMap.liftBaseC
hange T (Algebra.Extension.Cotangent.map (Q.toComp P).toExtensionHom)；Algebra.Ex
tension.Cotangent.map (Q.ofComp P).toExtensionHom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.exact_of_comp_of_mem_range`：exact_of_comp_of_mem_range (h1 : g
 ∘ₗ f = 0) (h2 : forall x, g x = 0 -> x in range f) : Exact f g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.liftBaseChange_comp`：liftBaseChange_comp {P} [AddCommMonoid P]
 [Module A P] [Module R P] [IsScalarTower R A P] (l : M ->ₗ[R] N) (l' : N ->ₗ[A]
 P) : l' ∘ₗ l.liftB…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.Extension.Cotangent.map_comp`：∀ {R : Type u} {S : Type v} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensio
n R S}   {R' : Type u_1} {…
· 使用定理 `EmbeddingLike.map_eq_zero_iff`：∀ {F : Type u_1} {M : Type u_4} {N : Type
 u_5} [inst : Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [EmbeddingLik
e F M N] [ZeroHomCl…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.Extension.Cotangent.ext`：∀ {R : Type u} {S : Type v} [inst : Com
mRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S
}   {x y : P.Cotangen…
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_1`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `Algebra.Generators.instIsScalarTowerRing`：∀ {R : Type u} {S : Type v} {ι
 : Type w} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P
 : Algebra.Generators R S ι) {…
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.Generators.Hom.toAlgHom_X`：∀ {R : Type u} {S : Type v} {ι : Type
 w} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Alge
bra.Generators R S ι} {…
· 使用引理 `Algebra.Generators.algebraMap_apply`：algebraMap_apply (x) : algebraMap P
.Ring S x = aeval (R
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
Given representations `0 → I → R[X] → S → 0` and `0 → K → S[Y] → T → 0`,
we may consider the induced representation `0 → J → R[X, Y] → T → 0`, and the se
quence
`T ⊗[S] (I/I²) → J/J² → K/K²` is exact.
-/
lemma Cotangent.exact :
    Function.Exact
      ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T)
      (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · rw [LinearMap.liftBaseChange_comp, ← Extension.Cotangent.map_comp,
      EmbeddingLike.map_eq_zero_iff]
    ext x
    obtain ⟨⟨x, hx⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
    simp only [map_mk, val_mk, LinearMap.zero_apply, val_zero]
    convert! Q.ker.toCotangent.map_zero
    trans ((IsScalarTower.toAlgHom R _ _).comp (IsScalarTower.toAlgHom R P.Ring S)) x
    · congr
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      change (Q.ofComp P).toAlgHom ((Q.toComp P).toAlgHom (X i)) = _
      simp
    · simp [aeval_val_eq_zero hx]
  · intro x hx
    obtain ⟨⟨x : (Q.comp P).Ring, hx'⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
    replace hx : (Q.ofComp P).toAlgHom x ∈ Q.ker ^ 2 := by
      simpa only [map_mk, val_mk, val_zero, Ideal.toCotangent_eq_zero] using! congr(($hx).val)
    rw [pow_two, ← map_ofComp_ker (P := P), ← Ideal.map_mul, Ideal.mem_map_iff_of_surjective
      _ (toAlgHom_ofComp_surjective Q P)] at hx
    obtain ⟨y, hy, e⟩ := hx
    rw [eq_comm, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ← map_toComp_ker] at e
    rw [LinearMap.range_liftBaseChange]
    let z : (Q.comp P).ker := ⟨x - y, Ideal.sub_mem _ hx' (Ideal.mul_le_right hy)⟩
    have hz : z.1 ∈ P.ker.map (Q.toComp P).toAlgHom.toRingHom := e
    have : Extension.Cotangent.mk (P := (Q.comp P).toExtension) ⟨x, hx'⟩ =
      Extension.Cotangent.mk z := by
      ext; simpa only [val_mk, Ideal.toCotangent_eq, sub_sub_cancel, pow_two, z]
    rw [this, ← Submodule.restrictScalars_mem (Q.comp P).Ring, ← Submodule.mem_comap,
      ← Submodule.span_singleton_le_iff_mem, ← Submodule.map_le_map_iff_of_injective
      (f := Submodule.subtype _) Subtype.val_injective, Submodule.map_subtype_span_singleton,
      Submodule.span_singleton_le_iff_mem]
    refine (show Ideal.map (Q.toComp P).toAlgHom.toRingHom P.ker ≤ _ from ?_) hz
    rw [Ideal.map_le_iff_le_comap]
    rintro w hw
    simp only [AlgHom.toRingHom_eq_coe, Ideal.mem_comap, RingHom.coe_coe,
      Submodule.mem_map, Submodule.mem_comap, Submodule.restrictScalars_mem, Submodule.coe_subtype,
      Subtype.exists, exists_and_right, exists_eq_right,
      toExtension_Ring]
    refine ⟨?_, Submodule.subset_span ⟨Extension.Cotangent.mk ⟨w, hw⟩, ?_⟩⟩
    · simp only [ker_eq_ker_aeval_val, RingHom.mem_ker, Hom.algebraMap_toAlgHom]
      rw [aeval_val_eq_zero hw, map_zero]
    · rw [map_mk]
      rfl

/-- Given `R[X] → S` and `S[Y] → T`, the cotangent space of `R[X][Y] → T` is isomorphic
to the direct product of the cotangent space of `S[Y] → T` and `R[X] → S` (base changed to `T`). -/
noncomputable
/-
**Algebra.Generators.CotangentSpace.compEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
.Generators.CotangentSpace`。
形式化陈述：{R : Type u₁} →   {S : Type u₂} →     [inst : CommRing R] →       [inst_1 
: CommRing S] →         [inst_2 : Algebra R S] →           {T : Type u₃} →      
       [inst_3 : CommRing T] →               [inst_4 : Algebra R T] →           
      [inst_5 : Algebra S T] →                   [inst_6 : IsScalarTower R S T] 
→                     {ι : Type w₁} →                       {σ : Type w₂} →     
                    (Q : Algebra.Generators S T ι) →                           (
P : Algebra.Generators R S σ) →                             (Q.comp P).toExtensi
on.CotangentSpace ≃ₗ[T]                               Q.toExtension.CotangentSpa
ce × TensorProduct S T P.toExtension.CotangentSpace
参数：Q : Algebra.Generators S T ι；P : Algebra.Generators R S σ；Q.comp P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def CotangentSpace.compEquiv :
    (Q.comp P).toExtension.CotangentSpace ≃ₗ[T]
      Q.toExtension.CotangentSpace × (T ⊗[S] P.toExtension.CotangentSpace) :=
  (Q.comp P).cotangentSpaceBasis.repr.trans
    (Q.cotangentSpaceBasis.prod (P.cotangentSpaceBasis.baseChange T)).repr.symm
/-
**Algebra.Generators.CotangentSpace.compEquiv_symm_inr** 是 Mathlib 中的一个定理，位于命名空间
 `Algebra.Generators.CotangentSpace`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] {T : Type u₃}   [inst_3 : CommRing T] [inst_4 : Algebra R T
] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T] {ι : Type w₁}   {σ : Typ
e w₂} (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ),   ↑(Algebra
.Generators.CotangentSpace.compEquiv Q P).symm ∘ₗ       LinearMap.inr T Q.toExte
nsion.CotangentSpace (TensorProduct S T P.toExtension.CotangentSpace) =     Line
arMap.liftBaseChange T (Algebra.Extension.CotangentSpace.map (Q.toComp P).toExte
nsionHom)
参数：Q : Algebra.Generators S T ι；P : Algebra.Generators R S σ；Algebra.Generators.
CotangentSpace.compEquiv Q P；TensorProduct S T P.toExtension.CotangentSpace；Alge
bra.Extension.CotangentSpace.map (Q.toComp P).toExtensionHom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Module.Basis.baseChange_apply`：baseChange_apply (b : Basis ι R M) (i) : 
b.baseChange S i = 1 otimesₜ b i
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Module.Basis.repr_linearCombination`：repr_linearCombination (v) : b.repr
 (Finsupp.linearCombination _ b v) = v
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `Algebra.Generators.repr_CotangentSpaceMap`：repr_CotangentSpaceMap (f : H
om P P') (i j) : P'.cotangentSpaceBasis.repr (CotangentSpace.map f.toExtensionHo
m (P.cotangentSpaceBasis i)) j …
· 使用定理 `Algebra.Generators.toComp_val`：∀ {R : Type u} {S : Type v} {ι : Type w} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {ι' : Type u_
3} {T : Type u_7} […
· 使用定理 `MvPolynomial.pderiv_X`：pderiv_X [DecidableEq σ] (i j : σ) : pderiv i (X 
j : MvPolynomial σ R) = Pi.single (M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
（共 41 条，此处仅展示前 30 条）
-/
lemma CotangentSpace.compEquiv_symm_inr :
    (compEquiv Q P).symm.toLinearMap ∘ₗ
      LinearMap.inr T Q.toExtension.CotangentSpace (T ⊗[S] P.toExtension.CotangentSpace) =
        (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T := by
  classical
  apply (P.cotangentSpaceBasis.baseChange T).ext
  intro i
  apply (Q.comp P).cotangentSpaceBasis.repr.injective
  ext j
  simp only [compEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    Basis.baseChange_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inr,
    Function.comp_apply, LinearEquiv.trans_apply, Basis.repr_symm_apply, pderiv_X, toComp_val,
    Basis.repr_linearCombination, LinearMap.liftBaseChange_tmul, one_smul, repr_CotangentSpaceMap]
  obtain (j | j) := j <;>
    simp only [Basis.prod_repr_inr, Basis.baseChange_repr_tmul,
      Basis.repr_self, Basis.prod_repr_inl, map_zero, Finsupp.coe_zero,
      Pi.zero_apply, ne_eq, not_false_eq_true, Pi.single_eq_of_ne, Pi.single_apply,
      Finsupp.single_apply, ite_smul, one_smul, zero_smul, Sum.inr.injEq,
      MonoidWithZeroHom.map_ite_one_zero, reduceCtorEq]
/-
**Algebra.Generators.CotangentSpace.compEquiv_symm_zero** 是 Mathlib 中的一个定理，位于命名空
间 `Algebra.Generators.CotangentSpace`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] {T : Type u₃}   [inst_3 : CommRing T] [inst_4 : Algebra R T
] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T] {ι : Type w₁}   {σ : Typ
e w₂} (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ)   (x : Tenso
rProduct S T P.toExtension.CotangentSpace),   (Algebra.Generators.CotangentSpace
.compEquiv Q P).symm (0, x) =     (LinearMap.liftBaseChange T (Algebra.Extension
.CotangentSpace.map (Q.toComp P).toExtensionHom)) x
参数：Q : Algebra.Generators S T ι；P : Algebra.Generators R S σ；x : TensorProduct S
 T P.toExtension.CotangentSpace；Algebra.Generators.CotangentSpace.compEquiv Q P；
0, x；LinearMap.liftBaseChange T (Algebra.Extension.CotangentSpace.map (Q.toComp 
P).toExtensionHom)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Generators.CotangentSpace.compEquiv_symm_inr`：∀ {R : Type u₁} {S
 : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {T 
: Type u₃}   [inst_3 : CommRing T] [inst_4…
-/
lemma CotangentSpace.compEquiv_symm_zero (x) :
    (compEquiv Q P).symm (0, x) =
        (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T x :=
  DFunLike.congr_fun (compEquiv_symm_inr Q P) x
/-
**Algebra.Generators.CotangentSpace.fst_compEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra.Generators.CotangentSpace`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] {T : Type u₃}   [inst_3 : CommRing T] [inst_4 : Algebra R T
] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T] {ι : Type w₁}   {σ : Typ
e w₂} (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ),   LinearMap
.fst T Q.toExtension.CotangentSpace (TensorProduct S T P.toExtension.CotangentSp
ace) ∘ₗ       ↑(Algebra.Generators.CotangentSpace.compEquiv Q P) =     Algebra.E
xtension.CotangentSpace.map (Q.ofComp P).toExtensionHom
参数：Q : Algebra.Generators S T ι；P : Algebra.Generators R S σ；TensorProduct S T P
.toExtension.CotangentSpace；Algebra.Generators.CotangentSpace.compEquiv Q P；Q.of
Comp P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用引理 `Algebra.Generators.repr_CotangentSpaceMap`：repr_CotangentSpaceMap (f : H
om P P') (i j) : P'.cotangentSpaceBasis.repr (CotangentSpace.map f.toExtensionHo
m (P.cotangentSpaceBasis i)) j …
· 使用定理 `Algebra.Generators.ofComp_val`：∀ {R : Type u} {S : Type v} {ι : Type w} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {ι' : Type u_
3} {T : Type u_7} […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `Module.Basis.prod_apply`：prod_apply (i) : b.prod b' i = Sum.elim (Linear
Map.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `MvPolynomial.pderiv_X`：pderiv_X [DecidableEq σ] (i j : σ) : pderiv i (X 
j : MvPolynomial σ R) = Pi.single (M
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `MonoidWithZeroHom.map_ite_one_zero`：map_ite_one_zero {F : Type*} [FunLik
e F α β] [MonoidWithZeroHomClass F α β] (f : F) (p : Prop) [Decidable p] : f (it
e p 1 0) = ite p 1 0
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Module.Basis.baseChange_apply`：baseChange_apply (b : Basis ι R M) (i) : 
b.baseChange S i = 1 otimesₜ b i
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
（共 34 条，此处仅展示前 30 条）
-/
lemma CotangentSpace.fst_compEquiv :
    LinearMap.fst T Q.toExtension.CotangentSpace (T ⊗[S] P.toExtension.CotangentSpace) ∘ₗ
      (compEquiv Q P).toLinearMap = Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom := by
  classical
  apply (Q.comp P).cotangentSpaceBasis.ext
  intro i
  apply Q.cotangentSpaceBasis.repr.injective
  ext j
  simp only [compEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ofComp_val,
    LinearEquiv.trans_apply, Basis.repr_self, LinearMap.fst_apply, repr_CotangentSpaceMap]
  obtain (i | i) := i <;>
    simp only [Basis.repr_symm_apply, Finsupp.linearCombination_single, Basis.prod_apply,
      LinearMap.coe_inl, LinearMap.coe_inr, Sum.elim_inl, Function.comp_apply, one_smul,
      Basis.repr_self, Finsupp.single_apply, pderiv_X, Pi.single_apply,
      Sum.elim_inr, Function.comp_apply, Basis.baseChange_apply, one_smul,
      MonoidWithZeroHom.map_ite_one_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply, derivation_C]
/-
**Algebra.Generators.CotangentSpace.fst_compEquiv_apply** 是 Mathlib 中的一个定理，位于命名空
间 `Algebra.Generators.CotangentSpace`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] {T : Type u₃}   [inst_3 : CommRing T] [inst_4 : Algebra R T
] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T] {ι : Type w₁}   {σ : Typ
e w₂} (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ)   (x : (Q.co
mp P).toExtension.CotangentSpace),   ((Algebra.Generators.CotangentSpace.compEqu
iv Q P) x).1 =     (Algebra.Extension.CotangentSpace.map (Q.ofComp P).toExtensio
nHom) x
参数：Q : Algebra.Generators S T ι；P : Algebra.Generators R S σ；x : (Q.comp P).toEx
tension.CotangentSpace；(Algebra.Generators.CotangentSpace.compEquiv Q P) x；Algeb
ra.Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Generators.CotangentSpace.fst_compEquiv`：∀ {R : Type u₁} {S : Ty
pe u₂} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {T : Typ
e u₃}   [inst_3 : CommRing T] [inst_4…
-/
lemma CotangentSpace.fst_compEquiv_apply (x) :
    (compEquiv Q P x).1 = Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom x :=
  DFunLike.congr_fun (fst_compEquiv Q P) x
/-
**Algebra.Generators.CotangentSpace.map_toComp_injective** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra.Generators.CotangentSpace`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] {T : Type u₃}   [inst_3 : CommRing T] [inst_4 : Algebra R T
] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T] {ι : Type w₁}   {σ : Typ
e w₂} (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ),   Function.
Injective ⇑(LinearMap.liftBaseChange T (Algebra.Extension.CotangentSpace.map (Q.
toComp P).toExtensionHom))
参数：Q : Algebra.Generators S T ι；P : Algebra.Generators R S σ；LinearMap.liftBaseC
hange T (Algebra.Extension.CotangentSpace.map (Q.toComp P).toExtensionHom)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.Generators.CotangentSpace.compEquiv_symm_inr`：∀ {R : Type u₁} {S
 : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {T 
: Type u₃}   [inst_3 : CommRing T] [inst_4…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
-/
lemma CotangentSpace.map_toComp_injective :
    Function.Injective
      ((Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T) := by
  rw [← compEquiv_symm_inr]
  apply (compEquiv Q P).symm.injective.comp
  exact Prod.mk_right_injective _
/-
**Algebra.Generators.CotangentSpace.map_ofComp_surjective** 是 Mathlib 中的一个定理，位于命
名空间 `Algebra.Generators.CotangentSpace`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] {T : Type u₃}   [inst_3 : CommRing T] [inst_4 : Algebra R T
] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T] {ι : Type w₁}   {σ : Typ
e w₂} (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ),   Function.
Surjective ⇑(Algebra.Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom)
参数：Q : Algebra.Generators S T ι；P : Algebra.Generators R S σ；Algebra.Extension.C
otangentSpace.map (Q.ofComp P).toExtensionHom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.Generators.CotangentSpace.fst_compEquiv`：∀ {R : Type u₁} {S : Ty
pe u₂} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {T : Typ
e u₃}   [inst_3 : CommRing T] [inst_4…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
-/
lemma CotangentSpace.map_ofComp_surjective :
    Function.Surjective (Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom) := by
  rw [← fst_compEquiv]
  exact (Prod.fst_surjective).comp (compEquiv Q P).surjective

/-!
Given representations `R[X] → S` and `S[Y] → T`, the sequence
`T ⊗[S] (⨁ₓ S dx) → (⨁ₓ T dx) ⊕ (⨁ᵧ T dy) → ⨁ᵧ T dy`
is exact.
-/
/-
**Algebra.Generators.CotangentSpace.exact** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Gen
erators.CotangentSpace`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] {T : Type u₃}   [inst_3 : CommRing T] [inst_4 : Algebra R T
] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T] {ι : Type w₁}   {σ : Typ
e w₂} (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ),   Function.
Exact ⇑(LinearMap.liftBaseChange T (Algebra.Extension.CotangentSpace.map (Q.toCo
mp P).toExtensionHom))     ⇑(Algebra.Extension.CotangentSpace.map (Q.ofComp P).t
oExtensionHom)
参数：Q : Algebra.Generators S T ι；P : Algebra.Generators R S σ；LinearMap.liftBaseC
hange T (Algebra.Extension.CotangentSpace.map (Q.toComp P).toExtensionHom)；Algeb
ra.Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.Generators.CotangentSpace.fst_compEquiv`：∀ {R : Type u₁} {S : Ty
pe u₂} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {T : Typ
e u₃}   [inst_3 : CommRing T] [inst_4…
· 使用定理 `Algebra.Generators.CotangentSpace.compEquiv_symm_inr`：∀ {R : Type u₁} {S
 : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {T 
: Type u₃}   [inst_3 : CommRing T] [inst_4…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.symm_symm`：symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e
· 使用引理 `LinearEquiv.conj_exact_iff_exact`：LinearEquiv.conj_exact_iff_exact (e : 
N ≃ₗ[R] N') : Function.Exact (e ∘ₗ f) (g ∘ₗ (e.symm : N' ->ₗ[R] N)) ↔ Exact f g
· 使用定理 `Function.Exact.inr_fst`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_4} [
inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [inst
_3 : _root_.…

--- 原说明 ---
Given representations `R[X] → S` and `S[Y] → T`, the sequence
`T ⊗[S] (⨁ₓ S dx) → (⨁ₓ T dx) ⊕ (⨁ᵧ T dy) → ⨁ᵧ T dy`
is exact.
-/
lemma CotangentSpace.exact :
    Function.Exact ((Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T)
      (Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom) := by
  rw [← fst_compEquiv, ← compEquiv_symm_inr]
  conv_rhs => rw [← LinearEquiv.symm_symm (compEquiv Q P)]
  rw [LinearEquiv.conj_exact_iff_exact]
  exact Function.Exact.inr_fst

namespace H1Cotangent

variable (R) in
/--
Given `0 → I → S[Y] → T → 0`, this is an auxiliary map from `S[Y]` to `T ⊗[S] Ω[S⁄R]` whose
restriction to `ker(I/I² → ⊕ S dyᵢ)` is the connecting homomorphism in the Jacobi-Zariski sequence.
-/
noncomputable
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def δAux :
    Q.Ring →ₗ[R] T ⊗[S] Ω[S⁄R] :=
  Finsupp.lsum R (R := R) (fun f ↦
    (TensorProduct.mk S T _ (f.prod (Q.val · ^ ·))).restrictScalars R ∘ₗ (D R S).toLinearMap)
    ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv _).toLinearMap
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δAux_monomial (n r) :
    δAux R Q (monomial n r) = (n.prod (Q.val · ^ ·)) ⊗ₜ D R S r := by simp [δAux]

@[simp]
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δAux_X (i) :
    δAux R Q (X i) = 0 := by
  rw [X, δAux_monomial]
  simp only [Derivation.map_one_eq_zero, tmul_zero]
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δAux_mul (x y) :
    δAux R Q (x * y) = x • (δAux R Q y) + y • (δAux R Q x) := by
  induction x using MvPolynomial.induction_on' with
  | monomial n r =>
    induction y using MvPolynomial.induction_on' with
    | monomial m s =>
      simp only [monomial_mul, δAux_monomial, Derivation.leibniz, tmul_add, tmul_smul,
        smul_tmul', Algebra.smul_def, algebraMap_apply, aeval_monomial, mul_assoc]
      rw [mul_comm (m.prod _) (n.prod _)]
      simp only [pow_zero, implies_true, pow_add, Finsupp.prod_add_index']
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, smul_add, hy₁, hy₂, mul_add, add_smul]; abel
  | add x₁ x₂ hx₁ hx₂ => simp only [add_mul, map_add, hx₁, hx₂, add_smul, smul_add]; abel
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δAux_C (r) :
    δAux R Q (C r) = 1 ⊗ₜ D R S r := by
  rw [← monomial_zero', δAux_monomial, Finsupp.prod_zero_index]

set_option backward.isDefEq.respectTransparency false in
variable {Q} {Q'} in
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δAux_toAlgHom (f : Hom Q Q') (x) :
    δAux R Q' (f.toAlgHom x) = δAux R Q x + Finsupp.linearCombination _ (δAux R Q' ∘ f.val)
      (Q.cotangentSpaceBasis.repr ((1 : T) ⊗ₜ[Q.Ring] D S Q.Ring x :)) := by
  let : AddCommGroup (T ⊗[S] Ω[S⁄R]) := inferInstance
  have : IsScalarTower Q.Ring Q.Ring T := IsScalarTower.left _
  induction x using MvPolynomial.induction_on with
  | C s => simp [MvPolynomial.algebraMap_eq, δAux_C]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, hx₁, hx₂, tmul_add]
    rw [add_add_add_comm]
  | mul_X p n IH =>
    simp only [map_mul, Hom.toAlgHom_X, δAux_mul, algebraMap_apply, Hom.algebraMap_toAlgHom,
      ← @IsScalarTower.algebraMap_smul Q'.Ring T, algebraMap_self, δAux_X,
      RingHom.id_apply, coe_eval₂Hom, IH, Hom.aeval_val, smul_add, map_aeval, tmul_add, tmul_smul,
      ← @IsScalarTower.algebraMap_smul Q.Ring T, smul_zero, aeval_X, zero_add, Derivation.leibniz,
      Basis.repr_self, map_add, one_smul, map_smul, Finsupp.linearCombination_single,
      RingHomCompTriple.comp_eq, Function.comp_apply, ← cotangentSpaceBasis_apply]
    rw [add_left_comm]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δAux_ofComp (x : (Q.comp P).Ring) :
    δAux R Q ((Q.ofComp P).toAlgHom x) =
      P.toExtension.toKaehler.baseChange T (CotangentSpace.compEquiv Q P
        (1 ⊗ₜ[(Q.comp P).Ring] (D R (Q.comp P).Ring) x : _)).2 := by
  let : AddCommGroup (T ⊗[S] Ω[S⁄R]) := inferInstance
  have : IsScalarTower (Q.comp P).Ring (Q.comp P).Ring T := IsScalarTower.left _
  induction x using MvPolynomial.induction_on with
  | C s =>
    simp only [algHom_C, δAux_C, derivation_C, Derivation.map_algebraMap,
      tmul_zero, map_zero, MvPolynomial.algebraMap_apply, Prod.snd_zero]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, hx₁, hx₂, tmul_add, Prod.snd_add]
  | mul_X p n IH =>
    simp only [map_mul, Hom.toAlgHom_X, ofComp_val, δAux_mul,
      ← @IsScalarTower.algebraMap_smul Q.Ring T, algebraMap_apply, Hom.algebraMap_toAlgHom,
      algebraMap_self, map_aeval, RingHomCompTriple.comp_eq, comp_val, RingHom.id_apply,
      IH, Derivation.leibniz, tmul_add, tmul_smul, ← cotangentSpaceBasis_apply, coe_eval₂Hom,
      ← @IsScalarTower.algebraMap_smul (Q.comp P).Ring T, aeval_X, map_smul, Prod.snd_add,
      Prod.smul_snd, map_add]
    obtain (n | n) := n
    · simp only [Sum.elim_inl, δAux_X, smul_zero, aeval_X,
        CotangentSpace.compEquiv, LinearEquiv.trans_apply, Basis.repr_symm_apply, zero_add,
        Basis.repr_self, Finsupp.linearCombination_single, Basis.prod_apply, LinearMap.coe_inl,
        LinearMap.coe_inr, Function.comp_apply, one_smul, map_zero]
    · simp only [Sum.elim_inr, Function.comp_apply, algHom_C, δAux_C,
        CotangentSpace.compEquiv, LinearEquiv.trans_apply, Basis.repr_symm_apply,
        algebraMap_smul, Basis.repr_self, Finsupp.linearCombination_single, Basis.prod_apply,
        LinearMap.coe_inr, Basis.baseChange_apply, one_smul, LinearMap.baseChange_tmul,
        toKaehler_cotangentSpaceBasis, add_left_inj, LinearMap.coe_inl]
      rfl
/-
**Algebra.Generators.H1Cotangent.map_comp_cotangentComplex_baseChange** 是 Mathli
b 中的一个引理，位于命名空间 `Algebra.Generators.H1Cotangent`。
形式化陈述：map_comp_cotangentComplex_baseChange : (Extension.CotangentSpace.map (Q.to
Comp P).toExtensionHom).liftBaseChange T ∘ₗ P.toExtension.cotangentComplex.baseC
hange T = (Q.comp P).toExtension.cotangentComplex ∘ₗ (Extension.Cotangent.map (Q
.toComp P).toExtensionHom).liftBaseChange T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `Algebra.Extension.CotangentSpace.map_cotangentComplex`：map_cotangentComp
lex (f : Hom P P') (x) : CotangentSpace.map f (P.cotangentComplex x) = P'.cotang
entComplex (.map f x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_cotangentComplex_baseChange :
    (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T ∘ₗ
      P.toExtension.cotangentComplex.baseChange T =
    (Q.comp P).toExtension.cotangentComplex ∘ₗ
      (Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T := by
  ext x; simp [Extension.CotangentSpace.map_cotangentComplex]

open Generators in
/--
The connecting homomorphism in the Jacobi-Zariski sequence for given presentations.
Given representations `0 → I → R[X] → S → 0` and `0 → K → S[Y] → T → 0`,
we may consider the induced representation `0 → J → R[X, Y] → T → 0`,
and this map is obtained by applying snake lemma to the following diagram
```
    T ⊗[S] Ω[S/R]    →          Ω[T/R]        →   Ω[T/S]  → 0
        ↑                         ↑                 ↑
0 → T ⊗[S] (⨁ₓ S dx) → (⨁ₓ T dx) ⊕ (⨁ᵧ T dy) →  ⨁ᵧ T dy → 0
        ↑                         ↑                 ↑
    T ⊗[S] (I/I²)    →           J/J²         →    K/K²   → 0
                                  ↑                 ↑
                             H¹(L_{T/R})      → H¹(L_{T/S})

```
This is independent from the presentations chosen. See `H1Cotangent.δ_comp_equiv`.
-/
noncomputable
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def δ :
    Q.toExtension.H1Cotangent →ₗ[T] T ⊗[S] Ω[S⁄R] :=
  SnakeLemma.δ'
    (P.toExtension.cotangentComplex.baseChange T)
    (Q.comp P).toExtension.cotangentComplex
    Q.toExtension.cotangentComplex
    ((Extension.Cotangent.map (toComp Q P).toExtensionHom).liftBaseChange T)
    (Extension.Cotangent.map (ofComp Q P).toExtensionHom)
    (Cotangent.exact Q P)
    ((Extension.CotangentSpace.map (toComp Q P).toExtensionHom).liftBaseChange T)
    (Extension.CotangentSpace.map (ofComp Q P).toExtensionHom)
    (CotangentSpace.exact Q P)
    (map_comp_cotangentComplex_baseChange Q P)
    (by ext; exact Extension.CotangentSpace.map_cotangentComplex (ofComp Q P).toExtensionHom _)
    Q.toExtension.h1Cotangentι
    (LinearMap.exact_subtype_ker_map _)
    (N₁ := T ⊗[S] P.toExtension.CotangentSpace)
    (P.toExtension.toKaehler.baseChange T)
    (lTensor_exact T P.toExtension.exact_cotangentComplex_toKaehler
      P.toExtension.toKaehler_surjective)
    (Cotangent.surjective_map_ofComp Q P)
    (CotangentSpace.map_toComp_injective Q P)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.H1Cotangent.exact_** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Gener
ators.H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact_δ_map :
    Function.Exact (δ Q P) (mapBaseChange R S T) := by
  simp only [δ]
  apply SnakeLemma.exact_δ_left (π₂ := (Q.comp P).toExtension.toKaehler)
    (hπ₂ := (Q.comp P).toExtension.exact_cotangentComplex_toKaehler)
  · apply (P.cotangentSpaceBasis.baseChange T).ext
    intro i
    simp only [Basis.baseChange_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.baseChange_tmul, toKaehler_cotangentSpaceBasis, mapBaseChange_tmul, map_D,
      one_smul, LinearMap.liftBaseChange_tmul]
    rw [cotangentSpaceBasis_apply]
    conv_rhs => enter [2]; tactic => exact Extension.CotangentSpace.map_tmul ..
    simp only [map_one, mapBaseChange_tmul, map_D, one_smul]
    simp [Extension.Hom.toAlgHom]
  · exact LinearMap.lTensor_surjective T P.toExtension.toKaehler_surjective
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_eq (x : Q.toExtension.H1Cotangent) (y)
    (hy : Extension.Cotangent.map (ofComp Q P).toExtensionHom y = x.1) (z)
    (hz : (Extension.CotangentSpace.map (toComp Q P).toExtensionHom).liftBaseChange T z =
      (Q.comp P).toExtension.cotangentComplex y) :
    δ Q P x = P.toExtension.toKaehler.baseChange T z := by
  simp only [δ]
  apply SnakeLemma.δ_eq
  exacts [hy, hz]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_eq_δAux (x : Q.ker) (hx) :
    δ Q P ⟨.mk x, hx⟩ = δAux R Q x.1 := by
  let y := Extension.Cotangent.mk (P := (Q.comp P).toExtension) (Q.kerCompPreimage P x)
  have hy : (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) y = Extension.Cotangent.mk x := by
    simp only [y, Extension.Cotangent.map_mk]
    congr
    exact ofComp_kerCompPreimage Q P x
  let z := (CotangentSpace.compEquiv Q P ((Q.comp P).toExtension.cotangentComplex y)).2
  rw [H1Cotangent.δ_eq (y := y) (z := z)]
  · rw [← ofComp_kerCompPreimage Q P x, δAux_ofComp]
    rfl
  · exact hy
  · rw [← CotangentSpace.compEquiv_symm_inr]
    apply (CotangentSpace.compEquiv Q P).injective
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inr, Function.comp_apply,
      LinearEquiv.apply_symm_apply, z]
    ext
    swap; · rfl
    change 0 = (LinearMap.fst T Q.toExtension.CotangentSpace
        (T ⊗[S] P.toExtension.CotangentSpace) ∘ₗ (CotangentSpace.compEquiv Q P).toLinearMap)
      ((Q.comp P).toExtension.cotangentComplex y)
    rw [CotangentSpace.fst_compEquiv, Extension.CotangentSpace.map_cotangentComplex, hy, hx]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_C {r : S} (hr : C r ∈ Q.ker) :
    δ Q P ⟨Extension.Cotangent.mk ⟨C r, hr⟩, Extension.Cotangent.mk_C_mem_ker_cotangentComplex ..⟩
      = 1 ⊗ₜ[S] D R S r := by
  rw [δ_eq_δAux, δAux_C]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_eq_δ : δ Q P = δ Q P' := by
  ext ⟨x, hx⟩
  obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective x
  rw [δ_eq_δAux, δ_eq_δAux]
/-
**Algebra.Generators.H1Cotangent.exact_map_** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.G
enerators.H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact_map_δ :
    Function.Exact (Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom) (δ Q P) := by
  simp only [δ]
  apply SnakeLemma.exact_δ_right
    (ι₂ := (Q.comp P).toExtension.h1Cotangentι)
    (hι₂ := LinearMap.exact_subtype_ker_map _)
  · ext x; rfl
  · exact Subtype.val_injective

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_map (f : Hom Q' Q) (x) :
    δ Q P (Extension.H1Cotangent.map f.toExtensionHom x) = δ Q' P' x := by
  let : AddCommGroup (T ⊗[S] Ω[S⁄R]) := inferInstance
  obtain ⟨x, hx⟩ := x
  obtain ⟨⟨y, hy⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  change δ _ _ ⟨_, _⟩ = δ _ _ _
  replace hx : (1 : T) ⊗ₜ[Q'.Ring] (D S Q'.Ring) y = 0 := by
    simpa only [LinearMap.mem_ker, Extension.cotangentComplex_mk, ker, RingHom.mem_ker] using! hx
  simp only [LinearMap.domRestrict_apply, Extension.Cotangent.map_mk, δ_eq_δAux]
  refine (δAux_toAlgHom f _).trans ?_
  rw [hx, map_zero, map_zero, add_zero]
/-
**Algebra.Generators.H1Cotangent.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.
H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_equiv :
    δ Q P ∘ₗ (H1Cotangent.equiv _ _).toLinearMap = δ Q' P' := by
  ext x
  exact δ_map Q P Q' P' _ _

/-- A variant of `exact_map_δ` that takes in an arbitrary map between generators. -/
/-
**Algebra.Generators.H1Cotangent.exact_map_** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.G
enerators.H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `exact_map_δ` that takes in an arbitrary map between generators.
-/
lemma exact_map_δ' (f : Hom W Q) :
    Function.Exact (Extension.H1Cotangent.map f.toExtensionHom) (δ Q P) := by
  refine (H1Cotangent.equiv (Q.comp P) W).surjective.comp_exact_iff_exact.mp ?_
  change Function.Exact ((Extension.H1Cotangent.map f.toExtensionHom).restrictScalars T ∘ₗ
    (Extension.H1Cotangent.map _)) (δ Q P)
  rw [← Extension.H1Cotangent.map_comp, Extension.H1Cotangent.map_eq _ (Q.ofComp P).toExtensionHom]
  exact exact_map_δ Q P

set_option backward.isDefEq.respectTransparency.types false in
open LinearMap in
/-
**Algebra.Generators.H1Cotangent.liftBaseChange_range_le** 是 Mathlib 中的一个引理，位于命名
空间 `Algebra.Generators.H1Cotangent`。
形式化陈述：liftBaseChange_range_le : (liftBaseChange T (Extension.H1Cotangent.map (Q.
toComp P).toExtensionHom)).range <= (Extension.H1Cotangent.map (Q.ofComp P).toEx
tensionHom).ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerH1CotangentOfCotangent`：∀ {R : Type u
} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] 
{P : Algebra.Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.range_liftBaseChange`：range_liftBaseChange (l : M ->ₗ[R] N) : 
LinearMap.range (l.liftBaseChange A) = Submodule.span A (LinearMap.range l)
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `Algebra.Extension.h1Cotangentι_ext`：∀ {R : Type u} {S : Type v} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension 
R S}   (x y : P.H1Cotang…
· 使用定理 `Algebra.Extension.Cotangent.ext`：∀ {R : Type u} {S : Type v} [inst : Com
mRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S
}   {x y : P.Cotangen…
· 使用引理 `Algebra.Generators.toComp_toAlgHom`：toComp_toAlgHom (Q : Generators S T 
ι') (P : Generators R S ι) : (Q.toComp P).toAlgHom = rename Sum.inr
· 使用引理 `Algebra.Generators.toAlgHom_ofComp_rename`：toAlgHom_ofComp_rename (Q : G
enerators S T ι') (P : Generators R S ι) (p : P.Ring) : (Q.ofComp P).toAlgHom ((
rename Sum.inr) p) = C (algebra…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.Generators.algebraMap_eq`：∀ {R : Type u} {S : Type v} {ι : Type 
w} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : Al
gebra.Generators R S ι…
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用引理 `Algebra.Generators.ker_eq_ker_aeval_val`：ker_eq_ker_aeval_val : P.ker = 
RingHom.ker (aeval P.val)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.Generators.ker.eq_1`：∀ {R : Type u} {S : Type v} {ι : Type w} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P : Algebra.Ge
nerators R S ι), …
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.Generators.Hom.toExtensionHom_toRingHom`：∀ {R : Type u} {S : Typ
e v} {ι : Type w} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R 
S]   {P : Algebra.Generators R S ι} {…
· 使用定理 `Algebra.Extension.H1Cotangent.map_apply_coe`：∀ {R : Type u} {S : Type v}
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.E
xtension R S}   {R' : Type u'} {S…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
-/
lemma liftBaseChange_range_le :
    (liftBaseChange T (Extension.H1Cotangent.map (Q.toComp P).toExtensionHom)).range ≤
      (Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom).ker := by
  rw [range_liftBaseChange, coe_range, Submodule.span_le, Set.range_subset_iff]
  rintro ⟨x, _⟩
  obtain ⟨⟨(x : P.Ring), x_in⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  ext; suffices (Q.ofComp P).toAlgHom ((Q.toComp P).toAlgHom x) ∈ Q.toExtension.ker ^ 2 by
    simpa [Ideal.toCotangent_eq_zero]
  rw [← Generators.ker, Generators.ker_eq_ker_aeval_val] at x_in
  rw [toComp_toAlgHom, toAlgHom_ofComp_rename, Generators.algebraMap_eq, RingHom.coe_coe,
    x_in, RingHom.map_zero]
  exact Ideal.zero_mem _

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.Generators.H1Cotangent.auxMemKer** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Ge
nerators.H1Cotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma auxMemKer (z : T ⊗[S] P.toExtension.H1Cotangent) :
    LinearMap.liftBaseChange T (Extension.Cotangent.map (Q.toComp P).toExtensionHom)
      ((LinearMap.lTensor T Extension.h1Cotangentι) z) ∈
        (Q.comp P).toExtension.cotangentComplex.ker := by
  induction z with
  | zero => simp
  | tmul x y => simp [← Extension.CotangentSpace.map_cotangentComplex]
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy

set_option backward.isDefEq.respectTransparency.types false in
open LinearMap in
/-- When $T$ is flat over $S$, the left bottom part of the snake lemma diagram used in
the construction of the connecting homomorphism `Algebra.Generators.H1Cotangent.δ`
naturally extends via a base change map. -/
/-
**Algebra.Generators.H1Cotangent.exact_liftBaseChange_map_of_flat** 是 Mathlib 中的
一个定理，位于命名空间 `Algebra.Generators.H1Cotangent`。
形式化陈述：exact_liftBaseChange_map_of_flat [Module.Flat S T] : Function.Exact ((Exte
nsion.H1Cotangent.map (toComp Q P).toExtensionHom).liftBaseChange T) (Extension.
H1Cotangent.map (ofComp Q P).toExtensionHom)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerH1CotangentOfCotangent`：∀ {R : Type u
} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] 
{P : Algebra.Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Algebra.Extension.h1Cotangentι_injective`：h1Cotangentι_injective : Funct
ion.Injective P.h1Cotangentι
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.Extension.h1Cotangentι_apply`：∀ {R : Type u} {S : Type v} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensio
n R S}   (self : ↥P.cotang…
· 使用定理 `Algebra.Extension.H1Cotangent.map_apply_coe`：∀ {R : Type u} {S : Type v}
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.E
xtension R S}   {R' : Type u'} {S…
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `Algebra.Generators.Cotangent.exact`：∀ {R : Type u₁} {S : Type u₂} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {T : Type u₃}   [inst
_3 : CommRing T] [inst_4…
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用引理 `Module.Flat.lTensor_exact`：lTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄ [
AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] 
[Module R N''] …
· 使用引理 `Algebra.Extension.exact_hCotangentι_cotangentComplex`：exact_hCotangentι_
cotangentComplex : Function.Exact h1Cotangentι P.cotangentComplex
· 使用定理 `LinearMap.baseChange_eq_ltensor`：baseChange_eq_ltensor : (f.baseChange A
 : A otimes M -> A otimes N) = f.lTensor A
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Algebra.Generators.CotangentSpace.map_toComp_injective`：∀ {R : Type u₁} 
{S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {
T : Type u₃}   [inst_3 : CommRing T] [inst_4…
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用引理 `Algebra.Generators.H1Cotangent.map_comp_cotangentComplex_baseChange`：map
_comp_cotangentComplex_baseChange : (Extension.CotangentSpace.map (Q.toComp P).t
oExtensionHom).liftBaseChange T ∘ₗ P.toExtension.cotangen…
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `Algebra.Extension.h1Cotangentι_ext`：∀ {R : Type u} {S : Type v} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension 
R S}   (x y : P.H1Cotang…
· 使用定理 `Algebra.Extension.Cotangent.ext`：∀ {R : Type u} {S : Type v} [inst : Com
mRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S
}   {x y : P.Cotangen…
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
When $T$ is flat over $S$, the left bottom part of the snake lemma diagram used 
in
the construction of the connecting homomorphism `Algebra.Generators.H1Cotangent.
δ`
naturally extends via a base change map.
-/
theorem exact_liftBaseChange_map_of_flat [Module.Flat S T] :
    Function.Exact ((Extension.H1Cotangent.map (toComp Q P).toExtensionHom).liftBaseChange T)
      (Extension.H1Cotangent.map (ofComp Q P).toExtensionHom) := by
  rw [exact_iff]
  refine le_antisymm ?_ (liftBaseChange_range_le Q P)
  rintro ⟨x, x_in⟩ hx
  replace hx : Extension.Cotangent.map (Q.ofComp P).toExtensionHom x = 0 := by
    simpa [← Extension.h1Cotangentι_injective.eq_iff] using hx
  rw [← mem_ker, (Cotangent.exact Q P).linearMap_ker_eq] at hx
  rcases hx with ⟨x, rfl⟩
  rw [mem_ker, ← comp_apply, ← map_comp_cotangentComplex_baseChange, comp_apply,
    ← mem_ker, ker_eq_bot.mpr (CotangentSpace.map_toComp_injective Q P), Submodule.mem_bot,
    baseChange_eq_ltensor, ← mem_ker, (Module.Flat.lTensor_exact T
      P.toExtension.exact_hCotangentι_cotangentComplex).linearMap_ker_eq] at x_in
  rcases x_in with ⟨x, rfl⟩
  use x; induction x with
  | zero => ext; simp
  | tmul x y => ext; simp
  | add x y hx hy => ext; simp [hx (auxMemKer Q P x), hy (auxMemKer Q P y)]

/-- A variant of `exact_liftBaseChange_map_of_flat` that takes in
arbitrary maps between generators. -/
/-
**Algebra.Generators.H1Cotangent.exact_liftBaseChange_map_of_flat'** 是 Mathlib 中
的一个定理，位于命名空间 `Algebra.Generators.H1Cotangent`。
形式化陈述：exact_liftBaseChange_map_of_flat' [Module.Flat S T] (f : Hom W Q) (g : Hom
 P W) : Function.Exact ((Extension.H1Cotangent.map g.toExtensionHom).liftBaseCha
nge T) (Extension.H1Cotangent.map f.toExtensionHom)
参数：f : Hom W Q；g : Hom P W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerH1CotangentOfCotangent`：∀ {R : Type u
} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] 
{P : Algebra.Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearEquiv.conj_exact_iff_exact`：LinearEquiv.conj_exact_iff_exact (e : 
N ≃ₗ[R] N') : Function.Exact (e ∘ₗ f) (g ∘ₗ (e.symm : N' ->ₗ[R] N)) ↔ Exact f g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用引理 `LinearMap.liftBaseChange_comp`：liftBaseChange_comp {P} [AddCommMonoid P]
 [Module A P] [Module R P] [IsScalarTower R A P] (l : M ->ₗ[R] N) (l' : N ->ₗ[A]
 P) : l' ∘ₗ l.liftB…
· 使用定理 `Algebra.Extension.H1Cotangent.map_comp`：∀ {R : Type u} {S : Type v} [ins
t : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extens
ion R S}   {R' : Type u'} {S…
· 使用定理 `Algebra.Extension.H1Cotangent.map_eq`：∀ {R : Type u} {S : Type v} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensio
n R S}   {R' : Type u'} {S…
· 使用定理 `Algebra.Generators.H1Cotangent.exact_liftBaseChange_map_of_flat`：exact_l
iftBaseChange_map_of_flat [Module.Flat S T] : Function.Exact ((Extension.H1Cotan
gent.map (toComp Q P).toExtensionHom).liftBaseChange …

--- 原说明 ---
A variant of `exact_liftBaseChange_map_of_flat` that takes in
arbitrary maps between generators.
-/
theorem exact_liftBaseChange_map_of_flat' [Module.Flat S T] (f : Hom W Q) (g : Hom P W) :
    Function.Exact ((Extension.H1Cotangent.map g.toExtensionHom).liftBaseChange T)
      (Extension.H1Cotangent.map f.toExtensionHom) := by
  rw [← LinearEquiv.conj_exact_iff_exact _ _ (H1Cotangent.equiv W (Q.comp P))]
  convert! exact_liftBaseChange_map_of_flat Q P
  · change Extension.H1Cotangent.map (W.defaultHom (Q.comp P)).toExtensionHom ∘ₗ _ = _
    rw [LinearMap.liftBaseChange_comp, ← Extension.H1Cotangent.map_comp,
      Extension.H1Cotangent.map_eq]
  · change (Extension.H1Cotangent.map f.toExtensionHom).restrictScalars T ∘ₗ
      (Extension.H1Cotangent.map _) = _
    rw [← Extension.H1Cotangent.map_comp, Extension.H1Cotangent.map_eq]

end H1Cotangent

end Generators

variable {T : Type u₃} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

variable (R S T)

/-- The connecting homomorphism in the Jacobi-Zariski sequence. -/
noncomputable
/-
**Algebra.H1Cotangent.** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def H1Cotangent.δ : H1Cotangent S T →ₗ[T] T ⊗[S] Ω[S⁄R] :=
  Generators.H1Cotangent.δ (Generators.self S T) (Generators.self R S)

/-- Given algebras $R \to S \to T$, the sequence
$H_1(L_{T/R}) \to H_1(L_{T/S}) \to T \otimes_S \Omega_{S/R}$
is exact. -/
@[stacks 00S2]
/-
**Algebra.H1Cotangent.exact_map_** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given algebras $R \to S \to T$, the sequence
$H_1(L_{T/R}) \to H_1(L_{T/S}) \to T \otimes_S \Omega_{S/R}$
is exact.
-/
lemma H1Cotangent.exact_map_δ : Function.Exact (map R S T T) (δ R S T) :=
  Generators.H1Cotangent.exact_map_δ' (Generators.self S T)
    (Generators.self R S) (Generators.self R T) (Generators.defaultHom _ _)

/-- Given algebras $R \to S \to T$, the sequence
$H_1(L_{T/S}) \to T \otimes_S \Omega_{S/R} \to \Omega_{T/R}$
is exact. -/
@[stacks 00S2]
/-
**Algebra.H1Cotangent.exact_** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given algebras $R \to S \to T$, the sequence
$H_1(L_{T/S}) \to T \otimes_S \Omega_{S/R} \to \Omega_{T/R}$
is exact.
-/
lemma H1Cotangent.exact_δ_mapBaseChange : Function.Exact (δ R S T) (mapBaseChange R S T) :=
  Generators.H1Cotangent.exact_δ_map (Generators.self S T) (Generators.self R S)

/-- Given algebras $R \to S \to T$ and $T$ flat over $S$, the sequence
$T \otimes_S H_1(L_{S/R}) \to H_1(L_{T/R}) \to H_1(L_{T/S})$
is exact. -/
@[stacks 00S2]
/-
**Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat** 是 Mathlib 中的一个定理，位于命名空间
 `Algebra.H1Cotangent`。
形式化陈述：∀ (R : Type u₁) (S : Type u₂) [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] (T : Type u₃)   [inst_3 : CommRing T] [inst_4 : Algebra R T
] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T] [Module.Flat S T],   Fun
ction.Exact ⇑(LinearMap.liftBaseChange T (Algebra.H1Cotangent.map R R S T)) ⇑(Al
gebra.H1Cotangent.map R S T T)
参数：R : Type u₁；S : Type u₂；T : Type u₃；LinearMap.liftBaseChange T (Algebra.H1Cot
angent.map R R S T)；Algebra.H1Cotangent.map R S T T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Generators.H1Cotangent.exact_liftBaseChange_map_of_flat'`：exact_
liftBaseChange_map_of_flat' [Module.Flat S T] (f : Hom W Q) (g : Hom P W) : Func
tion.Exact ((Extension.H1Cotangent.map g.toExtensionHo…

--- 原说明 ---
Given algebras $R \to S \to T$ and $T$ flat over $S$, the sequence
$T \otimes_S H_1(L_{S/R}) \to H_1(L_{T/R}) \to H_1(L_{T/S})$
is exact.
-/
lemma H1Cotangent.exact_liftBaseChange_map_of_flat [Module.Flat S T] :
    Function.Exact ((map R R S T).liftBaseChange T) (map R S T T) :=
  Generators.H1Cotangent.exact_liftBaseChange_map_of_flat'
    (Generators.self S T) (Generators.self R S) (Generators.self R T)
    (Generators.defaultHom _ _) (Generators.defaultHom _ _)

end Algebra

