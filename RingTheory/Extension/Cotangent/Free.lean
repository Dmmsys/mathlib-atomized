/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Basis.Exact
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive

/-!
# Computation of Jacobian of presentations from basis of Cotangent

Let `P` be a presentation of an `R`-algebra `S` with kernel `I = (fᵢ)`.
In this file we provide lemmas to show that `P` is submersive when given suitable bases of
`I/I²` and `Ω[S⁄R]`.

We will later deduce from this a presentation-independent characterisation of standard
smooth algebras (TODO @chrisflav).

## Main results

- `PreSubmersivePresentation.isUnit_jacobian_of_cotangentRestrict_bijective`:
  If the `fᵢ` form a basis of `I/I²` and the restricted cotangent complex
  `I/I² → S ⊗[R] (Ω[R[Xᵢ]⁄R]) = ⊕ᵢ S → ⊕ⱼ S` is bijective, `P` is submersive.
-/

public section

universe t₂ t₁ u v

open KaehlerDifferential MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι σ κ : Type*}

namespace Algebra

namespace Generators

variable (P : Generators R S ι) {u : σ → ι} (hu : Function.Injective u)
  {v : κ → ι} (hv : Function.Injective v)

/--
If `H¹(L_{S/R}) = 0` and `R[xᵢ] → S` are generators indexed by `σ ⊕ κ` such that the images
of `dxₖ` for `k : κ` span `Ω[S⁄R]` and the span of the `dXₖ` for `k : κ` in
`S ⊗[R] Ω[R[Xᵢ⁄R]]` intersects the kernel of the projection trivially, then the restriction of
`I/I² → ⊕ S dxᵢ` to the direct sum indexed by `i : ι` is an isomorphism.

The assumptions are in particular satisfied if the `dsₖ` form an `S`-basis of `Ω[S⁄R]`,
see `Generators.disjoint_ker_toKaehler_of_linearIndependent` for one half.
Via `PreSubmersivePresentation.isUnit_jacobian_of_cotangentRestrict_bijective`, this can be useful
to show a presentation is submersive.
-/
/-
**Algebra.Generators.cotangentRestrict_bijective_of_isCompl** 是 Mathlib 中的一个引理，位
于命名空间 `Algebra.Generators`。
形式化陈述：cotangentRestrict_bijective_of_isCompl (huv : IsCompl (Set.range v) (Set.r
ange u)) (hm : Submodule.span S (.range fun i => D R S (P.val (v i))) = ⊤) (hk :
 Disjoint (LinearMap.ker P.toExtension.toKaehler) (.span S (.range fun x => P.co
tangentSpaceBasis (v x)))) [Subsingleton (H1Cotangent R S)] : Function.Bijective
 (cotangentRestrict P hu)
参数：huv : IsCompl (Set.range v) (Set.range u)；hm : Submodule.span S (.range fun i
 => D R S (P.val (v i))) = ⊤；hk : Disjoint (LinearMap.ker P.toExtension.toKaehle
r) (.span S (.range fun x => P.cotangentSpaceBasis (v x)))；H1Cotangent R S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Generators.cotangentRestrict.eq_1`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {ι : Type w}   (
P : Algebra.Generators R S ι) {…
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)
· 使用引理 `Finsupp.isCompl_range_lmapDomain_span`：isCompl_range_lmapDomain_span {α 
β : Type*} {u : α -> ι} {v : β -> ι} (huv : IsCompl (Set.range u) (Set.range v))
 : IsCompl (LinearMap.range…
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用引理 `Finsupp.lcomapDomain_eq_linearProjOfIsCompl`：lcomapDomain_eq_linearProjO
fIsCompl {α β : Type*} {u : α -> ι} {v : β -> ι} (hu : u.Injective) (h : IsCompl
 (Set.range u) (Set.range v)) : l…
· 使用引理 `Algebra.Extension.exact_cotangentComplex_toKaehler`：exact_cotangentCompl
ex_toKaehler : Function.Exact P.cotangentComplex P.toKaehler
· 使用引理 `LinearMap.linearProjOfIsCompl_comp_bijective_of_exact`：LinearMap.linearP
rojOfIsCompl_comp_bijective_of_exact (hf : Function.Injective f) {q : Submodule 
R M} {E : Type*} [AddCommGroup E] [Module R…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Algebra.Extension.subsingleton_h1Cotangent`：subsingleton_h1Cotangent (P 
: Extension R S) : Subsingleton P.H1Cotangent ↔ Function.Injective P.cotangentCo
mplex
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `Submodule.map_inf`：map_inf (f : M ->ₛₗ[σ₁₂] M₂) {p q : Submodule R M} (h
f : Injective f) : (p ⊓ q).map f = p.map f ⊓ q.map f
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `Submodule.map_comap_eq_of_surjective`：map_comap_eq_of_surjective (p : Su
bmodule R₂ M₂) : (p.comap f).map f = p
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.coe_repr_symm`：coe_repr_symm : ↑b.repr.symm = Finsupp.linea
rCombination R b
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If `H¹(L_{S/R}) = 0` and `R[xᵢ] → S` are generators indexed by `σ ⊕ κ` such that
 the images
of `dxₖ` for `k : κ` span `Ω[S⁄R]` and the span of the `dXₖ` for `k : κ` in
`S ⊗[R] Ω[R[Xᵢ⁄R]]` intersects the kernel of the projection trivially, then the 
restriction of
`I/I² → ⊕ S dxᵢ` to the direct sum indexed by `i : ι` is an isomorphism.

The assumptions are in particular satisfied if the `dsₖ` form an `S`-basis of `Ω
[S⁄R]`,
see `Generators.disjoint_ker_toKaehler_of_linearIndependent` for one half.
Via `PreSubmersivePresentation.isUnit_jacobian_of_cotangentRestrict_bijective`, 
this can be useful
to show a presentation is submersive.
-/
lemma cotangentRestrict_bijective_of_isCompl
    (huv : IsCompl (Set.range v) (Set.range u))
    (hm : Submodule.span S (.range fun i ↦ D R S (P.val (v i))) = ⊤)
    (hk : Disjoint (LinearMap.ker P.toExtension.toKaehler)
        (.span S (.range fun x ↦ P.cotangentSpaceBasis (v x))))
    [Subsingleton (H1Cotangent R S)] :
    Function.Bijective (cotangentRestrict P hu) := by
  rw [cotangentRestrict, Finsupp.lcomapDomain_eq_linearProjOfIsCompl _ huv.symm]
  set f : _ →ₗ[S] (ι →₀ S) := P.cotangentSpaceBasis.repr ∘ₗ P.toExtension.cotangentComplex
  let g : (ι →₀ S) →ₗ[S] (Ω[S⁄R]) := P.toExtension.toKaehler ∘ₗ P.cotangentSpaceBasis.repr.symm
  have hfg : Function.Exact f g := by
    simp only [f, g, LinearEquiv.conj_exact_iff_exact]
    exact Extension.exact_cotangentComplex_toKaehler
  apply LinearMap.linearProjOfIsCompl_comp_bijective_of_exact hfg
  · exact P.cotangentSpaceBasis.repr.injective.comp <|
      (Extension.subsingleton_h1Cotangent P.toExtension).mp P.equivH1Cotangent.subsingleton
  · simp only [disjoint_iff, g]
    apply Submodule.map_injective_of_injective (f := P.cotangentSpaceBasis.repr.symm.toLinearMap)
      P.cotangentSpaceBasis.repr.symm.injective
    rw [Submodule.map_inf P.cotangentSpaceBasis.repr.symm.toLinearMap
        P.cotangentSpaceBasis.repr.symm.injective, Submodule.map_span, ← Set.range_comp,
        Function.comp_def, LinearMap.ker_comp, Submodule.map_comap_eq_of_surjective]
    · simpa [← disjoint_iff]
    · exact P.cotangentSpaceBasis.repr.symm.surjective
  · simpa [g, Submodule.map_comp, Submodule.map_span, ← Set.range_comp, Function.comp_def]
/-
**Algebra.Generators.disjoint_ker_toKaehler_of_linearIndependent** 是 Mathlib 中的一
个引理，位于命名空间 `Algebra.Generators`。
形式化陈述：disjoint_ker_toKaehler_of_linearIndependent (h : LinearIndependent S (fun 
k => D R S (P.val (v k)))) : Disjoint (LinearMap.ker P.toExtension.toKaehler) (.
span S <| .range fun x => P.cotangentSpaceBasis (v x))
参数：h : LinearIndependent S (fun k => D R S (P.val (v k)))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Finsupp.mem_span_range_iff_exists_finsupp`：mem_span_range_iff_exists_fin
supp {v : α -> M} {x : M} : x in span R (range v) ↔ exists c : α ->₀ R, (c.sum f
un i a => a • v i) = x
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndependent_iff`：linearIndependent_iff : LinearIndependent R v ↔ f
orall l, Finsupp.linearCombination R v l = 0 -> l = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `Algebra.Generators.toKaehler_cotangentSpaceBasis`：toKaehler_cotangentSpa
ceBasis (i) : P.toExtension.toKaehler (P.cotangentSpaceBasis i) = D R S (P.val i
)
-/
lemma disjoint_ker_toKaehler_of_linearIndependent
    (h : LinearIndependent S (fun k ↦ D R S (P.val (v k)))) :
    Disjoint (LinearMap.ker P.toExtension.toKaehler)
        (.span S <| .range fun x ↦ P.cotangentSpaceBasis (v x)) := by
  rw [disjoint_iff, Submodule.eq_bot_iff]
  intro x ⟨hx, hxs⟩
  rw [SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp] at hxs
  obtain ⟨c, rfl⟩ := hxs
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_finsuppSum, map_smul,
    toKaehler_cotangentSpaceBasis] at hx
  obtain rfl := (linearIndependent_iff.mp h) c hx
  simp
/-
**Algebra.Generators.cotangentRestrict_bijective_of_basis_kaehlerDifferential** 
是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators`。
形式化陈述：cotangentRestrict_bijective_of_basis_kaehlerDifferential (huv : IsCompl (S
et.range v) (Set.range u)) (b : Module.Basis κ S (Ω[S⁄R])) (hb : forall k, b k =
 (D R S) (P.val (v k))) [Subsingleton (H1Cotangent R S)] : Function.Bijective (c
otangentRestrict P hu)
参数：huv : IsCompl (Set.range v) (Set.range u)；b : Module.Basis κ S (Ω[S⁄R])；hb : 
forall k, b k = (D R S) (P.val (v k))；H1Cotangent R S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Algebra.Generators.cotangentRestrict_bijective_of_isCompl`：cotangentRest
rict_bijective_of_isCompl (huv : IsCompl (Set.range v) (Set.range u)) (hm : Subm
odule.span S (.range fun i => D R S (P.val (v i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用引理 `Algebra.Generators.disjoint_ker_toKaehler_of_linearIndependent`：disjoint
_ker_toKaehler_of_linearIndependent (h : LinearIndependent S (fun k => D R S (P.
val (v k)))) : Disjoint (LinearMap.ker P.toExtension…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
-/
lemma cotangentRestrict_bijective_of_basis_kaehlerDifferential
    (huv : IsCompl (Set.range v) (Set.range u)) (b : Module.Basis κ S (Ω[S⁄R]))
    (hb : ∀ k, b k = (D R S) (P.val (v k))) [Subsingleton (H1Cotangent R S)] :
    Function.Bijective (cotangentRestrict P hu) := by
  refine P.cotangentRestrict_bijective_of_isCompl _ huv ?_ ?_
  · simp_rw [← hb]
    exact b.span_eq
  · apply disjoint_ker_toKaehler_of_linearIndependent
    simp_rw [← hb]
    exact b.linearIndependent

end Generators

namespace PreSubmersivePresentation

open Generators

variable (P : PreSubmersivePresentation R S ι σ) [Finite σ]

set_option backward.isDefEq.respectTransparency.types false in
/-- To show a pre-submersive presentation with kernel `I = (fᵢ)` is submersive, it suffices to show
that the images of the `fᵢ` form a basis of `I/I²` and that the restricted
cotangent complex `I/I² → S ⊗[R] (Ω[R[Xᵢ]⁄R]) = ⊕ᵢ S → ⊕ⱼ S` is bijective. -/
/-
**Algebra.PreSubmersivePresentation.isUnit_jacobian_of_cotangentRestrict_bijecti
ve** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：isUnit_jacobian_of_cotangentRestrict_bijective (b : Module.Basis σ S P.toE
xtension.Cotangent) (hb : forall r, b r = Extension.Cotangent.mk ⟨P.relation r, 
P.relation_mem_ker r⟩) (h : Function.Bijective (P.cotangentRestrict P.map_inj)) 
: IsUnit P.jacobian
参数：b : Module.Basis σ S P.toExtension.Cotangent；hb : forall r, b r = Extension.C
otangent.mk ⟨P.relation r, P.relation_mem_ker r⟩；h : Function.Bijective (P.cotan
gentRestrict P.map_inj)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.Presentation.relation_mem_ker`：relation_mem_ker (i) : P.relation
 i in P.ker
· 使用定理 `Algebra.PreSubmersivePresentation.map_inj`：∀ {R : Type u} {S : Type v} {
ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alg
ebra R S]   (self : Algebra.Pre…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.linearEquivFunOnFinite_apply`：∀ (R : Type u_9) (M : Type u_11) (
α : Type u_12) [inst : Finite α] [inst_1 : AddCommMonoid M] [inst_2 : Semiring R
]   [inst_3 : _root_.Modul…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Algebra.Generators.cotangentRestrict_mk`：cotangentRestrict_mk {σ : Type*
} {u : σ -> ι} (hu : Function.Injective u) (x : P.ker) : cotangentRestrict P hu 
(Extension.Cotangent.mk x) = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Algebra.PreSubmersivePresentation.isUnit_jacobian_of_linearIndependent_o
f_span_eq_top`：isUnit_jacobian_of_linearIndependent_of_span_eq_top (hli : Linear
Independent S (fun j i : σ => aeval P.val <| pderiv (P.map i) (P.relation j…
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Submodule.span_image_linearEquiv`：span_image_linearEquiv {σ₂₁} [RingHomI
nvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (f : M ≃ₛₗ[σ₁₂] M₂) : span R₂ (f '' s) 
= map (f : M ->ₛₗ[σ₁₂]…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearMap.range_eq_top_of_surjective`：range_eq_top_of_surjective [RingHo
mSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (hf : Surjective f) : range f = ⊤
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…

--- 原说明 ---
To show a pre-submersive presentation with kernel `I = (fᵢ)` is submersive, it s
uffices to show
that the images of the `fᵢ` form a basis of `I/I²` and that the restricted
cotangent complex `I/I² → S ⊗[R] (Ω[R[Xᵢ]⁄R]) = ⊕ᵢ S → ⊕ⱼ S` is bijective.
-/
lemma isUnit_jacobian_of_cotangentRestrict_bijective
    (b : Module.Basis σ S P.toExtension.Cotangent)
    (hb : ∀ r, b r = Extension.Cotangent.mk ⟨P.relation r, P.relation_mem_ker r⟩)
    (h : Function.Bijective (P.cotangentRestrict P.map_inj)) :
    IsUnit P.jacobian := by
  have heq : (fun j i ↦ (aeval P.val) (pderiv (P.map i) (P.relation j))) =
      Finsupp.linearEquivFunOnFinite S S _ ∘ P.cotangentRestrict P.map_inj ∘ ⇑b := by
    ext i j
    simp only [Function.comp_apply, hb, Finsupp.linearEquivFunOnFinite_apply, cotangentRestrict_mk]
  apply P.isUnit_jacobian_of_linearIndependent_of_span_eq_top
  · rw [heq]
    exact (b.linearIndependent.map' _ (LinearMap.ker_eq_bot_of_injective h.injective)).map' _
      (Finsupp.linearEquivFunOnFinite S S σ).ker
  · rw [heq, Set.range_comp, Set.range_comp, Submodule.span_image_linearEquiv, ← Submodule.map_span,
      b.span_eq, Submodule.map_top, LinearMap.range_eq_top_of_surjective _ h.surjective,
      Submodule.map_top, LinearEquiv.range]

end PreSubmersivePresentation

end Algebra

