/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basis
public import Mathlib.RingTheory.Extension.Cotangent.Free
public import Mathlib.RingTheory.Smooth.Locus

/-!
# Standard smooth of free Kaehler differentials

In this file we show a presentation independent characterization of being
standard smooth: An `R`-algebra `S` of finite presentation is standard smooth if and only if
`H¹(S/R) = 0` and `Ω[S⁄R]` is free on `{d sᵢ}ᵢ` for some `sᵢ : S`.

From this we deduce relations of standard smooth with other local properties.

## Main results

- `IsStandardSmooth.iff_exists_basis_kaehlerDifferential`: An `R`-algebra `S` of finite
  presentation is standard smooth if and only if `H¹(S/R) = 0` and `Ω[S⁄R]` is free on
  `{d sᵢ}ᵢ` for some `sᵢ : S`.
- `Etale.iff_isStandardSmoothOfRelativeDimension_zero`: An `R`-algebra `S` is
  étale if and only if it is standard smooth of relative dimension zero.
- `IsSmoothAt.exists_notMem_isStandardSmooth`: If `S` is `R`-smooth at a prime `p`,
  it is standard smooth on a standard open containing `p`.

## Notes

For an example of an algebra with `H¹(S/R) = 0` and `Ω[S⁄R]` finite and free, but
`S` not standard smooth over `R`, consider `R = ℝ` and `S = R[x,y]/(x² + y² - 1)` the
coordinate ring of the circle. One can show that then `Ω[S⁄R]` is `S`-free on `ω = xdy - ydx`,
but there are no `f g : S` such that `ω = g df`.
-/

public section

namespace Algebra

open KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `H¹(S/R) = 0` and `Ω[S⁄R]` is free on `{d sᵢ}ᵢ` for some `sᵢ : S`, then `S`
is `R`-standard smooth. -/
/-
**Algebra.IsStandardSmooth.of_basis_kaehlerDifferential** 是 Mathlib 中的一个定理，位于命名空
间 `Algebra.IsStandardSmooth`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.FinitePresentation R S] [Subsingleton (Algebra
.H1Cotangent R S)] {I : Type u_3}   (b : Module.Basis I S Ω[S⁄R]), Set.range ⇑b 
⊆ Set.range ⇑(KaehlerDifferential.D R S) → Algebra.IsStandardSmooth R S
参数：Algebra.H1Cotangent R S；b : Module.Basis I S Ω[S⁄R]；KaehlerDifferential.D R S
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Algebra.instIsStandardSmoothOfSubsingleton`：∀ {R : Type u} {S : Type v} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Subsingleton S
],   Algebra.IsStandardSmooth R …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FiniteType.iff_exists_generators`：∀ {R : Type u} {S : Type v} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S],   Algebra.Finite
Type R S ↔ ∃ n, Nonempty (Alge…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用引理 `Algebra.Generators.cotangentRestrict_bijective_of_basis_kaehlerDifferent
ial`：cotangentRestrict_bijective_of_basis_kaehlerDifferential (huv : IsCompl (Se
t.range v) (Set.range u)) (b : Module.Basis κ S (Ω[S⁄R])) (hb : f…
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Set.isCompl_range_inl_range_inr`：isCompl_range_inl_range_inr : IsCompl (
range <| @Sum.inl α β) (range Sum.inr)
· 使用引理 `Module.Finite.finite_basis`：finite_basis [Nontrivial R] {ι} [Module.Fini
te R M] (b : Basis ι R M) : _root_.Finite ι
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用引理 `Algebra.Presentation.relation_mem_ker`：relation_mem_ker (i) : P.relation
 i in P.ker
· 使用定理 `Algebra.Generators.exists_presentation_of_basis_cotangent`：∀ {R : Type u
_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R
 S]   [Algebra.FinitePresentation R S] {α : Typ…
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sum.map_injective`：map_injective {f : α -> γ} {g : β -> δ} : Injective (
Sum.map f g) ↔ Injective f ∧ Injective g where mp h
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
If `H¹(S/R) = 0` and `Ω[S⁄R]` is free on `{d sᵢ}ᵢ` for some `sᵢ : S`, then `S`
is `R`-standard smooth.
-/
theorem IsStandardSmooth.of_basis_kaehlerDifferential [FinitePresentation R S]
    [Subsingleton (H1Cotangent R S)]
    {I : Type*} (b : Module.Basis I S (Ω[S⁄R])) (hb : Set.range b ⊆ Set.range (D R S)) :
    IsStandardSmooth R S := by
  nontriviality S
  obtain ⟨n, ⟨P⟩⟩ := (FiniteType.iff_exists_generators (R := R) (S := S)).mp inferInstance
  choose f' hf' using hb
  let P := P.extend fun i ↦ f' ⟨i, rfl⟩
  have hb (i : I) : b i = D R S (P.val (Sum.inr i)) := by simp [P, hf']
  have : Function.Bijective (P.cotangentRestrict _) :=
    P.cotangentRestrict_bijective_of_basis_kaehlerDifferential Sum.inl_injective
      Set.isCompl_range_inl_range_inr.symm b hb
  let bcot' : Module.Basis (Fin n) S P.toExtension.Cotangent :=
    .ofRepr (.ofBijective (P.cotangentRestrict _) this)
  have : Finite I := Module.Finite.finite_basis b
  obtain ⟨Q, bcot, hcomp, hbcot⟩ := P.exists_presentation_of_basis_cotangent bcot'
  let P' : PreSubmersivePresentation R S (Unit ⊕ Fin n ⊕ I) (Unit ⊕ Fin n) :=
    { __ := Q
      map := Sum.map _root_.id Sum.inl
      map_inj := Sum.map_injective.mpr ⟨fun _ _ h ↦ h, Sum.inl_injective⟩ }
  have hcompl : IsCompl (Set.range (Sum.inr ∘ Sum.inr)) (Set.range P'.map) := by
    simp [P', ← eq_compl_iff_isCompl, Set.ext_iff, Set.mem_compl_iff]
  have hbij : Function.Bijective (P'.cotangentRestrict P'.map_inj) := by
    apply P'.cotangentRestrict_bijective_of_basis_kaehlerDifferential P'.map_inj hcompl b
    intro k
    simp only [hb, ← hcomp, P', Function.comp_def]
  let P'' : SubmersivePresentation R S _ _ :=
    ⟨P', P'.isUnit_jacobian_of_cotangentRestrict_bijective bcot hbcot hbij⟩
  exact P''.isStandardSmooth

/-- An `R`-algebra `S` of finite presentation is standard smooth if and only if
`H¹(S/R) = 0` and `Ω[S⁄R]` is free on `{d sᵢ}ᵢ` for some `sᵢ : S`. -/
/-
**Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential** 是 Mathlib 中的一个
定理，位于命名空间 `Algebra.IsStandardSmooth`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.FinitePresentation R S],   Algebra.IsStandardS
mooth R S ↔     Subsingleton (Algebra.H1Cotangent R S) ∧ ∃ I b, Set.range ⇑b ⊆ S
et.range ⇑(KaehlerDifferential.D R S)
参数：Algebra.H1Cotangent R S；KaehlerDifferential.D R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.IsStandardSmooth.subsingleton_h1Cotangent`：∀ {R : Type u_1} {S :
 Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [A
lgebra.IsStandardSmooth R S], Subsingle…
· 使用定理 `Algebra.IsStandardSmooth.out`：∀ {R : Type u} {S : Type v} {inst : CommRi
ng R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [self : Algebra.IsStandardS
mooth R S],   ∃ ι …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.SubmersivePresentation.basisKaehler_apply`：basisKaehler_apply (k
 : ((Set.range P.map)ᶜ : Set _)) : P.basisKaehler k = KaehlerDifferential.D _ _ 
(P.val k)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Algebra.IsStandardSmooth.of_basis_kaehlerDifferential`：∀ {R : Type u_1} 
{S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] 
  [Algebra.FinitePresentation R S] [Subsing…

--- 原说明 ---
An `R`-algebra `S` of finite presentation is standard smooth if and only if
`H¹(S/R) = 0` and `Ω[S⁄R]` is free on `{d sᵢ}ᵢ` for some `sᵢ : S`.
-/
theorem IsStandardSmooth.iff_exists_basis_kaehlerDifferential [FinitePresentation R S] :
    IsStandardSmooth R S ↔ Subsingleton (H1Cotangent R S) ∧
      ∃ (I : Type) (b : Module.Basis I S (Ω[S⁄R])), Set.range b ⊆ Set.range (D R S) := by
  refine ⟨fun h ↦ ⟨inferInstance, ?_⟩, fun ⟨h, ⟨_, b, hb⟩⟩ ↦ .of_basis_kaehlerDifferential b hb⟩
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := R) (S := S)
  exact ⟨_, P.basisKaehler, by simp [Set.range_subset_iff]⟩

/-- `S` is an étale `R`-algebra if and only if it is standard smooth of relative dimension `0`. -/
/-
**Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero** 是 Mathlib 中的一个定理，
位于命名空间 `Algebra.Etale`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S],   Algebra.Etale R S ↔ Algebra.IsStandardSmoothOfRelative
Dimension 0 R S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Algebra.instIsStandardSmoothOfRelativeDimensionOfNatNatOfSubsingleton`：∀
 {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : A
lgebra R S] [Subsingleton S],   Algebra.IsStandardSmoothOfR…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential`：∀ {R : Ty
pe u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algeb
ra R S]   [Algebra.FinitePresentation R S],   Algeb…
· 使用定理 `Algebra.Etale.finitePresentation`：∀ {R : Type u} {A : Type v} {inst : Co
mmRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A
],   Algebra.FinitePre…
· 使用定理 `Algebra.FormallyEtale.subsingleton_h1Cotangent`：∀ {R : Type u} {A : Type
 v} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : A
lgebra.FormallyEtale R A], Subsingle…
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
· 使用定理 `Algebra.FormallyEtale.subsingleton_kaehlerDifferential`：∀ {R : Type u} {
A : Type v} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [
self : Algebra.FormallyEtale R A], Subsingle…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.instEtaleOfIsStandardSmoothOfRelativeDimensionOfNatNat`：∀ {R : T
ype u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alge
bra R S]   [Algebra.IsStandardSmoothOfRelativeDimens…

--- 原说明 ---
`S` is an étale `R`-algebra if and only if it is standard smooth of relative dim
ension `0`.
-/
theorem Etale.iff_isStandardSmoothOfRelativeDimension_zero :
    Etale R S ↔ IsStandardSmoothOfRelativeDimension 0 R S := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  nontriviality S
  suffices h : IsStandardSmooth R S by
    simp [IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  rw [IsStandardSmooth.iff_exists_basis_kaehlerDifferential]
  refine ⟨inferInstance, ⟨Empty, Module.Basis.empty Ω[S⁄R], ?_⟩⟩
  simp [Set.range_subset_iff]

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
/-- If `S` is `R`-smooth at a prime `p`, then `S` is `R`-standard-smooth in a neighbourhood of `p`:
there exists a basic open `p ∈ D(f)` of `Spec S` such that `S[1/f]` is standard smooth. -/
/-
**Algebra.IsSmoothAt.exists_notMem_isStandardSmooth** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra.IsSmoothAt`。
形式化陈述：∀ (R : Type u_1) {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.FinitePresentation R S] (p : Ideal S) [inst_4 
: p.IsPrime] [Algebra.IsSmoothAt R p],   ∃ f ∉ p, Algebra.IsStandardSmooth R (Lo
calization.Away f)
参数：R : Type u_1；p : Ideal S；Localization.Away f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Module.exists_basis_of_span_of_flat`：exists_basis_of_span_of_flat [Modul
e.FinitePresentation R M] [Module.Flat R M] {ι : Type u} (v : ι -> M) (hv : Subm
odule.span R (Set.range v…
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Algebra.FormallySmooth.instFinitePresentationKaehlerDifferentialOfEssFin
iteType`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [
inst_2 : Algebra R A] [Algebra.EssFiniteType R A]   [Algebra.Formally…
· 使用定理 `Algebra.instEssFiniteTypeLocalization`：∀ (R : Type u_1) (S : Type u_2) [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.EssFi
niteType R S] (M : Submonoi…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Algebra.FormallySmooth.projective_kaehlerDifferential`：∀ {R : Type u} {A
 : Type v} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [s
elf : Algebra.FormallySmooth R A], Module.P…
· 使用引理 `KaehlerDifferential.span_range_map_derivation_of_isLocalization`：Kaehler
Differential.span_range_map_derivation_of_isLocalization (M : Submonoid S) [IsLo
calization M T] : Submodule.span T (Set.range <| map …
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `instIsLocalizedModuleFinsuppLinearMap`：∀ (R : Type u_1) [inst : CommSemi
ring R] (S : Submonoid R) (M : Type u_3) [inst_1 : AddCommMonoid M]   [inst_2 : 
_root_.Module R M] {M' : Ty…
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.mapExtendScalars_apply_apply`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddC
ommMonoid M]   [inst_2 : AddCommMono…
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
If `S` is `R`-smooth at a prime `p`, then `S` is `R`-standard-smooth in a neighb
ourhood of `p`:
there exists a basic open `p ∈ D(f)` of `Spec S` such that `S[1/f]` is standard 
smooth.
-/
theorem IsSmoothAt.exists_notMem_isStandardSmooth [FinitePresentation R S] (p : Ideal S) [p.IsPrime]
    [IsSmoothAt R p] :
    ∃ (f : S), f ∉ p ∧ IsStandardSmooth R (Localization.Away f) := by
  -- By replacing `S` by some `S[1/g]` we may assume `S` is globally smooth.
  wlog h : Smooth R S
  · obtain ⟨g, hg, hsm⟩ := IsSmoothAt.exists_notMem_smooth R p
    have _ : (Ideal.map (algebraMap S (Localization.Away g)) p).IsPrime := by
      apply IsLocalization.isPrime_of_isPrime_disjoint (.powers g) _ _ ‹_›
      rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    obtain ⟨g', hg', hstd⟩ := this (R := R) (p.map (algebraMap S (Localization.Away g))) hsm
    have : IsLocalization.Away (g * (IsLocalization.Away.sec g g').1) (Localization.Away g') :=
      .mul_of_associated _ _ g' <| IsLocalization.Away.associated_sec_fst g g'
    let e : Localization.Away (g * (IsLocalization.Away.sec g g').1) ≃ₐ[S] Localization.Away g' :=
      Localization.algEquiv _ _
    refine ⟨g * (IsLocalization.Away.sec g g').1, ?_, .of_algEquiv (e.restrictScalars R).symm⟩
    refine Ideal.IsPrime.mul_notMem ‹_› hg fun hmem ↦ hg' ?_
    rw [Ideal.mem_iff_of_associated (IsLocalization.Away.associated_sec_fst g g').symm]
    exact Ideal.mem_map_of_mem (algebraMap S (Localization.Away g)) hmem
  -- `Ω[Sₚ⁄R]` is projective, so free over the local ring `Sₚ` and
  -- a basis extends to a neighbourhood `D(g)`.
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _
    (span_range_map_derivation_of_isLocalization R _ (Localization.AtPrime p) p.primeCompl)
  let e : (κ →₀ S) →ₗ[S] Ω[S⁄R] :=
    Finsupp.linearCombination S fun i : κ ↦ D R S (a i)
  let l₁ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  let l₂ : Ω[S⁄R] →ₗ[S] Ω[Localization.AtPrime p⁄R] := map R R S (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e <| l₁ <| Finsupp.single i 1
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb]
  have heₚ : Function.Bijective eₚ := this ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ : Ω[S⁄R] →ₗ[S] Ω[Localization.Away g⁄R] :=
    map R R S (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  refine ⟨g, hg, .of_basis_kaehlerDifferential (.ofRepr (LinearEquiv.ofBijective eₜ' h).symm) ?_⟩
  rintro - ⟨i, rfl⟩
  exact ⟨algebraMap S _ (a i), by simp +zetaDelta [IsLocalizedModule.map_linearCombination]⟩

variable (R S) in
/-- If `S` is `R`-smooth, there exists a cover by basic opens `D(sᵢ)` such that
`S[1/sᵢ]` is `R`-standard-smooth. -/
/-
**Algebra.Smooth.exists_span_eq_top_isStandardSmooth** 是 Mathlib 中的一个定理，位于命名空间 `
Algebra.Smooth`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [Algebra.Smooth R S],   ∃ s, Ideal.span s = ⊤ ∧ ∀ x ∈ s, 
Algebra.IsStandardSmooth R (Localization.Away x)
参数：R : Type u_1；S : Type u_2；Localization.Away x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Algebra.FormallySmooth.instLocalization`：∀ {R : Type u_4} {A : Type u_5}
 [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.For
mallySmooth R A] (M : Submono…
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`：∀ (R : Type u_1) {S :
 Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [A
lgebra.FinitePresentation R S] (p : Ide…
· 使用定理 `Algebra.Smooth.finitePresentation`：∀ {R : Type u_4} {inst : CommRing R} 
{A : Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smoo
th R A], Algebra.Finite…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `S` is `R`-smooth, there exists a cover by basic opens `D(sᵢ)` such that
`S[1/sᵢ]` is `R`-standard-smooth.
-/
theorem Smooth.exists_span_eq_top_isStandardSmooth [Smooth R S] :
    ∃ (s : Set S), Ideal.span s = ⊤ ∧ ∀ x ∈ s, IsStandardSmooth R (Localization.Away x) := by
  choose f hf₁ hf₂ using IsSmoothAt.exists_notMem_isStandardSmooth R (S := S)
  /- #adaptation_note Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), the original proof was:
  `refine ⟨Set.range (fun p : PrimeSpectrum S ↦ f p.asIdeal), ?_, by grind⟩`
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. -/
  refine ⟨Set.range (fun p : PrimeSpectrum S ↦ f p.asIdeal), ?_, by
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]; intro; apply hf₂⟩
  simp [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, TopologicalSpace.Opens.ext_iff, Set.ext_iff]
  grind

end Algebra

