/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Amelia Livingston
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Hilbert's Theorem 90

Let `L/K` be a finite extension of fields. Then this file proves Noether's generalization of
Hilbert's Theorem 90: that the 1st group cohomology $H^1(Aut_K(L), L^\times)$ is trivial. We state
it both in terms of $H^1$ and in terms of cocycles being coboundaries.

Hilbert's original statement was that if $L/K$ is Galois, and $Gal(L/K)$ is cyclic, generated
by an element `σ`, then for every `x : L` such that $N_{L/K}(x) = 1,$ there exists `y : L` such
that $x = y/σ(y).$ Using the fact that `H¹(G, A) ≅ Ker(N_A)/(ρ(g) - 1)(A)` for any finite cyclic
group `G` with generator `g`, we deduce the original statement from Noether's generalization.

Noether's generalization also holds for infinite Galois extensions.

## Main statements

* `groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`: Noether's generalization
  of Hilbert's Theorem 90: for all $f: Aut_K(L) \to L^\times$ satisfying the 1-cocycle
  condition, there exists `β : Lˣ` such that $g(β)/β = f(g)$ for all `g : Aut_K(L)`.
* `groupCohomology.H1ofAutOnUnitsUnique`: Noether's generalization of Hilbert's Theorem 90:
  $H^1(Aut_K(L), L^\times)$ is trivial.
* `groupCohomology.exists_div_of_norm_eq_one`: Hilbert's Theorem 90: given a finite cyclic Galois
  extension `L/K`, an element `x : L` such that `N_{L/K}(x) = 1`, and a generator `g` of
  `Gal(L/K)`, there exists `y : Lˣ` such that `y/g y = x`.

## Implementation notes

Given a commutative ring `k` and a group `G`, group cohomology is developed in terms of `k`-linear
`G`-representations on `k`-modules. Therefore stating Noether's generalization of Hilbert 90 in
terms of `H¹` requires us to turn the natural action of `Aut_K(L)` on `Lˣ` into a morphism
`Aut_K(L) →* (Additive Lˣ →ₗ[ℤ] Additive Lˣ)`. Thus we provide the non-`H¹` version too, as its
statement is clearer.

## TODO

* Develop Galois cohomology to extend Noether's result to infinite Galois extensions.
* "Additive Hilbert 90": let `L/K` be a finite Galois extension. Then $H^n(Gal(L/K), L)$ is trivial
  for all $1 ≤ n.$

-/

@[expose] public section


namespace groupCohomology
namespace Hilbert90

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Given `f : Aut_K(L) → Lˣ`, the sum `∑ f(φ) • φ` for `φ ∈ Aut_K(L)`, as a function `L → L`. -/
/-
**groupCohomology.Hilbert90.aux** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology.Hilbe
rt90`。
形式化陈述：aux (f : Gal(L/K) -> Lˣ) : L -> L
参数：f : Gal(L/K) -> Lˣ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `f : Aut_K(L) → Lˣ`, the sum `∑ f(φ) • φ` for `φ ∈ Aut_K(L)`, as a functio
n `L → L`.
-/
noncomputable def aux (f : Gal(L/K) → Lˣ) : L → L :=
  Finsupp.linearCombination L (fun φ : Gal(L/K) ↦ (φ : L → L))
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))
/-
**groupCohomology.Hilbert90.aux_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomolo
gy.Hilbert90`。
形式化陈述：aux_ne_zero (f : Gal(L/K) -> Lˣ) : aux f != 0
参数：f : Gal(L/K) -> Lˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `linearIndependent_monoidHom`：linearIndependent_monoidHom (G : Type*) [Mu
lOneClass G] (L : Type*) [CommRing L] [IsDomain L] : LinearIndependent L (M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
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
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `linearIndependent_iff`：linearIndependent_iff : LinearIndependent R v ↔ f
orall l, Finsupp.linearCombination R v l = 0 -> l = 0
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem aux_ne_zero (f : Gal(L/K) → Lˣ) : aux f ≠ 0 :=
/- the set `Aut_K(L)` is linearly independent in the `L`-vector space `L → L`, by Dedekind's
linear independence of characters -/
  have : LinearIndependent L (fun (f : Gal(L/K)) => (f : L → L)) :=
    LinearIndependent.comp (ι' := Gal(L/K))
      (linearIndependent_monoidHom L L) (fun f => f)
      (fun x y h => by ext; exact DFunLike.ext_iff.1 h _)
  have h := linearIndependent_iff.1 this
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))
  fun H => Units.ne_zero (f 1) (DFunLike.ext_iff.1 (h H) 1)

end Hilbert90
section
open Hilbert90
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Noether's generalization of Hilbert's Theorem 90: given a finite extension of fields and a
function `f : Aut_K(L) → Lˣ` satisfying `f(gh) = g(f(h)) * f(g)` for all `g, h : Aut_K(L)`, there
exists `β : Lˣ` such that `g(β)/β = f(g)` for all `g : Aut_K(L).` -/
/-
**groupCohomology.isMulCoboundary** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noether's generalization of Hilbert's Theorem 90: given a finite extension of fi
elds and a
function `f : Aut_K(L) → Lˣ` satisfying `f(gh) = g(f(h)) * f(g)` for all `g, h :
 Aut_K(L)`, there
exists `β : Lˣ` such that `g(β)/β = f(g)` for all `g : Aut_K(L).`
-/
theorem isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
    (f : Gal(L/K) → Lˣ) (hf : IsMulCocycle₁ f) :
    IsMulCoboundary₁ f := by
/- Let `z : L` be such that `∑ f(h) * h(z) ≠ 0`, for `h ∈ Aut_K(L)` -/
  obtain ⟨z, hz⟩ : ∃ z, aux f z ≠ 0 :=
    not_forall.1 (fun H => aux_ne_zero f <| funext <| fun x => H x)
  have : aux f z = ∑ h, f h * h z := by simp [aux, Finsupp.linearCombination, Finsupp.sum_fintype]
/- Let `β = (∑ f(h) * h(z))⁻¹.` -/
  use (Units.mk0 (aux f z) hz)⁻¹
  intro g
/- Then the equality follows from the hypothesis that `f` is a 1-cocycle. -/
  simp only [IsMulCocycle₁, AlgEquiv.smul_units_def,
    map_inv, div_inv_eq_mul, inv_mul_eq_iff_eq_mul, Units.ext_iff, this,
    Units.val_mul, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe] at hf ⊢
  simp_rw [map_sum, map_mul, Finset.sum_mul, mul_assoc, mul_comm _ (f _ : L), ← mul_assoc, ← hf g]
  exact eq_comm.1 (Fintype.sum_bijective (fun i => g * i)
    (Group.mulLeft_bijective g) _ _ (fun i => rfl))

end
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Noether's generalization of Hilbert's Theorem 90: given a finite extension of fields `L/K`, the
first group cohomology `H¹(Aut_K(L), Lˣ)` is trivial. -/
/-
**groupCohomology.H1ofAutOnUnitsUnique** 是 Mathlib 中的一个实例，位于命名空间 `groupCohomolog
y`。
形式化陈述：H1ofAutOnUnitsUnique : Unique (H1 (Rep.ofAlgebraAutOnUnits K L)) where def
ault
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noether's generalization of Hilbert's Theorem 90: given a finite extension of fi
elds `L/K`, the
first group cohomology `H¹(Aut_K(L), Lˣ)` is trivial.
-/
noncomputable instance H1ofAutOnUnitsUnique : Unique (H1 (Rep.ofAlgebraAutOnUnits K L)) where
  default := 0
  uniq := fun a => H1_induction_on a fun x => (H1π_eq_zero_iff _).2 <| by
    refine (coboundariesOfIsMulCoboundary₁ ?_).2
    rcases isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units x.1
      (isMulCocycle₁_of_mem_cocycles₁ _ x.2) with ⟨β, hβ⟩
    use β

variable {K L} [IsGalois K L]

open Additive Rep

set_option backward.isDefEq.respectTransparency false in
/-- Given `L/K` finite and Galois, and `x : Lˣ`, this essentially says
`(∏ σ) • x = N_{L/K}(x)`, where the product is over `σ ∈ Gal(L/K)`. -/
/-
**groupCohomology.norm_ofAlgebraAutOnUnits_eq** 是 Mathlib 中的一个定理，位于命名空间 `groupCo
homology`。
形式化陈述：norm_ofAlgebraAutOnUnits_eq (x : Lˣ) : (toMul <| toAdditive ((Rep.ofAlgebr
aAutOnUnits K L).norm.hom (toAdditive.symm <| ofMul x))).1 = algebraMap K L (Alg
ebra.norm K (x : L))
参数：x : Lˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
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
· 使用定理 `Rep.toAdditive_symm_apply`：∀ {M : Type u_1} {G : Type u_2} [inst : Monoi
d M] [inst_1 : CommGroup G] [inst_2 : MulDistribMulAction M G]   (a : ↑(Rep.ofMu
lDistribMulActi…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Rep.toAdditive_apply`：∀ {M : Type u_1} {G : Type u_2} [inst : Monoid M] 
[inst_1 : CommGroup G] [inst_2 : MulDistribMulAction M G]   (a : ↑(Rep.ofMulDist
ribMulActi…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Units.coe_prod`：Units.coe_prod [CommMonoid M] (f : α -> Mˣ) (s : Finset 
α) : (↑(∏ i in s, f i) : M) = ∏ i in s, (f i : M)
· 使用定理 `Algebra.norm_eq_prod_automorphisms`：norm_eq_prod_automorphisms [IsGalois
 K L] (x : L) : algebraMap K L (norm K x) = ∏ σ : Gal(L/K), σ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given `L/K` finite and Galois, and `x : Lˣ`, this essentially says
`(∏ σ) • x = N_{L/K}(x)`, where the product is over `σ ∈ Gal(L/K)`.
-/
theorem norm_ofAlgebraAutOnUnits_eq (x : Lˣ) :
    (toMul <| toAdditive ((Rep.ofAlgebraAutOnUnits K L).norm.hom
      (toAdditive.symm <| ofMul x))).1 = algebraMap K L (Algebra.norm K (x : L)) := by
  simp [Algebra.norm_eq_prod_automorphisms, Representation.norm]

variable [IsCyclic (L ≃ₐ[K] L)] {g : Gal(L/K)}

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] IsCyclic.commGroup in
/-- Hilbert's Theorem 90: given a finite cyclic Galois extension `L/K`, an element `x : L` such
that `N_{L/K}(x) = 1`, and a generator `g` of `Gal(L/K)`, there exists `y : Lˣ`
such that `y/g y = x`. -/
/-
**groupCohomology.exists_div_of_norm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `groupCoho
mology`。
形式化陈述：exists_div_of_norm_eq_one (hg : forall x, x in Subgroup.zpowers g) {x : L}
 (hx : Algebra.norm K x = 1) : exists y : Lˣ, y / g y = x
参数：hg : forall x, x in Subgroup.zpowers g；hx : Algebra.norm K x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.norm_ne_zero_iff`：norm_ne_zero_iff [IsDomain R] [IsDomain S] [Mo
dule.Free R S] [Module.Finite R S] {x : S} : norm R x != 0 ↔ x != 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rep.toAdditive_symm_apply`：∀ {M : Type u_1} {G : Type u_2} [inst : Monoi
d M] [inst_1 : CommGroup G] [inst_2 : MulDistribMulAction M G]   (a : ↑(Rep.ofMu
lDistribMulActi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rep.toAdditive_apply`：∀ {M : Type u_1} {G : Type u_2} [inst : Monoid M] 
[inst_1 : CommGroup G] [inst_2 : MulDistribMulAction M G]   (a : ↑(Rep.ofMulDist
ribMulActi…
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
· 使用定理 `groupCohomology.norm_ofAlgebraAutOnUnits_eq`：norm_ofAlgebraAutOnUnits_eq
 (x : Lˣ) : (toMul <| toAdditive ((Rep.ofAlgebraAutOnUnits K L).norm.hom (toAddi
tive.symm <| ofMul x))).1 = algeb…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff`：groupCohomologyπO
dd_eq_zero_iff (i : Nat) (hi : Odd i) (x : LinearMap.ker A.norm.hom.toLinearMap)
 : groupCohomologyπOdd A g hg i hi x = 0 ↔ …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 67 条，此处仅展示前 30 条）

--- 原说明 ---
Hilbert's Theorem 90: given a finite cyclic Galois extension `L/K`, an element `
x : L` such
that `N_{L/K}(x) = 1`, and a generator `g` of `Gal(L/K)`, there exists `y : Lˣ`
such that `y/g y = x`.
-/
theorem exists_div_of_norm_eq_one (hg : ∀ x, x ∈ Subgroup.zpowers g) {x : L}
    (hx : Algebra.norm K x = 1) : ∃ y : Lˣ, y / g y = x := by
  suffices H : ∀ x, Algebra.norm K x = 1 → ∃ y : Lˣ, g y / y = x by
    have hxinv : Algebra.norm K x⁻¹ = 1 := by simp [Algebra.norm_inv, hx]
    obtain ⟨y, hy⟩ := H _ hxinv
    use y
    rw [IsUnit.div_eq_iff y.isUnit] at hy
    rw [hy]
    field_simp
  intro x hx
  let xu : Lˣ := (Algebra.norm_ne_zero_iff.1 <| hx ▸ zero_ne_one.symm).isUnit.unit
  have hx' : algebraMap K L (Algebra.norm K (xu : L)) = _ := congrArg (algebraMap K L) hx
  rw [← norm_ofAlgebraAutOnUnits_eq xu, map_one] at hx'
  have := FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff (ofAlgebraAutOnUnits K L) g hg
    1 (by simp) ⟨toAdditive.symm <| ofMul xu, by simp_all⟩
  rcases this.1 (Subsingleton.elim (α := groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)) _ _)
    with ⟨y, hy⟩
  use toMul <| toAdditive y
  have := Units.ext_iff.1 congr(toMul <| toAdditive $hy)
  simp only [sub_hom, hom_id,
    Representation.IntertwiningMap.sub_toLinearMap, Representation.IntertwiningMap.toLinearMap_id,
    LinearMap.sub_apply, Representation.IntertwiningMap.coe_toLinearMap, applyAsHom_apply,
    LinearMap.id_coe, id_eq,
    toAdditive_symm_apply, toAdditive_apply, toMul_ofMul, IsUnit.unit_spec, xu] at this
  rw [← this, toMul_sub]
  simp

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
variable [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K] [IsDomain A]
variable [IsIntegralClosure B A L]

open scoped nonZeroDivisors

/-- The integral version of the classical formulation of Hilbert's theorem 90: in the `ABKL`
setting, suppose that `L/K` is a finite Galois extension such that the Galois group is cyclic
generated by `g` and let `η : B` be an element of norm `1` (when viewed as an element of `L`).
Then there exists `ε : B` such that `ε ≠ 0` and `η * g ε = ε`. -/
/-
**groupCohomology.exists_mul_galRestrict_of_norm_eq_one** 是 Mathlib 中的一个引理，位于命名空
间 `groupCohomology`。
形式化陈述：exists_mul_galRestrict_of_norm_eq_one (hg : forall x, x in Subgroup.zpower
s g) {η : B} (hη : Algebra.norm K (algebraMap B L η) = 1) : exists ε : B, ε != 0
 ∧ η * galRestrict A K L B g ε = ε
参数：hg : forall x, x in Subgroup.zpowers g；hη : Algebra.norm K (algebraMap B L η)
 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.isTorsionFree_iff_algebraMap_injective`：isTorsionFree_iff_algebra
Map_injective : IsTorsionFree R A ↔ Injective (algebraMap R A)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.norm_zero`：norm_zero [Nontrivial S] [Module.Free R S] [Module.Fi
nite R S] : norm R (0 : S) = 0
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `groupCohomology.exists_div_of_norm_eq_one`：exists_div_of_norm_eq_one (hg
 : forall x, x in Subgroup.zpowers g) {x : L} (hx : Algebra.norm K x = 1) : exis
ts y : Lˣ, y / g y = x
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `IsLocalization.mk'_spec'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLocalization.mk'_zero`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
The integral version of the classical formulation of Hilbert's theorem 90: in th
e `ABKL`
setting, suppose that `L/K` is a finite Galois extension such that the Galois gr
oup is cyclic
generated by `g` and let `η : B` be an element of norm `1` (when viewed as an el
ement of `L`).
Then there exists `ε : B` such that `ε ≠ 0` and `η * g ε = ε`.
-/
lemma exists_mul_galRestrict_of_norm_eq_one (hg : ∀ x, x ∈ Subgroup.zpowers g) {η : B}
    (hη : Algebra.norm K (algebraMap B L η) = 1) :
    ∃ ε : B, ε ≠ 0 ∧ η * galRestrict A K L B g ε = ε := by
  have : Module.IsTorsionFree A L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  let η' : Lˣ := Units.mk0 (algebraMap B L η) (fun h ↦ by simp [h] at hη)
  obtain ⟨ε, hε⟩ := exists_div_of_norm_eq_one hg hη
  obtain ⟨a, b, h⟩ := IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid B A⁰) ε.1
  obtain ⟨t, ht, ht'⟩ := b.prop
  have : t • IsLocalization.mk' L a b = algebraMap _ _ a := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B L, ht', IsLocalization.mk'_spec']
  refine ⟨a, ?_, ?_⟩
  · rintro rfl
    simp only [IsLocalization.mk'_zero, _root_.map_zero, div_zero, ← h] at hε
    rw [← hε, Algebra.norm_zero] at hη
    exact zero_ne_one hη
  · replace hε := hε.symm
    rw [← h, eq_div_iff_mul_eq] at hε
    · replace hε := congr_arg (t • ·) hε
      rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def t, ← g.toAlgHom_apply,
        ← AlgHom.map_smul_of_tower, this] at hε
      apply IsIntegralClosure.algebraMap_injective B A L
      rw [map_mul, ← hε]
      congr 1
      exact algebraMap_galRestrictHom_apply A K L B g a
    · intro e
      rw [(map_eq_zero _).mp e, zero_div] at hε
      rw [hε, Algebra.norm_zero] at hη
      exact zero_ne_one hη

end groupCohomology

