/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Algebra.Polynomial

/-!
# The fundamental theorem of algebra

This file proves that every nonconstant complex polynomial has a root using Liouville's theorem.

As a consequence, the complex numbers are algebraically closed.

We also provide some specific results about the Galois groups of ℚ-polynomials with specific numbers
of non-real roots.

We also show that an irreducible real polynomial has degree at most two.
-/

public section

open Polynomial Bornology Complex

open scoped ComplexConjugate

namespace Complex

/-- **Fundamental theorem of algebra**: every nonconstant complex polynomial
  has a root. -/
/-
**Complex.exists_root** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：exists_root {f : Complex[X]} (hf : 0 < degree f) : exists z : Complex, IsR
oot f z
参数：hf : 0 < degree f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Differentiable.apply_eq_of_tendsto_cocompact`：apply_eq_of_tendsto_cocomp
act [Nontrivial E] {f : E -> F} (hf : Differentiable Complex f) {c : F} (x : E) 
(hb : Tendsto f (cocompact E) (𝓝 c…
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Differentiable.inv`：Differentiable.inv (hf : Differentiable 𝕜 h) (hz : f
orall x, h x != 0) : Differentiable 𝕜 (h⁻¹)
· 使用定理 `Polynomial.differentiable`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFiel
d 𝕜] (p : Polynomial 𝕜), Differentiable 𝕜 fun x => Polynomial.eval x p
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_inv₀_cobounded`：tendsto_inv₀_cobounded : Tendsto Inv.inv 
(cobounded α) (𝓝 0)
· 使用定理 `Polynomial.tendsto_norm_atTop`：tendsto_norm_atTop (p : R[X]) (h : 0 < de
gree p) {l : Filter α} {z : α -> R} (hz : Tendsto (fun x => ‖z x‖) l atTop) : Te
ndsto (fun x => ‖p.…
· 使用定理 `tendsto_norm_cobounded_atTop`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E], Filter.Tendsto norm (Bornology.cobounded E) Filter.atTop
· 使用定理 `Metric.cobounded_eq_cocompact`：Metric.cobounded_eq_cocompact [ProperSpac
e α] : cobounded α = cocompact α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.funext`：funext [Infinite R] {p q : R[X]} (ext : forall r : R,
 p.eval r = q.eval r) : p = q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `CharZero.infinite`：∀ (M : Type u_1) [inst : AddMonoidWithOne M] [CharZer
o M], Infinite M
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Fundamental theorem of algebra**: every nonconstant complex polynomial
  has a root.
-/
theorem exists_root {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, IsRoot f z := by
  by_contra! hf'
  /- Since `f` has no roots, `f⁻¹` is differentiable. And since `f` is a polynomial, it tends to
  infinity at infinity, thus `f⁻¹` tends to zero at infinity. By Liouville's theorem, `f⁻¹ = 0`. -/
  have (z : ℂ) : (f.eval z)⁻¹ = 0 :=
    (f.differentiable.inv hf').apply_eq_of_tendsto_cocompact z <|
      Metric.cobounded_eq_cocompact (α := ℂ) ▸ (Filter.tendsto_inv₀_cobounded.comp <| by
        simpa only [tendsto_norm_atTop_iff_cobounded]
          using f.tendsto_norm_atTop hf tendsto_norm_cobounded_atTop)
  -- Thus `f = 0`, contradicting the fact that `0 < degree f`.
  obtain rfl : f = C 0 := Polynomial.funext fun z ↦ inv_injective <| by simp [this]
  simp at hf

/-- **Fundamental theorem of algebra**: the field `ℂ` of complex numbers is algebraically closed. -/
@[wikidata Q192760]
/-
**Complex.isAlgClosed** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：isAlgClosed : IsAlgClosed Complex
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.of_exists_root`：of_exists_root (H : forall p : k[X], p.Monic
 -> Irreducible p -> exists x, p.eval x = 0) : IsAlgClosed k
· 使用定理 `Complex.exists_root`：exists_root {f : Complex[X]} (hf : 0 < degree f) : 
exists z : Complex, IsRoot f z
· 使用定理 `Polynomial.degree_pos_of_irreducible`：degree_pos_of_irreducible (hp : Ir
reducible p) : 0 < p.degree

--- 原说明 ---
**Fundamental theorem of algebra**: the field `ℂ` of complex numbers is algebrai
cally closed.
-/
instance isAlgClosed : IsAlgClosed ℂ :=
  IsAlgClosed.of_exists_root _ fun _p _ hp => Complex.exists_root <| degree_pos_of_irreducible hp

end Complex

/-- An algebraic extension of ℝ is isomorphic to either ℝ or ℂ as an ℝ-algebra. -/
/-
**Real.nonempty_algEquiv_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.nonempty_algEquiv_or (F : Type*) [Field F] [Algebra Real F] [Algebra.
IsAlgebraic Real F] : Nonempty (F ≃ₐ[Real] Real) ∨ Nonempty (F ≃ₐ[Real] Complex)
参数：F : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two`：nonempty_algEquiv_or
_of_finrank_eq_two {F F' : Type*} (E : Type*) [Field F] [Field F'] [Field E] [Al
gebra F F'] [Algebra F E] [Algebra.IsAlg…
· 使用定理 `Complex.finrank_real_complex`：finrank_real_complex : finrank Real Comple
x = 2

--- 原说明 ---
An algebraic extension of ℝ is isomorphic to either ℝ or ℂ as an ℝ-algebra.
-/
theorem Real.nonempty_algEquiv_or (F : Type*) [Field F] [Algebra ℝ F] [Algebra.IsAlgebraic ℝ F] :
    Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) :=
  IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two F Complex.finrank_real_complex

namespace Polynomial.Gal

section Rationals

/-
**Polynomial.Gal.splits_** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Gal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem splits_ℚ_ℂ {p : ℚ[X]} : Fact ((p.map (algebraMap ℚ ℂ)).Splits) :=
  ⟨IsAlgClosed.splits _⟩

attribute [local instance] splits_ℚ_ℂ
attribute [local ext] Complex.ext

/-- The number of complex roots equals the number of real roots plus
the number of roots not fixed by complex conjugation (i.e. with some imaginary component). -/
/-
**Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv** 是 Mathli
b 中的一个定理，位于命名空间 `Polynomial.Gal`。
形式化陈述：card_complex_roots_eq_card_real_add_card_not_gal_inv (p : Rat[X]) : (p.roo
tSet Complex).toFinset.card = (p.rootSet Real).toFinset.card + (galActionHom p C
omplex (restrict p Complex (AlgEquiv.restrictScalars Rat Complex.conjAe))).suppo
rt.card
参数：p : Rat[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Polynomial.Gal.splits_ℚ_ℂ`：∀ {p : Polynomial ℚ}, Fact (Polynomial.map (a
lgebraMap ℚ ℂ) p).Splits
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootSet_zero`：rootSet_zero (S) [CommRing S] [IsDomain S] [Alg
ebra T S] : (0 : T[X]).rootSet S = ∅
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `Finset.eq_empty_of_isEmpty`：eq_empty_of_isEmpty [IsEmpty α] (s : Finset 
α) : s = ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.toFinset_empty`：toFinset_empty [Fintype (∅ : Set α)] : (∅ : Set α).t
oFinset = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用引理 `Polynomial.mem_rootSet_of_ne`：mem_rootSet_of_ne {p : T[X]} {S : Type*} [
IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] (
hp : p != 0) {a : …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The number of complex roots equals the number of real roots plus
the number of roots not fixed by complex conjugation (i.e. with some imaginary c
omponent).
-/
theorem card_complex_roots_eq_card_real_add_card_not_gal_inv (p : ℚ[X]) :
    (p.rootSet ℂ).toFinset.card =
      (p.rootSet ℝ).toFinset.card +
        (galActionHom p ℂ (restrict p ℂ
        (AlgEquiv.restrictScalars ℚ Complex.conjAe))).support.card := by
  by_cases hp : p = 0
  · have : IsEmpty (p.rootSet ℂ) := by rw [hp, rootSet_zero]; infer_instance
    simp_rw [(galActionHom p ℂ _).support.eq_empty_of_isEmpty, hp, rootSet_zero,
      Set.toFinset_empty, Finset.card_empty]
  have inj : Function.Injective (IsScalarTower.toAlgHom ℚ ℝ ℂ) := (algebraMap ℝ ℂ).injective
  rw [← Finset.card_image_of_injective _ Subtype.coe_injective, ←
    Finset.card_image_of_injective _ inj]
  let a : Finset ℂ := ?_
  on_goal 1 => let b : Finset ℂ := ?_
  on_goal 1 => let c : Finset ℂ := ?_
  change a.card = b.card + c.card
  have ha : ∀ z : ℂ, z ∈ a ↔ aeval z p = 0 := by
    intro z; rw [Set.mem_toFinset, mem_rootSet_of_ne hp]
  have hb : ∀ z : ℂ, z ∈ b ↔ aeval z p = 0 ∧ z.im = 0 := by
    intro z
    simp_rw [b, Finset.mem_image, Set.mem_toFinset, mem_rootSet_of_ne hp]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨by rw [aeval_algHom_apply, hw, map_zero], rfl⟩
    · rintro ⟨hz1, hz2⟩
      have key : IsScalarTower.toAlgHom ℚ ℝ ℂ z.re = z := by
        ext
        · rfl
        · rw [hz2]; rfl
      exact ⟨z.re, inj (by rwa [← aeval_algHom_apply, key, map_zero]), key⟩
  have hc0 :
    ∀ w : p.rootSet ℂ, galActionHom p ℂ (restrict p ℂ (Complex.conjAe.restrictScalars ℚ)) w = w ↔
        w.val.im = 0 := by
    intro w
    rw [Subtype.ext_iff, galActionHom_restrict]
    exact Complex.conj_eq_iff_im
  have hc : ∀ z : ℂ, z ∈ c ↔ aeval z p = 0 ∧ z.im ≠ 0 := by
    intro z
    simp_rw [c, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(mem_rootSet.mp w.2).2, mt (hc0 w).mpr (Equiv.Perm.mem_support.mp hw)⟩
    · rintro ⟨hz1, hz2⟩
      exact ⟨⟨z, mem_rootSet.mpr ⟨hp, hz1⟩⟩, Equiv.Perm.mem_support.mpr (mt (hc0 _).mp hz2), rfl⟩
  rw [← Finset.card_union_of_disjoint]
  · apply congr_arg Finset.card
    simp_rw [Finset.ext_iff, Finset.mem_union, ha, hb, hc]
    tauto
  · rw [Finset.disjoint_left]
    intro z
    rw [hb, hc]
    tauto

/-- An irreducible polynomial of prime degree with two non-real roots has full Galois group. -/
/-
**Polynomial.Gal.galActionHom_bijective_of_prime_degree** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial.Gal`。
形式化陈述：galActionHom_bijective_of_prime_degree {p : Rat[X]} (p_irr : Irreducible p
) (p_deg : p.natDegree.Prime) (p_roots : Fintype.card (p.rootSet Complex) = Fint
ype.card (p.rootSet Real) + 2) : Function.Bijective (galActionHom p Complex)
参数：p_irr : Irreducible p；p_deg : p.natDegree.Prime；p_roots : Fintype.card (p.roo
tSet Complex) = Fintype.card (p.rootSet Real) + 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Polynomial.rootSet_def`：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomai
n S] [Algebra T S] [DecidableEq S] : p.rootSet S = (p.aroots S).toFinset
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Multiset.toFinset_card_of_nodup`：Multiset.toFinset_card_of_nodup {m : Mu
ltiset α} (h : m.Nodup) : #m.toFinset = Multiset.card m
· 使用定理 `Polynomial.nodup_roots`：nodup_roots {p : R[X]} (hsep : Separable p) : p.
roots.Nodup
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.separable_map`：separable_map {S} [CommRing S] [Nontrivial S] 
(f : F ->+* S) {p : F[X]} : (p.map f).Separable ↔ p.Separable
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Irreducible.separable`：∀ {F : Type u} [inst : Field F] [CharZero F] {f :
 Polynomial F}, Irreducible f → f.Separable
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Splits.natDegree_eq_card_roots`：∀ {R : Type u_1} [inst : Comm
Ring R] {f : Polynomial R} [inst_1 : IsDomain R], f.Splits → f.natDegree = f.roo
ts.card
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Polynomial.Gal.splits_ℚ_ℂ`：∀ {p : Polynomial ℚ}, Fact (Polynomial.map (a
lgebraMap ℚ ℂ) p).Splits
· 使用定理 `Polynomial.Gal.galActionHom_injective`：galActionHom_injective [Fact ((p.
map (algebraMap F E)).Splits)] : Function.Injective (galActionHom p E)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.Perm.subgroup_eq_top_of_swap_mem`：subgroup_eq_top_of_swap_mem [Dec
idableEq α] {H : Subgroup (Perm α)} [d : DecidablePred (· in H)] {τ : Perm α} (h
0 : (Fintype.card α).Prime) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Polynomial.Gal.prime_degree_dvd_card`：prime_degree_dvd_card [CharZero F]
 (p_irr : Irreducible p) (p_deg : p.natDegree.Prime) : p.natDegree ∣ Nat.card p.
Gal
· 使用定理 `Equiv.Perm.card_support_eq_two`：card_support_eq_two {f : Perm α} : #f.su
pport = 2 ↔ IsSwap f
· 使用定理 `Nat.add_left_cancel`：∀ {n m k : ℕ}, n + m = n + k → m = k
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
An irreducible polynomial of prime degree with two non-real roots has full Galoi
s group.
-/
theorem galActionHom_bijective_of_prime_degree {p : ℚ[X]} (p_irr : Irreducible p)
    (p_deg : p.natDegree.Prime)
    (p_roots : Fintype.card (p.rootSet ℂ) = Fintype.card (p.rootSet ℝ) + 2) :
    Function.Bijective (galActionHom p ℂ) := by
  have h1 : Fintype.card (p.rootSet ℂ) = p.natDegree := by
    simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
    rw [Multiset.toFinset_card_of_nodup, ← Splits.natDegree_eq_card_roots, natDegree_map]
    · exact IsAlgClosed.splits _
    · exact nodup_roots ((separable_map (algebraMap ℚ ℂ)).mpr p_irr.separable)
  let conj' := restrict p ℂ (Complex.conjAe.restrictScalars ℚ)
  refine
    ⟨galActionHom_injective p ℂ, fun x =>
      (congr_arg (x ∈ ·) (show (galActionHom p ℂ).range = ⊤ from ?_)).mpr
        (Subgroup.mem_top x)⟩
  apply Equiv.Perm.subgroup_eq_top_of_swap_mem
  · rwa [h1]
  · rw [h1]
    simpa only [Fintype.card_eq_nat_card,
      Nat.card_congr (MonoidHom.ofInjective (galActionHom_injective p ℂ)).toEquiv.symm]
      using prime_degree_dvd_card p_irr p_deg
  · exact ⟨conj', rfl⟩
  · rw [← Equiv.Perm.card_support_eq_two]
    apply Nat.add_left_cancel
    rw [← p_roots, ← Set.toFinset_card (rootSet p ℝ), ← Set.toFinset_card (rootSet p ℂ)]
    exact (card_complex_roots_eq_card_real_add_card_not_gal_inv p).symm

/-- An irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group. -/
/-
**Polynomial.Gal.galActionHom_bijective_of_prime_degree'** 是 Mathlib 中的一个定理，位于命名
空间 `Polynomial.Gal`。
形式化陈述：galActionHom_bijective_of_prime_degree' {p : Rat[X]} (p_irr : Irreducible 
p) (p_deg : p.natDegree.Prime) (p_roots1 : Fintype.card (p.rootSet Real) + 1 <= 
Fintype.card (p.rootSet Complex)) (p_roots2 : Fintype.card (p.rootSet Complex) <
= Fintype.card (p.rootSet Real) + 3) : Function.Bijective (galActionHom p Comple
x)
参数：p_irr : Irreducible p；p_deg : p.natDegree.Prime；p_roots1 : Fintype.card (p.ro
otSet Real) + 1 <= Fintype.card (p.rootSet Complex)；p_roots2 : Fintype.card (p.r
ootSet Complex) <= Fintype.card (p.rootSet Real) + 3。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.Gal.galActionHom_bijective_of_prime_degree`：galActionHom_bije
ctive_of_prime_degree {p : Rat[X]} (p_irr : Irreducible p) (p_deg : p.natDegree.
Prime) (p_roots : Fintype.card (p.rootSet C…
· 使用定理 `Polynomial.Gal.splits_ℚ_ℂ`：∀ {p : Polynomial ℚ}, Fact (Polynomial.map (a
lgebraMap ℚ ℂ) p).Splits
· 使用定理 `Equiv.Perm.two_dvd_card_support`：two_dvd_card_support {σ : Perm α} (hσ :
 σ ^ 2 = 1) : 2 ∣ #σ.support
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Complex.conj_conj`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : Star
Ring R] (x : R), (starRingEnd R) ((starRingEnd R) x) = x
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv`：car
d_complex_roots_eq_card_real_add_card_not_gal_inv (p : Rat[X]) : (p.rootSet Comp
lex).toFinset.card = (p.rootSet Real).toFinset.card + (ga…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
An irreducible polynomial of prime degree with 1-3 non-real roots has full Galoi
s group.
-/
theorem galActionHom_bijective_of_prime_degree' {p : ℚ[X]} (p_irr : Irreducible p)
    (p_deg : p.natDegree.Prime)
    (p_roots1 : Fintype.card (p.rootSet ℝ) + 1 ≤ Fintype.card (p.rootSet ℂ))
    (p_roots2 : Fintype.card (p.rootSet ℂ) ≤ Fintype.card (p.rootSet ℝ) + 3) :
    Function.Bijective (galActionHom p ℂ) := by
  apply galActionHom_bijective_of_prime_degree p_irr p_deg
  let n := (galActionHom p ℂ (restrict p ℂ (Complex.conjAe.restrictScalars ℚ))).support.card
  have hn : 2 ∣ n :=
    Equiv.Perm.two_dvd_card_support
      (by
         rw [← map_pow, ← map_pow,
          show AlgEquiv.restrictScalars ℚ Complex.conjAe ^ 2 = 1 from
            AlgEquiv.ext Complex.conj_conj,
          map_one, map_one])
  have key := card_complex_roots_eq_card_real_add_card_not_gal_inv p
  simp_rw [Set.toFinset_card] at key
  lia

end Rationals

end Polynomial.Gal

/-
**Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero (p : Real[X]) {z : Com
plex} (h0 : aeval z p = 0) (hz : z.im != 0) : (X - C ((starRingEnd Complex) z)) 
* (X - C z) ∣ map (algebraMap Real Complex) p
参数：p : Real[X]；h0 : aeval z p = 0；hz : z.im != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.mul_dvd`：IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H
2 : y ∣ z) : x * y ∣ z
· 使用定理 `Polynomial.isCoprime_X_sub_C_of_isUnit_sub`：isCoprime_X_sub_C_of_isUnit_
sub {R} [CommRing R] {a b : R} (h : IsUnit (a - b)) : IsCoprime (X - C a) (X - C
 b)
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.conj_eq_iff_im`：conj_eq_iff_im {z : Complex} : conj z = z ↔ z.im
 = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用引理 `Polynomial.aeval_conj`：aeval_conj (p : Real[X]) (z : K) : aeval (conj z)
 p = conj (aeval z p)
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero (p : ℝ[X]) {z : ℂ} (h0 : aeval z p = 0)
    (hz : z.im ≠ 0) : (X - C ((starRingEnd ℂ) z)) * (X - C z) ∣ map (algebraMap ℝ ℂ) p := by
  apply IsCoprime.mul_dvd
  · exact isCoprime_X_sub_C_of_isUnit_sub <| .mk0 _ <| sub_ne_zero.2 <| mt conj_eq_iff_im.1 hz
  · simpa [dvd_iff_isRoot, aeval_conj]
  · simpa [dvd_iff_isRoot]

/-- If `z` is a non-real complex root of a real polynomial,
then `p` is divisible by a quadratic polynomial. -/
/-
**Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero (p : Real[X]) {z : Co
mplex} (h0 : aeval z p = 0) (hz : z.im != 0) : X ^ 2 - C (2 * z.re) * X + C (‖z‖
 ^ 2) ∣ p
参数：p : Real[X]；h0 : aeval z p = 0；hz : z.im != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_dvd_map'`：map_dvd_map' [Field k] (f : R ->+* k) {x y : R[
X]} : x.map f ∣ y.map f ↔ x ∣ y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.add_conj`：add_conj (z : Complex) : z + conj z = (2 * z.re : Real
)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Complex.mul_conj'`：∀ (z : ℂ), z * (starRingEnd ℂ) z = ↑‖z‖ ^ 2
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 68 条，此处仅展示前 30 条）

--- 原说明 ---
If `z` is a non-real complex root of a real polynomial,
then `p` is divisible by a quadratic polynomial.
-/
lemma Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero (p : ℝ[X]) {z : ℂ} (h0 : aeval z p = 0)
    (hz : z.im ≠ 0) : X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) ∣ p := by
  rw [← map_dvd_map' (algebraMap ℝ ℂ)]
  convert! p.mul_star_dvd_of_aeval_eq_zero_im_ne_zero h0 hz
  calc
    map (algebraMap ℝ ℂ) (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2))
    _ = X ^ 2 - C (↑(2 * z.re) : ℂ) * X + C (‖z‖ ^ 2 : ℂ) := by simp
    _ = (X - C (conj z)) * (X - C z) := by
      rw [← add_conj, map_add, ← mul_conj', map_mul]
      ring

/-- An irreducible real polynomial has natural degree at most two. -/
/-
**Irreducible.natDegree_le_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Irreducible.natDegree_le_two {p : Real[X]} (hp : Irreducible p) : natDegre
e p <= 2
参数：hp : Irreducible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.exists_aeval_eq_zero`：exists_aeval_eq_zero {R : Type*} [Comm
Semiring R] [IsAlgClosed k] [Algebra R k] [FaithfulSMul R k] (p : R[X]) (hp : p.
degree != 0) : exists …
· 使用定理 `instFaithfulSMul_1`：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] [IsSimpleRing R]   [Nontrivial A], 
Faithful…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Polynomial.degree_pos_of_irreducible`：degree_pos_of_irreducible (hp : Ir
reducible p) : 0 < p.degree
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.finrank_real_complex`：finrank_real_complex : finrank Real Comple
x = 2
· 使用定理 `minpoly.eq_of_irreducible`：eq_of_irreducible [Nontrivial B] {p : A[X]} (
hp1 : Irreducible p) (hp2 : Polynomial.aeval x p = 0) : p * C p.leadingCoeff⁻¹ =
 minpoly A x
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `minpoly.natDegree_le`：natDegree_le [Module.Free A B] : (minpoly A x).nat
Degree <= Module.finrank A B
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
An irreducible real polynomial has natural degree at most two.
-/
lemma Irreducible.natDegree_le_two {p : ℝ[X]} (hp : Irreducible p) : natDegree p ≤ 2 := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, aeval z p = 0 :=
    IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne'
  rw [← finrank_real_complex]
  suffices p.natDegree = (minpoly ℝ z).natDegree from this ▸ minpoly.natDegree_le (A := ℝ) z
  rw [← minpoly.eq_of_irreducible hp hz, natDegree_mul hp.ne_zero (by simpa using hp.ne_zero),
    natDegree_C, add_zero]

/-- An irreducible real polynomial has degree at most two. -/
/-
**Irreducible.degree_le_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Irreducible.degree_le_two {p : Real[X]} (hp : Irreducible p) : degree p <=
 2
参数：hp : Irreducible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.natDegree_le_iff_degree_le`：natDegree_le_iff_degree_le {n : N
at} : natDegree p <= n ↔ degree p <= n
· 使用引理 `Irreducible.natDegree_le_two`：Irreducible.natDegree_le_two {p : Real[X]}
 (hp : Irreducible p) : natDegree p <= 2

--- 原说明 ---
An irreducible real polynomial has degree at most two.
-/
lemma Irreducible.degree_le_two {p : ℝ[X]} (hp : Irreducible p) : degree p ≤ 2 :=
  natDegree_le_iff_degree_le.1 hp.natDegree_le_two
