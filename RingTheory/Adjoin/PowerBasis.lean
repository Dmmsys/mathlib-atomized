/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Power basis for `R[x]`

This file defines the canonical power basis on `R[x]`,
where `x` is an integral element over `R`.
-/

@[expose] public section

open Module Polynomial PowerBasis

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

namespace Algebra

/-- The elements `1, x, ..., x ^ (d - 1)` for a basis for the `K`-module `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
/-
**Algebra.adjoin.powerBasisAux** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.adjoin`。
形式化陈述：{K : Type u_1} →   {S : Type u_2} →     [inst : Field K] →       [inst_1 :
 CommRing S] →         [inst_2 : Algebra K S] → {x : S} → IsIntegral K x → Modul
e.Basis (Fin (minpoly K x).natDegree) K ↥K[x]
参数：Fin (minpoly K x).natDegree。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The elements `1, x, ..., x ^ (d - 1)` for a basis for the `K`-module `K[x]`,
where `d` is the degree of the minimal polynomial of `x`.
-/
noncomputable def adjoin.powerBasisAux {x : S} (hx : IsIntegral K x) :
    Basis (Fin (minpoly K x).natDegree) K (K[(x : S)]) := by
  have hST : Function.Injective (algebraMap (K[(x : S)]) S) := Subtype.coe_injective
  have hx' :
    IsIntegral K (⟨x, subset_adjoin (Set.mem_singleton x)⟩ : K[(x : S)]) := by
    apply (isIntegral_algebraMap_iff hST).mp
    convert! hx
  apply Basis.mk (v := fun i : Fin _ ↦ ⟨x, subset_adjoin (Set.mem_singleton x)⟩ ^ (i : ℕ))
  · have : LinearIndependent K _ := linearIndependent_pow
      (⟨x, self_mem_adjoin_singleton _ _⟩ : K[x])
    rwa [← minpoly.algebraMap_eq hST] at this
  · rintro ⟨y, hy⟩ _
    have := hx'.mem_span_pow (y := ⟨y, hy⟩)
    rw [← minpoly.algebraMap_eq hST] at this
    apply this
    rw [adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨f, rfl⟩ := (aeval x).mem_range.mp hy
    use f
    ext
    exact aeval_algebraMap_apply S (⟨x, _⟩ : K[x]) _

set_option backward.isDefEq.respectTransparency.types false in
/-- The power basis `1, x, ..., x ^ (d - 1)` for `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. See `Algebra.adjoin.powerBasis'` for
a version over a more general base ring. -/
@[simps gen dim]
/-
**Algebra.adjoin.powerBasis** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.adjoin`。
形式化陈述：{K : Type u_1} →   {S : Type u_2} →     [inst : Field K] → [inst_1 : CommR
ing S] → [inst_2 : Algebra K S] → {x : S} → IsIntegral K x → PowerBasis K ↥K[x]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power basis `1, x, ..., x ^ (d - 1)` for `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. See `Algebra.adjoin.po
werBasis'` for
a version over a more general base ring.
-/
noncomputable def adjoin.powerBasis {x : S} (hx : IsIntegral K x) :
    PowerBasis K K[(x : S)] where
  gen := ⟨x, subset_adjoin (Set.mem_singleton x)⟩
  dim := (minpoly K x).natDegree
  basis := adjoin.powerBasisAux hx
  basis_eq_pow i := by rw [adjoin.powerBasisAux, Basis.mk_apply]

/--
If `x` generates `S` over `K` and is integral over `K`, then it defines a power basis.
See `PowerBasis.ofAdjoinEqTop'` for a version over a more general base ring.
-/
/-
**Algebra._root_.PowerBasis.ofAdjoinEqTop** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x` generates `S` over `K` and is integral over `K`, then it defines a power 
basis.
See `PowerBasis.ofAdjoinEqTop'` for a version over a more general base ring.
-/
noncomputable def _root_.PowerBasis.ofAdjoinEqTop {x : S} (hx : IsIntegral K x)
    (hx' : K[x] = ⊤) : PowerBasis K S :=
  (adjoin.powerBasis hx).map ((Subalgebra.equivOfEq _ _ hx').trans Subalgebra.topEquiv)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Algebra._root_.PowerBasis.ofAdjoinEqTop_gen** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.PowerBasis.ofAdjoinEqTop_gen {x : S} (hx : IsIntegral K x)
    (hx' : K[x] = ⊤) : (PowerBasis.ofAdjoinEqTop hx hx').gen = x := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Algebra._root_.PowerBasis.ofAdjoinEqTop_dim** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.PowerBasis.ofAdjoinEqTop_dim {x : S} (hx : IsIntegral K x)
    (hx' : K[x] = ⊤) :
    (PowerBasis.ofAdjoinEqTop hx hx').dim = (minpoly K x).natDegree := rfl

end Algebra

open Algebra

section IsIntegral

namespace PowerBasis

open Polynomial

variable {R : Type*} [CommRing R] [Algebra R S] [Algebra R K] [IsScalarTower R K S]
variable {A : Type*} [CommRing A] [Algebra R A] [Algebra S A]
variable [IsScalarTower R S A] {B : PowerBasis S A}

/-- If `B : PowerBasis S A` is such that `IsIntegral R B.gen`, then
`IsIntegral R (B.basis.repr (B.gen ^ n) i)` for all `i` if
`minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)`. This is the case if `R` is a GCD domain
and `S` is its fraction ring. -/
/-
**PowerBasis.repr_gen_pow_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `PowerBasis`。
形式化陈述：repr_gen_pow_isIntegral (hB : IsIntegral R B.gen) (hmin : minpoly S B.gen 
= (minpoly R B.gen).map (algebraMap R S)) (n : Nat) : forall i, IsIntegral R (B.
basis.repr (B.gen ^ n) i)
参数：hB : IsIntegral R B.gen；hmin : minpoly S B.gen = (minpoly R B.gen).map (algeb
raMap R S)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_X_pow`：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n)
 = x ^ n
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `minpoly.aeval_modByMonic_minpoly`：aeval_modByMonic_minpoly (p : A[X]) (x
 : B) : (p %ₘ minpoly A x).aeval x = p.aeval x
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
If `B : PowerBasis S A` is such that `IsIntegral R B.gen`, then
`IsIntegral R (B.basis.repr (B.gen ^ n) i)` for all `i` if
`minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)`. This is the case if 
`R` is a GCD domain
and `S` is its fraction ring.
-/
theorem repr_gen_pow_isIntegral (hB : IsIntegral R B.gen)
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) (n : ℕ) :
    ∀ i, IsIntegral R (B.basis.repr (B.gen ^ n) i) := by
  intro i
  nontriviality S
  let Q := X ^ n %ₘ minpoly R B.gen
  have : B.gen ^ n = aeval B.gen Q := by
    rw [← @aeval_X_pow R _ _ _ _ B.gen, ← modByMonic_add_div (X ^ n) (minpoly R B.gen)]
    simp [Q]
  by_cases hQ : Q = 0
  · simp [this, hQ, isIntegral_zero]
  have hlt : Q.natDegree < B.dim := by
    rw [← B.natDegree_minpoly, hmin, (minpoly.monic hB).natDegree_map,
      natDegree_lt_natDegree_iff hQ]
    let : Nontrivial R := Nontrivial.of_polynomial_ne hQ
    exact degree_modByMonic_lt _ (minpoly.monic hB)
  rw [this, aeval_eq_sum_range' hlt]
  simp only [map_sum, Finset.sum_apply']
  refine IsIntegral.sum _ fun j hj => ?_
  replace hj := Finset.mem_range.1 hj
  rw [← Fin.val_mk hj, ← B.basis_eq_pow, Algebra.smul_def, IsScalarTower.algebraMap_apply R S A, ←
    Algebra.smul_def, map_smul]
  simp only [algebraMap_smul, Finsupp.coe_smul, Pi.smul_apply, B.basis.repr_self_apply]
  by_cases hij : (⟨j, hj⟩ : Fin _) = i
  · simp only [hij, if_true]
    rw [Algebra.smul_def, mul_one]
    exact isIntegral_algebraMap
  · simp [hij, isIntegral_zero]

/-- Let `B : PowerBasis S A` be such that `IsIntegral R B.gen`, and let `x y : A` be elements with
integral coordinates in the base `B.basis`. Then `IsIntegral R ((B.basis.repr (x * y) i)` for all
`i` if `minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)`. This is the case if `R` is a GCD
domain and `S` is its fraction ring. -/
/-
**PowerBasis.repr_mul_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `PowerBasis`。
形式化陈述：repr_mul_isIntegral (hB : IsIntegral R B.gen) {x y : A} (hx : forall i, Is
Integral R (B.basis.repr x i)) (hy : forall i, IsIntegral R (B.basis.repr y i)) 
(hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) : forall i, Is
Integral R (B.basis.repr (x * y) i)
参数：hB : IsIntegral R B.gen；hx : forall i, IsIntegral R (B.basis.repr x i)；hy : f
orall i, IsIntegral R (B.basis.repr y i)；hmin : minpoly S B.gen = (minpoly R B.g
en).map (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用引理 `Finset.sum_mul_sum`：sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι -> 
R) (g : κ -> R) : (∑ i in s, f i) * ∑ j in t, g j = ∑ i in s, ∑ j in t, f i * g 
j
· 使用定理 `Finset.sum_product'`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [ins
t : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ → α → β),   ∑ x ∈ s ×ˢ
 t, f x.1…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
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
· 使用定理 `Finset.sum_apply'`：Finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k
 i
· 使用定理 `IsIntegral.sum`：IsIntegral.sum {α : Type*} {s : Finset α} (f : α -> A) (
h : forall x in s, IsIntegral R (f x)) : IsIntegral R (∑ x in s, f x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerBasis.coe_basis`：coe_basis (pb : PowerBasis R S) : ⇑pb.basis = fun 
i : Fin pb.dim => pb.gen ^ (i : Nat)
· 使用定理 `PowerBasis.repr_gen_pow_isIntegral`：repr_gen_pow_isIntegral (hB : IsInte
gral R B.gen) (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) 
(n : Nat) : forall i, Is…

--- 原说明 ---
Let `B : PowerBasis S A` be such that `IsIntegral R B.gen`, and let `x y : A` be
 elements with
integral coordinates in the base `B.basis`. Then `IsIntegral R ((B.basis.repr (x
 * y) i)` for all
`i` if `minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)`. This is the c
ase if `R` is a GCD
domain and `S` is its fraction ring.
-/
theorem repr_mul_isIntegral (hB : IsIntegral R B.gen) {x y : A}
    (hx : ∀ i, IsIntegral R (B.basis.repr x i)) (hy : ∀ i, IsIntegral R (B.basis.repr y i))
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) :
    ∀ i, IsIntegral R (B.basis.repr (x * y) i) := by
  intro i
  rw [← B.basis.sum_repr x, ← B.basis.sum_repr y, Finset.sum_mul_sum, ← Finset.sum_product',
    map_sum, Finset.sum_apply']
  refine IsIntegral.sum _ fun I _ => ?_
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, map_smulₛₗ, RingHom.id_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  refine (hy _).mul ((hx _).mul ?_)
  simp only [coe_basis, ← pow_add]
  exact repr_gen_pow_isIntegral hB hmin _ _

/-- Let `B : PowerBasis S A` be such that `IsIntegral R B.gen`, and let `x : A` be an element
with integral coordinates in the base `B.basis`. Then `IsIntegral R ((B.basis.repr (x ^ n) i)` for
all `i` and all `n` if `minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)`. This is the case
if `R` is a GCD domain and `S` is its fraction ring. -/
/-
**PowerBasis.repr_pow_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `PowerBasis`。
形式化陈述：repr_pow_isIntegral (hB : IsIntegral R B.gen) {x : A} (hx : forall i, IsIn
tegral R (B.basis.repr x i)) (hmin : minpoly S B.gen = (minpoly R B.gen).map (al
gebraMap R S)) (n : Nat) : forall i, IsIntegral R (B.basis.repr (x ^ n) i)
参数：hB : IsIntegral R B.gen；hx : forall i, IsIntegral R (B.basis.repr x i)；hmin :
 minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
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
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.case_strong_induction_on`：∀ {p : ℕ → Prop} (a : ℕ), p 0 → (∀ (n : ℕ)
, (∀ m ≤ n, p m) → p (n + 1)) → p a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerBasis.dim_pos`：dim_pos [Nontrivial S] (pb : PowerBasis R S) : 0 < p
b.dim
· 使用定理 `Fin.val_mk`：∀ {m n : ℕ} (h : m < n), ↑⟨m, h⟩ = m
· 使用定理 `PowerBasis.basis_eq_pow`：∀ {R : Type u_7} {S : Type u_8} [inst : CommRin
g R] [inst_1 : Ring S] [inst_2 : Algebra R S] (self : PowerBasis R S)   (i : Fin
 self.dim), s…
· 使用定理 `Module.Basis.repr_self_apply`：repr_self_apply (j) [Decidable (i = j)] : 
b.repr (b i) j = if i = j then 1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `isIntegral_one`：isIntegral_one [Algebra R B] : IsIntegral R (1 : B)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `isIntegral_zero`：isIntegral_zero [Algebra R B] : IsIntegral R (0 : B)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `PowerBasis.repr_mul_isIntegral`：repr_mul_isIntegral (hB : IsIntegral R B
.gen) {x y : A} (hx : forall i, IsIntegral R (B.basis.repr x i)) (hy : forall i,
 IsIntegral R (B.bas…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
Let `B : PowerBasis S A` be such that `IsIntegral R B.gen`, and let `x : A` be a
n element
with integral coordinates in the base `B.basis`. Then `IsIntegral R ((B.basis.re
pr (x ^ n) i)` for
all `i` and all `n` if `minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)
`. This is the case
if `R` is a GCD domain and `S` is its fraction ring.
-/
theorem repr_pow_isIntegral (hB : IsIntegral R B.gen) {x : A}
    (hx : ∀ i, IsIntegral R (B.basis.repr x i))
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) (n : ℕ) :
    ∀ i, IsIntegral R (B.basis.repr (x ^ n) i) := by
  nontriviality A using Subsingleton.elim (x ^ n) 0, isIntegral_zero
  revert hx
  refine Nat.case_strong_induction_on
    -- Porting note: had to hint what to induct on
    (p := fun n ↦ _ → ∀ (i : Fin B.dim), IsIntegral R (B.basis.repr (x ^ n) i))
    n ?_ fun n hn => ?_
  · intro _ i
    rw [pow_zero, ← pow_zero B.gen, ← Fin.val_mk B.dim_pos, ← B.basis_eq_pow,
      B.basis.repr_self_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · intro hx
    rw [pow_succ]
    exact repr_mul_isIntegral hB (fun _ => hn _ le_rfl (fun _ => hx _) _) hx hmin

/-- Let `B B' : PowerBasis K S` be such that `IsIntegral R B.gen`, and let `P : R[X]` be such that
`aeval B.gen P = B'.gen`. Then `IsIntegral R (B.basis.to_matrix B'.basis i j)` for all `i` and `j`
if `minpoly K B.gen = (minpoly R B.gen).map (algebraMap R L)`. This is the case
if `R` is a GCD domain and `K` is its fraction ring. -/
/-
**PowerBasis.toMatrix_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `PowerBasis`。
形式化陈述：toMatrix_isIntegral {B B' : PowerBasis K S} {P : R[X]} (h : aeval B.gen P 
= B'.gen) (hB : IsIntegral R B.gen) (hmin : minpoly K B.gen = (minpoly R B.gen).
map (algebraMap R K)) : forall i j, IsIntegral R (B.basis.toMatrix B'.basis i j)
参数：h : aeval B.gen P = B'.gen；hB : IsIntegral R B.gen；hmin : minpoly K B.gen = (
minpoly R B.gen).map (algebraMap R K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.toMatrix_apply`：toMatrix_apply : e.toMatrix v i j = e.repr 
(v j) i
· 使用定理 `PowerBasis.coe_basis`：coe_basis (pb : PowerBasis R S) : ⇑pb.basis = fun 
i : Fin pb.dim => pb.gen ^ (i : Nat)
· 使用定理 `PowerBasis.repr_pow_isIntegral`：repr_pow_isIntegral (hB : IsIntegral R B
.gen) {x : A} (hx : forall i, IsIntegral R (B.basis.repr x i)) (hmin : minpoly S
 B.gen = (minpoly R …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_eq_sum_range`：aeval_eq_sum_range [Algebra R S] {p : R[X
]} (x : S) : aeval x p = ∑ i in Finset.range (p.natDegree + 1), p.coeff i • x ^ 
i
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
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
· 使用定理 `Finset.sum_apply'`：Finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k
 i
· 使用定理 `IsIntegral.sum`：IsIntegral.sum {α : Type*} {s : Finset α} (f : α -> A) (
h : forall x in s, IsIntegral R (f x)) : IsIntegral R (∑ x in s, f x)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsIntegral.smul`：IsIntegral.smul {R} [CommSemiring R] [Algebra R B] [Alg
ebra S B] [Algebra R S] [IsScalarTower R S B] {x : B} (r : R) (hx : IsIntegral S
 x) :…
· 使用定理 `PowerBasis.repr_gen_pow_isIntegral`：repr_gen_pow_isIntegral (hB : IsInte
gral R B.gen) (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) 
(n : Nat) : forall i, Is…

--- 原说明 ---
Let `B B' : PowerBasis K S` be such that `IsIntegral R B.gen`, and let `P : R[X]
` be such that
`aeval B.gen P = B'.gen`. Then `IsIntegral R (B.basis.to_matrix B'.basis i j)` f
or all `i` and `j`
if `minpoly K B.gen = (minpoly R B.gen).map (algebraMap R L)`. This is the case
if `R` is a GCD domain and `K` is its fraction ring.
-/
theorem toMatrix_isIntegral {B B' : PowerBasis K S} {P : R[X]} (h : aeval B.gen P = B'.gen)
    (hB : IsIntegral R B.gen) (hmin : minpoly K B.gen = (minpoly R B.gen).map (algebraMap R K)) :
    ∀ i j, IsIntegral R (B.basis.toMatrix B'.basis i j) := by
  intro i j
  rw [B.basis.toMatrix_apply, B'.coe_basis]
  refine repr_pow_isIntegral hB (fun i => ?_) hmin _ _
  rw [← h, aeval_eq_sum_range, map_sum, Finset.sum_apply']
  refine IsIntegral.sum _ fun n _ => ?_
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R K S, ← Algebra.smul_def, map_smul,
    algebraMap_smul]
  exact (repr_gen_pow_isIntegral hB hmin _ _).smul _

end PowerBasis

end IsIntegral

