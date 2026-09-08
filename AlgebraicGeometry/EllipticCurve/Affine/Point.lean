/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.LinearAlgebra.FreeModule.Norm
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Nonsingular points and the group law in affine coordinates

Let `W` be a Weierstrass curve over a field `F` given by a Weierstrass equation `W(X, Y) = 0` in
affine coordinates. The type of nonsingular points in affine coordinates is an inductive, consisting
of the unique point at infinity `𝓞` and nonsingular affine points `(x, y)`. It can be endowed with a
group law, with `𝓞` as the identity nonsingular point, which is uniquely determined by the formulae
in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`.

With this description, there is an addition-preserving injection from the nonsingular points to the
ideal class group of the *affine coordinate ring* `F[W] := F[X, Y] / ⟨W(X, Y)⟩`. This is given by
mapping `𝓞` to the trivial ideal class and a nonsingular affine point `(x, y)` to the ideal class of
the invertible ideal `⟨X - x, Y - y⟩`. Proving that this is well-defined and preserves addition
reduces to equalities of ideals checked in `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul`
and in `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal` via explicit ideal computations.
Now `F[W]` is a free rank two `F[X]`-algebra with basis `{1, Y}`, so every element of `F[W]` is of
the form `p + qY` for some `p, q` in `F[X]`, and there is an algebra norm `N : F[W] → F[X]`.
Injectivity can then be shown by computing the degree of such a norm `N(p + qY)` in two different
ways, which is done in `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis` and in the
auxiliary lemmas in the proof of `WeierstrassCurve.Affine.Point.instAddCommGroup`.

This file defines the group law on nonsingular points in affine coordinates.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing`: the affine coordinate ring `F[W]`.
* `WeierstrassCurve.Affine.CoordinateRing.basis`: the power basis of `F[W]` over `F[X]`.
* `WeierstrassCurve.Affine.Point`: a nonsingular point in affine coordinates.
* `WeierstrassCurve.Affine.Point.neg`: the negation of a nonsingular point in affine coordinates.
* `WeierstrassCurve.Affine.Point.add`: the addition of a nonsingular point in affine coordinates.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.instIsDomainCoordinateRing`: the affine coordinate ring
  of a Weierstrass curve is an integral domain.
* `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis`: the degree of the norm of an
  element in the affine coordinate ring in terms of its power basis.
* `WeierstrassCurve.Affine.Point.instAddCommGroup`: the type of nonsingular points in affine
  coordinates forms an abelian group under addition.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]
* https://drops.dagstuhl.de/storage/00lipics/lipics-vol268-itp2023/LIPIcs.ITP.2023.6/LIPIcs.ITP.2023.6.pdf

## Tags

elliptic curve, affine, point, group law, class group
-/

@[expose] public section

open FractionalIdeal (coeIdeal_mul)

open Ideal hiding map_mul

open Module Polynomial

open scoped nonZeroDivisors Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

universe r s u v w

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} {L : Type w} [CommRing R]
  [CommRing S] [CommRing A] [CommRing B] [Field F] [Field K] [Field L] {W' : Affine R}
  {W : Affine F}

namespace Affine

/-! ## The affine coordinate ring -/

variable (W') in
/-- The affine coordinate ring `R[W] := R[X, Y] / ⟨W(X, Y)⟩` of a Weierstrass curve `W`. -/
/-
**WeierstrassCurve.Affine.CoordinateRing** 是 Mathlib 中的一个缩写定义，位于命名空间 `Weierstras
sCurve.Affine`。
形式化陈述：CoordinateRing : Type r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine coordinate ring `R[W] := R[X, Y] / ⟨W(X, Y)⟩` of a Weierstrass curve 
`W`.
-/
abbrev CoordinateRing : Type r :=
  AdjoinRoot W'.polynomial

variable (W') in
/-- The function field `R(W) := Frac(R[W])` of a Weierstrass curve `W`. -/
/-
**WeierstrassCurve.Affine.FunctionField** 是 Mathlib 中的一个缩写定义，位于命名空间 `Weierstrass
Curve.Affine`。
形式化陈述：FunctionField : Type r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function field `R(W) := Frac(R[W])` of a Weierstrass curve `W`.
-/
abbrev FunctionField : Type r :=
  FractionRing W'.CoordinateRing

namespace CoordinateRing

/-
**WeierstrassCurve.Affine.CoordinateRing.** 是 Mathlib 中的一个实例，位于命名空间 `Weierstrass
Curve.Affine.CoordinateRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Algebra R W'.CoordinateRing := inferInstance
/-
**WeierstrassCurve.Affine.CoordinateRing.** 是 Mathlib 中的一个实例，位于命名空间 `Weierstrass
Curve.Affine.CoordinateRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Algebra R[X] W'.CoordinateRing := inferInstance
/-
**WeierstrassCurve.Affine.CoordinateRing.** 是 Mathlib 中的一个实例，位于命名空间 `Weierstrass
Curve.Affine.CoordinateRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R R[X] W'.CoordinateRing := inferInstance
/-
**WeierstrassCurve.Affine.CoordinateRing.** 是 Mathlib 中的一个实例，位于命名空间 `Weierstrass
Curve.Affine.CoordinateRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton R] : Subsingleton W'.CoordinateRing :=
  Module.subsingleton R[X] _

variable (W') in
/-- The natural ring homomorphism mapping `R[X][Y]` to `R[W]`. -/
/-
**WeierstrassCurve.Affine.CoordinateRing.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Weierst
rassCurve.Affine.CoordinateRing`。
形式化陈述：mk : R[X][Y] ->+* W'.CoordinateRing
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural ring homomorphism mapping `R[X][Y]` to `R[W]`.
-/
noncomputable abbrev mk : R[X][Y] →+* W'.CoordinateRing :=
  AdjoinRoot.mk W'.polynomial

open scoped Classical in
variable (W') in
/-- The power basis `{1, Y}` for `R[W]` over `R[X]`. -/
/-
**WeierstrassCurve.Affine.CoordinateRing.basis** 是 Mathlib 中的一个定义，位于命名空间 `Weiers
trassCurve.Affine.CoordinateRing`。
形式化陈述：{R : Type r} →   [inst : CommRing R] → (W' : WeierstrassCurve.Affine R) → 
Module.Basis (Fin 2) (Polynomial R) W'.CoordinateRing
参数：W' : WeierstrassCurve.Affine R；Fin 2；Polynomial R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用引理 `WeierstrassCurve.Affine.monic_polynomial`：monic_polynomial : W.polynomia
l.Monic
· 使用引理 `WeierstrassCurve.Affine.natDegree_polynomial`：natDegree_polynomial [Nont
rivial R] : W.polynomial.natDegree = 2

--- 原说明 ---
The power basis `{1, Y}` for `R[W]` over `R[X]`.
-/
protected noncomputable def basis : Basis (Fin 2) R[X] W'.CoordinateRing :=
  (subsingleton_or_nontrivial R).by_cases (fun _ => default) fun _ =>
    (AdjoinRoot.powerBasis' monic_polynomial).basis.reindex <| finCongr natDegree_polynomial

set_option backward.isDefEq.respectTransparency.types false in
/-
**WeierstrassCurve.Affine.CoordinateRing.basis_apply** 是 Mathlib 中的一个引理，位于命名空间 `
WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：basis_apply (n : Fin 2) : CoordinateRing.basis W' n = (AdjoinRoot.powerBas
is' monic_polynomial).gen ^ (n : Nat)
参数：n : Fin 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用引理 `WeierstrassCurve.Affine.monic_polynomial`：monic_polynomial : W.polynomia
l.Monic
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AdjoinRoot.powerBasis'_gen`：∀ {R : Type u_1} [inst : CommRing R] {g : Po
lynomial R} (hg : g.Monic),   (AdjoinRoot.powerBasis' hg).gen = AdjoinRoot.root 
g
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.instSubsingleton`：∀ {R : Type r} 
[inst : CommRing R] {W' : WeierstrassCurve.Affine R} [Subsingleton R], Subsingle
ton W'.CoordinateRing
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用引理 `WeierstrassCurve.Affine.natDegree_polynomial`：natDegree_polynomial [Nont
rivial R] : W.polynomial.natDegree = 2
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.basis.eq_1`：∀ {R : Type r} [inst 
: CommRing R] (W' : WeierstrassCurve.Affine R),   WeierstrassCurve.Affine.Coordi
nateRing.basis W' =     ⋯.by_cases (fun…
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Or.by_cases.eq_1`：∀ {p q : Prop} [inst : Decidable p] {α : Sort u} (h : 
p ∨ q) (h₁ : p → α) (h₂ : q → α),   h.by_cases h₁ h₂ = if hp : p then h₁ hp else
 h₂ ⋯
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.reindex_apply`：reindex_apply (i' : ι') : b.reindex e i' = b
 (e.symm i')
· 使用定理 `PowerBasis.basis_eq_pow`：∀ {R : Type u_7} {S : Type u_8} [inst : CommRin
g R] [inst_1 : Ring S] [inst_2 : Algebra R S] (self : PowerBasis R S)   (i : Fin
 self.dim), s…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finCongr_symm_apply`：∀ {n m : ℕ} (eq : n = m) (a : Fin m), (finCongr eq)
.symm a = Fin.cast ⋯ a
· 使用定理 `Fin.val_cast`：∀ {n m : ℕ} (h : n = m) (i : Fin n), ↑(Fin.cast h i) = ↑i
-/
lemma basis_apply (n : Fin 2) :
    CoordinateRing.basis W' n = (AdjoinRoot.powerBasis' monic_polynomial).gen ^ (n : ℕ) := by
  classical
  nontriviality R
  rw [CoordinateRing.basis, Or.by_cases, dif_neg <| not_subsingleton R, Basis.reindex_apply,
    PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast]

@[simp]
/-
**WeierstrassCurve.Affine.CoordinateRing.basis_zero** 是 Mathlib 中的一个引理，位于命名空间 `W
eierstrassCurve.Affine.CoordinateRing`。
形式化陈述：basis_zero : CoordinateRing.basis W' 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Affine.monic_polynomial`：monic_polynomial : W.polynomia
l.Monic
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.basis_apply`：basis_apply (n : Fin
 2) : CoordinateRing.basis W' n = (AdjoinRoot.powerBasis' monic_polynomial).gen 
^ (n : Nat)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
lemma basis_zero : CoordinateRing.basis W' 0 = 1 := by
  simpa only [basis_apply] using! pow_zero _

@[simp]
/-
**WeierstrassCurve.Affine.CoordinateRing.basis_one** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Affine.CoordinateRing`。
形式化陈述：basis_one : CoordinateRing.basis W' 1 = mk W' Y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.Affine.monic_polynomial`：monic_polynomial : W.polynomia
l.Monic
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.basis_apply`：basis_apply (n : Fin
 2) : CoordinateRing.basis W' n = (AdjoinRoot.powerBasis' monic_polynomial).gen 
^ (n : Nat)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma basis_one : CoordinateRing.basis W' 1 = mk W' Y := by
  simpa only [basis_apply] using! pow_one _
/-
**WeierstrassCurve.Affine.CoordinateRing.coe_basis** 是 Mathlib 中的一个引理，位于命名空间 `We
ierstrassCurve.Affine.CoordinateRing`。
形式化陈述：coe_basis : (CoordinateRing.basis W' : Fin 2 -> W'.CoordinateRing) = ![1, 
mk W' Y]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.basis_zero`：basis_zero : Coordina
teRing.basis W' 0 = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.basis_one`：basis_one : Coordinate
Ring.basis W' 1 = mk W' Y
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma coe_basis : (CoordinateRing.basis W' : Fin 2 → W'.CoordinateRing) = ![1, mk W' Y] := by
  ext n
  fin_cases n
  exacts [basis_zero, basis_one]
/-
**WeierstrassCurve.Affine.CoordinateRing.** 是 Mathlib 中的一个实例，位于命名空间 `Weierstrass
Curve.Affine.CoordinateRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Free R[X] W'.CoordinateRing := .of_basis (CoordinateRing.basis W')
/-
**WeierstrassCurve.Affine.CoordinateRing.** 是 Mathlib 中的一个实例，位于命名空间 `Weierstrass
Curve.Affine.CoordinateRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Free R W'.CoordinateRing := .trans (S := R[X])
/-
**WeierstrassCurve.Affine.CoordinateRing.** 是 Mathlib 中的一个实例，位于命名空间 `Weierstrass
Curve.Affine.CoordinateRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nontrivial W'.CoordinateRing :=
  ⟨_, _, (CoordinateRing.basis W').ne_zero 0⟩
/-
**WeierstrassCurve.Affine.CoordinateRing.** 是 Mathlib 中的一个实例，位于命名空间 `Weierstrass
Curve.Affine.CoordinateRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FaithfulSMul R[X] W'.CoordinateRing := by nontriviality R; infer_instance
/-
**WeierstrassCurve.Affine.CoordinateRing.** 是 Mathlib 中的一个实例，位于命名空间 `Weierstrass
Curve.Affine.CoordinateRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FaithfulSMul R W'.CoordinateRing := .trans R R[X] _
/-
**WeierstrassCurve.Affine.CoordinateRing.smul** 是 Mathlib 中的一个引理，位于命名空间 `Weierst
rassCurve.Affine.CoordinateRing`。
形式化陈述：smul (x : R[X]) (y : W'.CoordinateRing) : x • y = mk W' (C x) * y
参数：x : R[X]；y : W'.CoordinateRing。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma smul (x : R[X]) (y : W'.CoordinateRing) : x • y = mk W' (C x) * y :=
  (algebraMap_smul W'.CoordinateRing x y).symm
/-
**WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero** 是 Mathlib 中的一个引理，位
于命名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：smul_basis_eq_zero {p q : R[X]} (hpq : p • (1 : W'.CoordinateRing) + q • m
k W' Y = 0) : p = 0 ∧ q = 0
参数：hpq : p • (1 : W'.CoordinateRing) + q • mk W' Y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.basis_one`：basis_one : Coordinate
Ring.basis W' 1 = mk W' Y
· 使用定理 `Fin.succ_zero_eq_one`：∀ {n : ℕ}, Fin.succ 0 = 1
· 使用定理 `Fin.sum_univ_one`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 1 →
 M), ∑ i, f i = f 0
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.basis_zero`：basis_zero : Coordina
teRing.basis W' 0 = 1
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
-/
lemma smul_basis_eq_zero {p q : R[X]} (hpq : p • (1 : W'.CoordinateRing) + q • mk W' Y = 0) :
    p = 0 ∧ q = 0 := by
  have h := Fintype.linearIndependent_iff.mp (CoordinateRing.basis W').linearIndependent ![p, q]
  rw [Fin.sum_univ_succ, basis_zero, Fin.sum_univ_one, Fin.succ_zero_eq_one, basis_one] at h
  exact ⟨h hpq 0, h hpq 1⟩
/-
**WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq** 是 Mathlib 中的一个引理
，位于命名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：exists_smul_basis_eq (x : W'.CoordinateRing) : exists p q : R[X], p • (1 :
 W'.CoordinateRing) + q • mk W' Y = x
参数：x : W'.CoordinateRing。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Basis.sum_equivFun`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6
} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : Finty…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.basis_one`：basis_one : Coordinate
Ring.basis W' 1 = mk W' Y
· 使用定理 `Fin.succ_zero_eq_one`：∀ {n : ℕ}, Fin.succ 0 = 1
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.basis_zero`：basis_zero : Coordina
teRing.basis W' 0 = 1
· 使用定理 `Fin.sum_univ_one`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 1 →
 M), ∑ i, f i = f 0
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
-/
lemma exists_smul_basis_eq (x : W'.CoordinateRing) :
    ∃ p q : R[X], p • (1 : W'.CoordinateRing) + q • mk W' Y = x := by
  have h := (CoordinateRing.basis W').sum_equivFun x
  rw [Fin.sum_univ_succ, Fin.sum_univ_one, basis_zero, Fin.succ_zero_eq_one, basis_one] at h
  exact ⟨_, _, h⟩
/-
**WeierstrassCurve.Affine.CoordinateRing.smul_basis_mul_C** 是 Mathlib 中的一个引理，位于命
名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：smul_basis_mul_C (y : R[X]) (p q : R[X]) : (p • (1 : W'.CoordinateRing) + 
q • mk W' Y) * mk W' (C y) = (p * y) • (1 : W'.CoordinateRing) + (q * y) • mk W'
 Y
参数：y : R[X]；p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.smul`：smul (x : R[X]) (y : W'.Coo
rdinateRing) : x • y = mk W' (C x) * y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
-/
lemma smul_basis_mul_C (y : R[X]) (p q : R[X]) :
    (p • (1 : W'.CoordinateRing) + q • mk W' Y) * mk W' (C y) =
      (p * y) • (1 : W'.CoordinateRing) + (q * y) • mk W' Y := by
  simp only [smul, map_mul]
  ring1
/-
**WeierstrassCurve.Affine.CoordinateRing.smul_basis_mul_Y** 是 Mathlib 中的一个引理，位于命
名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：smul_basis_mul_Y (p q : R[X]) : (p • (1 : W'.CoordinateRing) + q • mk W' Y
) * mk W' Y = (q * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆)) • (1 : W'.
CoordinateRing) + (p - q * (C W'.a₁ * X + C W'.a₃)) • mk W' Y
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AdjoinRoot.mk_eq_mk`：mk_eq_mk {g h : R[X]} : mk f g = mk f h ↔ f ∣ g - h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Affine.polynomial.eq_1`：∀ {R : Type r} [inst : CommRing
 R] (W : WeierstrassCurve.Affine R),   W.polynomial =     Polynomial.X ^ 2 + Pol
ynomial.C (Polynomial.C W.a₁ …
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 55 条，此处仅展示前 30 条）
-/
lemma smul_basis_mul_Y (p q : R[X]) : (p • (1 : W'.CoordinateRing) + q • mk W' Y) * mk W' Y =
    (q * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆)) • (1 : W'.CoordinateRing) +
      (p - q * (C W'.a₁ * X + C W'.a₃)) • mk W' Y := by
  have Y_sq : mk W' Y ^ 2 = mk W' (C (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆) -
      C (C W'.a₁ * X + C W'.a₃) * Y) := AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [polynomial]; ring1⟩
  simp only [smul, add_mul, mul_assoc, ← sq, Y_sq, map_sub, map_mul]
  ring1

variable (W') in
/-- The ring homomorphism `R[W] →+* S[W.map f]` induced by a ring homomorphism `f : R →+* S`. -/
/-
**WeierstrassCurve.Affine.CoordinateRing.map** 是 Mathlib 中的一个定义，位于命名空间 `Weierstr
assCurve.Affine.CoordinateRing`。
形式化陈述：map (f : R ->+* S) : W'.CoordinateRing ->+* (W'.map f).CoordinateRing
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism `R[W] →+* S[W.map f]` induced by a ring homomorphism `f : 
R →+* S`.
-/
noncomputable def map (f : R →+* S) : W'.CoordinateRing →+* (W'.map f).CoordinateRing :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp <| mapRingHom f) (AdjoinRoot.root (W'.map f).polynomial)
    (by rw [← eval₂_map, ← map_polynomial, AdjoinRoot.eval₂_root])
/-
**WeierstrassCurve.Affine.CoordinateRing.map_mk** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Affine.CoordinateRing`。
形式化陈述：map_mk (f : R ->+* S) (x : R[X][Y]) : map W' f (mk W' x) = mk (W'.map f) (
x.map <| mapRingHom f)
参数：f : R ->+* S；x : R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.map.eq_1`：∀ {R : Type r} {S : Typ
e s} [inst : CommRing R] [inst_1 : CommRing S] (W' : WeierstrassCurve.Affine R) 
(f : R →+* S),   WeierstrassCurve.Aff…
· 使用定理 `AdjoinRoot.lift_mk`：lift_mk (g : R[X]) : lift i a h (mk f g) = g.eval₂ i
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval₂_map`：eval₂_map [Semiring T] (g : S ->+* T) (x : T) : (p
.map f).eval₂ g x = p.eval₂ (g.comp f) x
· 使用定理 `AdjoinRoot.aeval_eq`：aeval_eq (p : R[X]) : aeval (root f) p = mk f p
-/
lemma map_mk (f : R →+* S) (x : R[X][Y]) :
    map W' f (mk W' x) = mk (W'.map f) (x.map <| mapRingHom f) := by
  rw [map, AdjoinRoot.lift_mk, ← eval₂_map]
  exact AdjoinRoot.aeval_eq <| x.map <| mapRingHom f
/-
**WeierstrassCurve.Affine.CoordinateRing.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `Wei
erstrassCurve.Affine.CoordinateRing`。
形式化陈述：∀ {R : Type r} {S : Type s} [inst : CommRing R] [inst_1 : CommRing S] {W' 
: WeierstrassCurve.Affine R} (f : R →+* S)   (x : Polynomial R) (y : W'.Coordina
teRing),   (WeierstrassCurve.Affine.CoordinateRing.map W' f) (x • y) =     Polyn
omial.map f x • (WeierstrassCurve.Affine.CoordinateRing.map W' f) y
参数：f : R →+* S；x : Polynomial R；y : W'.CoordinateRing；WeierstrassCurve.Affine.Co
ordinateRing.map W' f；x • y；WeierstrassCurve.Affine.CoordinateRing.map W' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.smul`：smul (x : R[X]) (y : W'.Coo
rdinateRing) : x • y = mk W' (C x) * y
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.map_mk`：map_mk (f : R ->+* S) (x 
: R[X][Y]) : map W' f (mk W' x) = mk (W'.map f) (x.map <| mapRingHom f)
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
-/
protected lemma map_smul (f : R →+* S) (x : R[X]) (y : W'.CoordinateRing) :
    map W' f (x • y) = x.map f • map W' f y := by
  rw [smul, map_mul, map_mk, map_C, smul]
  rfl
/-
**WeierstrassCurve.Affine.CoordinateRing.map_injective** 是 Mathlib 中的一个引理，位于命名空间
 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：map_injective {f : R ->+* S} (hf : Function.Injective f) : Function.Inject
ive map W' f
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq`：exists_smul
_basis_eq (x : W'.CoordinateRing) : exists p q : R[X], p • (1 : W'.CoordinateRin
g) + q • mk W' Y = x
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero`：smul_basis_eq
_zero {p q : R[X]} (hpq : p • (1 : W'.CoordinateRing) + q • mk W' Y = 0) : p = 0
 ∧ q = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.map_mk`：map_mk (f : R ->+* S) (x 
: R[X][Y]) : map W' f (mk W' x) = mk (W'.map f) (x.map <| mapRingHom f)
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.map_smul`：∀ {R : Type r} {S : Typ
e s} [inst : CommRing R] [inst_1 : CommRing S] {W' : WeierstrassCurve.Affine R} 
(f : R →+* S)   (x : Polynomial R) (y…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Polynomial.map_eq_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_injective {f : R →+* S} (hf : Function.Injective f) : Function.Injective <| map W' f :=
  (injective_iff_map_eq_zero _).mpr fun y hy => by
    obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq y
    simp_rw [map_add, CoordinateRing.map_smul, map_one, map_mk, map_X] at hy
    obtain ⟨hp, hq⟩ := smul_basis_eq_zero hy
    rw [Polynomial.map_eq_zero_iff hf] at hp hq
    simp_rw [hp, hq, zero_smul, add_zero]
/-
**WeierstrassCurve.Affine.CoordinateRing.** 是 Mathlib 中的一个实例，位于命名空间 `Weierstrass
Curve.Affine.CoordinateRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDomain R] : IsDomain W'.CoordinateRing :=
  have : IsDomain (W'.map <| algebraMap R <| FractionRing R).CoordinateRing :=
    AdjoinRoot.isDomain_of_prime irreducible_polynomial.prime
  (map_injective <| IsFractionRing.injective R <| FractionRing R).isDomain

/-! ## Ideals in the affine coordinate ring -/

variable (W') in
/-- The class of the element `X - x` in `R[W]` for some `x` in `R`. -/
/-
**WeierstrassCurve.Affine.CoordinateRing.XClass** 是 Mathlib 中的一个定义，位于命名空间 `Weier
strassCurve.Affine.CoordinateRing`。
形式化陈述：XClass (x : R) : W'.CoordinateRing
参数：x : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of the element `X - x` in `R[W]` for some `x` in `R`.
-/
noncomputable def XClass (x : R) : W'.CoordinateRing :=
  mk W' <| C <| X - C x
/-
**WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero** 是 Mathlib 中的一个引理，位于命名空
间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：XClass_ne_zero [Nontrivial R] (x : R) : XClass W' x != 0
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdjoinRoot.mk_ne_zero_of_natDegree_lt`：mk_ne_zero_of_natDegree_lt (hf : 
Monic f) {g : R[X]} (h0 : g != 0) (hd : natDegree g < natDegree f) : mk f g != 0
· 使用引理 `WeierstrassCurve.Affine.monic_polynomial`：monic_polynomial : W.polynomia
l.Monic
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.C_ne_zero`：C_ne_zero : C a != 0 ↔ a != 0
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.natDegree_polynomial`：natDegree_polynomial [Nont
rivial R] : W.polynomial.natDegree = 2
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
-/
lemma XClass_ne_zero [Nontrivial R] (x : R) : XClass W' x ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial (C_ne_zero.mpr <| X_sub_C_ne_zero x) <|
    by rw [natDegree_polynomial, natDegree_C]; norm_num1

variable (W') in
/-- The class of the element `Y - y(X)` in `R[W]` for some `y(X)` in `R[X]`. -/
/-
**WeierstrassCurve.Affine.CoordinateRing.YClass** 是 Mathlib 中的一个定义，位于命名空间 `Weier
strassCurve.Affine.CoordinateRing`。
形式化陈述：YClass (y : R[X]) : W'.CoordinateRing
参数：y : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of the element `Y - y(X)` in `R[W]` for some `y(X)` in `R[X]`.
-/
noncomputable def YClass (y : R[X]) : W'.CoordinateRing :=
  mk W' <| Y - C y
/-
**WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero** 是 Mathlib 中的一个引理，位于命名空
间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：YClass_ne_zero [Nontrivial R] (y : R[X]) : YClass W' y != 0
参数：y : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdjoinRoot.mk_ne_zero_of_natDegree_lt`：mk_ne_zero_of_natDegree_lt (hf : 
Monic f) {g : R[X]} (h0 : g != 0) (hd : natDegree g < natDegree f) : mk f g != 0
· 使用引理 `WeierstrassCurve.Affine.monic_polynomial`：monic_polynomial : W.polynomia
l.Monic
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.natDegree_polynomial`：natDegree_polynomial [Nont
rivial R] : W.polynomial.natDegree = 2
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
-/
lemma YClass_ne_zero [Nontrivial R] (y : R[X]) : YClass W' y ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial (X_sub_C_ne_zero y) <|
    by rw [natDegree_polynomial, natDegree_X_sub_C]; norm_num1
/-
**WeierstrassCurve.Affine.CoordinateRing.C_addPolynomial** 是 Mathlib 中的一个引理，位于命名
空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：C_addPolynomial (x y ℓ : R) : mk W' (C <| W'.addPolynomial x y ℓ) = mk W' 
((Y - C (linePolynomial x y ℓ)) * (W'.negPolynomial - C (linePolynomial x y ℓ)))
参数：x y ℓ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AdjoinRoot.mk_eq_mk`：mk_eq_mk {g h : R[X]} : mk f g = mk f h ↔ f ∣ g - h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.C_addPolynomial`：C_addPolynomial (x y ℓ : R) : C
 (W'.addPolynomial x y ℓ) = (Y - C (linePolynomial x y ℓ)) * (W'.negPolynomial -
 C (linePolynomial x y ℓ)) + …
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma C_addPolynomial (x y ℓ : R) : mk W' (C <| W'.addPolynomial x y ℓ) =
    mk W' ((Y - C (linePolynomial x y ℓ)) * (W'.negPolynomial - C (linePolynomial x y ℓ))) :=
  AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [W'.C_addPolynomial, add_sub_cancel_left, mul_one]⟩
/-
**WeierstrassCurve.Affine.CoordinateRing.C_addPolynomial_slope** 是 Mathlib 中的一个引
理，位于命名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：C_addPolynomial_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x
₁ y₁) (h₂ : W.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) : mk W (C <
| W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) = -(XClass W x₁ * XClass W x₂ * 
XClass W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))
参数：h₁ : W.Equation x₁ y₁；h₂ : W.Equation x₂ y₂；hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ 
y₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.C_addPolynomial_slope`：C_addPolynomial_slope {x₁
 x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ 
∧ y₁ = W.negY x₂ y₂)) : C (W.addPol…
-/
lemma C_addPolynomial_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    mk W (C <| W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -(XClass W x₁ * XClass W x₂ * XClass W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)) :=
  congr_arg (mk W) <| W.C_addPolynomial_slope h₁ h₂ hxy

variable (W') in
/-- The ideal `⟨X - x⟩` of `R[W]` for some `x` in `R`. -/
/-
**WeierstrassCurve.Affine.CoordinateRing.XIdeal** 是 Mathlib 中的一个定义，位于命名空间 `Weier
strassCurve.Affine.CoordinateRing`。
形式化陈述：XIdeal (x : R) : Ideal W'.CoordinateRing
参数：x : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ideal `⟨X - x⟩` of `R[W]` for some `x` in `R`.
-/
noncomputable def XIdeal (x : R) : Ideal W'.CoordinateRing :=
  .span {XClass W' x}

variable (W') in
/-- The ideal `⟨Y - y(X)⟩` of `R[W]` for some `y(X)` in `R[X]`. -/
/-
**WeierstrassCurve.Affine.CoordinateRing.YIdeal** 是 Mathlib 中的一个定义，位于命名空间 `Weier
strassCurve.Affine.CoordinateRing`。
形式化陈述：YIdeal (y : R[X]) : Ideal W'.CoordinateRing
参数：y : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ideal `⟨Y - y(X)⟩` of `R[W]` for some `y(X)` in `R[X]`.
-/
noncomputable def YIdeal (y : R[X]) : Ideal W'.CoordinateRing :=
  .span {YClass W' y}

variable (W') in
/-- The ideal `⟨X - x, Y - y(X)⟩` of `R[W]` for some `x` in `R` and `y(X)` in `R[X]`. -/
/-
**WeierstrassCurve.Affine.CoordinateRing.XYIdeal** 是 Mathlib 中的一个定义，位于命名空间 `Weie
rstrassCurve.Affine.CoordinateRing`。
形式化陈述：XYIdeal (x : R) (y : R[X]) : Ideal W'.CoordinateRing
参数：x : R；y : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ideal `⟨X - x, Y - y(X)⟩` of `R[W]` for some `x` in `R` and `y(X)` in `R[X]`
.
-/
noncomputable def XYIdeal (x : R) (y : R[X]) : Ideal W'.CoordinateRing :=
  .span {XClass W' x, YClass W' y}

set_option backward.isDefEq.respectTransparency.types false in
/-- The `R`-algebra isomorphism from `R[W] / ⟨X - x, Y - y(X)⟩` to `R` obtained by evaluation at
some `y(X)` in `R[X]` and at some `x` in `R` provided that `W(x, y(x)) = 0`. -/
/-
**WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv** 是 Mathlib 中的一个定义
，位于命名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：quotientXYIdealEquiv {x : R} {y : R[X]} (h : (W'.polynomial.eval y).eval x
 = 0) : (W'.CoordinateRing ⧸ XYIdeal W' x y) ≃ₐ[R] R
参数：h : (W'.polynomial.eval y).eval x = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-algebra isomorphism from `R[W] / ⟨X - x, Y - y(X)⟩` to `R` obtained by e
valuation at
some `y(X)` in `R[X]` and at some `x` in `R` provided that `W(x, y(x)) = 0`.
-/
noncomputable def quotientXYIdealEquiv {x : R} {y : R[X]} (h : (W'.polynomial.eval y).eval x = 0) :
    (W'.CoordinateRing ⧸ XYIdeal W' x y) ≃ₐ[R] R :=
  ((quotientEquivAlgOfEq R <| by
      simp only [XYIdeal, XClass, YClass, ← Set.image_pair, ← map_span]; rfl).trans <|
        DoubleQuot.quotQuotEquivQuotOfLEₐ R <| (span_singleton_le_iff_mem _).mpr <|
          mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h).trans
    quotientSpanCXSubCXSubCAlgEquiv
/-
**WeierstrassCurve.Affine.CoordinateRing.XYIdeal_add_eq** 是 Mathlib 中的一个引理，位于命名空
间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：XYIdeal_add_eq (x₁ x₂ y₁ ℓ : R) : XYIdeal W' (W'.addX x₁ x₂ ℓ) (C <| W'.ad
dY x₁ x₂ y₁ ℓ) = .span {mk W' <| W'.negPolynomial - C (linePolynomial x₁ y₁ ℓ)} 
⊔ XIdeal W' (W'.addX x₁ x₂ ℓ)
参数：x₁ x₂ y₁ ℓ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `neg_sub_left`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -
a - b = -(b + a)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Ideal.span_singleton_neg`：span_singleton_neg : span {-x} = span {x}
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_insert`：span_insert (x) (s : Set α) : span (insert x s) = spa
n ({x} : Set α) ⊔ span s
· 使用定理 `Ideal.span_pair_add_left_mul`：span_pair_add_left_mul : span {x, y + x * 
z} = span {x, y}
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.C_sub`：C_sub : C (a - b) = C a - C b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `Polynomial.C_add`：C_add : C (a + b) = C a + C b
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
（共 56 条，此处仅展示前 30 条）
-/
lemma XYIdeal_add_eq (x₁ x₂ y₁ ℓ : R) : XYIdeal W' (W'.addX x₁ x₂ ℓ) (C <| W'.addY x₁ x₂ y₁ ℓ) =
    .span {mk W' <| W'.negPolynomial - C (linePolynomial x₁ y₁ ℓ)} ⊔
      XIdeal W' (W'.addX x₁ x₂ ℓ) := by
  simp only [XYIdeal, XIdeal, XClass, YClass, addY, negAddY, negY, negPolynomial, linePolynomial]
  rw [sub_sub <| -(Y : R[X][Y]), neg_sub_left (Y : R[X][Y]), map_neg, span_singleton_neg, sup_comm,
    ← span_insert, ← span_pair_add_left_mul _ _ <| mk W' <| C <| C <| W'.a₁ + ℓ, ← map_mul,
    ← map_add]
  congr 4
  C_simp
  ring1
/-
**WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq** 是 Mathlib 中的一个引理，位于命名空间 `W
eierstrassCurve.Affine.CoordinateRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma XYIdeal_eq₁ (x y ℓ : R) : XYIdeal W' x (C y) = XYIdeal W' x (linePolynomial x y ℓ) := by
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_left_mul _ _ <| mk W' <| C <| C <| -ℓ, ← map_mul, ← map_add]
  congr 4
  C_simp
  ring1

-- Non-terminal simp, used to be field_simp
set_option linter.flexible false in
/-
**WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq** 是 Mathlib 中的一个引理，位于命名空间 `W
eierstrassCurve.Affine.CoordinateRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma XYIdeal_eq₂ [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    XYIdeal W x₂ (C y₂) = XYIdeal W x₂ (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  have hy₂ : y₂ = (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂).eval x₂ := by
    by_cases hx : x₁ = x₂
    · have hy : y₁ ≠ W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
      rcases hx, Y_eq_of_Y_ne h₁ h₂ hx hy with ⟨rfl, rfl⟩
      simp [linePolynomial]
    · simp [field, linePolynomial, slope_of_X_ne hx]
      ring1
  nth_rw 1 [hy₂]
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_left_mul _ _ <| mk W <| C <| C <| -W.slope x₁ x₂ y₁ y₂, ← map_mul, ← map_add]
  congr 4
  simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul]
  C_simp
  ring1
/-
**WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul** 是 Mathlib 中的一个引理，位于命名
空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：XYIdeal_neg_mul {x y : F} (h : W.Nonsingular x y) : XYIdeal W x (C <| W.ne
gY x y) * XYIdeal W x (C y) = XIdeal W x
参数：h : W.Nonsingular x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Affine.equation_iff`：equation_iff (x y : R) : W.Equatio
n x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Affine.negY.eq_1`：∀ {R : Type r} [inst : CommRing R] (W
' : WeierstrassCurve.Affine R) (x y : R), W'.negY x y = -y - W'.a₁ * x - W'.a₃
· 使用定理 `WeierstrassCurve.Affine.polynomial.eq_1`：∀ {R : Type r} [inst : CommRing
 R] (W : WeierstrassCurve.Affine R),   W.polynomial =     Polynomial.X ^ 2 + Pol
ynomial.C (Polynomial.C W.a₁ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.C_sub`：C_sub : C (a - b) = C a - C b
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `Polynomial.C_add`：C_add : C (a + b) = C a + C b
· 使用定理 `Polynomial.C_pow`：C_pow : C (a ^ n) = C a ^ n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 97 条，此处仅展示前 30 条）
-/
lemma XYIdeal_neg_mul {x y : F} (h : W.Nonsingular x y) :
    XYIdeal W x (C <| W.negY x y) * XYIdeal W x (C y) = XIdeal W x := by
  have Y_rw : (Y - C (C y)) * (Y - C (C <| W.negY x y)) -
      C (X - C x) * (C (X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)) - C (C W.a₁) * Y) =
        W.polynomial * 1 := by
    linear_combination (norm := (rw [negY, polynomial]; C_simp; ring1))
      congr_arg C (congr_arg C ((equation_iff ..).mp h.left).symm)
  simp_rw [XYIdeal, XClass, YClass, span_pair_mul_span_pair, mul_comm, ← map_mul,
    AdjoinRoot.mk_eq_mk.mpr ⟨1, Y_rw⟩, map_mul, span_insert, ← span_singleton_mul_span_singleton,
    ← Ideal.mul_sup, ← span_insert]
  convert! mul_top (_ : Ideal W.CoordinateRing) using 2
  on_goal 2 => infer_instance
  simp_rw [← Set.image_singleton (f := mk W), ← Set.image_insert_eq, ← map_span]
  convert! map_top (R := F[X][Y]) (mk W) using 1
  apply congr_arg
  simp_rw [eq_top_iff_one, mem_span_insert', mem_span_singleton']
  rcases ((nonsingular_iff' ..).mp h).right with hx | hy
  · let W_X := W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
    refine
      ⟨C <| C W_X⁻¹ * -(X + C (2 * x + W.a₂)), C <| C <| W_X⁻¹ * W.a₁, 0, C <| C <| W_X⁻¹ * -1, ?_⟩
    rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hx]
    simp only [W_X, mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hx]
    C_simp
    ring1
  · let W_Y := 2 * y + W.a₁ * x + W.a₃
    refine ⟨0, C <| C W_Y⁻¹, C <| C <| W_Y⁻¹ * -1, 0, ?_⟩
    rw [negY, ← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hy]
    simp only [W_Y, mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hy]
    C_simp
    ring1
/-
**WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal** 是 Mathlib 中的一个引理，
位于命名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：XYIdeal_mul_XYIdeal [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ 
y₁) (h₂ : W.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) : XIdeal W (W
.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) * (XYIdeal W x₁ (C y₁) * XYIdeal W x₂ (C y₂)
) = YIdeal W (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) * XYIdeal W (W.addX x
₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (C <| W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂)
参数：h₁ : W.Equation x₁ y₁；h₂ : W.Equation x₂ y₂；hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ 
y₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_sup_sup_comm`：sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔
 c ⊔ (b ⊔ d)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_add_eq`：XYIdeal_add_eq (x
₁ x₂ y₁ ℓ : R) : XYIdeal W' (W'.addX x₁ x₂ ℓ) (C <| W'.addY x₁ x₂ y₁ ℓ) = .span 
{mk W' <| W'.negPolynomial - C (linePolynom…
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.XIdeal.eq_1`：∀ {R : Type r} [inst
 : CommRing R] (W' : WeierstrassCurve.Affine R) (x : R),   WeierstrassCurve.Affi
ne.CoordinateRing.XIdeal W' x = Ideal.sp…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq₁`：XYIdeal_eq₁ (x y ℓ :
 R) : XYIdeal W' x (C y) = XYIdeal W' x (linePolynomial x y ℓ)
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.XYIdeal.eq_1`：∀ {R : Type r} [ins
t : CommRing R] (W' : WeierstrassCurve.Affine R) (x : R) (y : Polynomial R),   W
eierstrassCurve.Affine.CoordinateRing.XYI…
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq₂`：XYIdeal_eq₂ [Decidab
leEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hxy :
 ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) : XYIde…
· 使用定理 `Ideal.span_pair_mul_span_pair`：span_pair_mul_span_pair (w x y z : R) [(s
pan {w, x}).IsTwoSided] : (span {w, x} : Ideal R) * span {y, z} = span {w * y, w
 * z, x * y, x * z}
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.span_insert`：span_insert (x) (s : Set α) : span (insert x s) = spa
n ({x} : Set α) ⊔ span s
· 使用定理 `Ideal.sup_mul`：sup_mul : (I ⊔ J) * K = I * K ⊔ J * K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.span_singleton_mul_span_singleton`：span_singleton_mul_span_singlet
on (r s : R) [(span {r}).IsTwoSided] : span {r} * span {s} = (span {r * s} : Ide
al R)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.C_addPolynomial_slope`：C_addPolyn
omial_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Eq
uation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂…
· 使用定理 `Ideal.span_singleton_neg`：span_singleton_neg : span {-x} = span {x}
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.C_addPolynomial`：C_addPolynomial 
(x y ℓ : R) : mk W' (C <| W'.addPolynomial x y ℓ) = mk W' ((Y - C (linePolynomia
l x y ℓ)) * (W'.negPolynomial - C (linePolyn…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.YClass.eq_1`：∀ {R : Type r} [inst
 : CommRing R] (W' : WeierstrassCurve.Affine R) (y : Polynomial R),   Weierstras
sCurve.Affine.CoordinateRing.YClass W' y…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 140 条，此处仅展示前 30 条）
-/
lemma XYIdeal_mul_XYIdeal [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    XIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) * (XYIdeal W x₁ (C y₁) * XYIdeal W x₂ (C y₂)) =
      YIdeal W (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) *
        XYIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)
          (C <| W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  have sup_rw : ∀ a b c d : Ideal W.CoordinateRing, a ⊔ (b ⊔ (c ⊔ d)) = a ⊔ d ⊔ b ⊔ c :=
    fun _ _ c _ => by rw [← sup_assoc, sup_comm c, sup_sup_sup_comm, ← sup_assoc]
  rw [XYIdeal_add_eq, XIdeal, mul_comm, XYIdeal_eq₁ x₁ y₁ <| W.slope x₁ x₂ y₁ y₂, XYIdeal,
    XYIdeal_eq₂ h₁ h₂ hxy, XYIdeal, span_pair_mul_span_pair]
  simp_rw [span_insert, sup_rw, Ideal.sup_mul, span_singleton_mul_span_singleton]
  rw [← neg_eq_iff_eq_neg.mpr <| C_addPolynomial_slope h₁ h₂ hxy, span_singleton_neg,
    C_addPolynomial, map_mul, YClass]
  simp_rw [mul_comm <| XClass W x₁, mul_assoc, ← span_singleton_mul_span_singleton, ← Ideal.mul_sup]
  rw [span_singleton_mul_span_singleton, ← span_insert,
    ← span_pair_add_left_mul _ _ <| -(XClass W <| W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂), mul_neg,
    ← sub_eq_add_neg, ← sub_mul, ← map_sub <| mk W, sub_sub_sub_cancel_right, span_insert,
    ← span_singleton_mul_span_singleton, ← sup_rw, ← Ideal.sup_mul, ← Ideal.sup_mul]
  apply congr_arg (_ ∘ _)
  convert! top_mul (_ : Ideal W.CoordinateRing)
  simp_rw [XClass, ← Set.image_singleton (f := mk W), ← map_span, ← Ideal.map_sup, eq_top_iff_one,
    mem_map_iff_of_surjective _ AdjoinRoot.mk_surjective, ← span_insert, mem_span_insert',
    mem_span_singleton']
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    rcases hx, Y_eq_of_Y_ne h₁ h₂ hx hy with ⟨rfl, rfl⟩
    let y := (y₁ - W.negY x₁ y₁) ^ 2
    replace hxy := pow_ne_zero 2 <| sub_ne_zero_of_ne hy
    refine ⟨1 + C (C <| y⁻¹ * 4) * W.polynomial,
      ⟨C <| C y⁻¹ * (C 4 * X ^ 2 + C (4 * x₁ + W.b₂) * X + C (4 * x₁ ^ 2 + W.b₂ * x₁ + 2 * W.b₄)),
        0, C (C y⁻¹) * (Y - W.negPolynomial), ?_⟩, by
      rw [map_add, map_one, map_mul <| mk W, AdjoinRoot.mk_self, mul_zero, add_zero]⟩
    rw [polynomial, negPolynomial, ← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hxy]
    simp only [y, mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hxy]
    linear_combination (norm := (rw [b₂, b₄, negY]; C_simp; ring1))
      -4 * congr_arg C (congr_arg C <| (equation_iff ..).mp h₁)
  · replace hx := sub_ne_zero_of_ne hx
    refine ⟨_, ⟨⟨C <| C (x₁ - x₂)⁻¹, C <| C <| (x₁ - x₂)⁻¹ * -1, 0, ?_⟩, map_one _⟩⟩
    rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hx]
    simp only [← mul_assoc, mul_add, ← C_mul, mul_inv_cancel₀ hx]
    C_simp
    ring1

/-- The non-zero fractional ideal `⟨X - x, Y - y⟩` of `F(W)` for some `x` and `y` in `F`. -/
/-
**WeierstrassCurve.Affine.CoordinateRing.XYIdeal'** 是 Mathlib 中的一个定义，位于命名空间 `Wei
erstrassCurve.Affine.CoordinateRing`。
形式化陈述：XYIdeal' {x y : F} (h : W.Nonsingular x y) : (FractionalIdeal W.Coordinate
Ring⁰ W.FunctionField)ˣ
参数：h : W.Nonsingular x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The non-zero fractional ideal `⟨X - x, Y - y⟩` of `F(W)` for some `x` and `y` in
 `F`.
-/
noncomputable def XYIdeal' {x y : F} (h : W.Nonsingular x y) :
    (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ :=
  Units.mkOfMulEqOne (XYIdeal W x (C y)) (XYIdeal W x (C <| W.negY x y) *
      (XIdeal W x : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)⁻¹) <| by
    rw [← mul_assoc, ← coeIdeal_mul, mul_comm <| XYIdeal W .., XYIdeal_neg_mul h, XIdeal,
      FractionalIdeal.coe_ideal_span_singleton_mul_inv W.FunctionField <| XClass_ne_zero x]
/-
**WeierstrassCurve.Affine.CoordinateRing.XYIdeal'_eq** 是 Mathlib 中的一个定理，位于命名空间 `
WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：∀ {F : Type u} [inst : Field F] {W : WeierstrassCurve.Affine F} {x y : F} 
(h : W.Nonsingular x y),   ↑(WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h) 
=     ↑(WeierstrassCurve.Affine.CoordinateRing.XYIdeal W x (Polynomial.C y))
参数：h : W.Nonsingular x y；WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h；Weier
strassCurve.Affine.CoordinateRing.XYIdeal W x (Polynomial.C y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma XYIdeal'_eq {x y : F} (h : W.Nonsingular x y) :
    (XYIdeal' h : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = XYIdeal W x (C y) :=
  rfl
/-
**WeierstrassCurve.Affine.CoordinateRing.mk_XYIdeal'_neg_mul** 是 Mathlib 中的一个定理，
位于命名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：∀ {F : Type u} [inst : Field F] {W : WeierstrassCurve.Affine F} {x y : F} 
(h : W.Nonsingular x y),   (ClassGroup.mk W.FunctionField) (WeierstrassCurve.Aff
ine.CoordinateRing.XYIdeal' ⋯) *       (ClassGroup.mk W.FunctionField) (Weierstr
assCurve.Affine.CoordinateRing.XYIdeal' h) =     1
参数：h : W.Nonsingular x y；ClassGroup.mk W.FunctionField；WeierstrassCurve.Affine.C
oordinateRing.XYIdeal' ⋯；ClassGroup.mk W.FunctionField；WeierstrassCurve.Affine.C
oordinateRing.XYIdeal' h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.instIsDomain`：∀ {R : Type r} [ins
t : CommRing R] {W' : WeierstrassCurve.Affine R} [IsDomain R], IsDomain W'.Coord
inateRing
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WeierstrassCurve.Affine.nonsingular_neg`：nonsingular_neg (x y : R) : W'.
Nonsingular x (W'.negY x y) ↔ W'.Nonsingular x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `ClassGroup.mk_eq_one_of_coe_ideal`：ClassGroup.mk_eq_one_of_coe_ideal {I 
: (FractionalIdeal R⁰ <| FractionRing R)ˣ} {I' : Ideal R} (hI : (I : FractionalI
deal R⁰ <| FractionRing…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionalIdeal.coeIdeal_mul`：coeIdeal_mul (I J : Ideal R) : (↑(I * J) :
 FractionalIdeal S P) = I * J
· 使用定理 `FractionalIdeal.coeIdeal_inj`：coeIdeal_inj {I J : Ideal R} : (I : Fracti
onalIdeal R⁰ K) = (J : FractionalIdeal R⁰ K) ↔ I = J
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul`：XYIdeal_neg_mul 
{x y : F} (h : W.Nonsingular x y) : XYIdeal W x (C <| W.negY x y) * XYIdeal W x 
(C y) = XIdeal W x
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero`：XClass_ne_zero [N
ontrivial R] (x : R) : XClass W' x != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
lemma mk_XYIdeal'_neg_mul {x y : F} (h : W.Nonsingular x y) :
    ClassGroup.mk W.FunctionField (XYIdeal'  <| (nonsingular_neg ..).mpr h) *
      ClassGroup.mk W.FunctionField (XYIdeal' h) = 1 := by
  rw [← map_mul]
  exact (ClassGroup.mk_eq_one_of_coe_ideal <| (coeIdeal_mul ..).symm.trans <|
    FractionalIdeal.coeIdeal_inj.mpr <| XYIdeal_neg_mul h).mpr ⟨_, XClass_ne_zero x, rfl⟩
/-
**WeierstrassCurve.Affine.CoordinateRing.mk_XYIdeal'_mul_mk_XYIdeal'** 是 Mathlib
 中的一个定理，位于命名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：∀ {F : Type u} [inst : Field F] {W : WeierstrassCurve.Affine F} [inst_1 : 
DecidableEq F] {x₁ x₂ y₁ y₂ : F}   (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingula
r x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)),   (ClassGroup.mk W.FunctionFiel
d) (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h₁) *       (ClassGroup.mk W
.FunctionField) (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h₂) =     (Clas
sGroup.mk W.FunctionField) (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' ⋯)
参数：h₁ : W.Nonsingular x₁ y₁；h₂ : W.Nonsingular x₂ y₂；hxy : ¬(x₁ = x₂ ∧ y₁ = W.ne
gY x₂ y₂)；ClassGroup.mk W.FunctionField；WeierstrassCurve.Affine.CoordinateRing.X
YIdeal' h₁；ClassGroup.mk W.FunctionField；WeierstrassCurve.Affine.CoordinateRing.
XYIdeal' h₂；ClassGroup.mk W.FunctionField；WeierstrassCurve.Affine.CoordinateRing
.XYIdeal' ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.instIsDomain`：∀ {R : Type r} [ins
t : CommRing R] {W' : WeierstrassCurve.Affine R} [IsDomain R], IsDomain W'.Coord
inateRing
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `WeierstrassCurve.Affine.nonsingular_add`：nonsingular_add {x₁ x₂ y₁ y₂ : 
F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ =
 W.negY x₂ y₂)) : W.Nonsingul…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `ClassGroup.mk_eq_mk_of_coe_ideal`：ClassGroup.mk_eq_mk_of_coe_ideal {I J 
: (FractionalIdeal R⁰ <| FractionRing R)ˣ} {I' J' : Ideal R} (hI : (I : Fraction
alIdeal R⁰ <| Fraction…
· 使用定理 `FractionalIdeal.coeIdeal_mul`：coeIdeal_mul (I J : Ideal R) : (↑(I * J) :
 FractionalIdeal S P) = I * J
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.XYIdeal'_eq`：∀ {F : Type u} [inst
 : Field F] {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular x y),  
 ↑(WeierstrassCurve.Affine.CoordinateRin…
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero`：XClass_ne_zero [N
ontrivial R] (x : R) : XClass W' x != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero`：YClass_ne_zero [N
ontrivial R] (y : R[X]) : YClass W' y != 0
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal`：XYIdeal_mul_
XYIdeal [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equati
on x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂))…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma mk_XYIdeal'_mul_mk_XYIdeal' [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    ClassGroup.mk W.FunctionField (XYIdeal' h₁) *
        ClassGroup.mk W.FunctionField (XYIdeal' h₂) =
      ClassGroup.mk W.FunctionField (XYIdeal' <| nonsingular_add h₁ h₂ hxy) := by
  rw [← map_mul]
  exact (ClassGroup.mk_eq_mk_of_coe_ideal (coeIdeal_mul ..).symm <| XYIdeal'_eq _).mpr
    ⟨_, _, XClass_ne_zero _, YClass_ne_zero _, XYIdeal_mul_XYIdeal h₁.left h₂.left hxy⟩

/-! ## Norms on the affine coordinate ring -/

/-
**WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis** 是 Mathlib 中的一个引理，位于命名
空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：norm_smul_basis (p q : R[X]) : Algebra.norm R[X] (p • (1 : W'.CoordinateRi
ng) + q • mk W' Y) = p ^ 2 - p * q * (C W'.a₁ * X + C W'.a₃) - q ^ 2 * (X ^ 3 + 
C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆)
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_eq_matrix_det`：norm_eq_matrix_det [Fintype ι] [DecidableEq 
ι] (b : Basis ι R S) (s : S) : norm R s = Matrix.det (Algebra.leftMulMatrix b s)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.leftMulMatrix_eq_repr_mul`：leftMulMatrix_eq_repr_mul (x : S) (i 
j) : leftMulMatrix b x i j = b.repr (x * b j) i
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.basis_zero`：basis_zero : Coordina
teRing.basis W' 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.basis_one`：basis_one : Coordinate
Ring.basis W' 1 = mk W' Y
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.smul_basis_mul_Y`：smul_basis_mul_
Y (p q : R[X]) : (p • (1 : W'.CoordinateRing) + q • mk W' Y) * mk W' Y = (q * (X
 ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.repr_self_apply`：repr_self_apply (j) [Decidable (i = j)] : 
b.repr (b i) j = if i = j then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
## Norms on the affine coordinate ring
-/
lemma norm_smul_basis (p q : R[X]) : Algebra.norm R[X] (p • (1 : W'.CoordinateRing) + q • mk W' Y) =
    p ^ 2 - p * q * (C W'.a₁ * X + C W'.a₃) -
      q ^ 2 * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆) := by
  simp_rw [Algebra.norm_eq_matrix_det <| CoordinateRing.basis W', Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, basis_zero, mul_one, basis_one, smul_basis_mul_Y, map_add,
    Finsupp.add_apply, map_smul, Finsupp.smul_apply, ← basis_zero, ← basis_one,
    Basis.repr_self_apply, if_pos, one_ne_zero, if_false, smul_eq_mul]
  ring1
/-
**WeierstrassCurve.Affine.CoordinateRing.coe_norm_smul_basis** 是 Mathlib 中的一个引理，
位于命名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：coe_norm_smul_basis (p q : R[X]) : Algebra.norm R[X] (p • 1 + q • mk W' Y)
 = mk W' ((C p + C q * X) * (C p + C q * (-(Y : R[X][Y]) - C (C W'.a₁ * X + C W'
.a₃))))
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AdjoinRoot.mk_eq_mk`：mk_eq_mk {g h : R[X]} : mk f g = mk f h ↔ f ∣ g - h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis`：norm_smul_basis 
(p q : R[X]) : Algebra.norm R[X] (p • (1 : W'.CoordinateRing) + q • mk W' Y) = p
 ^ 2 - p * q * (C W'.a₁ * X + C W'.a₃) - q ^…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.C_sub`：C_sub : C (a - b) = C a - C b
· 使用定理 `Polynomial.C_pow`：C_pow : C (a ^ n) = C a ^ n
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `Polynomial.C_add`：C_add : C (a + b) = C a + C b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 55 条，此处仅展示前 30 条）
-/
lemma coe_norm_smul_basis (p q : R[X]) : Algebra.norm R[X] (p • 1 + q • mk W' Y) =
    mk W' ((C p + C q * X) * (C p + C q * (-(Y : R[X][Y]) - C (C W'.a₁ * X + C W'.a₃)))) :=
  AdjoinRoot.mk_eq_mk.mpr ⟨C q ^ 2, by simp only [norm_smul_basis, polynomial]; C_simp; ring1⟩
/-
**WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis** 是 Mathlib 中的一个
引理，位于命名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：degree_norm_smul_basis [IsDomain R] (p q : R[X]) : (Algebra.norm R[X] <| p
 • 1 + q • mk W' Y).degree = max (2 • p.degree) (2 • q.degree + 3)
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.degree_pow`：degree_pow [Nontrivial R] (p : R[X]) (n : Nat) : 
degree (p ^ n) = n • degree p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Polynomial.degree_linear_le`：degree_linear_le : degree (C a * X + C b) <
= 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.degree_cubic`：degree_cubic (ha : a != 0) : degree (C a * X ^ 
3 + C b * X ^ 2 + C c * X + C d) = 3
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis`：norm_smul_basis 
(p q : R[X]) : Algebra.norm R[X] (p • (1 : W'.CoordinateRing) + q • mk W' Y) = p
 ^ 2 - p * q * (C W'.a₁ * X + C W'.a₃) - q ^…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
· 使用定理 `max_bot_left`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : OrderBot
 α] (a : α), max ⊥ a = a
（共 100 条，此处仅展示前 30 条）
-/
lemma degree_norm_smul_basis [IsDomain R] (p q : R[X]) :
    (Algebra.norm R[X] <| p • 1 + q • mk W' Y).degree = max (2 • p.degree) (2 • q.degree + 3) := by
  have hdp : (p ^ 2).degree = 2 • p.degree := degree_pow p 2
  have hdpq : (p * q * (C W'.a₁ * X + C W'.a₃)).degree ≤ p.degree + q.degree + 1 := by
    grw [degree_mul, degree_mul, degree_linear_le]
  have hdq :
      (q ^ 2 * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆)).degree = 2 • q.degree + 3 := by
    rw [degree_mul, degree_pow, ← one_mul <| X ^ 3, ← C_1, degree_cubic <| one_ne_zero' R]
  rw [norm_smul_basis]
  by_cases hp : p = 0
  · simp only [hp, hdq, neg_zero, zero_sub, zero_mul, zero_pow two_ne_zero, degree_neg]
    exact (max_bot_left _).symm
  · by_cases hq : q = 0
    · simp only [hq, hdp, sub_zero, zero_mul, mul_zero, zero_pow two_ne_zero]
      exact (max_bot_right _).symm
    · rw [← not_congr degree_eq_bot] at hp hq
      -- Porting note: BUG `cases` tactic does not modify assumptions in `hp'` and `hq'`
      rcases hp' : p.degree with _ | dp -- `hp' : ` should be redundant
      · exact (hp hp').elim -- `hp'` should be `rfl`
      · rw [hp'] at hdp hdpq -- line should be redundant
        rcases hq' : q.degree with _ | dq -- `hq' : ` should be redundant
        · exact (hq hq').elim -- `hq'` should be `rfl`
        · rw [hq'] at hdpq hdq -- line should be redundant
          rcases le_or_gt dp (dq + 1) with hpq | hpq
          · convert!
            (degree_sub_eq_right_of_degree_lt <|
                  (degree_sub_le _ _).trans_lt <|
                    max_lt_iff.mpr ⟨hdp.trans_lt _, hdpq.trans_lt _⟩).trans
              (max_eq_right_of_lt _).symm <;> rw [hdq] <;>
                exact WithBot.coe_lt_coe.mpr <| by dsimp; linarith only [hpq]
          · rw [sub_sub]
            convert!
              (degree_sub_eq_left_of_degree_lt <|
                    (degree_add_le _ _).trans_lt <|
                      max_lt_iff.mpr ⟨hdpq.trans_lt _, hdq.trans_lt _⟩).trans
                (max_eq_left_of_lt _).symm <;> rw [hdp] <;>
                exact WithBot.coe_lt_coe.mpr <| by dsimp; linarith only [hpq]
/-
**WeierstrassCurve.Affine.CoordinateRing.degree_norm_ne_one** 是 Mathlib 中的一个引理，位
于命名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：degree_norm_ne_one [IsDomain R] (x : W'.CoordinateRing) : (Algebra.norm R[
X] x).degree != 1
参数：x : W'.CoordinateRing。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq`：exists_smul
_basis_eq (x : W'.CoordinateRing) : exists p q : R[X], p • (1 : W'.CoordinateRin
g) + q • mk W' Y = x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis`：degree_no
rm_smul_basis [IsDomain R] (p q : R[X]) : (Algebra.norm R[X] <| p • 1 + q • mk W
' Y).degree = max (2 • p.degree) (2 • q.degree + 3)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cmp_eq_lt_iff`：cmp_eq_lt_iff : cmp x y = Ordering.lt ↔ x < y
-/
lemma degree_norm_ne_one [IsDomain R] (x : W'.CoordinateRing) :
    (Algebra.norm R[X] x).degree ≠ 1 := by
  rcases exists_smul_basis_eq x with ⟨p, q, rfl⟩
  rw [degree_norm_smul_basis]
  rcases p.degree with (_ | _ | _ | _) <;> cases q.degree
  any_goals rintro (_ | _)
  exact (lt_max_of_lt_right <| (cmp_eq_lt_iff ..).mp rfl).ne'
/-
**WeierstrassCurve.Affine.CoordinateRing.natDegree_norm_ne_one** 是 Mathlib 中的一个引
理，位于命名空间 `WeierstrassCurve.Affine.CoordinateRing`。
形式化陈述：natDegree_norm_ne_one [IsDomain R] (x : W'.CoordinateRing) : (Algebra.norm
 R[X] x).natDegree != 1
参数：x : W'.CoordinateRing。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.degree_norm_ne_one`：degree_norm_n
e_one [IsDomain R] (x : W'.CoordinateRing) : (Algebra.norm R[X] x).degree != 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.degree_eq_iff_natDegree_eq_of_pos`：degree_eq_iff_natDegree_eq
_of_pos {p : R[X]} {n : Nat} (hn : 0 < n) : p.degree = n ↔ p.natDegree = n
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma natDegree_norm_ne_one [IsDomain R] (x : W'.CoordinateRing) :
    (Algebra.norm R[X] x).natDegree ≠ 1 :=
  degree_norm_ne_one x ∘ (degree_eq_iff_natDegree_eq_of_pos zero_lt_one).mpr

end CoordinateRing

/-! ## Nonsingular points in affine coordinates -/

variable (W') in
/-- A nonsingular point on a Weierstrass curve `W` in affine coordinates. This is either the unique
point at infinity `WeierstrassCurve.Affine.Point.zero` or a nonsingular affine point
`WeierstrassCurve.Affine.Point.some (x, y)` satisfying the Weierstrass equation of `W`. -/
/-
**WeierstrassCurve.Affine.Point** 是 Mathlib 中的一个归纳类型，位于命名空间 `WeierstrassCurve.Af
fine`。
形式化陈述：{R : Type r} → [CommRing R] → WeierstrassCurve.Affine R → Type r
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonsingular point on a Weierstrass curve `W` in affine coordinates. This is ei
ther the unique
point at infinity `WeierstrassCurve.Affine.Point.zero` or a nonsingular affine p
oint
`WeierstrassCurve.Affine.Point.some (x, y)` satisfying the Weierstrass equation 
of `W`.
-/
inductive Point
  | zero
  | some (x y : R) (h : W'.Nonsingular x y)
deriving DecidableEq

/-- The equivalence between the nonsingular points on a Weierstrass curve `W` in affine coordinates
satisfying a predicate and the set of pairs `⟨x, y⟩` satisfying `W.Nonsingular x y` with zero. -/
/-
**WeierstrassCurve.Affine.nonsingularPointEquivSubtype** 是 Mathlib 中的一个定义，位于命名空间
 `WeierstrassCurve.Affine`。
形式化陈述：nonsingularPointEquivSubtype {p : W'.Point -> Prop} (p0 : p .zero) : {P : 
W'.Point // p P} ≃ WithZero {xy : R × R // exists h : W'.Nonsingular xy.fst xy.s
nd, p <| .some _ _ h} where toFun | ⟨.zero, _⟩ => none | ⟨.some _ _ h, ph⟩ => .s
ome ⟨⟨_, _⟩, h, ph⟩ invFun P
参数：p0 : p .zero。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the nonsingular points on a Weierstrass curve `W` in aff
ine coordinates
satisfying a predicate and the set of pairs `⟨x, y⟩` satisfying `W.Nonsingular x
 y` with zero.
-/
def nonsingularPointEquivSubtype {p : W'.Point → Prop} (p0 : p .zero) : {P : W'.Point // p P} ≃
    WithZero {xy : R × R // ∃ h : W'.Nonsingular xy.fst xy.snd, p <| .some _ _ h} where
  toFun
    | ⟨.zero, _⟩ => none
    | ⟨.some _ _ h, ph⟩ => .some ⟨⟨_, _⟩, h, ph⟩
  invFun P := P.casesOn ⟨.zero, p0⟩ fun xy => ⟨.some _ _ xy.prop.choose, xy.prop.choose_spec⟩
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

@[simp]
/-
**WeierstrassCurve.Affine.nonsingularPointEquivSubtype_zero** 是 Mathlib 中的一个引理，位
于命名空间 `WeierstrassCurve.Affine`。
形式化陈述：nonsingularPointEquivSubtype_zero {p : W'.Point -> Prop} (p0 : p .zero) : 
nonsingularPointEquivSubtype p0 ⟨.zero, p0⟩ = none
参数：p0 : p .zero。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nonsingularPointEquivSubtype_zero {p : W'.Point → Prop} (p0 : p .zero) :
    nonsingularPointEquivSubtype p0 ⟨.zero, p0⟩ = none :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.nonsingularPointEquivSubtype_some** 是 Mathlib 中的一个引理，位
于命名空间 `WeierstrassCurve.Affine`。
形式化陈述：nonsingularPointEquivSubtype_some {x y : R} {h : W'.Nonsingular x y} {p : 
W'.Point -> Prop} (p0 : p .zero) (ph : p <| .some _ _ h) : nonsingularPointEquiv
Subtype p0 ⟨.some _ _ h, ph⟩ = .some ⟨⟨x, y⟩, h, ph⟩
参数：p0 : p .zero；ph : p <| .some _ _ h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nonsingularPointEquivSubtype_some {x y : R} {h : W'.Nonsingular x y} {p : W'.Point → Prop}
    (p0 : p .zero) (ph : p <| .some _ _ h) :
    nonsingularPointEquivSubtype p0 ⟨.some _ _ h, ph⟩ = .some ⟨⟨x, y⟩, h, ph⟩ :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.nonsingularPointEquivSubtype_symm_none** 是 Mathlib 中的一
个引理，位于命名空间 `WeierstrassCurve.Affine`。
形式化陈述：nonsingularPointEquivSubtype_symm_none {p : W'.Point -> Prop} (p0 : p .zer
o) : (nonsingularPointEquivSubtype p0).symm none = ⟨.zero, p0⟩
参数：p0 : p .zero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma nonsingularPointEquivSubtype_symm_none {p : W'.Point → Prop} (p0 : p .zero) :
    (nonsingularPointEquivSubtype p0).symm none = ⟨.zero, p0⟩ :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.nonsingularPointEquivSubtype_symm_some** 是 Mathlib 中的一
个引理，位于命名空间 `WeierstrassCurve.Affine`。
形式化陈述：nonsingularPointEquivSubtype_symm_some {x y : R} {h : W'.Nonsingular x y} 
{p : W'.Point -> Prop} (p0 : p .zero) (ph : p <| .some _ _ h) : (nonsingularPoin
tEquivSubtype p0).symm (.some ⟨⟨x, y⟩, h, ph⟩) = ⟨.some _ _ h, ph⟩
参数：p0 : p .zero；ph : p <| .some _ _ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma nonsingularPointEquivSubtype_symm_some {x y : R} {h : W'.Nonsingular x y}
    {p : W'.Point → Prop} (p0 : p .zero) (ph : p <| .some _ _ h) :
    (nonsingularPointEquivSubtype p0).symm (.some ⟨⟨x, y⟩, h, ph⟩) = ⟨.some _ _ h, ph⟩ :=
  rfl

variable (W') in
/-- The equivalence between the nonsingular points on a Weierstrass curve `W` in affine coordinates
and the set of pairs `⟨x, y⟩` satisfying `W.Nonsingular x y` with zero. -/
/-
**WeierstrassCurve.Affine.nonsingularPointEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Weier
strassCurve.Affine`。
形式化陈述：nonsingularPointEquiv : W'.Point ≃ WithZero {xy : R × R // W'.Nonsingular 
xy.fst xy.snd}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `trivial`：True

--- 原说明 ---
The equivalence between the nonsingular points on a Weierstrass curve `W` in aff
ine coordinates
and the set of pairs `⟨x, y⟩` satisfying `W.Nonsingular x y` with zero.
-/
def nonsingularPointEquiv : W'.Point ≃ WithZero {xy : R × R // W'.Nonsingular xy.fst xy.snd} :=
  (Equiv.Set.univ W'.Point).symm.trans <| (nonsingularPointEquivSubtype trivial).trans
    (Equiv.subtypeEquivProp <| by simp).optionCongr

@[simp]
/-
**WeierstrassCurve.Affine.nonsingularPointEquiv_zero** 是 Mathlib 中的一个引理，位于命名空间 `
WeierstrassCurve.Affine`。
形式化陈述：nonsingularPointEquiv_zero : nonsingularPointEquiv W' .zero = none
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nonsingularPointEquiv_zero : nonsingularPointEquiv W' .zero = none :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.nonsingularPointEquiv_some** 是 Mathlib 中的一个引理，位于命名空间 `
WeierstrassCurve.Affine`。
形式化陈述：nonsingularPointEquiv_some {x y : R} (h : W'.Nonsingular x y) : W'.nonsing
ularPointEquiv (.some _ _ h) = .some ⟨⟨x, y⟩, h⟩
参数：h : W'.Nonsingular x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nonsingularPointEquiv_some {x y : R} (h : W'.Nonsingular x y) :
    W'.nonsingularPointEquiv (.some _ _ h) = .some ⟨⟨x, y⟩, h⟩ := by
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.nonsingularPointEquiv_symm_none** 是 Mathlib 中的一个引理，位于命
名空间 `WeierstrassCurve.Affine`。
形式化陈述：nonsingularPointEquiv_symm_none : W'.nonsingularPointEquiv.symm none = .ze
ro
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma nonsingularPointEquiv_symm_none : W'.nonsingularPointEquiv.symm none = .zero :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.nonsingularPointEquiv_symm_some** 是 Mathlib 中的一个引理，位于命
名空间 `WeierstrassCurve.Affine`。
形式化陈述：nonsingularPointEquiv_symm_some {x y : R} (h : W'.Nonsingular x y) : W'.no
nsingularPointEquiv.symm (.some ⟨⟨x, y⟩, h⟩) = .some _ _ h
参数：h : W'.Nonsingular x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma nonsingularPointEquiv_symm_some {x y : R} (h : W'.Nonsingular x y) :
    W'.nonsingularPointEquiv.symm (.some ⟨⟨x, y⟩, h⟩) = .some _ _ h :=
  rfl

section IsElliptic

variable [Nontrivial R] [W'.IsElliptic]

/-- A point on an elliptic curve `W` over `R`. -/
/-
**WeierstrassCurve.Affine.Point.mk** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve.A
ffine.Point`。
形式化陈述：{R : Type r} →   [inst : CommRing R] →     {W' : WeierstrassCurve.Affine R
} →       [Nontrivial R] → [WeierstrassCurve.IsElliptic W'] → {x y : R} → W'.Equ
ation x y → W'.Point
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A point on an elliptic curve `W` over `R`.
-/
def Point.mk {x y : R} (h : W'.Equation x y) : W'.Point :=
  .some _ _ <| equation_iff_nonsingular.mp h

/-- The equivalence between the points on an elliptic curve `W` in affine coordinates satisfying a
predicate and the set of pairs `⟨x, y⟩` satisfying `W.Equation x y` with zero. -/
/-
**WeierstrassCurve.Affine.pointEquivSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Weierstra
ssCurve.Affine`。
形式化陈述：pointEquivSubtype {p : W'.Point -> Prop} (p0 : p .zero) : {P : W'.Point //
 p P} ≃ WithZero {xy : R × R // exists h : W'.Equation xy.fst xy.snd, p <| .mk h
}
参数：p0 : p .zero。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The equivalence between the points on an elliptic curve `W` in affine coordinate
s satisfying a
predicate and the set of pairs `⟨x, y⟩` satisfying `W.Equation x y` with zero.
-/
def pointEquivSubtype {p : W'.Point → Prop} (p0 : p .zero) :
    {P : W'.Point // p P} ≃ WithZero {xy : R × R // ∃ h : W'.Equation xy.fst xy.snd, p <| .mk h} :=
  (nonsingularPointEquivSubtype p0).trans
    (Equiv.subtypeEquivProp <| by ext; simp [equation_iff_nonsingular, Point.mk]).optionCongr

@[simp]
/-
**WeierstrassCurve.Affine.pointEquivSubtype_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Affine`。
形式化陈述：pointEquivSubtype_zero {p : W'.Point -> Prop} (p0 : p .zero) : pointEquivS
ubtype p0 ⟨.zero, p0⟩ = none
参数：p0 : p .zero。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pointEquivSubtype_zero {p : W'.Point → Prop} (p0 : p .zero) :
    pointEquivSubtype p0 ⟨.zero, p0⟩ = none :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.pointEquivSubtype_some** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Affine`。
形式化陈述：pointEquivSubtype_some {x y : R} {h : W'.Equation x y} {p : W'.Point -> Pr
op} (p0 : p .zero) (ph : p <| .mk h) : pointEquivSubtype p0 ⟨.mk h, ph⟩ = .some 
⟨⟨x, y⟩, h, ph⟩
参数：p0 : p .zero；ph : p <| .mk h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pointEquivSubtype_some {x y : R} {h : W'.Equation x y} {p : W'.Point → Prop} (p0 : p .zero)
    (ph : p <| .mk h) : pointEquivSubtype p0 ⟨.mk h, ph⟩ = .some ⟨⟨x, y⟩, h, ph⟩ :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.pointEquivSubtype_symm_none** 是 Mathlib 中的一个引理，位于命名空间 
`WeierstrassCurve.Affine`。
形式化陈述：pointEquivSubtype_symm_none {p : W'.Point -> Prop} (p0 : p .zero) : (point
EquivSubtype p0).symm none = ⟨.zero, p0⟩
参数：p0 : p .zero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma pointEquivSubtype_symm_none {p : W'.Point → Prop} (p0 : p .zero) :
    (pointEquivSubtype p0).symm none = ⟨.zero, p0⟩ :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.pointEquivSubtype_symm_some** 是 Mathlib 中的一个引理，位于命名空间 
`WeierstrassCurve.Affine`。
形式化陈述：pointEquivSubtype_symm_some {x y : R} {h : W'.Equation x y} {p : W'.Point 
-> Prop} (p0 : p .zero) (ph : p <| .mk h) : (pointEquivSubtype p0).symm (.some ⟨
⟨x, y⟩, h, ph⟩) = ⟨.mk h, ph⟩
参数：p0 : p .zero；ph : p <| .mk h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma pointEquivSubtype_symm_some {x y : R} {h : W'.Equation x y} {p : W'.Point → Prop}
    (p0 : p .zero) (ph : p <| .mk h) :
    (pointEquivSubtype p0).symm (.some ⟨⟨x, y⟩, h, ph⟩) = ⟨.mk h, ph⟩ :=
  rfl

variable (W') in
/-- The equivalence between the rational points on an elliptic curve `E` and the set of pairs
`⟨x, y⟩` satisfying `E.Equation x y` with zero. -/
/-
**WeierstrassCurve.Affine.pointEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve
.Affine`。
形式化陈述：pointEquiv : W'.Point ≃ WithZero {xy : R × R // W'.Equation xy.fst xy.snd}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `trivial`：True

--- 原说明 ---
The equivalence between the rational points on an elliptic curve `E` and the set
 of pairs
`⟨x, y⟩` satisfying `E.Equation x y` with zero.
-/
def pointEquiv : W'.Point ≃ WithZero {xy : R × R // W'.Equation xy.fst xy.snd} :=
  (Equiv.Set.univ W'.Point).symm.trans <| (pointEquivSubtype trivial).trans
    (Equiv.subtypeEquivProp <| by simp).optionCongr

@[simp]
/-
**WeierstrassCurve.Affine.pointEquiv_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Affine`。
形式化陈述：pointEquiv_zero : W'.pointEquiv .zero = none
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pointEquiv_zero : W'.pointEquiv .zero = none :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.pointEquiv_some** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Affine`。
形式化陈述：pointEquiv_some {x y : R} (h : W'.Equation x y) : pointEquiv W' (.mk h) = 
.some ⟨⟨x, y⟩, h⟩
参数：h : W'.Equation x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pointEquiv_some {x y : R} (h : W'.Equation x y) :
    pointEquiv W' (.mk h) = .some ⟨⟨x, y⟩, h⟩ := by
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.pointEquiv_symm_none** 是 Mathlib 中的一个引理，位于命名空间 `Weiers
trassCurve.Affine`。
形式化陈述：pointEquiv_symm_none : (pointEquiv W').symm none = .zero
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma pointEquiv_symm_none : (pointEquiv W').symm none = .zero :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.pointEquiv_symm_some** 是 Mathlib 中的一个引理，位于命名空间 `Weiers
trassCurve.Affine`。
形式化陈述：pointEquiv_symm_some {x y : R} (h : W'.Equation x y) : (pointEquiv W').sym
m (.some ⟨⟨x, y⟩, h⟩) = .mk h
参数：h : W'.Equation x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma pointEquiv_symm_some {x y : R} (h : W'.Equation x y) :
    (pointEquiv W').symm (.some ⟨⟨x, y⟩, h⟩) = .mk h :=
  rfl

end IsElliptic

namespace Point

/-! ## Group law in affine coordinates -/

/-
**WeierstrassCurve.Affine.Point.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.Aff
ine.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## Group law in affine coordinates
-/
instance : Inhabited W'.Point :=
  ⟨zero⟩
/-
**WeierstrassCurve.Affine.Point.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.Aff
ine.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero W'.Point :=
  ⟨zero⟩
/-
**WeierstrassCurve.Affine.Point.zero_def** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Affine.Point`。
形式化陈述：zero_def : 0 = (zero : W'.Point)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_def : 0 = (zero : W'.Point) :=
  rfl
/-
**WeierstrassCurve.Affine.Point.some_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Affine.Point`。
形式化陈述：some_ne_zero {x y : R} (h : W'.Nonsingular x y) : some _ _ h != 0
参数：h : W'.Nonsingular x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma some_ne_zero {x y : R} (h : W'.Nonsingular x y) : some _ _ h ≠ 0 := by
  rintro (_ | _)

/-- The negation of a nonsingular point on a Weierstrass curve in affine coordinates.

Given a nonsingular point `P` in affine coordinates, use `-P` instead of `neg P`. -/
/-
**WeierstrassCurve.Affine.Point.neg** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve.
Affine.Point`。
形式化陈述：{R : Type r} → [inst : CommRing R] → {W' : WeierstrassCurve.Affine R} → W'
.Point → W'.Point
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The negation of a nonsingular point on a Weierstrass curve in affine coordinates
.

Given a nonsingular point `P` in affine coordinates, use `-P` instead of `neg P`
.
-/
def neg : W'.Point → W'.Point
  | 0 => 0
  | some _ _ h => some _ _ <| (nonsingular_neg ..).mpr h
/-
**WeierstrassCurve.Affine.Point.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.Aff
ine.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg W'.Point :=
  ⟨neg⟩
/-
**WeierstrassCurve.Affine.Point.neg_def** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCu
rve.Affine.Point`。
形式化陈述：neg_def (P : W'.Point) : -P = P.neg
参数：P : W'.Point。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_def (P : W'.Point) : -P = P.neg :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.Point.neg_zero** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Affine.Point`。
形式化陈述：neg_zero : (-0 : W'.Point) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_zero : (-0 : W'.Point) = 0 :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.Point.neg_some** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Affine.Point`。
形式化陈述：neg_some {x y : R} (h : W'.Nonsingular x y) : -some _ _ h = some _ _ ((non
singular_neg ..).mpr h)
参数：h : W'.Nonsingular x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_some {x y : R} (h : W'.Nonsingular x y) :
    -some _ _ h = some _ _ ((nonsingular_neg ..).mpr h) :=
  rfl
/-
**WeierstrassCurve.Affine.Point.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.Aff
ine.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InvolutiveNeg W'.Point where
  neg_neg := by
    rintro (_ | _)
    · rfl
    · simp only [neg_some, negY_negY]
/-
**WeierstrassCurve.Affine.Point.X_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Affine.Point`。
形式化陈述：X_eq_iff {x₁ y₁ x₂ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular 
x₂ y₂} : x₁ = x₂ ↔ some x₁ y₁ h₁ = some x₂ y₂ h₂ ∨ some x₁ y₁ h₁ = -some x₂ y₂ h
₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WeierstrassCurve.Affine.nonsingular_neg`：nonsingular_neg (x y : R) : W'.
Nonsingular x (W'.negY x y) ↔ W'.Nonsingular x y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.Affine.Point.some.injEq`：∀ {R : Type r} [inst : CommRin
g R] {W' : WeierstrassCurve.Affine R} (x y : R) (h : W'.Nonsingular x y) (x_1 y_
1 : R)   (h_1 : W'.Nonsingular…
· 使用引理 `WeierstrassCurve.Affine.Y_eq_of_X_eq`：Y_eq_of_X_eq {x₁ x₂ y₁ y₂ : F} (h₁
 : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hx : x₁ = x₂) : y₁ = y₂ ∨ y₁ = W.n
egY x₂ y₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma X_eq_iff {x₁ y₁ x₂ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} :
    x₁ = x₂ ↔ some x₁ y₁ h₁ = some x₂ y₂ h₂ ∨ some x₁ y₁ h₁ = -some x₂ y₂ h₂ := by
  refine ⟨fun H ↦ ?_, fun H ↦ by grind [neg_some]⟩
  simp_rw [neg_some, some.injEq, ← and_or_left]
  exact ⟨H, Y_eq_of_X_eq h₁.1 h₂.1 H⟩

variable [DecidableEq F] [DecidableEq K] [DecidableEq L]

/-- The addition of two nonsingular points on a Weierstrass curve in affine coordinates.

Given two nonsingular points `P` and `Q` in affine coordinates, use `P + Q` instead of `add P Q`. -/
/-
**WeierstrassCurve.Affine.Point.add** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve.
Affine.Point`。
形式化陈述：{F : Type u} → [inst : Field F] → {W : WeierstrassCurve.Affine F} → [Decid
ableEq F] → W.Point → W.Point → W.Point
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Affine.nonsingular_add`：nonsingular_add {x₁ x₂ y₁ y₂ : 
F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ =
 W.negY x₂ y₂)) : W.Nonsingul…

--- 原说明 ---
The addition of two nonsingular points on a Weierstrass curve in affine coordina
tes.

Given two nonsingular points `P` and `Q` in affine coordinates, use `P + Q` inst
ead of `add P Q`.
-/
def add : W.Point → W.Point → W.Point
  | 0, P => P
  | P, 0 => P
  | some x₁ y₁ h₁, some x₂ y₂ h₂ =>
    if hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then 0 else some _ _ <| nonsingular_add h₁ h₂ hxy
/-
**WeierstrassCurve.Affine.Point.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.Aff
ine.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add W.Point :=
  ⟨add⟩
/-
**WeierstrassCurve.Affine.Point.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.Aff
ine.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddZeroClass W.Point where
  zero_add := by rintro (_ | _) <;> rfl
  add_zero := by rintro (_ | _) <;> rfl
/-
**WeierstrassCurve.Affine.Point.add_def** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCu
rve.Affine.Point`。
形式化陈述：add_def (P Q : W.Point) : P + Q = P.add Q
参数：P Q : W.Point。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_def (P Q : W.Point) : P + Q = P.add Q :=
  rfl
/-
**WeierstrassCurve.Affine.Point.add_some** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Affine.Point`。
形式化陈述：add_some {x₁ x₂ y₁ y₂ : F} (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) {h₁ : W.
Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} : some _ _ h₁ + some _ _ h₂ = some
 _ _ (nonsingular_add h₁ h₂ hxy)
参数：hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `WeierstrassCurve.Affine.nonsingular_add`：nonsingular_add {x₁ x₂ y₁ y₂ : 
F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ =
 W.negY x₂ y₂)) : W.Nonsingul…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_some {x₁ x₂ y₁ y₂ : F} (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) {h₁ : W.Nonsingular x₁ y₁}
    {h₂ : W.Nonsingular x₂ y₂} :
    some _ _ h₁ + some _ _ h₂ = some _ _ (nonsingular_add h₁ h₂ hxy) := by
  simp only [add_def, add, dif_neg hxy]

@[simp]
/-
**WeierstrassCurve.Affine.Point.add_of_Y_eq** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Affine.Point`。
形式化陈述：add_of_Y_eq {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingul
ar x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) : some _ _ h₁ + some _ _ h₂ = 
0
参数：hx : x₁ = x₂；hy : y₁ = W.negY x₂ y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `WeierstrassCurve.Affine.nonsingular_add`：nonsingular_add {x₁ x₂ y₁ y₂ : 
F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ =
 W.negY x₂ y₂)) : W.Nonsingul…
-/
lemma add_of_Y_eq {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) : some _ _ h₁ + some _ _ h₂ = 0 := by
  simpa only [add_def, add] using dif_pos ⟨hx, hy⟩

-- Removing `@[simp]`, because `hy` causes a maximum recursion depth error in the simpNF linter.
/-
**WeierstrassCurve.Affine.Point.add_self_of_Y_eq** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Affine.Point`。
形式化陈述：add_self_of_Y_eq {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ = W.negY 
x₁ y₁) : some _ _ h₁ + some _ _ h₁ = 0
参数：hy : y₁ = W.negY x₁ y₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Affine.Point.add_of_Y_eq`：add_of_Y_eq {x₁ x₂ y₁ y₂ : F}
 {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ =
 W.negY x₂ y₂) : some _ _ h₁ + …
-/
lemma add_self_of_Y_eq {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ = W.negY x₁ y₁) :
    some _ _ h₁ + some _ _ h₁ = 0 :=
  add_of_Y_eq rfl hy

-- @[simp] -- Not a good simp lemma, since `hy` is not in simp normal form.
/-
**WeierstrassCurve.Affine.Point.add_of_Y_ne** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Affine.Point`。
形式化陈述：add_of_Y_ne {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingul
ar x₂ y₂} (hy : y₁ != W.negY x₂ y₂) : some _ _ h₁ + some _ _ h₂ = some _ _ (nons
ingular_add h₁ h₂ fun hxy => hy hxy.right)
参数：hy : y₁ != W.negY x₂ y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Affine.Point.add_some`：add_some {x₁ x₂ y₁ y₂ : F} (hxy 
: ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular
 x₂ y₂} : some _ _ h₁ + some…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma add_of_Y_ne {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hy : y₁ ≠ W.negY x₂ y₂) :
    some _ _ h₁ + some _ _ h₂ = some _ _ (nonsingular_add h₁ h₂ fun hxy => hy hxy.right) :=
  add_some fun hxy => hy hxy.right
/-
**WeierstrassCurve.Affine.Point.add_of_Y_ne'** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Affine.Point`。
形式化陈述：add_of_Y_ne' {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingu
lar x₂ y₂} (hy : y₁ != W.negY x₂ y₂) : some _ _ h₁ + some _ _ h₂ = -some _ _ (no
nsingular_negAdd h₁ h₂ fun hxy => hy hxy.right)
参数：hy : y₁ != W.negY x₂ y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Affine.Point.add_of_Y_ne`：add_of_Y_ne {x₁ x₂ y₁ y₂ : F}
 {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} (hy : y₁ != W.negY x₂ y₂)
 : some _ _ h₁ + some _ _ h₂ = …
-/
lemma add_of_Y_ne' {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hy : y₁ ≠ W.negY x₂ y₂) :
    some _ _ h₁ + some _ _ h₂ = -some _ _ (nonsingular_negAdd h₁ h₂ fun hxy => hy hxy.right) :=
  add_of_Y_ne hy

-- @[simp] -- Not a good simp lemma, since `hy` is not in simp normal form.
/-
**WeierstrassCurve.Affine.Point.add_self_of_Y_ne** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Affine.Point`。
形式化陈述：add_self_of_Y_ne {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ != W.negY
 x₁ y₁) : some _ _ h₁ + some _ _ h₁ = some _ _ (nonsingular_add h₁ h₁ fun hxy =>
 hy hxy.right)
参数：hy : y₁ != W.negY x₁ y₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Affine.Point.add_of_Y_ne`：add_of_Y_ne {x₁ x₂ y₁ y₂ : F}
 {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} (hy : y₁ != W.negY x₂ y₂)
 : some _ _ h₁ + some _ _ h₂ = …
-/
lemma add_self_of_Y_ne {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ ≠ W.negY x₁ y₁) :
    some _ _ h₁ + some _ _ h₁ = some _ _ (nonsingular_add h₁ h₁ fun hxy => hy hxy.right) :=
  add_of_Y_ne hy
/-
**WeierstrassCurve.Affine.Point.add_self_of_Y_ne'** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Affine.Point`。
形式化陈述：add_self_of_Y_ne' {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ != W.neg
Y x₁ y₁) : some _ _ h₁ + some _ _ h₁ = -some _ _ (nonsingular_negAdd h₁ h₁ fun h
xy => hy hxy.right)
参数：hy : y₁ != W.negY x₁ y₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Affine.Point.add_of_Y_ne`：add_of_Y_ne {x₁ x₂ y₁ y₂ : F}
 {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} (hy : y₁ != W.negY x₂ y₂)
 : some _ _ h₁ + some _ _ h₂ = …
-/
lemma add_self_of_Y_ne' {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ ≠ W.negY x₁ y₁) :
    some _ _ h₁ + some _ _ h₁ = -some _ _ (nonsingular_negAdd h₁ h₁ fun hxy => hy hxy.right) :=
  add_of_Y_ne hy

@[simp]
/-
**WeierstrassCurve.Affine.Point.add_of_X_ne** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Affine.Point`。
形式化陈述：add_of_X_ne {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingul
ar x₂ y₂} (hx : x₁ != x₂) : some _ _ h₁ + some _ _ h₂ = some _ _ (nonsingular_ad
d h₁ h₂ fun hxy => hx hxy.left)
参数：hx : x₁ != x₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Affine.Point.add_some`：add_some {x₁ x₂ y₁ y₂ : F} (hxy 
: ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular
 x₂ y₂} : some _ _ h₁ + some…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma add_of_X_ne {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    some _ _ h₁ + some _ _ h₂ = some _ _ (nonsingular_add h₁ h₂ fun hxy => hx hxy.left) :=
  add_some fun hxy => hx hxy.left
/-
**WeierstrassCurve.Affine.Point.add_of_X_ne'** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Affine.Point`。
形式化陈述：add_of_X_ne' {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingu
lar x₂ y₂} (hx : x₁ != x₂) : some _ _ h₁ + some _ _ h₂ = -some _ _ (nonsingular_
negAdd h₁ h₂ fun hxy => hx hxy.left)
参数：hx : x₁ != x₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Affine.Point.add_of_X_ne`：add_of_X_ne {x₁ x₂ y₁ y₂ : F}
 {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} (hx : x₁ != x₂) : some _ 
_ h₁ + some _ _ h₂ = some _ _ (…
-/
lemma add_of_X_ne' {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    some _ _ h₁ + some _ _ h₂ = -some _ _ (nonsingular_negAdd h₁ h₂ fun hxy => hx hxy.left) :=
  add_of_X_ne hx

set_option backward.isDefEq.respectTransparency.types false in
/-- The group homomorphism mapping a nonsingular affine point `(x, y)` of a Weierstrass curve `W` to
the class of the non-zero fractional ideal `⟨X - x, Y - y⟩` in the ideal class group of `F[W]`. -/
@[simps]
/-
**WeierstrassCurve.Affine.Point.toClass** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCu
rve.Affine.Point`。
形式化陈述：toClass : W.Point ->+ Additive (ClassGroup W.CoordinateRing) where toFun P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group homomorphism mapping a nonsingular affine point `(x, y)` of a Weierstr
ass curve `W` to
the class of the non-zero fractional ideal `⟨X - x, Y - y⟩` in the ideal class g
roup of `F[W]`.
-/
noncomputable def toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing) where
  toFun P := match P with
    | 0 => 0
    | some _ _ h => ClassGroup.mk W.FunctionField <| CoordinateRing.XYIdeal' h
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals simp only [← zero_def, zero_add, add_zero]
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
    · simp only [hxy.left, hxy.right, add_of_Y_eq rfl rfl]
      exact (CoordinateRing.mk_XYIdeal'_neg_mul h₂).symm
    · simp only [add_some hxy]
      exact (CoordinateRing.mk_XYIdeal'_mul_mk_XYIdeal' h₁ h₂ hxy).symm
/-
**WeierstrassCurve.Affine.Point.toClass_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Affine.Point`。
形式化陈述：toClass_zero : toClass (0 : W.Point) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.instIsDomain`：∀ {R : Type r} [ins
t : CommRing R] {W' : WeierstrassCurve.Affine R} [IsDomain R], IsDomain W'.Coord
inateRing
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
lemma toClass_zero : toClass (0 : W.Point) = 0 :=
  rfl

-- note: giving `W` to `XYIdeal'` explicitly hugely speeds up elaboration for some reason.
-- see https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Field.20.28FunctionField.20.3Fm.2E19.29/near/594011283
/-
**WeierstrassCurve.Affine.Point.toClass_some** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Affine.Point`。
形式化陈述：toClass_some {x y : F} (h : W.Nonsingular x y) : toClass (some _ _ h) = Cl
assGroup.mk W.FunctionField (CoordinateRing.XYIdeal' (W
参数：h : W.Nonsingular x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.instIsDomain`：∀ {R : Type r} [ins
t : CommRing R] {W' : WeierstrassCurve.Affine R} [IsDomain R], IsDomain W'.Coord
inateRing
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
lemma toClass_some {x y : F} (h : W.Nonsingular x y) :
    toClass (some _ _ h) = ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' (W := W) h) :=
  rfl
/-
**WeierstrassCurve.Affine.Point.add_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstra
ssCurve.Affine.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma add_eq_zero (P Q : W.Point) : P + Q = 0 ↔ P = -Q := by
  rcases P, Q with ⟨_ | ⟨x₁, y₁, _⟩, _ | ⟨x₂, y₂, _⟩⟩
  any_goals rfl
  · rw [← zero_def, zero_add, eq_comm (a := 0), neg_eq_iff_eq_neg, neg_zero]
  · rw [neg_some, some.injEq]
    constructor
    · contrapose
      exact fun hxy => by simpa only [add_some hxy] using some_ne_zero _
    · exact fun ⟨hx, hy⟩ => add_of_Y_eq hx hy
/-
**WeierstrassCurve.Affine.Point.toClass_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.Affine.Point`。
形式化陈述：toClass_eq_zero (P : W.Point) : toClass P = 0 ↔ P = 0
参数：P : W.Point。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.instIsDomain`：∀ {R : Type r} [ins
t : CommRing R] {W' : WeierstrassCurve.Affine R} [IsDomain R], IsDomain W'.Coord
inateRing
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ClassGroup.mk_eq_one_of_coe_ideal`：ClassGroup.mk_eq_one_of_coe_ideal {I 
: (FractionalIdeal R⁰ <| FractionRing R)ˣ} {I' : Ideal R} (hI : (I : FractionalI
deal R⁰ <| FractionRing…
· 使用引理 `WeierstrassCurve.Affine.CoordinateRing.natDegree_norm_ne_one`：natDegree_
norm_ne_one [IsDomain R] (x : W'.CoordinateRing) : (Algebra.norm R[X] x).natDegr
ee != 1
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finrank_quotient_span_eq_natDegree_norm`：finrank_quotient_span_eq_natDeg
ree_norm [Algebra F S] [IsScalarTower F F[X] S] (b : Basis ι F[X] S) {f : S} (hf
 : f != 0) : Module.finrank F…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.instIsScalarTowerPolynomial`：∀ {R
 : Type r} [inst : CommRing R] {W' : WeierstrassCurve.Affine R}, IsScalarTower R
 (Polynomial R) W'.CoordinateRing
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma toClass_eq_zero (P : W.Point) : toClass P = 0 ↔ P = 0 := by
  constructor
  · intro hP
    rcases P with (_ | ⟨_, _, h, _⟩)
    · rfl
    · rcases (ClassGroup.mk_eq_one_of_coe_ideal <| by rfl).mp hP with ⟨p, h0, hp⟩
      apply (p.natDegree_norm_ne_one _).elim
      rw [← finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) h0,
        ← (quotientEquivAlgOfEq F hp).toLinearEquiv.finrank_eq,
        (CoordinateRing.quotientXYIdealEquiv h).toLinearEquiv.finrank_eq, Module.finrank_self]
  · exact congr_arg toClass
/-
**WeierstrassCurve.Affine.Point.toClass_injective** 是 Mathlib 中的一个引理，位于命名空间 `Wei
erstrassCurve.Affine.Point`。
形式化陈述：toClass_injective : Function.Injective toClass (W
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.instIsDomain`：∀ {R : Type r} [ins
t : CommRing R] {W' : WeierstrassCurve.Affine R} [IsDomain R], IsDomain W'.Coord
inateRing
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `_private.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point.0.Weierstr
assCurve.Affine.Point.add_eq_zero`：∀ {F : Type u} [inst : Field F] {W : Weierstr
assCurve.Affine F} [inst_1 : DecidableEq F] (P Q : W.Point),   P + Q = 0 ↔ P = -
Q
· 使用引理 `WeierstrassCurve.Affine.Point.toClass_eq_zero`：toClass_eq_zero (P : W.Po
int) : toClass P = 0 ↔ P = 0
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `WeierstrassCurve.Affine.CoordinateRing.mk_XYIdeal'_neg_mul`：∀ {F : Type 
u} [inst : Field F] {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular
 x y),   (ClassGroup.mk W.FunctionField) (Weiers…
-/
lemma toClass_injective : Function.Injective <| toClass (W := W) := by
  rintro (_ | ⟨_, _, h⟩) _ hP
  all_goals rw [← neg_inj, ← add_eq_zero, ← toClass_eq_zero, map_add, ← hP]
  · exact zero_add 0
  · exact CoordinateRing.mk_XYIdeal'_neg_mul h
/-
**WeierstrassCurve.Affine.Point.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.Aff
ine.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommSemigroup W.Point where
  add_comm _ _ := toClass_injective <| by simp only [map_add, add_comm]
  add_assoc _ _ _ := toClass_injective <| by simp only [map_add, add_assoc]
/-
**WeierstrassCurve.Affine.Point.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.Aff
ine.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup W.Point where
  nsmul := nsmulBinRec
  nsmul_succ := nsmulBinRec_succ
  zsmul := zsmulRec nsmulBinRec
  zsmul_succ' := nsmulBinRec_succ
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel _ := by rw [add_eq_zero]

/-! ## Maps and base changes -/

variable [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] [Algebra R L] [Algebra S L] [IsScalarTower R S L] (f : F →ₐ[S] K)
  (g : K →ₐ[S] L)

/-- The group homomorphism on nonsingular points induced by an algebra homomorphism `f : F →ₐ[S] K`,
where `W` is defined over a subring of a ring `S`, and `F` and `K` are field extensions of `S`. -/
/-
**WeierstrassCurve.Affine.Point.map** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve.
Affine.Point`。
形式化陈述：map : (W'⁄F).Point ->+ (W'⁄K).Point where toFun P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group homomorphism on nonsingular points induced by an algebra homomorphism 
`f : F →ₐ[S] K`,
where `W` is defined over a subring of a ring `S`, and `F` and `K` are field ext
ensions of `S`.
-/
noncomputable def map : (W'⁄F).Point →+ (W'⁄K).Point where
  toFun P := match P with
    | 0 => 0
    | some _ _ h => some _ _ <| (W'.baseChange_nonsingular f.injective ..).mpr h
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = (W'⁄F).negY x₂ y₂
    · rw [add_of_Y_eq hxy.left hxy.right,
        add_of_Y_eq (congr_arg _ hxy.left) <| by rw [hxy.right, baseChange_negY]]
    · simpa only [add_some hxy, ← baseChange_addX, ← baseChange_addY, ← baseChange_slope] using!
        (add_some fun h ↦ hxy ⟨f.injective h.1, f.injective (W'.baseChange_negY f .. ▸ h).2⟩).symm
/-
**WeierstrassCurve.Affine.Point.map_zero** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Affine.Point`。
形式化陈述：map_zero : map f (0 : (W'⁄F).Point) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_zero : map f (0 : (W'⁄F).Point) = 0 :=
  rfl
/-
**WeierstrassCurve.Affine.Point.map_some** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Affine.Point`。
形式化陈述：map_some {x y : F} (h : (W'⁄F).Nonsingular x y) : map f (some _ _ h) = som
e _ _ ((W'.baseChange_nonsingular f.injective ..).mpr h)
参数：h : (W'⁄F).Nonsingular x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_some {x y : F} (h : (W'⁄F).Nonsingular x y) :
    map f (some _ _ h) = some _ _ ((W'.baseChange_nonsingular f.injective ..).mpr h) :=
  rfl
/-
**WeierstrassCurve.Affine.Point.map_id** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCur
ve.Affine.Point`。
形式化陈述：map_id (P : (W'⁄F).Point) : map (Algebra.ofId F F) P = P
参数：P : (W'⁄F).Point。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma map_id (P : (W'⁄F).Point) : map (Algebra.ofId F F) P = P := by
  cases P <;> rfl
/-
**WeierstrassCurve.Affine.Point.map_map** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCu
rve.Affine.Point`。
形式化陈述：map_map (P : (W'⁄F).Point) : map g (map f P) = map (g.comp f) P
参数：P : (W'⁄F).Point。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma map_map (P : (W'⁄F).Point) : map g (map f P) = map (g.comp f) P := by
  cases P <;> rfl
/-
**WeierstrassCurve.Affine.Point.map_injective** 是 Mathlib 中的一个引理，位于命名空间 `Weierst
rassCurve.Affine.Point`。
形式化陈述：map_injective : Function.Injective map (W'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `WeierstrassCurve.Affine.Point.some.injEq`：∀ {R : Type r} [inst : CommRin
g R] {W' : WeierstrassCurve.Affine R} (x y : R) (h : W'.Nonsingular x y) (x_1 y_
1 : R)   (h_1 : W'.Nonsingular…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `WeierstrassCurve.Affine.Point.some.inj`：∀ {R : Type r} {inst : CommRing 
R} {W' : WeierstrassCurve.Affine R} {x y : R} {h : W'.Nonsingular x y} {x_1 y_1 
: R}   {h_1 : W'.Nonsingular…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma map_injective : Function.Injective <| map (W' := W') f := by
  rintro (_ | _) (_ | _) h
  any_goals contradiction
  · rfl
  · simpa only [some.injEq] using ⟨f.injective (some.inj h).left, f.injective (some.inj h).right⟩

variable (F K) in
/-- The group homomorphism on nonsingular points induced by the base change from `F` to `K`, where
`W` is defined over a subring of a ring `S`, and `F` and `K` are field extensions of `S`. -/
/-
**WeierstrassCurve.Affine.Point.baseChange** 是 Mathlib 中的一个缩写定义，位于命名空间 `Weierstr
assCurve.Affine.Point`。
形式化陈述：baseChange [Algebra F K] [IsScalarTower R F K] : (W'⁄F).Point ->+ (W'⁄K).P
oint
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group homomorphism on nonsingular points induced by the base change from `F`
 to `K`, where
`W` is defined over a subring of a ring `S`, and `F` and `K` are field extension
s of `S`.
-/
noncomputable abbrev baseChange [Algebra F K] [IsScalarTower R F K] :
    (W'⁄F).Point →+ (W'⁄K).Point :=
  map <| Algebra.ofId F K
/-
**WeierstrassCurve.Affine.Point.map_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `Weiers
trassCurve.Affine.Point`。
形式化陈述：map_baseChange [Algebra F K] [IsScalarTower R F K] [Algebra F L] [IsScalar
Tower R F L] (f : K ->ₐ[F] L) (P : (W'⁄F).Point) : map f (baseChange F K P) = ba
seChange F L P
参数：f : K ->ₐ[F] L；P : (W'⁄F).Point。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.subsingleton`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Co
mmSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring 
B] [inst_…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `WeierstrassCurve.Affine.Point.map_map`：map_map (P : (W'⁄F).Point) : map 
g (map f P) = map (g.comp f) P
-/
lemma map_baseChange [Algebra F K] [IsScalarTower R F K] [Algebra F L] [IsScalarTower R F L]
    (f : K →ₐ[F] L) (P : (W'⁄F).Point) : map f (baseChange F K P) = baseChange F L P := by
  have : Subsingleton (F →ₐ[F] L) := inferInstance
  convert! map_map (Algebra.ofId F K) f P

end Point

/-!
### The x-coordinate map to ℙ¹

We define the map from points on an affine Weierstrass curve over `R` to the projective line
by producing a coordinate vector in `Fin 2 → R` that represents the projective point.
-/

namespace Point

/-- This map sends a point `P` on a Weierstrass curve `W'` in affine coordinates
to a representative of its image on ℙ¹ under the x-coordinate map.
We take `![1, 0]` for the point at infinity and `![x, 1]`,
where `x` is the x-coordinate of `P`, for an affine point.

We define it in the general setting of a commutative base ring, even though the definition
of points in this setting is not really correct. For Weierstrass curves over fields, this
gives the correct notion. -/
/-
**WeierstrassCurve.Affine.Point.xRep** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve
.Affine.Point`。
形式化陈述：{R : Type r} → [inst : CommRing R] → {W' : WeierstrassCurve.Affine R} → W'
.Point → Fin 2 → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This map sends a point `P` on a Weierstrass curve `W'` in affine coordinates
to a representative of its image on ℙ¹ under the x-coordinate map.
We take `![1, 0]` for the point at infinity and `![x, 1]`,
where `x` is the x-coordinate of `P`, for an affine point.

We define it in the general setting of a commutative base ring, even though the 
definition
of points in this setting is not really correct. For Weierstrass curves over fie
lds, this
gives the correct notion.
-/
noncomputable def xRep : W'.Point → Fin 2 → R
  | 0 => ![1, 0]
  | some x _ _ => ![x, 1]

@[simp]
/-
**WeierstrassCurve.Affine.Point.xRep_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Affine.Point`。
形式化陈述：xRep_zero : (0 : W'.Point).xRep = ![1, 0]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma xRep_zero : (0 : W'.Point).xRep = ![1, 0] :=
  rfl

@[simp]
/-
**WeierstrassCurve.Affine.Point.xRep_some** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.Affine.Point`。
形式化陈述：xRep_some {x y : R} (h : W'.Nonsingular x y) : (some x y h).xRep = ![x, 1]
参数：h : W'.Nonsingular x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma xRep_some {x y : R} (h : W'.Nonsingular x y) : (some x y h).xRep = ![x, 1] :=
  rfl
/-
**WeierstrassCurve.Affine.Point.xRep_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve.Affine.Point`。
形式化陈述：xRep_ne_zero [Nontrivial R] (P : W'.Point) : P.xRep != 0
参数：P : W'.Point。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma xRep_ne_zero [Nontrivial R] (P : W'.Point) : P.xRep ≠ 0 := by
  cases P <;> simp [xRep]

@[simp]
/-
**WeierstrassCurve.Affine.Point.xRep_neg** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.Affine.Point`。
形式化陈述：xRep_neg (P : W'.Point) : (-P).xRep = P.xRep
参数：P : W'.Point。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma xRep_neg (P : W'.Point) : (-P).xRep = P.xRep := by
  cases P <;> simp [← zero_def]

-- The following lemmas need a field as base ring.
/-
**WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep** 是 Mathlib 中的一个引理，
位于命名空间 `WeierstrassCurve.Affine.Point`。
形式化陈述：eq_or_eq_neg_of_xRep_eq_xRep {P Q : W.Point} (h : P.xRep = Q.xRep) : P = Q
 ∨ P = -Q
参数：h : P.xRep = Q.xRep。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WeierstrassCurve.Affine.Point.X_eq_iff`：X_eq_iff {x₁ y₁ x₂ y₂ : F} {h₁ :
 W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} : x₁ = x₂ ↔ some x₁ y₁ h₁ = som
e x₂ y₂ h₂ ∨ some x₁ y₁ h₁ =…
-/
lemma eq_or_eq_neg_of_xRep_eq_xRep {P Q : W.Point} (h : P.xRep = Q.xRep) : P = Q ∨ P = -Q := by
  match P, Q with
  | 0, 0 => exact .inl rfl
  | 0, some .. => simp [xRep] at h
  | some .., 0 => simp [xRep] at h
  | some x₁ .., some x₂ .. =>
    simp only [xRep, Matrix.vecCons_inj, and_true] at h
    exact X_eq_iff.mp h
/-
**WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.Affine.Point`。
形式化陈述：xRep_eq_xRep_iff {P Q : W.Point} : P.xRep = Q.xRep ↔ P = Q ∨ P = -Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep`：eq_or_eq_neg
_of_xRep_eq_xRep {P Q : W.Point} (h : P.xRep = Q.xRep) : P = Q ∨ P = -Q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeierstrassCurve.Affine.Point.xRep_neg`：xRep_neg (P : W'.Point) : (-P).x
Rep = P.xRep
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma xRep_eq_xRep_iff {P Q : W.Point} : P.xRep = Q.xRep ↔ P = Q ∨ P = -Q := by
  refine ⟨eq_or_eq_neg_of_xRep_eq_xRep, fun H ↦ ?_⟩
  rcases H with rfl | rfl <;> simp

end Point

end Affine

end WeierstrassCurve

