/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Equivalent power-multiplicative norms

In this file, we prove [BGR, Proposition 3.1.5/1][bosch-guntzer-remmert]: if `R` is a normed
commutative ring and `f₁` and `f₂` are two power-multiplicative `R`-algebra norms on `S`, then if
`f₁` and `f₂` are equivalent on every subring `R[y]` for `y : S`, it follows that `f₁ = f₂`.

## Main Results
* `eq_of_powMul_faithful` : the proof of [BGR, Proposition 3.1.5/1][bosch-guntzer-remmert].

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

norm, equivalent, power-multiplicative
-/

public section

open Filter Real Algebra
open scoped Topology

/-- If `f : α →+* β` is bounded with respect to a ring seminorm `nα` on `α` and a
  power-multiplicative function `nβ : β → ℝ`, then `∀ x : α, nβ (f x) ≤ nα x`. -/
/-
**contraction_of_isPowMul_of_boundedWrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contraction_of_isPowMul_of_boundedWrt {F : Type*} {α : outParam (Type*)} [
Ring α] [FunLike F α Real] [RingSeminormClass F α Real] {β : Type*} [Ring β] (nα
 : F) {nβ : β -> Real} (hβ : IsPowMul nβ) {f : α ->+* β} (hf : f.IsBoundedWrt nα
 nβ) (x : α) : nβ (f x) <= nα x
参数：Type*；nα : F；hβ : IsPowMul nβ；hf : f.IsBoundedWrt nα nβ；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuousAt_const_rpow`：continuousAt_const_rpow {a b : Real} (h : 
a != 0) : ContinuousAt (a ^ ·) b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `tendsto_const_div_atTop_nhds_zero_nat`：tendsto_const_div_atTop_nhds_zero
_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [Continu
ousSMul Rat>=0 𝕜] [Continuo…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNRat.instContinuousSMulOfIsScalarTowerOfRat`：∀ {R : Type u_1} [inst : T
opologicalSpace R] [inst_1 : MulAction ℚ R] [inst_2 : MulAction ℚ≥0 R] [IsScalar
Tower ℚ≥0 ℚ R]   [ContinuousSMul ℚ…
· 使用定理 `NNRat.instContinuousSMulRatReal`：ContinuousSMul ℚ ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : α →+* β` is bounded with respect to a ring seminorm `nα` on `α` and a
  power-multiplicative function `nβ : β → ℝ`, then `∀ x : α, nβ (f x) ≤ nα x`.
-/
theorem contraction_of_isPowMul_of_boundedWrt {F : Type*} {α : outParam (Type*)} [Ring α]
    [FunLike F α ℝ] [RingSeminormClass F α ℝ] {β : Type*} [Ring β] (nα : F) {nβ : β → ℝ}
    (hβ : IsPowMul nβ) {f : α →+* β} (hf : f.IsBoundedWrt nα nβ) (x : α) : nβ (f x) ≤ nα x := by
  obtain ⟨C, hC0, hC⟩ := hf
  have hlim : Tendsto (fun n : ℕ => C ^ (1 / (n : ℝ)) * nα x) atTop (𝓝 (nα x)) := by
    nth_rewrite 2 [← one_mul (nα x)]
    exact ((rpow_zero C ▸ ContinuousAt.tendsto (continuousAt_const_rpow (ne_of_gt hC0))).comp
      (tendsto_const_div_atTop_nhds_zero_nat 1)).mul tendsto_const_nhds
  apply ge_of_tendsto hlim
  simp only [eventually_atTop]
  use 1
  intro n hn
  have h : (C ^ (1 / n : ℝ)) ^ n = C := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
    rw [← rpow_natCast, ← rpow_mul hC0.le, one_div, inv_mul_cancel₀ hn0, rpow_one]
  apply le_of_pow_le_pow_left₀ (ne_of_gt hn) (by positivity)
  · rw [mul_pow, h, ← hβ _ hn, ← map_pow]
    apply le_trans (hC (x ^ n))
    rw [mul_le_mul_iff_right₀ hC0]
    exact map_pow_le_pow _ _ (Nat.one_le_iff_ne_zero.mp hn)

/-- Given a bounded `f : α →+* β` between seminormed rings, is the seminorm on `β` is
  power-multiplicative, then `f` is a contraction. -/
/-
**contraction_of_isPowMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contraction_of_isPowMul {α β : Type*} [SeminormedRing α] [SeminormedRing β
] (hβ : IsPowMul (norm : β -> Real)) {f : α ->+* β} (hf : f.IsBounded) (x : α) :
 norm (f x) <= norm x
参数：hβ : IsPowMul (norm : β -> Real)；hf : f.IsBounded；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contraction_of_isPowMul_of_boundedWrt`：contraction_of_isPowMul_of_bounde
dWrt {F : Type*} {α : outParam (Type*)} [Ring α] [FunLike F α Real] [RingSeminor
mClass F α Real] {β : Type*…

--- 原说明 ---
Given a bounded `f : α →+* β` between seminormed rings, is the seminorm on `β` i
s
  power-multiplicative, then `f` is a contraction.
-/
theorem contraction_of_isPowMul {α β : Type*} [SeminormedRing α] [SeminormedRing β]
    (hβ : IsPowMul (norm : β → ℝ)) {f : α →+* β} (hf : f.IsBounded) (x : α) : norm (f x) ≤ norm x :=
  contraction_of_isPowMul_of_boundedWrt (SeminormedRing.toRingSeminorm α) hβ hf x

/-- Given two power-multiplicative ring seminorms `f, g` on `α`, if `f` is bounded by a positive
  multiple of `g` and vice versa, then `f = g`. -/
/-
**eq_seminorms** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_seminorms {F : Type*} {α : outParam (Type*)} [Ring α] [FunLike F α Real
] [RingSeminormClass F α Real] {f g : F} (hfpm : IsPowMul f) (hgpm : IsPowMul g)
 (hfg : exists (r : Real) (_ : 0 < r), forall a : α, f a <= r * g a) (hgf : exis
ts (r : Real) (_ : 0 < r), forall a : α, g a <= r * f a) : f = g
参数：Type*；hfpm : IsPowMul f；hgpm : IsPowMul g；hfg : exists (r : Real) (_ : 0 < r)
, forall a : α, f a <= r * g a；hgf : exists (r : Real) (_ : 0 < r), forall a : α
, g a <= r * f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `contraction_of_isPowMul_of_boundedWrt`：contraction_of_isPowMul_of_bounde
dWrt {F : Type*} {α : outParam (Type*)} [Ring α] [FunLike F α Real] [RingSeminor
mClass F α Real] {β : Type*…

--- 原说明 ---
Given two power-multiplicative ring seminorms `f, g` on `α`, if `f` is bounded b
y a positive
  multiple of `g` and vice versa, then `f = g`.
-/
theorem eq_seminorms {F : Type*} {α : outParam (Type*)} [Ring α] [FunLike F α ℝ]
    [RingSeminormClass F α ℝ] {f g : F} (hfpm : IsPowMul f) (hgpm : IsPowMul g)
    (hfg : ∃ (r : ℝ) (_ : 0 < r), ∀ a : α, f a ≤ r * g a)
    (hgf : ∃ (r : ℝ) (_ : 0 < r), ∀ a : α, g a ≤ r * f a) : f = g := by
  obtain ⟨r, hr0, hr⟩ := hfg
  obtain ⟨s, hs0, hs⟩ := hgf
  have hle : RingHom.IsBoundedWrt f g (RingHom.id _) := ⟨s, hs0, hs⟩
  have hge : RingHom.IsBoundedWrt g f (RingHom.id _) := ⟨r, hr0, hr⟩
  rw [← Function.Injective.eq_iff DFunLike.coe_injective]
  ext x
  exact le_antisymm (contraction_of_isPowMul_of_boundedWrt g hfpm hge x)
    (contraction_of_isPowMul_of_boundedWrt f hgpm hle x)

variable {R S : Type*} [NormedCommRing R] [CommRing S] [Algebra R S]

/-- If `R` is a normed commutative ring and `f₁` and `f₂` are two power-multiplicative `R`-algebra
  norms on `S`, then if `f₁` and `f₂` are equivalent on every subring `R[y]` for `y : S`, it
  follows that `f₁ = f₂` [BGR, Proposition 3.1.5/1][bosch-guntzer-remmert]. -/
/-
**eq_of_powMul_faithful** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_powMul_faithful (f₁ : AlgebraNorm R S) (hf₁_pm : IsPowMul f₁) (f₂ : 
AlgebraNorm R S) (hf₂_pm : IsPowMul f₂) (h_eq : forall y : S, exists (C₁ C₂ : Re
al) (_ : 0 < C₁) (_ : 0 < C₂), forall x : R[y], f₁ x.val <= C₁ * f₂ x.val ∧ f₂ x
.val <= C₂ * f₁ x.val) : f₁ = f₂
参数：f₁ : AlgebraNorm R S；hf₁_pm : IsPowMul f₁；f₂ : AlgebraNorm R S；hf₂_pm : IsPow
Mul f₂；h_eq : forall y : S, exists (C₁ C₂ : Real) (_ : 0 < C₁) (_ : 0 < C₂), for
all x : R[y], f₁ x.val <= C₁ * f₂ x.val ∧ f₂ x.val <= C₂ * f₁ x.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraNorm.ext`：ext {p q : AlgebraNorm R S} : (forall x, p x = q x) -> 
p = q
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsPowMul.restriction`：IsPowMul.restriction {R S : Type*} [CommRing R] [R
ing S] [Algebra R S] (A : Subalgebra R S) {f : S -> Real} (hf_pm : IsPowMul f) :
 IsPowMul …
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_seminorms`：eq_seminorms {F : Type*} {α : outParam (Type*)} [Ring α] [
FunLike F α Real] [RingSeminormClass F α Real] {f g : F} (hfpm : IsPowMul f) (hg
pm…
· 使用定理 `RingNormClass.toRingSeminormClass`：∀ {F : Type u_7} {α : outParam (Type 
u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {inst_1 : Sem
iring β} {inst_2 : Part…
· 使用定理 `AlgebraNormClass.toRingNormClass`：∀ {F : Type u_1} {R : outParam (Type u
_2)} {inst : SeminormedCommRing R} {S : outParam (Type u_3)} {inst_1 : Ring S}  
 {inst_2 : Algebra R S…

--- 原说明 ---
If `R` is a normed commutative ring and `f₁` and `f₂` are two power-multiplicati
ve `R`-algebra
  norms on `S`, then if `f₁` and `f₂` are equivalent on every subring `R[y]` for
 `y : S`, it
  follows that `f₁ = f₂` [BGR, Proposition 3.1.5/1][bosch-guntzer-remmert].
-/
theorem eq_of_powMul_faithful (f₁ : AlgebraNorm R S) (hf₁_pm : IsPowMul f₁) (f₂ : AlgebraNorm R S)
    (hf₂_pm : IsPowMul f₂)
    (h_eq : ∀ y : S, ∃ (C₁ C₂ : ℝ) (_ : 0 < C₁) (_ : 0 < C₂),
      ∀ x : R[y], f₁ x.val ≤ C₁ * f₂ x.val ∧ f₂ x.val ≤ C₂ * f₁ x.val) :
    f₁ = f₂ := by
  ext x
  set g₁ : AlgebraNorm R R[(x : S)] := AlgebraNorm.restriction _ f₁
  set g₂ : AlgebraNorm R R[(x : S)] := AlgebraNorm.restriction _ f₂
  have hg₁_pm : IsPowMul g₁ := IsPowMul.restriction _ hf₁_pm
  have hg₂_pm : IsPowMul g₂ := IsPowMul.restriction _ hf₂_pm
  let y : R[(x : S)] := ⟨x, self_mem_adjoin_singleton R x⟩
  have hy : x = y.val := rfl
  have h1 : f₁ y.val = g₁ y := rfl
  have h2 : f₂ y.val = g₂ y := rfl
  obtain ⟨C₁, C₂, hC₁_pos, hC₂_pos, hC⟩ := h_eq x
  obtain ⟨hC₁, hC₂⟩ := forall_and.mp hC
  rw [hy, h1, h2, eq_seminorms hg₁_pm hg₂_pm ⟨C₁, hC₁_pos, hC₁⟩ ⟨C₂, hC₂_pos, hC₂⟩]
